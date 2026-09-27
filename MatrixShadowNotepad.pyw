"""
Matrix Shadow Notepad v6 - huge-file virtual notepad.

Core idea:
- The real file stays asleep on disk.
- The viewport renders only a small byte window.
- Edits are stored in a piece table / patch journal, not by loading the full file.
- Save writes a streamed merged file.

Install:
    python -m pip install PySide6
Run:
    python MatrixShadowNotepad.py

V6 keeps the v4/v5 internal zero-copy clipboard and fixes the replace-in-document crash by applying collected replacements in one linear batch piece-table rebuild, not thousands of individual replace calls:
- Mouse selection / marking text
- Copy / cut / paste / delete / backspace / typing
- Ctrl+A, Ctrl+C, Ctrl+X, Ctrl+V, Ctrl+S
- Internal app clipboard: multi-GB copy/paste inside Matrix Shadow without reading it into Windows clipboard
- Search all/count with sampled positions and optional future position-map thinking
- Human line parser: accepts 2000000000, 2b, 2 billion, 1.5m
- Apply replace-all as pending edits using one batch rebuild when the match count is sane; huge jobs still stream safely
- Token-cost analysis for ideas like 01001 -> 2
- Right-click menu
- Save / Save As using streamed piece-table merge
- Search current virtual document, including unsaved edits
- Replace-all current virtual document to a new file

Honest limit:
- This is a byte-oriented huge-file editor. UTF-8 display is supported, but the safest editing mode
  for arbitrary giant files is latin-1 / byte-safe mode because each screen character maps to one byte.
- Multi-GB selections are copied to the internal Matrix Shadow clipboard by reference. Windows clipboard receives a tiny marker, and Paste inside this app expands the internal reference.
"""

from __future__ import annotations

import bisect
import os
import sys
import time
import tempfile
from collections import OrderedDict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Deque, Iterable, List, Optional, Sequence, Tuple

try:
    from PySide6.QtCore import QObject, QRect, QRunnable, QThread, QThreadPool, Qt, Signal, Slot
    from PySide6.QtGui import QAction, QColor, QFont, QFontMetrics, QKeySequence, QPainter, QPen
    from PySide6.QtWidgets import (
        QApplication,
        QAbstractScrollArea,
        QCheckBox,
        QComboBox,
        QFileDialog,
        QGridLayout,
        QHBoxLayout,
        QLabel,
        QLineEdit,
        QMainWindow,
        QMenu,
        QMessageBox,
        QPushButton,
        QProgressBar,
        QSizePolicy,
        QStatusBar,
        QTextEdit,
        QToolBar,
        QVBoxLayout,
        QWidget,
    )
except Exception as exc:  # pragma: no cover
    print("PySide6 is required for Matrix Shadow Notepad.")
    print("Install it with: python -m pip install PySide6")
    print(f"Import error: {exc}")
    raise


APP_NAME = "Matrix Shadow Notepad v6"
SCROLLBAR_UNITS = 1_000_000       # UI-only; real offsets are Python ints.
DEFAULT_CHUNK_BYTES = 1 * 1024 * 1024
MAX_CACHE_CHUNKS = 32
WORKER_CHUNK_BYTES = 8 * 1024 * 1024
SPARSE_LINE_STEP = 100_000
CLIPBOARD_SAFE_BYTES = 64 * 1024 * 1024
INTERNAL_CLIPBOARD_MARKER = "[MatrixShadowInternalClipboard:v6]"
MAX_POSITION_SAMPLES = 2000
MAX_PENDING_REPLACE_MATCHES = 100000


# -----------------------------------------------------------------------------
# small helpers
# -----------------------------------------------------------------------------

def clamp(n: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, n))


def human_bytes(n: int) -> str:
    units = ["B", "KB", "MB", "GB", "TB", "PB"]
    f = float(n)
    for u in units:
        if abs(f) < 1024 or u == units[-1]:
            return f"{f:,.2f} {u}" if u != "B" else f"{n:,} B"
        f /= 1024.0
    return f"{n:,} B"



def parse_human_int(text: str) -> int:
    """Parse large human numbers: 2,000,000,000 / 2b / 2 billion / 1.5m."""
    raw = (text or "").strip().lower().replace(",", "").replace("_", "")
    if not raw:
        raise ValueError("empty number")
    # Keep a compact version too, so "2 billion" and "2b" both work.
    compact = raw.replace(" ", "")
    multipliers = [
        ("trillion", 1_000_000_000_000), ("tn", 1_000_000_000_000), ("t", 1_000_000_000_000),
        ("billion", 1_000_000_000), ("bn", 1_000_000_000), ("b", 1_000_000_000),
        ("million", 1_000_000), ("mn", 1_000_000), ("m", 1_000_000),
        ("thousand", 1_000), ("k", 1_000),
    ]
    for suffix, mul in multipliers:
        if compact.endswith(suffix):
            num = compact[: -len(suffix)]
            if not num:
                raise ValueError("missing number before suffix")
            return int(float(num) * mul)
    return int(compact, 0)

def safe_encode(text: str, encoding: str) -> bytes:
    if encoding.lower() in ("latin-1", "latin1", "byte-safe", "bytes"):
        return text.encode("latin-1", errors="replace")
    return text.encode(encoding, errors="replace")


def safe_decode_bytes(data: bytes, encoding: str) -> str:
    if encoding.lower() in ("latin-1", "latin1", "byte-safe", "bytes"):
        return data.decode("latin-1", errors="replace")
    return data.decode(encoding, errors="replace")


def copy_file_range(src, out, start: int, length: int, chunk_size: int = WORKER_CHUNK_BYTES) -> None:
    src.seek(start)
    remaining = length
    while remaining > 0:
        chunk = src.read(min(chunk_size, remaining))
        if not chunk:
            break
        out.write(chunk)
        remaining -= len(chunk)


# -----------------------------------------------------------------------------
# Piece table: the actual editor core.
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class Piece:
    # source can be:
    #   "orig"        -> current document original_path
    #   "add"         -> current document add_buffer
    #   "file:<path>" -> immutable bytes from another/on-disk file, used by internal clipboard paste
    #   "clip"        -> bytes inside ClipboardPayload.clip_buffer before paste conversion
    source: str
    start: int
    length: int


@dataclass
class ClipboardPayload:
    pieces: List[Piece]
    clip_buffer: bytes
    size: int
    source_label: str


def piece_file_path(source: str, original_path: str) -> Optional[str]:
    if source == "orig":
        return original_path
    if source.startswith("file:"):
        return source[5:]
    return None


def read_piece_bytes(original_path: str, add_buffer: bytes | bytearray, piece: Piece, inner: int, take: int) -> bytes:
    if take <= 0:
        return b""
    if piece.source == "add":
        return bytes(add_buffer[piece.start + inner:piece.start + inner + take])
    path = piece_file_path(piece.source, original_path)
    if path:
        with open(path, "rb", buffering=0) as f:
            f.seek(piece.start + inner)
            return f.read(take)
    return b""


class PieceTable:
    """Memory-light editable document over an original file plus an append-only add buffer."""

    def __init__(self) -> None:
        self.original_path: Optional[str] = None
        self.original_size: int = 0
        self.pieces: List[Piece] = []
        self.add_buffer = bytearray()
        self.generation = 0

    def open(self, path: str) -> None:
        self.original_path = path
        self.original_size = os.path.getsize(path)
        self.pieces = [Piece("orig", 0, self.original_size)] if self.original_size else []
        self.add_buffer.clear()
        self.generation += 1

    def new_empty(self) -> None:
        """Start a blank document so typing works immediately without opening a file."""
        f = tempfile.NamedTemporaryFile(delete=False)
        f.close()
        self.original_path = f.name
        self.original_size = 0
        self.pieces = []
        self.add_buffer.clear()
        self.generation += 1

    @property
    def size(self) -> int:
        return sum(p.length for p in self.pieces)

    @property
    def has_edits(self) -> bool:
        return bool(self.add_buffer) or self.size != self.original_size or len(self.pieces) != (1 if self.original_size else 0)

    def snapshot(self) -> Tuple[str, List[Piece], bytes, int]:
        if not self.original_path:
            raise RuntimeError("No file open")
        return self.original_path, list(self.pieces), bytes(self.add_buffer), self.size

    def pieces_for_range(self, start: int, end: int) -> List[Piece]:
        """Return source-level pieces covering virtual [start, end) without copying bytes."""
        start = clamp(start, 0, self.size)
        end = clamp(end, start, self.size)
        if end <= start:
            return []
        idx, inner = self._locate(start)
        remaining = end - start
        out: List[Piece] = []
        while remaining > 0 and idx < len(self.pieces):
            p = self.pieces[idx]
            take = min(remaining, p.length - inner)
            if take > 0:
                out.append(Piece(p.source, p.start + inner, take))
                remaining -= take
            idx += 1
            inner = 0
        return out

    def make_clipboard_payload(self, start: int, end: int, label: str = "selection") -> ClipboardPayload:
        """Create an internal clipboard payload. Large original-file ranges stay as file references."""
        raw = self.pieces_for_range(start, end)
        clip_buf = bytearray()
        clip_pieces: List[Piece] = []
        for p in raw:
            if p.source == "orig":
                if not self.original_path:
                    continue
                clip_pieces.append(Piece("file:" + self.original_path, p.start, p.length))
            elif p.source == "add":
                cs = len(clip_buf)
                clip_buf.extend(self.add_buffer[p.start:p.start + p.length])
                clip_pieces.append(Piece("clip", cs, p.length))
            elif p.source.startswith("file:"):
                clip_pieces.append(p)
            elif p.source == "clip":
                # Should not normally live in the document after paste conversion, but keep safe.
                continue
        return ClipboardPayload(clip_pieces, bytes(clip_buf), max(0, end - start), label)

    def replace_with_pieces(self, start: int, end: int, new_pieces: Sequence[Piece]) -> None:
        start = clamp(start, 0, self.size)
        end = clamp(end, start, self.size)
        right = self._split_at(end)
        left = self._split_at(start)
        self.pieces[left:right] = [p for p in new_pieces if p.length > 0]
        self._compact_neighbors()
        self.generation += 1

    def paste_clipboard_payload(self, start: int, end: int, payload: ClipboardPayload) -> int:
        """Paste internal clipboard without reading huge file-backed ranges into RAM."""
        pieces: List[Piece] = []
        for p in payload.pieces:
            if p.source == "clip":
                data = payload.clip_buffer[p.start:p.start + p.length]
                add_start = len(self.add_buffer)
                self.add_buffer.extend(data)
                pieces.append(Piece("add", add_start, len(data)))
            elif p.source == "add":
                # Defensive path: copy from our current add buffer.
                data = self.add_buffer[p.start:p.start + p.length]
                add_start = len(self.add_buffer)
                self.add_buffer.extend(data)
                pieces.append(Piece("add", add_start, len(data)))
            elif p.source == "orig":
                if self.original_path:
                    pieces.append(Piece("file:" + self.original_path, p.start, p.length))
            elif p.source.startswith("file:"):
                pieces.append(p)
        self.replace_with_pieces(start, end, pieces)
        return sum(p.length for p in pieces)

    def _locate(self, pos: int) -> Tuple[int, int]:
        """Return (piece index, inner offset) for a virtual position boundary."""
        pos = clamp(pos, 0, self.size)
        acc = 0
        for i, p in enumerate(self.pieces):
            nxt = acc + p.length
            if pos < nxt:
                return i, pos - acc
            if pos == nxt:
                return i + 1, 0
            acc = nxt
        return len(self.pieces), 0

    def _split_at(self, pos: int) -> int:
        """Ensure a piece boundary exists at virtual pos; return insertion index."""
        pos = clamp(pos, 0, self.size)
        idx, inner = self._locate(pos)
        if idx >= len(self.pieces):
            return len(self.pieces)
        if inner == 0:
            return idx
        p = self.pieces[idx]
        left = Piece(p.source, p.start, inner)
        right = Piece(p.source, p.start + inner, p.length - inner)
        self.pieces[idx:idx + 1] = [left, right]
        return idx + 1

    def replace(self, start: int, end: int, data: bytes) -> None:
        start = clamp(start, 0, self.size)
        end = clamp(end, start, self.size)
        right = self._split_at(end)
        left = self._split_at(start)
        new_pieces: List[Piece] = []
        if data:
            add_start = len(self.add_buffer)
            self.add_buffer.extend(data)
            new_pieces.append(Piece("add", add_start, len(data)))
        self.pieces[left:right] = new_pieces
        self._compact_neighbors()
        self.generation += 1

    def replace_many_at_positions(self, positions: Sequence[int], pattern_len: int, replacement: bytes) -> int:
        """Apply many non-overlapping replacements in one linear piece-table rebuild.

        V5 applied replacements by calling replace() thousands of times from the end.
        That was correct but too expensive for 30k+ matches because every call split and
        compacted the piece table again. V6 builds the final piece list once.
        The positions must refer to the document state before this batch operation.
        """
        if pattern_len <= 0:
            raise ValueError("pattern_len must be positive")
        if not positions:
            return 0

        old_pieces = list(self.pieces)
        old_size = sum(p.length for p in old_pieces)
        # Existing prefix table gives O(log pieces) range starts and linear copy inside each range.
        prefix = [0]
        for p in old_pieces:
            prefix.append(prefix[-1] + p.length)

        def append_range(out: List[Piece], start: int, end: int) -> None:
            start = clamp(start, 0, old_size)
            end = clamp(end, start, old_size)
            if end <= start:
                return
            idx = max(0, bisect.bisect_right(prefix, start) - 1)
            cur = start
            while cur < end and idx < len(old_pieces):
                p = old_pieces[idx]
                piece_start = prefix[idx]
                inner = cur - piece_start
                if inner < 0:
                    inner = 0
                take = min(end - cur, p.length - inner)
                if take > 0:
                    out.append(Piece(p.source, p.start + inner, take))
                    cur += take
                idx += 1

        clean_positions: List[int] = []
        last_end = 0
        for raw in sorted(int(x) for x in positions):
            pos = clamp(raw, 0, old_size)
            if pos < last_end:
                # Defensive: skip overlapping duplicates. The finder normally prevents this.
                continue
            if pos + pattern_len > old_size:
                continue
            clean_positions.append(pos)
            last_end = pos + pattern_len

        if not clean_positions:
            return 0

        repl_piece: Optional[Piece] = None
        if replacement:
            repl_start = len(self.add_buffer)
            self.add_buffer.extend(replacement)
            repl_piece = Piece("add", repl_start, len(replacement))

        new_pieces: List[Piece] = []
        cursor = 0
        for pos in clean_positions:
            append_range(new_pieces, cursor, pos)
            if repl_piece is not None:
                # Reuse the same add-buffer bytes for every replacement.
                # This avoids adding 34,825 separate copies of "@" to RAM.
                new_pieces.append(repl_piece)
            cursor = pos + pattern_len
        append_range(new_pieces, cursor, old_size)

        self.pieces = [p for p in new_pieces if p.length > 0]
        self._compact_neighbors()
        self.generation += 1
        return len(clean_positions)

    def _compact_neighbors(self) -> None:
        if not self.pieces:
            return
        out: List[Piece] = [self.pieces[0]]
        for p in self.pieces[1:]:
            prev = out[-1]
            if prev.source == p.source and prev.start + prev.length == p.start:
                out[-1] = Piece(prev.source, prev.start, prev.length + p.length)
            elif p.length > 0:
                out.append(p)
        self.pieces = out

    def read_at(self, offset: int, length: int) -> bytes:
        if not self.original_path or length <= 0:
            return b""
        offset = clamp(offset, 0, self.size)
        length = min(length, max(0, self.size - offset))
        if length <= 0:
            return b""
        out = bytearray()
        idx, inner = self._locate(offset)
        remaining = length
        while remaining > 0 and idx < len(self.pieces):
            p = self.pieces[idx]
            take = min(remaining, p.length - inner)
            if take > 0:
                data = read_piece_bytes(self.original_path, self.add_buffer, p, inner, take)
                if not data:
                    break
                out.extend(data)
                remaining -= len(data)
            idx += 1
            inner = 0
        return bytes(out)


# Worker-side helpers use immutable snapshots, so background tasks are not touching the UI object.

def iter_piece_chunks(original_path: str, pieces: Sequence[Piece], add_buffer: bytes, chunk_size: int = WORKER_CHUNK_BYTES) -> Iterable[Tuple[int, bytes]]:
    virtual = 0
    handles = {}
    try:
        for p in pieces:
            remaining = p.length
            inner = 0
            while remaining > 0:
                take = min(chunk_size, remaining)
                if p.source == "add":
                    data = add_buffer[p.start + inner:p.start + inner + take]
                else:
                    path = piece_file_path(p.source, original_path)
                    if not path:
                        break
                    f = handles.get(path)
                    if f is None:
                        f = open(path, "rb", buffering=0)
                        handles[path] = f
                    f.seek(p.start + inner)
                    data = f.read(take)
                if not data:
                    break
                yield virtual, data
                got = len(data)
                remaining -= got
                inner += got
                virtual += got
    finally:
        for f in handles.values():
            try:
                f.close()
            except Exception:
                pass


def read_snapshot_at(original_path: str, pieces: Sequence[Piece], add_buffer: bytes, total_size: int, offset: int, length: int) -> bytes:
    offset = clamp(offset, 0, total_size)
    length = min(length, max(0, total_size - offset))
    if length <= 0:
        return b""
    out = bytearray()
    acc = 0
    for p in pieces:
        if acc + p.length <= offset:
            acc += p.length
            continue
        inner = max(0, offset - acc)
        remaining_in_piece = p.length - inner
        take = min(length - len(out), remaining_in_piece)
        if take > 0:
            data = read_piece_bytes(original_path, add_buffer, p, inner, take)
            if not data:
                break
            out.extend(data)
        acc += p.length
        if len(out) >= length:
            break
    return bytes(out)


# -----------------------------------------------------------------------------
# Background workers
# -----------------------------------------------------------------------------

class DocSearchWorker(QThread):
    progress = Signal(int, str)
    found = Signal(object)
    done = Signal(bool, str)

    def __init__(self, snapshot: Tuple[str, List[Piece], bytes, int], pattern: bytes, start_offset: int, case_sensitive: bool):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.pattern = pattern
        self.start_offset = start_offset
        self.case_sensitive = case_sensitive
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def _search_range(self, begin: int, end: int) -> Optional[int]:
        if begin >= end:
            return None
        pat = self.pattern if self.case_sensitive else self.pattern.lower()
        overlap = max(0, len(pat) - 1)
        carry = b""
        pos = begin
        last_emit = time.monotonic()
        while pos < end and not self._cancel:
            chunk = read_snapshot_at(self.original_path, self.pieces, self.add_buffer, self.total_size, pos, min(WORKER_CHUNK_BYTES, end - pos))
            if not chunk:
                break
            data = carry + chunk
            search_data = data if self.case_sensitive else data.lower()
            base = pos - len(carry)
            idx = search_data.find(pat)
            if idx >= 0:
                absolute = base + idx
                if begin <= absolute < end:
                    return absolute
            carry = data[-overlap:] if overlap else b""
            pos += len(chunk)
            now = time.monotonic()
            if now - last_emit > 0.2:
                pct = int((pos / max(1, self.total_size)) * 100)
                self.progress.emit(clamp(pct, 0, 100), f"Searching virtual byte {pos:,}")
                last_emit = now
        return None

    def run(self) -> None:
        if not self.pattern:
            self.done.emit(False, "Empty search pattern.")
            return
        try:
            start = clamp(self.start_offset + 1, 0, self.total_size)
            result = self._search_range(start, self.total_size)
            if result is None and not self._cancel:
                result = self._search_range(0, min(start, self.total_size))
            if self._cancel:
                self.done.emit(False, "Search cancelled.")
            elif result is not None:
                self.found.emit(result)
                self.done.emit(True, f"Found at virtual byte {result:,}.")
            else:
                self.done.emit(False, "Pattern not found.")
        except Exception as exc:
            self.done.emit(False, f"Search failed: {exc}")


class SavePiecesWorker(QThread):
    progress = Signal(int, str)
    done = Signal(bool, str)

    def __init__(self, snapshot: Tuple[str, List[Piece], bytes, int], output_path: str):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.output_path = output_path
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        tmp_path = self.output_path + ".partial"
        written = 0
        try:
            with open(tmp_path, "wb", buffering=1024 * 1024) as out:
                for _, data in iter_piece_chunks(self.original_path, self.pieces, self.add_buffer):
                    if self._cancel:
                        self.done.emit(False, "Save cancelled. Partial file left for inspection.")
                        return
                    out.write(data)
                    written += len(data)
                    pct = int((written / max(1, self.total_size)) * 100)
                    self.progress.emit(clamp(pct, 0, 100), f"Saving merged document {written:,}/{self.total_size:,} bytes")
            if os.path.exists(self.output_path):
                os.remove(self.output_path)
            os.replace(tmp_path, self.output_path)
            self.done.emit(True, f"Saved streamed merged file: {self.output_path}")
        except Exception as exc:
            self.done.emit(False, f"Save failed: {exc}")


class ExportRangeWorker(QThread):
    progress = Signal(int, str)
    done = Signal(bool, str)

    def __init__(self, snapshot: Tuple[str, List[Piece], bytes, int], start: int, end: int, output_path: str):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.start = start
        self.end = end
        self.output_path = output_path
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        tmp_path = self.output_path + ".partial"
        wanted = max(0, self.end - self.start)
        written = 0
        try:
            with open(tmp_path, "wb", buffering=1024 * 1024) as out:
                pos = self.start
                while pos < self.end:
                    if self._cancel:
                        self.done.emit(False, "Export cancelled. Partial file left for inspection.")
                        return
                    data = read_snapshot_at(self.original_path, self.pieces, self.add_buffer, self.total_size, pos, min(WORKER_CHUNK_BYTES, self.end - pos))
                    if not data:
                        break
                    out.write(data)
                    pos += len(data)
                    written += len(data)
                    pct = int((written / max(1, wanted)) * 100)
                    self.progress.emit(clamp(pct, 0, 100), f"Exporting selection {written:,}/{wanted:,} bytes")
            if os.path.exists(self.output_path):
                os.remove(self.output_path)
            os.replace(tmp_path, self.output_path)
            self.done.emit(True, f"Exported selection to: {self.output_path}")
        except Exception as exc:
            self.done.emit(False, f"Export failed: {exc}")


class ReplaceAllToFileWorker(QThread):
    progress = Signal(int, str)
    done = Signal(bool, str)

    def __init__(self, snapshot: Tuple[str, List[Piece], bytes, int], output_path: str, pattern: bytes, replacement: bytes, case_sensitive: bool):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.output_path = output_path
        self.pattern = pattern
        self.replacement = replacement
        self.case_sensitive = case_sensitive
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        if not self.pattern:
            self.done.emit(False, "Empty find pattern; replace-all stopped.")
            return
        tmp_path = self.output_path + ".partial"
        written_input = 0
        output_count = 0
        tail_len = max(0, len(self.pattern) - 1)
        tail = b""
        pat = self.pattern if self.case_sensitive else self.pattern.lower()
        try:
            with open(tmp_path, "wb", buffering=1024 * 1024) as out:
                for _, chunk in iter_piece_chunks(self.original_path, self.pieces, self.add_buffer):
                    if self._cancel:
                        self.done.emit(False, "Replace-all cancelled. Partial file left for inspection.")
                        return
                    data = tail + chunk
                    if tail_len:
                        safe_len = max(0, len(data) - tail_len)
                        safe = data[:safe_len]
                        tail = data[safe_len:]
                    else:
                        safe = data
                        tail = b""
                    search_safe = safe if self.case_sensitive else safe.lower()
                    output_count += search_safe.count(pat)
                    if self.case_sensitive:
                        out.write(safe.replace(self.pattern, self.replacement))
                    else:
                        # Case-insensitive replacement while preserving stream behavior.
                        lower = search_safe
                        i = 0
                        while True:
                            j = lower.find(pat, i)
                            if j < 0:
                                out.write(safe[i:])
                                break
                            out.write(safe[i:j])
                            out.write(self.replacement)
                            i = j + len(self.pattern)
                    written_input += len(chunk)
                    pct = int((written_input / max(1, self.total_size)) * 100)
                    self.progress.emit(clamp(pct, 0, 100), f"Replace-all streaming {written_input:,}/{self.total_size:,} bytes")
                if tail:
                    search_tail = tail if self.case_sensitive else tail.lower()
                    output_count += search_tail.count(pat)
                    if self.case_sensitive:
                        out.write(tail.replace(self.pattern, self.replacement))
                    else:
                        i = 0
                        while True:
                            j = search_tail.find(pat, i)
                            if j < 0:
                                out.write(tail[i:])
                                break
                            out.write(tail[i:j])
                            out.write(self.replacement)
                            i = j + len(self.pattern)
            if os.path.exists(self.output_path):
                os.remove(self.output_path)
            os.replace(tmp_path, self.output_path)
            self.done.emit(True, f"Replace-all complete. {output_count:,} replacements written to {self.output_path}")
        except Exception as exc:
            self.done.emit(False, f"Replace-all failed: {exc}")



class FindAllWorker(QThread):
    """Stream the virtual document and count all matches without loading the document."""
    progress = Signal(int, str)
    done = Signal(bool, str, object, object)

    def __init__(
        self,
        snapshot: Tuple[str, List[Piece], bytes, int],
        pattern: bytes,
        case_sensitive: bool,
        max_samples: int = MAX_POSITION_SAMPLES,
        collect_limit: int = 0,
        stop_when_limit_exceeded: bool = False,
    ):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.pattern = pattern
        self.case_sensitive = case_sensitive
        self.max_samples = max_samples
        self.collect_limit = collect_limit
        self.stop_when_limit_exceeded = stop_when_limit_exceeded
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        if not self.pattern:
            self.done.emit(False, "Empty search pattern.", {"count": 0, "truncated": False}, [])
            return
        pat = self.pattern if self.case_sensitive else self.pattern.lower()
        overlap = max(0, len(pat) - 1)
        carry = b""
        count = 0
        samples: List[int] = []
        collected: List[int] = []
        absolute_done = 0
        last_emit = time.monotonic()
        truncated = False
        try:
            for virtual, chunk in iter_piece_chunks(self.original_path, self.pieces, self.add_buffer):
                if self._cancel:
                    self.done.emit(False, "Search-all cancelled.", {"count": count, "truncated": truncated}, samples)
                    return
                data = carry + chunk
                base = virtual - len(carry)
                # Hold the last pattern-1 bytes for cross-boundary matches.
                # Search the full data, but only accept starts that are safe;
                # otherwise a match ending inside the carry would be missed.
                if overlap:
                    safe_start_limit = max(0, len(data) - overlap)
                    carry = data[-overlap:]
                else:
                    safe_start_limit = len(data)
                    carry = b""
                search_data = data if self.case_sensitive else data.lower()
                i = 0
                while True:
                    j = search_data.find(pat, i)
                    if j < 0 or j >= safe_start_limit:
                        break
                    pos = base + j
                    count += 1
                    if len(samples) < self.max_samples:
                        samples.append(pos)
                    if self.collect_limit:
                        if len(collected) < self.collect_limit:
                            collected.append(pos)
                        else:
                            truncated = True
                            if self.stop_when_limit_exceeded:
                                msg = (
                                    f"Too many matches for pending in-document replace: more than {self.collect_limit:,}. "
                                    "Use streamed Replace to new file or a future replacement-map layer."
                                )
                                self.done.emit(False, msg, {"count": count, "truncated": True, "positions": collected}, samples)
                                return
                    i = j + max(1, len(pat))
                absolute_done = virtual + len(chunk)
                now = time.monotonic()
                if now - last_emit > 0.2:
                    pct = int((absolute_done / max(1, self.total_size)) * 100)
                    self.progress.emit(clamp(pct, 0, 100), f"Counting matches: {count:,} found so far at byte {absolute_done:,}")
                    last_emit = now
            # Final carry.
            if carry and not self._cancel:
                search_data = carry if self.case_sensitive else carry.lower()
                base = self.total_size - len(carry)
                i = 0
                while True:
                    j = search_data.find(pat, i)
                    if j < 0:
                        break
                    pos = base + j
                    count += 1
                    if len(samples) < self.max_samples:
                        samples.append(pos)
                    if self.collect_limit:
                        if len(collected) < self.collect_limit:
                            collected.append(pos)
                        else:
                            truncated = True
                            if self.stop_when_limit_exceeded:
                                msg = f"Too many matches for pending in-document replace: more than {self.collect_limit:,}."
                                self.done.emit(False, msg, {"count": count, "truncated": True, "positions": collected}, samples)
                                return
                    i = j + max(1, len(pat))
            meta = {"count": count, "truncated": truncated, "positions": collected}
            self.done.emit(True, f"Search-all complete: {count:,} matches.", meta, samples)
        except Exception as exc:
            self.done.emit(False, f"Search-all failed safely: {exc}", {"count": count, "truncated": truncated, "positions": collected}, samples)

class LineIndexWorker(QThread):
    progress = Signal(int, str)
    done = Signal(object, object, str)

    def __init__(self, snapshot: Tuple[str, List[Piece], bytes, int], step: int = SPARSE_LINE_STEP):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.step = step
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        try:
            records: List[Tuple[int, int]] = [(1, 0)]
            line_no = 1
            absolute = 0
            last_emit = time.monotonic()
            for _, chunk in iter_piece_chunks(self.original_path, self.pieces, self.add_buffer):
                if self._cancel:
                    break
                p = -1
                while True:
                    p = chunk.find(b"\n", p + 1)
                    if p < 0:
                        break
                    line_no += 1
                    if line_no % self.step == 0:
                        records.append((line_no, absolute + p + 1))
                absolute += len(chunk)
                now = time.monotonic()
                if now - last_emit > 0.2:
                    pct = int((absolute / max(1, self.total_size)) * 100)
                    self.progress.emit(clamp(pct, 0, 100), f"Indexing lines: {line_no:,} lines seen")
                    last_emit = now
            if self._cancel:
                self.done.emit(records, line_no, "Line indexing cancelled; partial index kept.")
            else:
                self.done.emit(records, line_no, f"Line index complete: {line_no:,} lines, {len(records):,} sparse records.")
        except Exception as exc:
            self.done.emit([], 0, f"Line indexing failed: {exc}")


class GoLineWorker(QThread):
    found = Signal(object, object)
    done = Signal(bool, str)

    def __init__(self, snapshot: Tuple[str, List[Piece], bytes, int], start_line: int, start_offset: int, target_line: int):
        super().__init__()
        self.original_path, self.pieces, self.add_buffer, self.total_size = snapshot
        self.start_line = start_line
        self.start_offset = start_offset
        self.target_line = target_line
        self._cancel = False

    def cancel(self) -> None:
        self._cancel = True

    def run(self) -> None:
        try:
            if self.target_line <= self.start_line:
                self.found.emit(self.start_offset, self.target_line)
                self.done.emit(True, f"Jumped to line {self.target_line:,}.")
                return
            line = self.start_line
            absolute = self.start_offset
            while absolute < self.total_size and not self._cancel:
                chunk = read_snapshot_at(self.original_path, self.pieces, self.add_buffer, self.total_size, absolute, WORKER_CHUNK_BYTES)
                if not chunk:
                    break
                p = -1
                while True:
                    p = chunk.find(b"\n", p + 1)
                    if p < 0:
                        break
                    line += 1
                    if line >= self.target_line:
                        offset = absolute + p + 1
                        self.found.emit(offset, line)
                        self.done.emit(True, f"Jumped to line {line:,}.")
                        return
                absolute += len(chunk)
            if self._cancel:
                self.done.emit(False, "Go-to-line cancelled.")
            else:
                self.done.emit(False, "Target line is past end of document.")
        except Exception as exc:
            self.done.emit(False, f"Go-to-line failed: {exc}")


# -----------------------------------------------------------------------------
# The custom huge-file viewport.
# -----------------------------------------------------------------------------

@dataclass
class DisplayBuildResult:
    rows: List[str]
    offsets: List[List[int]]
    folded: bool


class VirtualTextView(QAbstractScrollArea):
    status = Signal(str)
    command = Signal(str)
    modified_changed = Signal(bool)

    # One internal clipboard shared by all Matrix Shadow windows in this process.
    # It can hold multi-GB selections as file-backed pieces without loading them into RAM.
    internal_clipboard: Optional[ClipboardPayload] = None

    def __init__(self, parent=None):
        super().__init__(parent)
        self.doc = PieceTable()
        self.doc.new_empty()
        self.path: Optional[str] = self.doc.original_path
        self.offset = 0                     # virtual byte offset at top of viewport
        self.cursor = 0                     # virtual byte caret
        self.anchor: Optional[int] = None    # selection anchor; None means no selection
        self.chunk_bytes = DEFAULT_CHUNK_BYTES
        self.cache: "OrderedDict[Tuple[int, int], bytes]" = OrderedDict()  # (generation, aligned) -> data
        self.encoding = "latin-1"
        self.wrap = True
        self.fold_runs = True
        self.modified = False
        self._scrollbar_update = False
        self._last_rows: List[str] = []
        self._last_offsets: List[List[int]] = []
        self._last_visible_text = ""
        self._selecting = False
        self.setFont(QFont("Consolas", 11))
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMouseTracking(True)
        self.setContextMenuPolicy(Qt.DefaultContextMenu)
        self.verticalScrollBar().valueChanged.connect(self._on_scroll_value)
        self.horizontalScrollBar().setRange(0, 0)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

    # ----- basic document state -----
    @property
    def doc_size(self) -> int:
        return self.doc.size

    def set_file(self, path: str) -> None:
        self.path = path
        self.doc.open(path)
        self.offset = 0
        self.cursor = 0
        self.anchor = None
        self.modified = False
        self.cache.clear()
        self._configure_scrollbar()
        self.command.emit(f"OPEN_FILE path={path!r} original_size={self.doc.original_size}")
        self.modified_changed.emit(False)
        self.request_offset(0)
        self.setFocus()

    def mark_clean_after_save(self, new_path: Optional[str] = None) -> None:
        # Simplest safe behavior: after a save, reopen the saved file as the new base.
        if new_path:
            self.set_file(new_path)
        else:
            self.modified = False
            self.modified_changed.emit(False)

    def set_encoding(self, encoding: str) -> None:
        self.encoding = encoding
        self.command.emit(f"SET_ENCODING encoding={encoding}")
        self.viewport().update()

    def set_wrap(self, enabled: bool) -> None:
        self.wrap = enabled
        self.command.emit(f"SET_WRAP enabled={enabled}")
        self.viewport().update()

    def set_fold_runs(self, enabled: bool) -> None:
        self.fold_runs = enabled
        self.command.emit(f"SET_FOLD_REPEATED_RUNS enabled={enabled}")
        self.viewport().update()

    def visible_text(self) -> str:
        return self._last_visible_text

    def selection_range(self) -> Optional[Tuple[int, int]]:
        if self.anchor is None or self.anchor == self.cursor:
            return None
        return min(self.anchor, self.cursor), max(self.anchor, self.cursor)

    def has_selection(self) -> bool:
        return self.selection_range() is not None

    def _set_modified(self, value: bool) -> None:
        if self.modified != value:
            self.modified = value
            self.modified_changed.emit(value)

    # ----- scroll / chunk cache -----
    def _configure_scrollbar(self) -> None:
        sb = self.verticalScrollBar()
        self._scrollbar_update = True
        sb.setRange(0, SCROLLBAR_UNITS if self.doc_size > 0 else 0)
        sb.setPageStep(max(1, SCROLLBAR_UNITS // 1000))
        sb.setSingleStep(max(1, SCROLLBAR_UNITS // 10000))
        sb.setValue(self._scroll_value_from_offset(self.offset))
        self._scrollbar_update = False

    def _scroll_value_from_offset(self, offset: int) -> int:
        if self.doc_size <= 1:
            return 0
        return int((offset / max(1, self.doc_size - 1)) * SCROLLBAR_UNITS)

    def _offset_from_scroll_value(self, value: int) -> int:
        if self.doc_size <= 1:
            return 0
        return int((value / SCROLLBAR_UNITS) * (self.doc_size - 1))

    def _on_scroll_value(self, value: int) -> None:
        if self._scrollbar_update or not self.path:
            return
        self.request_offset(self._offset_from_scroll_value(value), move_cursor=False)

    def _sync_scrollbar_to_offset(self) -> None:
        self._scrollbar_update = True
        self.verticalScrollBar().setValue(self._scroll_value_from_offset(self.offset))
        self._scrollbar_update = False

    def request_offset(self, offset: int, move_cursor: bool = True) -> None:
        if not self.path:
            return
        self.offset = clamp(offset, 0, max(0, self.doc_size - 1))
        if move_cursor:
            self.cursor = self.offset
            self.anchor = None
        self.command.emit(f"LOAD_VIRTUAL_RANGE byte={self.offset} chunk={self.chunk_bytes}")
        self._sync_scrollbar_to_offset()
        self._emit_position_status()
        self.viewport().update()

    def _read_visible_segment(self) -> bytes:
        if not self.path or self.doc_size <= 0:
            return b""
        aligned = (self.offset // self.chunk_bytes) * self.chunk_bytes
        key = (self.doc.generation, aligned)
        data = self.cache.get(key)
        if data is None:
            data = self.doc.read_at(aligned, self.chunk_bytes)
            self.cache[key] = data
            self.cache.move_to_end(key)
            while len(self.cache) > MAX_CACHE_CHUNKS:
                self.cache.popitem(last=False)
        else:
            self.cache.move_to_end(key)
        start = self.offset - aligned
        return data[start:]

    def invalidate_cache(self) -> None:
        self.cache.clear()
        self._configure_scrollbar()
        self.viewport().update()

    def _emit_position_status(self, suffix: str = "") -> None:
        if self.doc_size:
            pct = (self.offset / max(1, self.doc_size - 1)) * 100.0
            sel = self.selection_range()
            sel_txt = f" selection {sel[0]:,}-{sel[1]:,} ({sel[1]-sel[0]:,} bytes)" if sel else ""
            mod = " modified" if self.modified else ""
            extra = f" ({suffix})" if suffix else ""
            self.status.emit(f"Virtual byte {self.offset:,} / {self.doc_size:,} ({pct:.4f}%){sel_txt}{mod}{extra}")

    # ----- display building -----
    def _font_metrics(self) -> Tuple[QFontMetrics, int, int, int, int]:
        fm = QFontMetrics(self.font())
        char_w = max(1, fm.horizontalAdvance("M"))
        line_h = max(1, fm.lineSpacing())
        cols = max(8, (self.viewport().width() - 18) // char_w)
        rows = max(1, (self.viewport().height() - 10) // line_h)
        return fm, char_w, line_h, cols, rows

    def _decode_cells(self, segment: bytes, base_offset: int) -> Iterable[Tuple[str, int, int]]:
        """Yield (text char, virtual offset, byte length). CR is yielded as empty marker by caller skip."""
        enc = self.encoding.lower()
        if enc in ("latin-1", "latin1", "byte-safe", "bytes"):
            for i, b in enumerate(segment):
                yield chr(b), base_offset + i, 1
            return
        # UTF-8-ish mapping: each decoded char maps to the first byte of the sequence.
        i = 0
        while i < len(segment):
            b = segment[i]
            if b < 0x80:
                yield chr(b), base_offset + i, 1
                i += 1
                continue
            if 0xC2 <= b <= 0xDF:
                need = 2
            elif 0xE0 <= b <= 0xEF:
                need = 3
            elif 0xF0 <= b <= 0xF4:
                need = 4
            else:
                yield "�", base_offset + i, 1
                i += 1
                continue
            raw = segment[i:i + need]
            try:
                ch = raw.decode("utf-8")
                yield ch, base_offset + i, need
                i += need
            except Exception:
                yield "�", base_offset + i, 1
                i += 1

    def _build_display_rows(self, segment: bytes, cols: int, max_rows: int) -> DisplayBuildResult:
        if not segment:
            return DisplayBuildResult([], [], False)

        # Fold obvious repeated data in the visible window. Disable when editing exact raw runs.
        if self.fold_runs and len(segment) >= 4096:
            b0 = segment[0]
            run = 0
            limit = min(len(segment), max(4096, cols * max_rows * 8))
            while run < limit and segment[run] == b0:
                run += 1
            if run >= 4096:
                printable = chr(b0) if 32 <= b0 <= 126 else f"0x{b0:02X}"
                line = f"[shadow fold] byte {printable!r} repeated at least {run:,} bytes in this loaded window"
                return DisplayBuildResult([line, "", "Turn off 'Fold repeated runs' to mark/edit the raw repeated characters."], [[self.offset], [], []], True)

        rows: List[str] = []
        offsets: List[List[int]] = []
        line_chars: List[str] = []
        line_offsets: List[int] = []
        col = 0
        hard_limit_bytes = min(len(segment), max(100_000, cols * max_rows * 32))
        for ch, vpos, _byte_len in self._decode_cells(segment[:hard_limit_bytes], self.offset):
            if ch == "\r":
                continue
            if ch == "\n":
                rows.append("".join(line_chars))
                offsets.append(list(line_offsets))
                line_chars.clear()
                line_offsets.clear()
                col = 0
            elif ch == "\t":
                for _ in range(4):
                    if self.wrap and col >= cols:
                        rows.append("".join(line_chars))
                        offsets.append(list(line_offsets))
                        line_chars.clear()
                        line_offsets.clear()
                        col = 0
                        if len(rows) >= max_rows:
                            break
                    if not self.wrap and col >= cols:
                        col += 1
                        continue
                    line_chars.append(" ")
                    line_offsets.append(vpos)
                    col += 1
            else:
                # Do not paint control chars except common whitespace.
                if ord(ch[0]) < 32 and ch not in ("\n", "\t"):
                    ch = "·"
                for sub in ch:
                    if self.wrap and col >= cols:
                        rows.append("".join(line_chars))
                        offsets.append(list(line_offsets))
                        line_chars.clear()
                        line_offsets.clear()
                        col = 0
                        if len(rows) >= max_rows:
                            break
                    if not self.wrap and col >= cols:
                        col += 1
                        continue
                    line_chars.append(sub)
                    line_offsets.append(vpos)
                    col += 1
            if len(rows) >= max_rows:
                break
        if len(rows) < max_rows and (line_chars or not rows):
            rows.append("".join(line_chars))
            offsets.append(list(line_offsets))
        return DisplayBuildResult(rows[:max_rows], offsets[:max_rows], False)

    # ----- painting and hit testing -----
    def paintEvent(self, event) -> None:  # noqa: N802
        painter = QPainter(self.viewport())
        painter.fillRect(self.viewport().rect(), QColor(16, 18, 22))
        painter.setFont(self.font())
        fm, char_w, line_h, cols, visible_rows = self._font_metrics()

        if not self.path:
            painter.setPen(QColor(225, 230, 235))
            painter.drawText(12, 30, "Open a huge text file. This is a real shadow editor: mark, copy, type, paste, save streamed.")
            return

        segment = self._read_visible_segment()
        result = self._build_display_rows(segment, cols, visible_rows + 2)
        self._last_rows = result.rows
        self._last_offsets = result.offsets
        self._last_visible_text = "\n".join(result.rows)

        # Top ruler/status inside viewport.
        painter.setPen(QColor(115, 190, 255))
        mod = " *modified*" if self.modified else ""
        painter.drawText(8, line_h, f"virtual byte {self.offset:,} / {self.doc_size:,}   cache {len(self.cache)} chunks   pieces {len(self.doc.pieces)}{mod}")

        sel = self.selection_range()
        y = line_h * 2
        left = 8
        for row_i, row in enumerate(result.rows):
            row_offsets = result.offsets[row_i] if row_i < len(result.offsets) else []
            # Selection background per character.
            if sel and row_offsets:
                s, e = sel
                for col_i, vpos in enumerate(row_offsets):
                    if s <= vpos < e:
                        painter.fillRect(QRect(left + col_i * char_w, y - fm.ascent(), char_w, line_h), QColor(42, 96, 160))
            # Cursor.
            for col_i, vpos in enumerate(row_offsets):
                if vpos == self.cursor:
                    painter.fillRect(QRect(left + col_i * char_w, y - fm.ascent(), 2, line_h), QColor(255, 255, 255))
                    break
            if row_offsets and self.cursor == row_offsets[-1] + 1:
                painter.fillRect(QRect(left + len(row_offsets) * char_w, y - fm.ascent(), 2, line_h), QColor(255, 255, 255))

            painter.setPen(QColor(225, 230, 235))
            painter.drawText(left, y, row)
            y += line_h
            if y > self.viewport().height() + line_h:
                break

    def _offset_from_mouse(self, x: int, y: int) -> int:
        fm, char_w, line_h, cols, visible_rows = self._font_metrics()
        row = (y - line_h * 2 + fm.ascent()) // line_h
        col = (x - 8) // char_w
        row = int(clamp(row, 0, max(0, len(self._last_offsets) - 1)))
        if not self._last_offsets:
            return self.offset
        offsets = self._last_offsets[row]
        if not offsets:
            # Empty row: approximate line start.
            return clamp(self.offset, 0, self.doc_size)
        col = int(clamp(col, 0, len(offsets)))
        if col >= len(offsets):
            return clamp(offsets[-1] + 1, 0, self.doc_size)
        return clamp(offsets[col], 0, self.doc_size)

    def mousePressEvent(self, event) -> None:  # noqa: N802
        if not self.path or event.button() != Qt.LeftButton:
            return super().mousePressEvent(event)
        self.setFocus()
        pos = self._offset_from_mouse(event.position().x(), event.position().y())
        self.cursor = pos
        self.anchor = pos if event.modifiers() & Qt.ShiftModifier else None
        self._selecting = True
        self._emit_position_status()
        self.viewport().update()
        event.accept()

    def mouseMoveEvent(self, event) -> None:  # noqa: N802
        if not self.path or not self._selecting:
            return super().mouseMoveEvent(event)
        pos = self._offset_from_mouse(event.position().x(), event.position().y())
        if self.anchor is None:
            self.anchor = self.cursor
        self.cursor = pos
        self._emit_position_status()
        self.viewport().update()
        event.accept()

    def mouseReleaseEvent(self, event) -> None:  # noqa: N802
        if event.button() == Qt.LeftButton:
            self._selecting = False
            self._emit_position_status()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def resizeEvent(self, event) -> None:  # noqa: N802
        super().resizeEvent(event)
        self.viewport().update()

    def wheelEvent(self, event) -> None:  # noqa: N802
        if not self.path:
            return
        fm, char_w, line_h, cols, rows = self._font_metrics()
        wheel_steps = event.angleDelta().y() / 120.0
        delta = int(-wheel_steps * max(256, cols * max(3, rows // 3)))
        self.request_offset(self.offset + delta, move_cursor=False)
        event.accept()

    # ----- editing / selection commands -----
    def select_all(self) -> None:
        if not self.path:
            return
        self.anchor = 0
        self.cursor = self.doc_size
        self.command.emit("SELECT_ALL virtual_document")
        self._emit_position_status()
        self.viewport().update()

    def clear_selection(self) -> None:
        self.anchor = None
        self.viewport().update()

    def read_selection_bytes(self, max_bytes: Optional[int] = None) -> Optional[bytes]:
        sel = self.selection_range()
        if not sel:
            return None
        s, e = sel
        length = e - s
        if max_bytes is not None and length > max_bytes:
            return None
        return self.doc.read_at(s, length)

    def _set_internal_clipboard_marker(self, length: int) -> None:
        QApplication.clipboard().setText(
            f"{INTERNAL_CLIPBOARD_MARKER} {human_bytes(length)} stored inside Matrix Shadow. "
            "Paste inside Matrix Shadow Notepad to insert it without loading it into Windows clipboard."
        )

    def copy_selection_or_visible(self) -> Tuple[bool, str]:
        sel = self.selection_range()
        if not sel:
            txt = self.visible_text()
            QApplication.clipboard().setText(txt)
            # Visible shadow is small, so no special internal payload is needed.
            return True, "Copied visible shadow text."
        s, e = sel
        length = e - s

        # Always prepare the internal clipboard. This is the backdoor command layer:
        # the selection becomes file-backed pieces, not a giant RAM string.
        VirtualTextView.internal_clipboard = self.doc.make_clipboard_payload(s, e, f"{s:,}-{e:,}")

        if length <= CLIPBOARD_SAFE_BYTES:
            data = self.doc.read_at(s, length)
            QApplication.clipboard().setText(safe_decode_bytes(data, self.encoding))
            return True, f"Copied selected {length:,} bytes to Windows clipboard and Matrix internal clipboard."

        self._set_internal_clipboard_marker(length)
        self.command.emit(f"COPY_INTERNAL_RANGE start={s} end={e} size={length} pieces={len(VirtualTextView.internal_clipboard.pieces)}")
        return True, f"Copied {human_bytes(length)} to Matrix internal clipboard by reference. Paste will insert it without loading all bytes."

    def cut_selection(self) -> Tuple[bool, str]:
        sel = self.selection_range()
        if not sel:
            return self.copy_selection_or_visible()
        s, e = sel
        ok, msg = self.copy_selection_or_visible()
        if ok:
            self.doc.replace(s, e, b"")
            self.cursor = s
            self.anchor = None
            self._after_edit(f"CUT_INTERNAL_RANGE start={s} end={e} copied_then_deleted=True")
            return True, f"Cut {human_bytes(e - s)} using Matrix internal clipboard."
        return ok, msg

    def delete_selection(self) -> None:
        sel = self.selection_range()
        if not sel:
            return
        s, e = sel
        self.doc.replace(s, e, b"")
        self.cursor = s
        self.anchor = None
        self._after_edit(f"DELETE_RANGE start={s} end={e}")

    def paste_from_clipboard(self) -> None:
        if not self.path:
            return
        cb = QApplication.clipboard()
        txt = cb.text() or ""
        payload = VirtualTextView.internal_clipboard
        if payload is not None and txt.startswith(INTERNAL_CLIPBOARD_MARKER):
            self.paste_internal_clipboard(payload)
            return
        # Normal Windows/Qt clipboard path: copy from browser/Notepad/other apps -> paste here.
        self.paste_text(txt)

    def paste_internal_clipboard(self, payload: ClipboardPayload) -> None:
        if not self.path or payload.size <= 0:
            return
        sel = self.selection_range()
        if sel:
            s, e = sel
        else:
            s = e = self.cursor
        inserted = self.doc.paste_clipboard_payload(s, e, payload)
        self.cursor = s + inserted
        self.anchor = None
        self._after_edit(f"PASTE_INTERNAL_CLIPBOARD start={s} replaced_end={e} insert_len={inserted} pieces={len(payload.pieces)}")
        self.status.emit(f"Pasted {human_bytes(inserted)} from Matrix internal clipboard without using Windows clipboard RAM.")

    def paste_text(self, text: str) -> None:
        if not self.path or text == "":
            return
        data = safe_encode(text, self.encoding)
        self.insert_bytes(data)

    def insert_bytes(self, data: bytes) -> None:
        if not self.path or not data:
            return
        sel = self.selection_range()
        if sel:
            s, e = sel
        else:
            s = e = self.cursor
        self.doc.replace(s, e, data)
        self.cursor = s + len(data)
        self.anchor = None
        self._after_edit(f"REPLACE_RANGE start={s} end={e} insert_len={len(data)}")

    def _after_edit(self, command: str) -> None:
        self.command.emit(command)
        self._set_modified(True)
        self.invalidate_cache()
        self.ensure_cursor_visible()
        self._emit_position_status("edited")

    def ensure_cursor_visible(self) -> None:
        fm, char_w, line_h, cols, rows = self._font_metrics()
        approx_window = max(1, cols * max(1, rows - 2))
        # IMPORTANT: never scroll the viewport start to exactly doc_size after typing/paste.
        # If offset == EOF, the visible segment is empty and the text looks like it disappeared.
        if self.cursor < self.offset:
            self.offset = clamp(self.cursor, 0, max(0, self.doc_size - 1))
            self._sync_scrollbar_to_offset()
        elif self.cursor >= self.offset + approx_window:
            new_offset = max(0, self.cursor - approx_window + 1)
            self.offset = clamp(new_offset, 0, max(0, self.doc_size - 1))
            self._sync_scrollbar_to_offset()

    def move_cursor(self, new_pos: int, keep_selection: bool = False) -> None:
        new_pos = clamp(new_pos, 0, self.doc_size)
        if keep_selection:
            if self.anchor is None:
                self.anchor = self.cursor
        else:
            self.anchor = None
        self.cursor = new_pos
        self.ensure_cursor_visible()
        self._emit_position_status()
        self.viewport().update()

    def keyPressEvent(self, event) -> None:  # noqa: N802
        if not self.path:
            return super().keyPressEvent(event)

        # Standard shortcuts.
        if event.matches(QKeySequence.Copy):
            ok, msg = self.copy_selection_or_visible()
            self.status.emit(msg)
            return
        if event.matches(QKeySequence.Cut):
            ok, msg = self.cut_selection()
            self.status.emit(msg)
            return
        if event.matches(QKeySequence.Paste):
            self.paste_from_clipboard()
            return
        if event.matches(QKeySequence.SelectAll):
            self.select_all()
            return

        key = event.key()
        shift = bool(event.modifiers() & Qt.ShiftModifier)
        ctrl = bool(event.modifiers() & Qt.ControlModifier)
        fm, char_w, line_h, cols, rows = self._font_metrics()
        step_line = max(1, cols)
        step_page = max(1, cols * max(1, rows - 3))

        if key == Qt.Key_Left:
            self.move_cursor(self.cursor - (step_line if ctrl else 1), shift)
        elif key == Qt.Key_Right:
            self.move_cursor(self.cursor + (step_line if ctrl else 1), shift)
        elif key == Qt.Key_Up:
            self.move_cursor(self.cursor - step_line, shift)
        elif key == Qt.Key_Down:
            self.move_cursor(self.cursor + step_line, shift)
        elif key == Qt.Key_PageUp:
            self.move_cursor(self.cursor - step_page, shift)
        elif key == Qt.Key_PageDown:
            self.move_cursor(self.cursor + step_page, shift)
        elif key == Qt.Key_Home:
            self.move_cursor(0 if ctrl else max(0, self.offset), shift)
        elif key == Qt.Key_End:
            self.move_cursor(self.doc_size if ctrl else min(self.doc_size, self.offset + step_line), shift)
        elif key == Qt.Key_Backspace:
            if self.selection_range():
                self.delete_selection()
            elif self.cursor > 0:
                s = self.cursor - 1
                self.doc.replace(s, self.cursor, b"")
                self.cursor = s
                self.anchor = None
                self._after_edit(f"BACKSPACE byte={s}")
        elif key == Qt.Key_Delete:
            if self.selection_range():
                self.delete_selection()
            elif self.cursor < self.doc_size:
                self.doc.replace(self.cursor, self.cursor + 1, b"")
                self._after_edit(f"DELETE byte={self.cursor}")
        elif key in (Qt.Key_Return, Qt.Key_Enter):
            self.insert_bytes(safe_encode("\n", self.encoding))
        else:
            txt = event.text()
            if txt and not ctrl and txt >= " ":
                self.insert_bytes(safe_encode(txt, self.encoding))
            else:
                super().keyPressEvent(event)

    def contextMenuEvent(self, event) -> None:  # noqa: N802
        menu = QMenu(self)
        copy_act = menu.addAction("Copy")
        cut_act = menu.addAction("Cut")
        paste_act = menu.addAction("Paste")
        delete_act = menu.addAction("Delete")
        menu.addSeparator()
        select_all_act = menu.addAction("Select All")
        export_sel_act = menu.addAction("Export Selection to File...")
        menu.addSeparator()
        save_as_act = menu.addAction("Save / Merge Edits As...")
        copy_act.setEnabled(bool(self.path))
        cut_act.setEnabled(self.has_selection())
        delete_act.setEnabled(self.has_selection())
        export_sel_act.setEnabled(self.has_selection())
        action = menu.exec(event.globalPos())
        if action == copy_act:
            ok, msg = self.copy_selection_or_visible()
            self.status.emit(msg)
        elif action == cut_act:
            ok, msg = self.cut_selection()
            self.status.emit(msg)
        elif action == paste_act:
            self.paste_from_clipboard()
        elif action == delete_act:
            self.delete_selection()
        elif action == select_all_act:
            self.select_all()
        elif action == export_sel_act:
            self.parentWidget().window().export_selection()  # type: ignore[attr-defined]
        elif action == save_as_act:
            self.parentWidget().window().save_as()  # type: ignore[attr-defined]


# -----------------------------------------------------------------------------
# Main window
# -----------------------------------------------------------------------------

class MatrixShadowWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(1380, 860)
        self.view = VirtualTextView()
        self.view.status.connect(self._set_status)
        self.view.command.connect(self._log_command)
        self.view.modified_changed.connect(self._modified_changed)
        self.command_log: Deque[str] = deque(maxlen=8000)
        self.search_worker: Optional[DocSearchWorker] = None
        self.find_all_worker: Optional[FindAllWorker] = None
        self.pending_replace_worker: Optional[FindAllWorker] = None
        self.replace_worker: Optional[ReplaceAllToFileWorker] = None
        self.save_worker: Optional[SavePiecesWorker] = None
        self.export_worker: Optional[ExportRangeWorker] = None
        self.index_worker: Optional[LineIndexWorker] = None
        self.go_line_worker: Optional[GoLineWorker] = None
        self.line_index: List[Tuple[int, int]] = []
        self.total_lines: Optional[int] = None
        self.last_search_count: Optional[int] = None
        self.last_search_samples: List[int] = []
        self._commands_window: Optional[QMainWindow] = None
        self.current_save_path: Optional[str] = None
        self._build_ui()

    def _build_ui(self) -> None:
        central = QWidget()
        layout = QVBoxLayout(central)
        layout.setContentsMargins(6, 6, 6, 6)
        layout.setSpacing(6)

        top = QGridLayout()
        top.setHorizontalSpacing(6)
        top.setVerticalSpacing(4)

        self.open_btn = QPushButton("Open file")
        self.open_btn.clicked.connect(self.open_file)
        top.addWidget(self.open_btn, 0, 0)

        self.open_hex_btn = QPushButton("Open HEX")
        self.open_hex_btn.clicked.connect(self.open_file_as_hex)
        top.addWidget(self.open_hex_btn, 0, 1)

        self.save_btn = QPushButton("Save As / Merge")
        self.save_btn.clicked.connect(self.save_as)
        top.addWidget(self.save_btn, 0, 2)

        self.export_btn = QPushButton("Export selection")
        self.export_btn.clicked.connect(self.export_selection)
        top.addWidget(self.export_btn, 0, 3)

        self.encoding_combo = QComboBox()
        self.encoding_combo.addItems(["latin-1", "utf-8"])
        self.encoding_combo.currentTextChanged.connect(self.view.set_encoding)
        top.addWidget(QLabel("Encoding"), 0, 4)
        top.addWidget(self.encoding_combo, 0, 5)

        self.wrap_check = QCheckBox("Wrap full window")
        self.wrap_check.setChecked(True)
        self.wrap_check.toggled.connect(self.view.set_wrap)
        top.addWidget(self.wrap_check, 0, 6)

        self.fold_check = QCheckBox("Fold repeated runs")
        self.fold_check.setChecked(True)
        self.fold_check.toggled.connect(self.view.set_fold_runs)
        top.addWidget(self.fold_check, 0, 7)

        self.byte_edit = QLineEdit()
        self.byte_edit.setPlaceholderText("Go to virtual byte offset or 50%")
        self.byte_edit.returnPressed.connect(self.go_to_byte)
        top.addWidget(self.byte_edit, 0, 8)
        go_byte_btn = QPushButton("Go byte")
        go_byte_btn.clicked.connect(self.go_to_byte)
        top.addWidget(go_byte_btn, 0, 9)

        self.find_edit = QLineEdit()
        self.find_edit.setPlaceholderText("Find text/bytes in selected encoding")
        top.addWidget(self.find_edit, 1, 0, 1, 4)
        self.case_check = QCheckBox("Case sensitive")
        self.case_check.setChecked(True)
        top.addWidget(self.case_check, 1, 4)
        self.find_btn = QPushButton("Find next")
        self.find_btn.clicked.connect(self.find_next)
        top.addWidget(self.find_btn, 1, 5)

        self.search_all_btn = QPushButton("Count / positions")
        self.search_all_btn.clicked.connect(self.search_all_count)
        top.addWidget(self.search_all_btn, 1, 6)

        self.replace_edit = QLineEdit()
        self.replace_edit.setPlaceholderText("Replacement / token, e.g. 2")
        top.addWidget(self.replace_edit, 1, 7)
        self.replace_btn = QPushButton("Replace in doc")
        self.replace_btn.clicked.connect(self.replace_all_in_document)
        top.addWidget(self.replace_btn, 1, 8)

        self.index_btn = QPushButton("Build line index")
        self.index_btn.clicked.connect(self.build_line_index)
        top.addWidget(self.index_btn, 2, 0)
        self.line_edit = QLineEdit()
        self.line_edit.setPlaceholderText("Go to line after index")
        self.line_edit.returnPressed.connect(self.go_to_line)
        top.addWidget(self.line_edit, 2, 1, 1, 2)
        line_btn = QPushButton("Go line")
        line_btn.clicked.connect(self.go_to_line)
        top.addWidget(line_btn, 2, 3)

        copy_btn = QPushButton("Copy")
        copy_btn.clicked.connect(self.copy)
        top.addWidget(copy_btn, 2, 4)
        paste_btn = QPushButton("Paste")
        paste_btn.clicked.connect(self.view.paste_from_clipboard)
        top.addWidget(paste_btn, 2, 5)
        select_all_btn = QPushButton("Select all")
        select_all_btn.clicked.connect(self.view.select_all)
        top.addWidget(select_all_btn, 2, 6)
        self.commands_btn = QPushButton("Hidden commands")
        self.commands_btn.clicked.connect(self.show_commands)
        top.addWidget(self.commands_btn, 2, 7)

        self.progress = QProgressBar()
        self.progress.setRange(0, 100)
        self.progress.setValue(0)
        top.addWidget(self.progress, 2, 8)

        self.insert_file_btn = QPushButton("Add text file")
        self.insert_file_btn.clicked.connect(self.insert_text_file_at_cursor)
        top.addWidget(self.insert_file_btn, 4, 0, 1, 2)

        self.insert_hex_btn = QPushButton("Add HEX from file")
        self.insert_hex_btn.clicked.connect(self.insert_file_as_hex_at_cursor)
        top.addWidget(self.insert_hex_btn, 4, 2, 1, 2)

        self.stream_replace_btn = QPushButton("Stream replace → file")
        self.stream_replace_btn.clicked.connect(self.replace_all_to_new_file)
        top.addWidget(self.stream_replace_btn, 3, 0, 1, 2)

        self.analyze_btn = QPushButton("Analyze token cost")
        self.analyze_btn.clicked.connect(self.analyze_token_cost)
        top.addWidget(self.analyze_btn, 3, 2, 1, 2)

        self.analysis_box = QTextEdit()
        self.analysis_box.setReadOnly(True)
        self.analysis_box.setFont(QFont("Consolas", 9))
        self.analysis_box.setMaximumHeight(115)
        self.analysis_box.setPlainText("Search/count results and token-cost analysis will appear here. Example: find 01001, replacement/token 2, then Count / positions + Analyze token cost.")
        top.addWidget(self.analysis_box, 3, 4, 1, 5)

        layout.addLayout(top)
        layout.addWidget(self.view)
        self.setCentralWidget(central)

        self.setStatusBar(QStatusBar())
        self._set_status("Ready. You can type immediately, paste normal text, Open file, or Open HEX.")

        tb = QToolBar("Main")
        self.addToolBar(tb)
        self._add_action(tb, "Open", QKeySequence.Open, self.open_file)
        self._add_action(tb, "Open HEX", None, self.open_file_as_hex)
        self._add_action(tb, "Add text file", None, self.insert_text_file_at_cursor)
        self._add_action(tb, "Add HEX", None, self.insert_file_as_hex_at_cursor)
        self._add_action(tb, "Save As", QKeySequence.Save, self.save_as)
        self._add_action(tb, "Find", QKeySequence.Find, lambda: self.find_edit.setFocus())
        self._add_action(tb, "Copy", QKeySequence.Copy, self.copy)
        self._add_action(tb, "Cut", QKeySequence.Cut, self.cut)
        self._add_action(tb, "Paste", QKeySequence.Paste, self.view.paste_from_clipboard)
        self._add_action(tb, "Select All", QKeySequence.SelectAll, self.view.select_all)

    def _add_action(self, tb: QToolBar, name: str, shortcut, fn) -> None:
        action = QAction(name, self)
        if shortcut:
            action.setShortcut(shortcut)
        action.triggered.connect(fn)
        tb.addAction(action)

    def _set_status(self, text: str) -> None:
        self.statusBar().showMessage(text)

    def _log_command(self, text: str) -> None:
        ts = time.strftime("%H:%M:%S")
        self.command_log.append(f"{ts}  {text}")

    def _modified_changed(self, modified: bool) -> None:
        base = Path(self.view.path).name if self.view.path else "Untitled"
        self.setWindowTitle(f"{APP_NAME} - {base}{' *' if modified else ''}")

    def show_commands(self) -> None:
        box = QTextEdit()
        box.setReadOnly(True)
        box.setFont(QFont("Consolas", 10))
        box.setText("\n".join(self.command_log) or "No hidden engine commands yet.")
        win = QMainWindow(self)
        win.setWindowTitle("Hidden engine command log - not part of the document")
        win.resize(980, 560)
        win.setCentralWidget(box)
        win.show()
        self._commands_window = win

    def _require_file(self) -> Optional[str]:
        if not self.view.path:
            QMessageBox.information(self, APP_NAME, "Open a file first.")
            return None
        return self.view.path

    # ----- file actions -----
    def _confirm_discard_edits(self, action_text: str = "continue") -> bool:
        if not self.view.modified:
            return True
        res = QMessageBox.question(
            self, APP_NAME,
            f"You have unsaved edits. {action_text}?",
            QMessageBox.Yes | QMessageBox.No,
        )
        return res == QMessageBox.Yes

    def _reset_after_loaded_path(self, path: str, status: str) -> None:
        self.current_save_path = path
        self.line_index = []
        self.total_lines = None
        self.last_search_count = None
        self.last_search_samples = []
        self.analysis_box.setPlainText(status)
        self.progress.setValue(0)

    def _make_hex_text_file(self, src_path: str) -> str:
        """Stream any file to a temporary visible HEX text file without loading it all into RAM."""
        src = Path(src_path)
        fd, out_path = tempfile.mkstemp(prefix=src.stem + "_HEX_", suffix=".txt")
        os.close(fd)
        with open(src_path, "rb", buffering=WORKER_CHUNK_BYTES) as inp, open(out_path, "w", encoding="ascii", newline="\n") as out:
            offset = 0
            while True:
                block = inp.read(1024 * 1024)
                if not block:
                    break
                for i in range(0, len(block), 16):
                    row = block[i:i + 16]
                    hex_part = " ".join(f"{b:02X}" for b in row)
                    ascii_part = "".join(chr(b) if 32 <= b <= 126 else "." for b in row)
                    out.write(f"{offset + i:012X}  {hex_part:<47}  |{ascii_part}|\n")
                offset += len(block)
        return out_path

    def open_file_as_hex(self) -> None:
        if not self._confirm_discard_edits("Open another file as HEX"):
            return
        path, _ = QFileDialog.getOpenFileName(self, "Open any file as visible HEX text", "", "All files (*.*)")
        if not path:
            return
        try:
            hex_path = self._make_hex_text_file(path)
            self.view.set_encoding("latin-1")
            self.encoding_combo.setCurrentText("latin-1")
            self.view.set_file(hex_path)
            self._reset_after_loaded_path(hex_path, f"Opened HEX view for: {path}\nThis is editable text output: OFFSET  HEX BYTES  |ASCII|. Save As writes the HEX text.")
            self._set_status(f"Opened HEX text view for {Path(path).name}.")
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Could not open as HEX:\n{exc}")

    def insert_text_file_at_cursor(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Insert text file at cursor", "", "Text / all files (*.txt *.hex *.log *.csv *.json *.*)")
        if not path:
            return
        try:
            data = Path(path).read_bytes()
            self.view.insert_bytes(data)
            self._set_status(f"Inserted {human_bytes(len(data))} from {Path(path).name}.")
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Could not insert file:\n{exc}")

    def insert_file_as_hex_at_cursor(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Insert file bytes as HEX text at cursor", "", "All files (*.*)")
        if not path:
            return
        try:
            # Stream to temp HEX text first, then insert. Safer for normal/small files; for huge files use Open HEX.
            hex_path = self._make_hex_text_file(path)
            data = Path(hex_path).read_bytes()
            self.view.insert_bytes(data)
            self._set_status(f"Inserted HEX text {human_bytes(len(data))} from {Path(path).name}.")
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Could not insert file as HEX:\n{exc}")

    def open_file(self) -> None:
        if not self._confirm_discard_edits("Open another file"):
            return
        path, _ = QFileDialog.getOpenFileName(self, "Open huge text-like file", "", "All files (*.*)")
        if not path:
            return
        try:
            self.view.set_file(path)
            self._reset_after_loaded_path(path, "Opened file. Use Count / positions to make the notepad understand patterns before replacing/tokenizing.")
            self._set_status(f"Opened {Path(path).name} ({human_bytes(os.path.getsize(path))}).")
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Could not open file:\n{exc}")

    def save_as(self) -> None:
        path = self._require_file()
        if not path:
            return
        suggested = str(Path(path).with_suffix(Path(path).suffix + ".merged.txt"))
        out_path, _ = QFileDialog.getSaveFileName(self, "Save merged document as", suggested, "All files (*.*)")
        if not out_path:
            return
        self._log_command(f"SAVE_MERGED output={out_path!r} pieces={len(self.view.doc.pieces)} size={self.view.doc_size}")
        self.save_worker = SavePiecesWorker(self.view.doc.snapshot(), out_path)
        self.save_worker.progress.connect(self._worker_progress)
        self.save_worker.done.connect(lambda ok, text, p=out_path: self._save_done(ok, text, p))
        self.progress.setValue(0)
        self.save_worker.start()

    @Slot(bool, str)
    def _save_done(self, ok: bool, text: str, out_path: str) -> None:
        self.progress.setValue(100 if ok else self.progress.value())
        self._set_status(text)
        if ok:
            # Reopen the saved file to make the saved merged stream the new base.
            self.view.mark_clean_after_save(out_path)
            self.current_save_path = out_path

    def export_selection(self) -> None:
        path = self._require_file()
        if not path:
            return
        sel = self.view.selection_range()
        if not sel:
            QMessageBox.information(self, APP_NAME, "Mark/select text first.")
            return
        s, e = sel
        suggested = str(Path(path).with_suffix(Path(path).suffix + f".selection_{s}_{e}.txt"))
        out_path, _ = QFileDialog.getSaveFileName(self, "Export selected range as", suggested, "All files (*.*)")
        if not out_path:
            return
        self._log_command(f"EXPORT_SELECTION start={s} end={e} output={out_path!r}")
        self.export_worker = ExportRangeWorker(self.view.doc.snapshot(), s, e, out_path)
        self.export_worker.progress.connect(self._worker_progress)
        self.export_worker.done.connect(self._worker_done)
        self.progress.setValue(0)
        self.export_worker.start()

    # ----- edit actions -----
    def copy(self) -> None:
        ok, msg = self.view.copy_selection_or_visible()
        if not ok:
            QMessageBox.information(self, APP_NAME, msg)
        self._set_status(msg)

    def cut(self) -> None:
        ok, msg = self.view.cut_selection()
        if not ok:
            QMessageBox.information(self, APP_NAME, msg)
        self._set_status(msg)

    # ----- navigation/search/replace -----
    def go_to_byte(self) -> None:
        path = self._require_file()
        if not path:
            return
        raw = self.byte_edit.text().strip().replace(",", "")
        if not raw:
            return
        try:
            if raw.endswith("%"):
                pct = float(raw[:-1]) / 100.0
                offset = int(pct * max(0, self.view.doc_size - 1))
            else:
                offset = parse_human_int(raw)
            self.view.request_offset(offset)
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Invalid byte offset: {exc}")

    def find_next(self) -> None:
        path = self._require_file()
        if not path:
            return
        query = self.find_edit.text()
        if not query:
            self.find_edit.setFocus()
            return
        if self.search_worker and self.search_worker.isRunning():
            self.search_worker.cancel()
        pattern = safe_encode(query, self.view.encoding)
        self._log_command(f"SEARCH pattern={query!r} from_virtual_byte={self.view.cursor} case_sensitive={self.case_check.isChecked()}")
        self.search_worker = DocSearchWorker(self.view.doc.snapshot(), pattern, self.view.cursor, self.case_check.isChecked())
        self.search_worker.progress.connect(self._worker_progress)
        self.search_worker.found.connect(self._search_found)
        self.search_worker.done.connect(self._worker_done)
        self.progress.setValue(0)
        self.search_worker.start()

    @Slot(object)
    def _search_found(self, offset: int) -> None:
        self.view.cursor = int(offset)
        self.view.anchor = None
        self.view.request_offset(int(offset), move_cursor=False)
        self.byte_edit.setText(str(offset))

    def search_all_count(self) -> None:
        path = self._require_file()
        if not path:
            return
        query = self.find_edit.text()
        if not query:
            self.find_edit.setFocus()
            return
        if self.find_all_worker and self.find_all_worker.isRunning():
            self.find_all_worker.cancel()
            return
        pattern = safe_encode(query, self.view.encoding)
        self._log_command(f"SEARCH_ALL_COUNT pattern={query!r} case_sensitive={self.case_check.isChecked()}")
        self.search_all_btn.setText("Cancel count")
        self.find_all_worker = FindAllWorker(self.view.doc.snapshot(), pattern, self.case_check.isChecked(), MAX_POSITION_SAMPLES, 0, False)
        self.find_all_worker.progress.connect(self._worker_progress)
        self.find_all_worker.done.connect(self._search_all_done)
        self.progress.setValue(0)
        self.find_all_worker.start()

    @Slot(bool, str, object, object)
    def _search_all_done(self, ok: bool, text: str, meta: object, samples: object) -> None:
        self.search_all_btn.setText("Count / positions")
        info = meta if isinstance(meta, dict) else {}
        count = int(info.get("count", 0))
        sample_list = [int(x) for x in samples] if isinstance(samples, list) else []
        self.last_search_count = count
        self.last_search_samples = sample_list
        self.progress.setValue(100 if ok else self.progress.value())
        self._set_status(text)
        lines = [text]
        lines.append(f"Pattern: {self.find_edit.text()!r} | Encoding: {self.view.encoding} | Case sensitive: {self.case_check.isChecked()}")
        lines.append(f"Count: {count:,}")
        if sample_list:
            preview = ", ".join(f"{p:,}" for p in sample_list[:80])
            more = " ..." if len(sample_list) > 80 else ""
            lines.append(f"First positions: {preview}{more}")
            lines.append("Tip: click Go byte with one of those positions to inspect it.")
        else:
            lines.append("No sampled positions.")
        self.analysis_box.setPlainText("\n".join(lines))

    def _token_cost_text(self, pattern: bytes, token: bytes, count: int) -> str:
        old_cost = count * len(pattern)
        token_stream_cost = count * len(token)
        # Minimal reversible map overhead estimate. Real file format may use a stronger header later.
        dictionary_cost = len(token) + 1 + len(pattern) + 1 + 16
        approx_total = token_stream_cost + dictionary_cost
        saved = old_cost - approx_total
        # Collision/escape thinking: if token appears in original 0/1 file, a decoder needs escaping.
        token_text = safe_decode_bytes(token, self.view.encoding)
        pattern_text = safe_decode_bytes(pattern, self.view.encoding)
        clean_binary_marker = set(pattern_text) <= {"0", "1"} and token_text not in {"0", "1"}
        lines = []
        lines.append("TOKEN COST ANALYSIS")
        lines.append(f"Rule idea: {pattern_text!r} -> {token_text!r}")
        lines.append(f"Matches: {count:,}")
        lines.append(f"Original repeated cost: {count:,} × {len(pattern)} bytes = {old_cost:,} bytes")
        lines.append(f"Token stream cost: {count:,} × {len(token)} bytes = {token_stream_cost:,} bytes")
        lines.append(f"Estimated dictionary/header cost once: ~{dictionary_cost:,} bytes")
        lines.append(f"Estimated reversible total: {approx_total:,} bytes")
        if saved > 0:
            lines.append(f"Estimated win: saves ~{saved:,} bytes before normal compression.")
        elif saved == 0:
            lines.append("Estimated break-even before normal compression.")
        else:
            lines.append(f"Estimated loss: costs ~{-saved:,} extra bytes before normal compression.")
        if clean_binary_marker:
            lines.append("Important: because the source pattern is 0/1 and the token is not 0/1, token collision is clean. Internally, '2' can mean 01001.")
        else:
            lines.append("Important: if the token already appears as normal data, a reversible format needs escape rules, which add cost.")
        lines.append("Plain physical replacement is not automatically reversible. It becomes reversible only if the file carries a rule like 2=01001 or the editor keeps that rule internally.")
        return "\n".join(lines)

    def analyze_token_cost(self) -> None:
        find = self.find_edit.text()
        repl = self.replace_edit.text()
        if not find or repl == "":
            QMessageBox.information(self, APP_NAME, "Type a find pattern and a replacement/token first. Example: find 01001, token 2.")
            return
        pattern = safe_encode(find, self.view.encoding)
        token = safe_encode(repl, self.view.encoding)
        if self.last_search_count is None:
            self.analysis_box.setPlainText("Run Count / positions first so the notepad knows how many matches exist, then Analyze token cost.")
            return
        self.analysis_box.setPlainText(self._token_cost_text(pattern, token, self.last_search_count))

    def replace_all_in_document(self) -> None:
        path = self._require_file()
        if not path:
            return
        find = self.find_edit.text()
        if not find:
            QMessageBox.information(self, APP_NAME, "Type the text/bytes to find first.")
            return
        if self.pending_replace_worker and self.pending_replace_worker.isRunning():
            self.pending_replace_worker.cancel()
            return
        pattern = safe_encode(find, self.view.encoding)
        replacement = safe_encode(self.replace_edit.text(), self.view.encoding)
        if not pattern:
            QMessageBox.information(self, APP_NAME, "Empty find pattern.")
            return
        self._log_command(
            f"REPLACE_ALL_IN_DOCUMENT_COLLECT find={find!r} repl_len={len(replacement)} limit={MAX_PENDING_REPLACE_MATCHES}"
        )
        self.replace_btn.setText("Cancel replace")
        self.pending_replace_worker = FindAllWorker(
            self.view.doc.snapshot(), pattern, self.case_check.isChecked(), 200,
            MAX_PENDING_REPLACE_MATCHES, True,
        )
        self.pending_replace_worker.progress.connect(self._worker_progress)
        self.pending_replace_worker.done.connect(lambda ok, text, meta, samples, p=pattern, r=replacement: self._pending_replace_done(ok, text, meta, samples, p, r))
        self.progress.setValue(0)
        self.pending_replace_worker.start()

    @Slot(bool, str, object, object)
    def _pending_replace_done(self, ok: bool, text: str, meta: object, samples: object, pattern: bytes, replacement: bytes) -> None:
        self.replace_btn.setText("Replace in doc")
        info = meta if isinstance(meta, dict) else {}
        positions = [int(x) for x in info.get("positions", [])]
        count = int(info.get("count", len(positions)))
        if not ok:
            self.progress.setValue(self.progress.value())
            self._set_status(text)
            self.analysis_box.setPlainText(
                text + "\n\n" +
                "Matrix did NOT fake it: applying millions of separate pending edits would make the piece table explode. "
                "Use 'Stream replace → file' for giant jobs, or use the token-map/analyzer layer for future compressed grammar work."
            )
            return
        if not positions:
            self._set_status("No matches to replace.")
            self.analysis_box.setPlainText("No matches to replace in the virtual document.")
            return
        # V6: apply all replacements as one batch. This avoids the V5 crash/slowdown
        # caused by thousands of repeated piece-table split/compact operations.
        try:
            applied = self.view.doc.replace_many_at_positions(positions, len(pattern), replacement)
            first_pos = positions[0] if positions else 0
            self.view.cursor = first_pos
            self.view.anchor = None
            self.view._after_edit(
                f"REPLACE_ALL_IN_DOCUMENT_BATCH_APPLY count={applied} pattern_len={len(pattern)} repl_len={len(replacement)}"
            )
            self.progress.setValue(100)
            msg = (
                f"Applied {applied:,} replacements directly into the virtual document as pending edits. "
                "No new output copy was written yet. Use Save/Merge when you want to commit it."
            )
            self._set_status(msg)
            self.last_search_count = count
            self.analysis_box.setPlainText(
                msg +
                f"\nPiece table pieces after batch: {len(self.view.doc.pieces):,}" +
                "\nReplacement bytes are reused internally when possible, so replacing 34,825 matches with @ does not store 34,825 separate @ buffers." +
                "\n" + self._token_cost_text(pattern, replacement, count)
            )
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Replace-in-document failed safely before save:\n{exc}")

    def replace_all_to_new_file(self) -> None:
        path = self._require_file()
        if not path:
            return
        find = self.find_edit.text()
        if not find:
            QMessageBox.information(self, APP_NAME, "Type the text/bytes to find first.")
            return
        suggested = str(Path(path).with_suffix(Path(path).suffix + ".replaced.txt"))
        out_path, _ = QFileDialog.getSaveFileName(self, "Write replaced copy as", suggested, "All files (*.*)")
        if not out_path:
            return
        pattern = safe_encode(find, self.view.encoding)
        replacement = safe_encode(self.replace_edit.text(), self.view.encoding)
        if self.replace_worker and self.replace_worker.isRunning():
            self.replace_worker.cancel()
        self._log_command(f"REPLACE_ALL_TO_NEW_FILE find={find!r} repl_len={len(replacement)} out={out_path!r}")
        self.replace_worker = ReplaceAllToFileWorker(self.view.doc.snapshot(), out_path, pattern, replacement, self.case_check.isChecked())
        self.replace_worker.progress.connect(self._worker_progress)
        self.replace_worker.done.connect(self._worker_done)
        self.progress.setValue(0)
        self.replace_worker.start()

    def build_line_index(self) -> None:
        path = self._require_file()
        if not path:
            return
        if self.index_worker and self.index_worker.isRunning():
            self.index_worker.cancel()
            return
        self._log_command(f"BUILD_LINE_INDEX step={SPARSE_LINE_STEP}")
        self.index_btn.setText("Cancel indexing")
        self.index_worker = LineIndexWorker(self.view.doc.snapshot(), SPARSE_LINE_STEP)
        self.index_worker.progress.connect(self._worker_progress)
        self.index_worker.done.connect(self._index_done)
        self.progress.setValue(0)
        self.index_worker.start()

    @Slot(object, object, str)
    def _index_done(self, records: list, total_lines: int, text: str) -> None:
        self.line_index = [(int(a), int(b)) for a, b in records]
        self.total_lines = int(total_lines) if total_lines else None
        self.index_btn.setText("Build line index")
        self.progress.setValue(100 if records else self.progress.value())
        self._set_status(text)

    def go_to_line(self) -> None:
        path = self._require_file()
        if not path:
            return
        raw = self.line_edit.text().strip()
        if not raw:
            return
        if not self.line_index:
            # Allow a slow exact scan from the beginning instead of just throwing an error.
            self.line_index = [(1, 0)]
            self._set_status("No sparse index yet; using slow exact scan from line 1. Build index for faster jumps.")
        try:
            target = max(1, parse_human_int(raw))
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Invalid line number: {exc}. Examples: 2000000000, 2b, 2 billion, 1.5m")
            return
        line_numbers = [r[0] for r in self.line_index]
        i = max(0, bisect.bisect_right(line_numbers, target) - 1)
        start_line, start_offset = self.line_index[i]
        self._log_command(f"GO_TO_LINE target={target} from_sparse_line={start_line} virtual_byte={start_offset}")
        if self.go_line_worker and self.go_line_worker.isRunning():
            self.go_line_worker.cancel()
        self.go_line_worker = GoLineWorker(self.view.doc.snapshot(), start_line, start_offset, target)
        self.go_line_worker.found.connect(self._go_line_found)
        self.go_line_worker.done.connect(self._worker_done)
        self.go_line_worker.start()

    @Slot(object, object)
    def _go_line_found(self, offset: int, line: int) -> None:
        self.view.cursor = int(offset)
        self.view.anchor = None
        self.view.request_offset(int(offset), move_cursor=False)
        self.byte_edit.setText(str(offset))
        self.line_edit.setText(str(line))

    @Slot(int, str)
    def _worker_progress(self, pct: int, text: str) -> None:
        self.progress.setValue(pct)
        self._set_status(text)

    @Slot(bool, str)
    def _worker_done(self, ok: bool, text: str) -> None:
        self.progress.setValue(100 if ok else self.progress.value())
        self._set_status(text)

    def closeEvent(self, event) -> None:  # noqa: N802
        if self.view.modified:
            res = QMessageBox.question(self, APP_NAME, "You have unsaved edits. Close anyway?", QMessageBox.Yes | QMessageBox.No)
            if res != QMessageBox.Yes:
                event.ignore()
                return
        for worker in (self.search_worker, self.find_all_worker, self.pending_replace_worker, self.replace_worker, self.save_worker, self.export_worker, self.index_worker, self.go_line_worker):
            if worker and worker.isRunning():
                try:
                    worker.cancel()
                except Exception:
                    pass
        super().closeEvent(event)


def main() -> int:
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    win = MatrixShadowWindow()
    win.show()
    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
