from __future__ import annotations

import json
import tkinter as tk
import tkinter.ttk as ttk
from tkinter import filedialog, messagebox, scrolledtext
import time
import threading
import re

# ─────────────────────────────────────────────────────────────────
#  BACKEND: Core data structures and logic
# ─────────────────────────────────────────────────────────────────

class Tape:
    """
    Represents an infinite tape using a Python dictionary.
    Keys are integer positions; missing positions are treated as BLANK ('_').
    Supports unlimited left/right expansion.
    """
    BLANK = '_'

    def __init__(self, input_string: str = ""):
        self.cells: dict[int, str] = {}
        self.head: int = 0                 # Current head position

        # Write the input string starting at position 0
        for i, ch in enumerate(input_string):
            self.cells[i] = ch

    def read(self) -> str:
        """Read the symbol under the head."""
        return self.cells.get(self.head, self.BLANK)

    def write(self, symbol: str):
        """Write a symbol under the head."""
        self.cells[self.head] = symbol

    def move(self, direction: str):
        """Move the head LEFT ('L') or RIGHT ('R')."""
        if direction == 'R':
            self.head += 1
        elif direction == 'L':
            self.head -= 1
        # 'S' (Stay) is also supported but not moved

    def get_visible_slice(self, center: int, width: int = 25) -> list[tuple[int, str]]:
        """Return (position, symbol) pairs for `width` cells centered at `center`."""
        half = width // 2
        start = center - half
        return [(pos, self.cells.get(pos, self.BLANK)) for pos in range(start, start + width)]

    def get_tape_content(self) -> str:
        """Return the meaningful tape content (trim leading/trailing blanks)."""
        if not self.cells:
            return self.BLANK
        lo = min(self.cells.keys())
        hi = max(self.cells.keys())
        return ''.join(self.cells.get(i, self.BLANK) for i in range(lo, hi + 1))

    def reset(self, input_string: str = ""):
        """Reset the tape with a new input string."""
        self.cells = {}
        self.head = 0
        for i, ch in enumerate(input_string):
            self.cells[i] = ch


class TuringMachine:
    """
    Stores the formal description of a Turing Machine:
        Q  = states
        Σ  = input alphabet
        Γ  = tape alphabet (Σ ∪ {_} ⊆ Γ)
        δ  = transition function: (state, symbol) → (new_symbol, direction, next_state)
        q0 = start state
        F  = set of accept states
        qr = reject state (optional)
    """

    def __init__(self):
        self.states: set[str] = set()
        self.input_alphabet: set[str] = set()
        self.tape_alphabet: set[str] = set()
        self.start_state: str = ""
        self.accept_states: set[str] = set()
        self.reject_state: str = ""
        # transitions[(state, symbol)] = (new_symbol, direction, next_state)
        self.transitions: dict[tuple, tuple] = {}

    def add_transition(self, state: str, symbol: str,
                       new_symbol: str, direction: str, next_state: str):
        """Register a transition rule."""
        self.transitions[(state, symbol)] = (new_symbol, direction, next_state)

    def get_transition(self, state: str, symbol: str):
        """Lookup transition; returns None if no rule exists."""
        return self.transitions.get((state, symbol))

    def parse_transitions(self, text: str) -> list[str]:
        """
        Parse transition rules from human-readable text.
        Supported format:
            q0,0 -> 1,R,q1
            q0,0->1,R,q1   (spaces around -> are optional)
        Returns a list of error messages (empty = success).
        Duplicate (state, symbol) keys produce a warning but the last rule wins.
        """
        errors = []
        self.transitions.clear()

        # Pattern: captures  state, read_sym, write_sym, direction, next_state
        pattern = re.compile(
            r'^\s*(\S+)\s*,\s*(\S+)\s*->\s*(\S+)\s*,\s*([LRlrSs])\s*,\s*(\S+)\s*$'
        )

        for lineno, raw in enumerate(text.strip().splitlines(), 1):
            line = raw.strip()
            if not line or line.startswith('#'):   # skip blanks / comments
                continue
            m = pattern.match(line)
            if not m:
                errors.append(f"Line {lineno}: Cannot parse '{line}'")
                continue
            state, sym, new_sym, direction, next_state = m.groups()
            direction = direction.upper()
            key = (state, sym)
            if key in self.transitions:
                errors.append(
                    f"Line {lineno}: Duplicate rule for ({state}, {sym}) — previous rule overwritten."
                )
            self.add_transition(state, sym, new_sym, direction, next_state)

        return errors

    def validate(self) -> list[str]:
        """Return a list of validation warnings/errors."""
        issues = []
        if not self.start_state:
            issues.append("Start state is not set.")
        if not self.accept_states:
            issues.append("No accept state(s) defined.")
        if self.start_state and self.start_state not in self.states:
            issues.append(f"Start state '{self.start_state}' not in states set.")
        for s in self.accept_states:
            if s not in self.states:
                issues.append(f"Accept state '{s}' not in states set.")
        return issues


class Simulator:
    """
    Controls step-by-step execution of a Turing Machine.
    Maintains the tape, current state, step count, and result.
    """
    MAX_STEPS = 10_000  # Infinite-loop guard

    def __init__(self, tm: TuringMachine):
        self.tm = tm
        self.tape = Tape()
        self.current_state: str = ""
        self.steps: int = 0
        self.halted: bool = False
        self.accepted: bool = False
        self.last_written_pos: int | None = None   # For highlighting changed cell
        self._history: list[tuple] = []            # Undo stack (snapshots before each step)

    def _snapshot(self) -> tuple:
        """Capture a complete, independent copy of the current machine state."""
        return (
            dict(self.tape.cells),
            self.tape.head,
            self.current_state,
            self.steps,
            self.last_written_pos,
            self.halted,
            self.accepted,
        )

    def _restore(self, snapshot: tuple):
        """Restore machine state from a snapshot produced by _snapshot()."""
        cells, head, state, steps, lwp, halted, accepted = snapshot
        self.tape.cells = cells
        self.tape.head = head
        self.current_state = state
        self.steps = steps
        self.last_written_pos = lwp
        self.halted = halted
        self.accepted = accepted

    def load(self, input_string: str):
        """Load a new input string and reset to start state."""
        self.tape.reset(input_string)
        self.current_state = self.tm.start_state
        self.steps = 0
        self.halted = False
        self.accepted = False
        self.last_written_pos = None
        self._history = []

    def undo(self) -> bool:
        """Undo the last step. Returns True if a snapshot was available."""
        if not self._history:
            return False
        self._restore(self._history.pop())
        return True

    def step(self) -> str:
        """
        Execute one transition step.
        Returns a status string: 'running', 'accepted', 'rejected', 'no_rule'.
        """
        if self.halted:
            return 'accepted' if self.accepted else 'rejected'

        # Check for explicit accept / reject states
        if self.current_state in self.tm.accept_states:
            self.halted = True
            self.accepted = True
            return 'accepted'

        if self.tm.reject_state and self.current_state == self.tm.reject_state:
            self.halted = True
            self.accepted = False
            return 'rejected'

        symbol = self.tape.read()
        rule = self.tm.get_transition(self.current_state, symbol)

        if rule is None:
            # No rule → implicit reject
            self.halted = True
            self.accepted = False
            return 'no_rule'

        new_symbol, direction, next_state = rule

        # Push snapshot so this step can be undone
        self._history.append(self._snapshot())

        # Execute the transition
        self.last_written_pos = self.tape.head
        self.tape.write(new_symbol)
        self.tape.move(direction)
        self.current_state = next_state
        self.steps += 1

        # Step limit guard
        if self.steps >= self.MAX_STEPS:
            self.halted = True
            self.accepted = False
            return 'timeout'

        # Check halting in new state
        if self.current_state in self.tm.accept_states:
            self.halted = True
            self.accepted = True
            return 'accepted'

        if self.tm.reject_state and self.current_state == self.tm.reject_state:
            self.halted = True
            self.accepted = False
            return 'rejected'

        return 'running'

    def run_to_halt(self) -> str:
        """Run until halted; return final status."""
        status = 'running'
        while status == 'running':
            status = self.step()
        return status


# ─────────────────────────────────────────────────────────────────
# ─────────────────────────────────────────────────────────────────
#  FRONTEND: Tkinter GUI  —  Rose Pine colour scheme
# ─────────────────────────────────────────────────────────────────

C = {
    # Backgrounds — darkest to lightest
    'bg':          '#191724',
    'panel':       '#1f1d2e',
    'panel2':      '#26233a',
    'panel3':      '#2d2b44',
    # Borders
    'border':      '#393552',
    'border_hi':   '#6e6a86',
    # Text
    'text':        '#e0def4',
    'muted':       '#908caa',
    'subtle':      '#6e6a86',
    # Accents
    'accent':      '#c4a7e7',   # iris / lavender
    'accent2':     '#9ccfd8',   # foam / teal
    'green':       '#3a9d70',   # pine  — accept
    'red':         '#eb6f92',   # love  — reject
    'yellow':      '#f6c177',   # gold
    # Tape
    'tape_cell':   '#1a1826',
    'tape_head':   '#c4a7e7',
    'tape_glow':   '#352860',
    'tape_chg':    '#3d2d00',
    'tape_text':   '#e0def4',
    # Buttons
    'btn':         '#2a273f',
    'btn_hover':   '#403b60',
    'btn_run':     '#0e2c1a',
    'btn_step':    '#111c40',
    'btn_reset':   '#252237',
    'btn_stop':    '#3f1222',
}

FONT_MONO     = ('Consolas', 10)
FONT_MONO_BIG = ('Consolas', 15, 'bold')
FONT_UI       = ('Segoe UI',  9)
FONT_UI_SM    = ('Segoe UI',  8)
FONT_UI_BOLD  = ('Segoe UI',  9, 'bold')
FONT_TITLE    = ('Segoe UI', 14, 'bold')
FONT_BTN      = ('Segoe UI',  9, 'bold')
FONT_HUD_VAL  = ('Segoe UI', 16, 'bold')
FONT_HUD_LBL  = ('Segoe UI',  7, 'bold')

TAPE_CELLS = 17
CELL_W     = 52
CELL_H     = 70
CELL_R     = 11


def _rr(canvas, x1, y1, x2, y2, r=8, **kw):
    """Draw a smooth rounded rectangle on *canvas* via a 12-point polygon."""
    fill    = kw.get('fill',    '')
    outline = kw.get('outline', fill)
    ow      = kw.get('width',   0)
    pts = [
        x1+r, y1,    x2-r, y1,
        x2,   y1,    x2,   y1+r,
        x2,   y2-r,  x2,   y2,
        x2-r, y2,    x1+r, y2,
        x1,   y2,    x1,   y2-r,
        x1,   y1+r,  x1,   y1,
    ]
    return canvas.create_polygon(pts, smooth=True,
                                 fill=fill, outline=outline, width=ow)


def _lighten(hex_color: str, factor: float = 0.20) -> str:
    """Return a brighter version of *hex_color* for hover states."""
    r = int(hex_color[1:3], 16)
    g = int(hex_color[3:5], 16)
    b = int(hex_color[5:7], 16)
    r = min(255, int(r + (255 - r) * factor))
    g = min(255, int(g + (255 - g) * factor))
    b = min(255, int(b + (255 - b) * factor))
    return f'#{r:02x}{g:02x}{b:02x}'


class TapeCanvas(tk.Canvas):
    """Draws the Turing tape: rounded cells, glow halo on head, head always centred."""

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C['panel'], highlightthickness=0,
                         height=CELL_H + 60, **kw)
        self.cell_data:   list[tuple[int, str]] = []
        self.head_pos:    int = 0
        self.changed_pos: int | None = None

    def render(self, cell_data: list[tuple[int, str]],
               head_pos: int, changed_pos: int | None = None):
        self.cell_data   = cell_data
        self.head_pos    = head_pos
        self.changed_pos = changed_pos
        self.after_idle(self._draw)

    def _draw(self):
        self.delete('all')
        w = self.winfo_width() or 800
        n = len(self.cell_data)
        if n == 0:
            return
        y0 = 36   # top of cells

        # Centre cell at index n//2 (the head cell) in the canvas
        x0 = w // 2 - (n // 2) * CELL_W - CELL_W // 2

        for idx, (pos, sym) in enumerate(self.cell_data):
            x       = x0 + idx * CELL_W
            cx      = x + CELL_W // 2
            is_head = (pos == self.head_pos)
            is_chg  = (self.changed_pos is not None
                       and pos == self.changed_pos and not is_head)

            if is_head:
                # Soft glow halo behind the cell
                _rr(self, x - 6, y0 - 6, x + CELL_W + 4, y0 + CELL_H + 6,
                    r=CELL_R + 6, fill=C['tape_glow'], outline='', width=0)
                fill, sym_col, ol, ow = C['tape_head'], '#ffffff', '#d8caff', 2
            elif is_chg:
                fill, sym_col, ol, ow = C['tape_chg'], C['yellow'], C['yellow'], 1
            else:
                fill, sym_col, ol, ow = C['tape_cell'], C['tape_text'], C['border'], 1

            _rr(self, x + 2, y0, x + CELL_W - 2, y0 + CELL_H,
                r=CELL_R, fill=fill, outline=ol, width=ow)
            self.create_text(cx, y0 + CELL_H // 2,
                             text=sym, fill=sym_col, font=FONT_MONO_BIG)

            # Position index below cells near the head
            if abs(pos - self.head_pos) <= 3:
                self.create_text(cx, y0 + CELL_H + 16,
                                 text=str(pos),
                                 fill=C['accent'] if is_head else C['subtle'],
                                 font=('Segoe UI', 7))

        # Head indicator: downward triangle above the centre cell
        hx = w // 2
        self.create_polygon(hx - 8, y0 - 7,
                            hx + 8, y0 - 7,
                            hx,     y0 - 1,
                            fill=C['accent'], outline='')
        self.create_text(hx, y0 - 18, text='READ/WRITE HEAD',
                         fill=C['muted'], font=('Segoe UI', 7))


class App(tk.Tk):
    """Main application window."""

    # Status chip presets  (label text, colour) — reference C palette
    _S_READY   = ('●  READY',    C['muted'])
    _S_RUNNING = ('⏵  RUNNING',  C['accent2'])
    _S_ACCEPT  = ('✔  ACCEPTED', C['green'])
    _S_REJECT  = ('✘  REJECTED', C['red'])

    def __init__(self):
        super().__init__()
        self.title('Turing Machine Simulator')
        self.configure(bg=C['bg'])
        self.resizable(True, True)
        self.minsize(960, 680)

        self.tm = TuringMachine()
        self.sim = Simulator(self.tm)
        self._run_thread: threading.Thread | None = None
        self._running    = False
        self._speed_ms   = 400
        self._table_win: tk.Toplevel | None = None

        self._build_ui()
        self._load_example()
        self._set_status(*self._S_READY)

    # ── Status chip ───────────────────────────────────────────────

    def _set_status(self, label: str, color: str):
        self.status_chip.config(text=label, fg=color)

    # ── Menu bar ──────────────────────────────────────────────────

    def _build_menu(self):
        bar = tk.Menu(self, bg=C['panel'], fg=C['text'],
                      activebackground=C['accent'], activeforeground=C['panel'],
                      relief='flat', bd=0)

        fm = tk.Menu(bar, tearoff=0, bg=C['panel'], fg=C['text'],
                     activebackground=C['accent'], activeforeground=C['panel'])
        fm.add_command(label='Open Configuration\u2026', command=self._load_config)
        fm.add_command(label='Save Configuration\u2026', command=self._save_config)
        fm.add_separator()
        fm.add_command(label='Exit', command=self.quit)
        bar.add_cascade(label='File', menu=fm)

        vm = tk.Menu(bar, tearoff=0, bg=C['panel'], fg=C['text'],
                     activebackground=C['accent'], activeforeground=C['panel'])
        vm.add_command(label='Transition Table', command=self._show_transition_table)
        bar.add_cascade(label='View', menu=vm)

        self.config(menu=bar)

    # ── Full UI ───────────────────────────────────────────────────

    def _build_ui(self):
        # TTK styling
        st = ttk.Style(self)
        st.theme_use('clam')
        st.configure('TM.TNotebook',
                     background=C['panel2'], borderwidth=0, relief='flat',
                     tabmargins=[0, 0, 0, 0])
        st.configure('TM.TNotebook.Tab',
                     background=C['btn'], foreground=C['muted'],
                     padding=[16, 6], font=FONT_UI_BOLD, borderwidth=0)
        st.map('TM.TNotebook.Tab',
               background=[('selected', C['panel2']), ('active', C['btn_hover'])],
               foreground=[('selected', C['accent']),  ('active', C['text'])])
        st.configure('TM.TScale',
                     background=C['bg'], troughcolor=C['panel2'],
                     sliderthickness=14, sliderlength=18)

        self._build_menu()

        # Header
        hdr = tk.Frame(self, bg=C['bg'], padx=20, pady=11)
        hdr.pack(fill='x')

        title_col = tk.Frame(hdr, bg=C['bg'])
        title_col.pack(side='left')
        tk.Label(title_col, text='\u25c8  TURING  MACHINE  SIMULATOR',
                 bg=C['bg'], fg=C['accent'], font=FONT_TITLE).pack(anchor='w')
        tk.Label(title_col,
                 text='Deterministic  \u00b7  Single-Tape  \u00b7  Step-by-Step Execution',
                 bg=C['bg'], fg=C['subtle'], font=FONT_UI_SM).pack(
                     anchor='w', pady=(3, 0))

        chip_outer = tk.Frame(hdr, bg=C['panel2'],
                              highlightbackground=C['border'], highlightthickness=1)
        chip_outer.pack(side='right', pady=4)
        _lbl, _clr = self._S_READY
        self.status_chip = tk.Label(chip_outer, text=_lbl,
                                    bg=C['panel2'], fg=_clr,
                                    font=FONT_UI_BOLD, padx=14, pady=6)
        self.status_chip.pack()

        # Two-tone accent separator bar
        sep = tk.Canvas(self, height=3, bg=C['bg'], highlightthickness=0)
        sep.pack(fill='x')

        def _draw_sep(e=None, c=sep):
            c.delete('all')
            w = c.winfo_width()
            c.create_rectangle(0, 0, w * 3 // 5, 3, fill=C['accent'],  outline='')
            c.create_rectangle(w * 3 // 5, 0, w * 4 // 5, 3,
                               fill=C['panel2'], outline='')
        sep.bind('<Configure>', _draw_sep)
        self.after(80, _draw_sep)

        # Main content area
        content = tk.Frame(self, bg=C['bg'])
        content.pack(fill='both', expand=True, padx=14, pady=(8, 10))

        left = tk.Frame(content, bg=C['bg'])
        left.pack(side='left', fill='both', expand=True)

        right = tk.Frame(content, bg=C['panel'],
                         highlightbackground=C['border'], highlightthickness=1)
        right.pack(side='right', fill='y', padx=(14, 0))

        # Tape card
        tape_card = tk.Frame(left, bg=C['panel'],
                             highlightbackground=C['border_hi'], highlightthickness=1)
        tape_card.pack(fill='x', pady=(0, 10))

        tape_top = tk.Frame(tape_card, bg=C['panel'])
        tape_top.pack(fill='x', padx=14, pady=(8, 0))
        tk.Label(tape_top, text='T A P E',
                 bg=C['panel'], fg=C['muted'],
                 font=('Segoe UI', 8, 'bold')).pack(side='left')

        self.tape_canvas = TapeCanvas(tape_card)
        self.tape_canvas.pack(fill='x', expand=True, padx=8, pady=(4, 8))

        # Status HUD — 4 metric cards
        hud = tk.Frame(left, bg=C['bg'])
        hud.pack(fill='x', pady=(0, 10))

        for title, attr, color in (
            ('STATE',  'lbl_state',  C['accent']),
            ('HEAD',   'lbl_head',   C['accent2']),
            ('SYMBOL', 'lbl_symbol', C['yellow']),
            ('STEPS',  'lbl_steps',  C['text']),
        ):
            card = tk.Frame(hud, bg=C['panel2'],
                            highlightbackground=C['border'], highlightthickness=1)
            card.pack(side='left', fill='both', expand=True, padx=(0, 8))
            tk.Frame(card, bg=color, height=3).pack(fill='x')
            tk.Label(card, text=title, bg=C['panel2'],
                     fg=C['subtle'], font=FONT_HUD_LBL).pack(pady=(7, 0))
            val = tk.Label(card, text='\u2014', bg=C['panel2'],
                           fg=color, font=FONT_HUD_VAL)
            val.pack(pady=(1, 8))
            setattr(self, attr, val)

        # Result banner
        self.result_banner = tk.Label(left, text='', bg=C['bg'],
                                      font=('Segoe UI', 12, 'bold'),
                                      pady=6, anchor='center')
        self.result_banner.pack(fill='x', pady=(0, 8))

        # Tabbed config / transitions
        nb = ttk.Notebook(left, style='TM.TNotebook')
        nb.pack(fill='both', expand=True, pady=(0, 8))

        # Tab 1 — Machine
        tab_m = tk.Frame(nb, bg=C['panel2'])
        nb.add(tab_m, text='  Machine  ')

        grid_m = tk.Frame(tab_m, bg=C['panel2'])
        grid_m.pack(fill='x', padx=14, pady=(14, 8))

        tk.Label(grid_m, text='States  (comma-separated)',
                 bg=C['panel2'], fg=C['muted'], font=FONT_UI_SM
                 ).grid(row=0, column=0, columnspan=6, sticky='w')
        self.entry_states = self._make_entry(grid_m, width=52)
        self.entry_states.grid(row=1, column=0, columnspan=6,
                               sticky='ew', pady=(3, 10))

        for col_i, (lbl_txt, attr, w) in enumerate([
            ('Start  state', 'entry_start',  12),
            ('Accept state', 'entry_accept', 16),
            ('Reject state', 'entry_reject', 12),
        ]):
            tk.Label(grid_m, text=lbl_txt,
                     bg=C['panel2'], fg=C['muted'], font=FONT_UI_SM
                     ).grid(row=2, column=col_i * 2, sticky='w', padx=(0, 4))
            e = self._make_entry(grid_m, width=w)
            e.grid(row=3, column=col_i * 2, sticky='ew',
                   padx=(0, 18), pady=(3, 10))
            setattr(self, attr, e)

        tk.Label(grid_m, text='Input string',
                 bg=C['panel2'], fg=C['muted'], font=FONT_UI_SM
                 ).grid(row=4, column=0, columnspan=6, sticky='w')
        self.entry_input = self._make_entry(grid_m, width=42)
        self.entry_input.grid(row=5, column=0, columnspan=6,
                              sticky='ew', pady=(3, 10))

        for c in range(6):
            grid_m.columnconfigure(c, weight=1)

        # Tab 2 — Transitions
        tab_t = tk.Frame(nb, bg=C['panel2'])
        nb.add(tab_t, text='  Transitions  ')

        tk.Label(tab_t,
                 text='  Format:  state, sym  \u2192  new_sym, Dir, next_state'
                      '      (# comment)',
                 bg=C['panel2'], fg=C['subtle'],
                 font=('Segoe UI', 8), anchor='w'
                 ).pack(fill='x', padx=12, pady=(8, 4))

        self.txt_transitions = scrolledtext.ScrolledText(
            tab_t, bg=C['panel'], fg=C['text'],
            insertbackground=C['accent'],
            relief='flat', font=FONT_MONO,
            highlightbackground=C['border_hi'], highlightthickness=1,
            padx=10, pady=8,
        )
        self.txt_transitions.pack(fill='both', expand=True, padx=8, pady=(0, 8))

        self.txt_transitions.tag_config('hl_comment',   foreground=C['subtle'])
        self.txt_transitions.tag_config('hl_state',     foreground=C['accent'])
        self.txt_transitions.tag_config('hl_symbol',    foreground=C['yellow'])
        self.txt_transitions.tag_config('hl_arrow',     foreground=C['subtle'])
        self.txt_transitions.tag_config('hl_direction', foreground=C['accent2'])
        self.txt_transitions.tag_config('hl_error',     foreground=C['red'],
                                        underline=True)

        self.txt_transitions.bind('<KeyRelease>',
                                  lambda _e: self._highlight_transitions())
        self.txt_transitions.bind('<<Paste>>',
                                  lambda _e: self.after(10, self._highlight_transitions))

        # Controls row
        ctrl = tk.Frame(left, bg=C['bg'])
        ctrl.pack(fill='x', pady=(0, 4))

        btn_row = tk.Frame(ctrl, bg=C['bg'])
        btn_row.pack(fill='x', pady=(0, 6))

        self.btn_load  = self._make_btn(btn_row, '\u2b06  Load',  C['btn'],       self._load_machine)
        self.btn_step  = self._make_btn(btn_row, '\u25b6  Step',  C['btn_step'],  self._step)
        self.btn_undo  = self._make_btn(btn_row, '\u25c4  Undo',  C['btn'],       self._undo)
        tk.Frame(btn_row, bg=C['border'], width=1).pack(
            side='left', fill='y', padx=8, pady=4)
        self.btn_run   = self._make_btn(btn_row, '\u23e9  Run',   C['btn_run'],   self._run)
        self.btn_stop  = self._make_btn(btn_row, '\u23f9  Stop',  C['btn_stop'],  self._stop)
        self.btn_reset = self._make_btn(btn_row, '\u21ba  Reset', C['btn_reset'], self._reset)

        for btn in (self.btn_load, self.btn_step, self.btn_undo,
                    self.btn_run,  self.btn_stop,  self.btn_reset):
            btn.pack(side='left', padx=3)

        self.btn_stop.config(state='disabled')

        # Speed strip
        spd = tk.Frame(ctrl, bg=C['bg'])
        spd.pack(fill='x')
        tk.Label(spd, text='Speed', bg=C['bg'],
                 fg=C['muted'], font=FONT_UI_SM).pack(side='left', padx=(2, 8))
        self.speed_var = tk.IntVar(value=400)
        ttk.Scale(spd, from_=50, to=1000, orient='horizontal',
                  variable=self.speed_var, style='TM.TScale',
                  length=180, command=self._on_speed_change).pack(side='left')
        self.spd_lbl = tk.Label(spd, text='400 ms', bg=C['bg'],
                                fg=C['muted'], font=FONT_UI_SM, width=8)
        self.spd_lbl.pack(side='left', padx=6)

        # Log panel
        log_hdr = tk.Frame(right, bg=C['panel'])
        log_hdr.pack(fill='x')
        tk.Label(log_hdr, text='EXECUTION LOG',
                 bg=C['panel'], fg=C['accent'],
                 font=('Segoe UI', 8, 'bold')).pack(side='left', padx=12, pady=8)
        clr = tk.Label(log_hdr, text='clear', bg=C['panel'],
                       fg=C['muted'], cursor='hand2', font=FONT_UI_SM)
        clr.pack(side='right', padx=12)
        clr.bind('<Button-1>', lambda _e: self._log_clear())

        tk.Frame(right, bg=C['border'], height=1).pack(fill='x')

        self.log_box = scrolledtext.ScrolledText(
            right, width=26,
            bg=C['panel'], fg=C['text'],
            insertbackground=C['text'],
            relief='flat', font=('Consolas', 8),
            state='disabled', highlightthickness=0,
            padx=8, pady=6,
        )
        self.log_box.pack(fill='both', expand=True)

        self.log_box.tag_config('accept', foreground=C['green'])
        self.log_box.tag_config('reject', foreground=C['red'])
        self.log_box.tag_config('step',   foreground=C['accent'])
        self.log_box.tag_config('info',   foreground=C['muted'])

    def _make_entry(self, parent, **kw):
        """Return a consistently styled tk.Entry."""
        return tk.Entry(parent,
                        bg=C['panel'], fg=C['text'],
                        insertbackground=C['accent'],
                        relief='flat', font=FONT_MONO,
                        highlightbackground=C['border_hi'],
                        highlightthickness=1,
                        selectbackground=C['accent'],
                        selectforeground=C['panel'], **kw)

    def _make_btn(self, parent, text: str, color: str, command):
        """Return a styled tk.Button with a hover-tint effect."""
        hover = _lighten(color)
        btn = tk.Button(parent,
                        text=text, bg=color, fg=C['text'],
                        activebackground=hover, activeforeground=C['text'],
                        relief='flat', font=FONT_BTN,
                        cursor='hand2', padx=14, pady=7,
                        command=command, bd=0)
        btn.bind('<Enter>', lambda _e, b=btn, h=hover:  b.config(bg=h))
        btn.bind('<Leave>', lambda _e, b=btn, c=color:  b.config(bg=c))
        return btn

    # ── Example pre-load ──────────────────────────────────────────

    def _load_example(self):
        """
        Pre-load a classic example: accepts binary strings with equal 0s and 1s
        using a simple incrementing/decrementing algorithm.

        Simpler demonstrative example: accepts strings of the form 0^n 1^n (n≥0).
        For a cleaner demo we load the classic 'cross off 0s and 1s' machine.
        """
        example_states     = "q0,q1,q2,q3,q4,qaccept,qreject"
        example_start      = "q0"
        example_accept     = "qaccept"
        example_reject     = "qreject"
        example_input      = "0011"
        example_transitions = """\
# Accepts strings of the form 0^n 1^n (n >= 1), e.g., 01, 0011, 000111
# q0: scan right looking for a 0
q0,0 -> X,R,q1
q0,Y -> Y,R,q0
q0,_ -> _,R,qaccept
# q1: move right past 0s and Ys to find a 1
q1,0 -> 0,R,q1
q1,Y -> Y,R,q1
q1,1 -> Y,L,q2
q1,_ -> _,R,qreject
# q2: move left back to the leftmost unmarked 0
q2,0 -> 0,L,q2
q2,Y -> Y,L,q2
q2,X -> X,R,q0
# Anything unmatched falls through to reject implicitly
"""

        self.entry_states.insert(0, example_states)
        self.entry_start .insert(0, example_start)
        self.entry_accept.insert(0, example_accept)
        self.entry_reject.insert(0, example_reject)
        self.entry_input .insert(0, example_input)
        self.txt_transitions.insert('1.0', example_transitions)
        self._highlight_transitions()

    # ── Event handlers ────────────────────────────────────────────

    def _on_speed_change(self, val):
        self._speed_ms = int(float(val))
        if hasattr(self, 'spd_lbl'):
            self.spd_lbl.config(text=f'{self._speed_ms} ms')

    def _load_machine(self):
        """Parse configuration fields and set up the TuringMachine object."""
        # Parse states
        states_raw = self.entry_states.get().strip()
        if not states_raw:
            messagebox.showerror("Config Error", "Please enter at least one state.")
            return
        self.tm.states = {s.strip() for s in states_raw.split(',')}

        # Start state
        start = self.entry_start.get().strip()
        if not start:
            messagebox.showerror("Config Error", "Please enter a start state.")
            return
        self.tm.start_state = start

        # Accept states
        accept_raw = self.entry_accept.get().strip()
        self.tm.accept_states = {s.strip() for s in accept_raw.split(',')} if accept_raw else set()

        # Reject state (optional)
        reject = self.entry_reject.get().strip()
        self.tm.reject_state = reject if reject else ""

        # Parse transitions
        tr_text = self.txt_transitions.get('1.0', 'end')
        errors = self.tm.parse_transitions(tr_text)
        if errors:
            messagebox.showerror("Transition Error", "\n".join(errors[:10]))
            return

        # Validate
        issues = self.tm.validate()
        if issues:
            proceed = messagebox.askyesno(
                "Validation Warnings",
                "Warnings:\n" + "\n".join(issues) + "\n\nContinue anyway?"
            )
            if not proceed:
                return

        # Load input and reset simulator
        input_str = self.entry_input.get().strip()
        self.sim = Simulator(self.tm)
        self.sim.load(input_str)

        self._log_clear()
        self._log(f"Machine loaded. Input: '{input_str}'", 'info')
        self._log(f"Transitions: {len(self.tm.transitions)}", 'info')
        self.result_banner.config(text="", bg=C['bg'])
        self._set_status(*self._S_READY)
        self._refresh_ui()
        # Auto-refresh the transition table if the window is already open
        if self._table_win and self._table_win.winfo_exists():
            self._show_transition_table()

    def _step(self):
        if self._running:
            messagebox.showwarning("Running", "Stop auto-run before stepping manually.")
            return
        if self.sim.halted:
            messagebox.showinfo("Halted", "Machine has already halted. Press RESET to restart.")
            return
        if not self.tm.start_state:
            messagebox.showwarning("Not Loaded", "Please load a machine first.")
            return

        status = self.sim.step()
        self._refresh_ui()
        self._log_step(status)

        if status != 'running':
            self._show_result(status)

    def _run(self):
        if self._running:
            return
        if self.sim.halted:
            messagebox.showinfo("Halted", "Machine halted. Press RESET first.")
            return
        if not self.tm.start_state:
            messagebox.showwarning("Not Loaded", "Please load a machine first.")
            return

        self._running = True
        self._set_run_mode(True)
        self._run_thread = threading.Thread(target=self._run_loop, daemon=True)
        self._run_thread.start()

    def _run_loop(self):
        """Background thread: steps machine with a delay, posts UI updates via `after`."""
        while self._running and not self.sim.halted:
            status = self.sim.step()
            # Schedule UI update on the main thread
            self.after(0, self._refresh_ui)
            self.after(0, self._log_step, status)
            if status != 'running':
                self.after(0, self._show_result, status)
                break
            time.sleep(self._speed_ms / 1000.0)
        self._running = False
        self.after(0, self._set_run_mode, False)

    def _stop(self):
        self._running = False

    def _reset(self):
        self._running = False
        input_str = self.entry_input.get().strip()
        self.sim.load(input_str)
        self.result_banner.config(text="", bg=C['bg'])
        self._log_clear()
        self._log("Reset. Ready.", 'info')
        self._set_status(*self._S_READY)
        self._refresh_ui()

    def _set_run_mode(self, running: bool):
        """Enable/disable buttons appropriately during auto-run."""
        idle_state  = 'normal' if not running else 'disabled'
        stop_state  = 'normal' if running     else 'disabled'
        for btn in (self.btn_load, self.btn_step, self.btn_undo,
                    self.btn_run, self.btn_reset):
            btn.config(state=idle_state)
        self.btn_stop.config(state=stop_state)
        if running:
            self._set_status(*self._S_RUNNING)

    # ── UI update helpers ─────────────────────────────────────────

    def _refresh_ui(self):
        """Redraw tape, update status labels."""
        head    = self.sim.tape.head
        state   = self.sim.current_state or "—"
        symbol  = self.sim.tape.read()
        steps   = self.sim.steps
        changed = self.sim.last_written_pos

        # Tape canvas
        cell_data = self.sim.tape.get_visible_slice(head, TAPE_CELLS)
        self.tape_canvas.render(cell_data, head, changed)

        # Status labels
        self.lbl_state .config(text=state)
        self.lbl_head  .config(text=str(head))
        self.lbl_symbol.config(text=symbol)
        self.lbl_steps .config(text=str(steps))

        # Colour the state label based on accept/reject
        if state in self.tm.accept_states:
            self.lbl_state.config(fg=C['green'])
        elif state == self.tm.reject_state and self.tm.reject_state:
            self.lbl_state.config(fg=C['red'])
        else:
            self.lbl_state.config(fg=C['accent'])

    def _show_result(self, status: str):
        """Display the ACCEPTED / REJECTED / TIMEOUT banner."""
        if status == 'accepted':
            self.result_banner.config(
                text=f"  ✔  ACCEPTED  after {self.sim.steps} steps  ",
                bg=C['green'], fg='white')
            self._set_status(*self._S_ACCEPT)
        elif status == 'timeout':
            self.result_banner.config(
                text=f"  ⚠  TIMEOUT  — exceeded {self.sim.MAX_STEPS} steps  ",
                bg=C['yellow'], fg=C['panel'])
            self._set_status(*self._S_REJECT)
        elif status == 'no_rule':
            self.result_banner.config(
                text=f"  ✘  REJECTED  (no rule) after {self.sim.steps} steps  ",
                bg=C['red'], fg='white')
            self._set_status(*self._S_REJECT)
        else:
            self.result_banner.config(
                text=f"  ✘  REJECTED  after {self.sim.steps} steps  ",
                bg=C['red'], fg='white')
            self._set_status(*self._S_REJECT)

    def _log(self, msg: str, tag: str = ''):
        """Append a line to the execution log."""
        self.log_box.config(state='normal')
        self.log_box.insert('end', msg + '\n', tag)
        self.log_box.see('end')
        self.log_box.config(state='disabled')

    def _log_step(self, status: str):
        state   = self.sim.current_state
        head    = self.sim.tape.head
        steps   = self.sim.steps
        tape    = self.sim.tape.get_tape_content()

        if status == 'running':
            self._log(f"[{steps:>5}] {state:<8} @{head}", 'step')
        elif status == 'accepted':
            self._log(f"[{steps:>5}] ACCEPTED", 'accept')
            self._log(f"       Tape: {tape}", 'accept')
        elif status == 'timeout':
            self._log(f"[{steps:>5}] TIMEOUT (>{self.sim.MAX_STEPS} steps)", 'reject')
            self._log(f"       Tape: {tape}", 'reject')
        else:
            self._log(f"[{steps:>5}] REJECTED ({status})", 'reject')
            self._log(f"       Tape: {tape}", 'reject')

    def _save_config(self):
        """Save current machine configuration to a JSON file."""
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Save Machine Configuration"
        )
        if not path:
            return
        config = {
            "states":      self.entry_states.get().strip(),
            "start_state": self.entry_start.get().strip(),
            "accept_states": self.entry_accept.get().strip(),
            "reject_state":  self.entry_reject.get().strip(),
            "input_string":  self.entry_input.get().strip(),
            "transitions":   self.txt_transitions.get('1.0', 'end').rstrip('\n'),
        }
        try:
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2)
            self._log(f"Config saved to {path}", 'info')
        except OSError as e:
            messagebox.showerror("Save Error", str(e))

    def _load_config(self):
        """Load a machine configuration from a JSON file."""
        path = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Open Machine Configuration"
        )
        if not path:
            return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                config = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            messagebox.showerror("Load Error", str(e))
            return

        # Clear and populate all fields
        for entry, key in (
            (self.entry_states,  "states"),
            (self.entry_start,   "start_state"),
            (self.entry_accept,  "accept_states"),
            (self.entry_reject,  "reject_state"),
            (self.entry_input,   "input_string"),
        ):
            entry.delete(0, 'end')
            entry.insert(0, config.get(key, ''))

        self.txt_transitions.delete('1.0', 'end')
        self.txt_transitions.insert('1.0', config.get('transitions', ''))
        self._highlight_transitions()
        self._log(f"Config loaded from {path}", 'info')

    # ── Step-back (Undo) ──────────────────────────────────────────

    def _undo(self):
        """Undo the last step and refresh the UI."""
        if self._running:
            messagebox.showwarning("Running", "Stop auto-run before undoing.")
            return
        if not self.tm.start_state:
            messagebox.showwarning("Not Loaded", "Please load a machine first.")
            return
        if not self.sim.undo():
            messagebox.showinfo("Undo", "Nothing to undo — already at the start.")
            return
        # Clear any halted result banner since we've gone back
        self.result_banner.config(text="", bg=C['bg'])
        self._set_status(*self._S_READY)
        self._refresh_ui()
        steps = self.sim.steps
        self._log(f"[{steps:>5}] \u21a9 UNDO \u2014 back to step {steps}", 'info')

    # ── Transition table viewer ───────────────────────────────────

    def _show_transition_table(self):
        """Open (or refresh) a Toplevel window showing the δ transition table."""
        if not self.tm.transitions:
            messagebox.showinfo("Table", "No transitions loaded. Press LOAD first.")
            return

        # Re-use existing window if still open
        if self._table_win and self._table_win.winfo_exists():
            self._table_win.lift()
        else:
            self._table_win = tk.Toplevel(self)
            self._table_win.title("Transition Table  δ(state, symbol)")
            self._table_win.configure(bg=C['bg'])
            self._table_win.resizable(True, True)
            # Build a Text widget inside the window
            self._table_text = tk.Text(
                self._table_win, bg=C['panel'], fg=C['text'],
                font=('Courier New', 10), relief='flat',
                wrap='none', state='disabled',
                highlightthickness=0
            )
            sb_x = tk.Scrollbar(self._table_win, orient='horizontal',
                                 command=self._table_text.xview)
            sb_y = tk.Scrollbar(self._table_win, orient='vertical',
                                 command=self._table_text.yview)
            self._table_text.configure(xscrollcommand=sb_x.set,
                                       yscrollcommand=sb_y.set)
            sb_y.pack(side='right', fill='y')
            sb_x.pack(side='bottom', fill='x')
            self._table_text.pack(fill='both', expand=True, padx=4, pady=4)

            # Configure colour tags for the table
            self._table_text.tag_config('hdr',    foreground=C['accent'], font=('Courier New', 10, 'bold'))
            self._table_text.tag_config('state',  foreground=C['accent'])
            self._table_text.tag_config('rule',   foreground=C['yellow'])
            self._table_text.tag_config('empty',  foreground=C['muted'])
            self._table_text.tag_config('sep',    foreground=C['border'])

        self._render_transition_table()

    def _render_transition_table(self):
        """Write the formatted δ table into self._table_text."""
        tm = self.tm
        states  = sorted(tm.states)
        symbols = sorted({sym for (_st, sym) in tm.transitions})

        STATE_W  = max([len(s) for s in states] or [5]) + 2
        SYM_W    = max([len(sym) for sym in symbols] or [3]) + 2
        CELL_W   = max(
            max([len(f"{w},{d},{ns}") for (_w, d, ns) in tm.transitions.values()] or [7]),
            SYM_W,
        ) + 2

        def pad(s, w):
            return s.center(w)

        sep_row = '─' * STATE_W + '┼' + ('─' * CELL_W + '┼') * len(symbols)

        t = self._table_text
        t.config(state='normal')
        t.delete('1.0', 'end')

        # Header row
        header = pad('δ', STATE_W) + '│' + '│'.join(pad(sym, CELL_W) for sym in symbols)
        t.insert('end', header + '\n', 'hdr')
        t.insert('end', sep_row + '\n', 'sep')

        for state in states:
            row_start = t.index('end')
            t.insert('end', pad(state, STATE_W), 'state')
            t.insert('end', '│', 'sep')
            for sym in symbols:
                rule = tm.transitions.get((state, sym))
                if rule:
                    cell = pad(f"{rule[0]},{rule[1]},{rule[2]}", CELL_W)
                    t.insert('end', cell, 'rule')
                else:
                    t.insert('end', pad('—', CELL_W), 'empty')
                t.insert('end', '│', 'sep')
            t.insert('end', '\n')
            t.insert('end', sep_row + '\n', 'sep')

        t.config(state='disabled')

    # ── Syntax highlighting ───────────────────────────────────────

    _TRANSITION_RE = re.compile(
        r'^(\s*)(\S+)(\s*,\s*)(\S+)(\s*->\s*)(\S+)(\s*,\s*)([LRSlrs])(\s*,\s*)(\S+)(\s*)$'
    )

    def _highlight_transitions(self):
        """Re-apply syntax highlighting to the entire transition editor."""
        t = self.txt_transitions
        # Remove all highlight tags
        for tag in ('hl_comment', 'hl_state', 'hl_symbol',
                    'hl_arrow', 'hl_direction', 'hl_error'):
            t.tag_remove(tag, '1.0', 'end')

        content = t.get('1.0', 'end')
        for lineno, raw in enumerate(content.splitlines(), 1):
            line_start = f'{lineno}.0'
            line_end   = f'{lineno}.end'
            stripped   = raw.strip()

            if not stripped:
                continue

            if stripped.startswith('#'):
                t.tag_add('hl_comment', line_start, line_end)
                continue

            m = self._TRANSITION_RE.match(raw)
            if not m:
                t.tag_add('hl_error', line_start, line_end)
                continue

            # m.groups(): lead_ws, state, comma1, sym, arrow, new_sym, comma2, dir, comma3, next_state, trail
            col = 0
            for i, chunk in enumerate(m.groups()):
                start = f'{lineno}.{col}'
                end   = f'{lineno}.{col + len(chunk)}'
                # Groups (0-indexed): 0=ws, 1=state, 2=,, 3=sym, 4=->, 5=new_sym, 6=,, 7=dir, 8=,, 9=next, 10=ws
                if   i == 1:  t.tag_add('hl_state',     start, end)
                elif i == 3:  t.tag_add('hl_symbol',    start, end)
                elif i == 4:  t.tag_add('hl_arrow',     start, end)
                elif i == 5:  t.tag_add('hl_symbol',    start, end)
                elif i == 7:  t.tag_add('hl_direction', start, end)
                elif i == 9:  t.tag_add('hl_state',     start, end)
                col += len(chunk)

    def _log_clear(self):
        self.log_box.config(state='normal')
        self.log_box.delete('1.0', 'end')
        self.log_box.config(state='disabled')


# ─────────────────────────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    app = App()

    # Force the canvas to draw once the window is ready
    def _initial_render():
        half = TAPE_CELLS // 2
        cells = [(i, '_') for i in range(-half, TAPE_CELLS - half)]
        app.tape_canvas.render(cells, head_pos=0)
    app.after(100, _initial_render)

    app.mainloop()