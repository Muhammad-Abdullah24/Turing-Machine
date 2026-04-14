from __future__ import annotations

import json
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext
import time
import threading
import re

# ─────────────────────────────────────────────────────────────────
#  BACKEND  —  Tape · TuringMachine · Simulator
# ─────────────────────────────────────────────────────────────────

class Tape:
    """Infinite tape backed by a dict. Missing positions read as BLANK ('_')."""
    BLANK = '_'

    def __init__(self, input_string: str = ''):
        self.cells: dict[int, str] = {}
        self.head: int = 0
        for i, ch in enumerate(input_string):
            self.cells[i] = ch

    def read(self) -> str:
        return self.cells.get(self.head, self.BLANK)

    def write(self, symbol: str):
        self.cells[self.head] = symbol

    def move(self, direction: str):
        if direction == 'R':
            self.head += 1
        elif direction == 'L':
            self.head -= 1

    def get_visible_slice(self, center: int, width: int = 21) -> list[tuple[int, str]]:
        half  = width // 2
        start = center - half
        return [(p, self.cells.get(p, self.BLANK)) for p in range(start, start + width)]

    def get_tape_content(self) -> str:
        if not self.cells:
            return self.BLANK
        lo = min(self.cells.keys())
        hi = max(self.cells.keys())
        return ''.join(self.cells.get(i, self.BLANK) for i in range(lo, hi + 1))

    def reset(self, input_string: str = ''):
        self.cells = {}
        self.head  = 0
        for i, ch in enumerate(input_string):
            self.cells[i] = ch


class TuringMachine:
    """Stores the formal description: Q, delta, q0, F, qr."""

    def __init__(self):
        self.states:         set[str]            = set()
        self.input_alphabet: set[str]            = set()
        self.tape_alphabet:  set[str]            = set()
        self.start_state:    str                 = ''
        self.accept_states:  set[str]            = set()
        self.reject_state:   str                 = ''
        self.transitions:    dict[tuple, tuple]  = {}

    def add_transition(self, state: str, symbol: str,
                       new_symbol: str, direction: str, next_state: str):
        self.transitions[(state, symbol)] = (new_symbol, direction, next_state)

    def get_transition(self, state: str, symbol: str):
        return self.transitions.get((state, symbol))

    def parse_transitions(self, text: str) -> list[str]:
        errors = []
        self.transitions.clear()
        pattern = re.compile(
            r'^\s*(\S+)\s*,\s*(\S+)\s*->\s*(\S+)\s*,\s*([LRlrSs])\s*,\s*(\S+)\s*$'
        )
        for lineno, raw in enumerate(text.strip().splitlines(), 1):
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            m = pattern.match(line)
            if not m:
                errors.append(f'Line {lineno}: Cannot parse  "{line}"')
                continue
            state, sym, new_sym, direction, next_state = m.groups()
            direction = direction.upper()
            key = (state, sym)
            if key in self.transitions:
                errors.append(
                    f'Line {lineno}: Duplicate rule for ({state}, {sym}) - new rule overwrites previous.')
            self.add_transition(state, sym, new_sym, direction, next_state)
        return errors

    def validate(self) -> list[str]:
        issues = []
        if not self.start_state:
            issues.append('Start state is not set.')
        if not self.accept_states:
            issues.append('No accept state(s) defined.')
        if self.start_state and self.start_state not in self.states:
            issues.append(f"Start state '{self.start_state}' not in states set.")
        for s in self.accept_states:
            if s not in self.states:
                issues.append(f"Accept state '{s}' not in states set.")
        return issues


class Simulator:
    """Step-by-step execution with full undo history."""
    MAX_STEPS = 10_000

    def __init__(self, tm: TuringMachine):
        self.tm               = tm
        self.tape             = Tape()
        self.current_state:   str          = ''
        self.steps:           int          = 0
        self.halted:          bool         = False
        self.accepted:        bool         = False
        self.last_written_pos: int | None  = None
        self._history:        list[tuple]  = []
        self.last_rule:       tuple | None = None

    def _snapshot(self) -> tuple:
        return (dict(self.tape.cells), self.tape.head,
                self.current_state, self.steps,
                self.last_written_pos, self.halted, self.accepted)

    def _restore(self, snap: tuple):
        cells, head, state, steps, lwp, halted, accepted = snap
        self.tape.cells       = cells
        self.tape.head        = head
        self.current_state    = state
        self.steps            = steps
        self.last_written_pos = lwp
        self.halted           = halted
        self.accepted         = accepted

    def load(self, input_string: str):
        self.tape.reset(input_string)
        self.current_state    = self.tm.start_state
        self.steps            = 0
        self.halted           = False
        self.accepted         = False
        self.last_written_pos = None
        self._history         = []
        self.last_rule        = None

    def undo(self) -> bool:
        if not self._history:
            return False
        self._restore(self._history.pop())
        return True

    def step(self) -> str:
        if self.halted:
            return 'accepted' if self.accepted else 'rejected'

        if self.current_state in self.tm.accept_states:
            self.halted   = True
            self.accepted = True
            return 'accepted'

        if self.tm.reject_state and self.current_state == self.tm.reject_state:
            self.halted   = True
            self.accepted = False
            return 'rejected'

        symbol = self.tape.read()
        rule   = self.tm.get_transition(self.current_state, symbol)

        if rule is None:
            self.halted    = True
            self.accepted  = False
            self.last_rule = None
            return 'no_rule'

        new_symbol, direction, next_state = rule
        self.last_rule = (self.current_state, symbol, new_symbol, direction, next_state)
        self._history.append(self._snapshot())

        self.last_written_pos = self.tape.head
        self.tape.write(new_symbol)
        self.tape.move(direction)
        self.current_state = next_state
        self.steps        += 1

        if self.steps >= self.MAX_STEPS:
            self.halted   = True
            self.accepted = False
            return 'timeout'

        if self.current_state in self.tm.accept_states:
            self.halted   = True
            self.accepted = True
            return 'accepted'

        if self.tm.reject_state and self.current_state == self.tm.reject_state:
            self.halted   = True
            self.accepted = False
            return 'rejected'

        return 'running'

    def run_to_halt(self) -> str:
        status = 'running'
        while status == 'running':
            status = self.step()
        return status


# ─────────────────────────────────────────────────────────────────
#  CONSTANTS  ·  COLOURS  ·  FONTS
# ─────────────────────────────────────────────────────────────────

C = {
    'bg':        '#191724',
    'panel':     '#1f1d2e',
    'panel2':    '#26233a',
    'border':    '#393552',
    'border_hi': '#6e6a86',
    'text':      '#e0def4',
    'muted':     '#908caa',
    'subtle':    '#6e6a86',
    'accent':    '#c4a7e7',
    'accent2':   '#9ccfd8',
    'green':     '#3a9d70',
    'red':       '#eb6f92',
    'yellow':    '#f6c177',
    'tape_cell': '#1a1826',
    'tape_head': '#c4a7e7',
    'tape_glow': '#352860',
    'tape_chg':  '#3d2d00',
    'tape_text': '#e0def4',
    'btn':       '#2a273f',
    'btn_hover': '#403b60',
    'btn_run':   '#0e2c1a',
    'btn_step':  '#111c40',
    'btn_reset': '#252237',
    'btn_stop':  '#3f1222',
}

FONT_MONO     = ('Consolas', 10)
FONT_MONO_BIG = ('Consolas', 15, 'bold')
FONT_MONO_SM  = ('Consolas',  8)
FONT_UI       = ('Segoe UI',  9)
FONT_UI_SM    = ('Segoe UI',  8)
FONT_UI_BOLD  = ('Segoe UI',  9, 'bold')
FONT_TITLE    = ('Segoe UI', 14, 'bold')
FONT_BTN      = ('Segoe UI',  9, 'bold')
FONT_HUD_VAL  = ('Segoe UI', 15, 'bold')
FONT_HUD_LBL  = ('Segoe UI',  7, 'bold')

TAPE_CELLS         = 19
CELL_W             = 50
CELL_H             = 62
CELL_R             = 10
DEFAULT_CANVAS_W   = 900  # fallback canvas width before first Configure event


def _draw_rounded_rect(canvas, x1, y1, x2, y2, r=8, **kw):
    """Draw a smooth rounded-rectangle polygon on canvas."""
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


def _lighten(color: str, factor: float = 0.22) -> str:
    r = int(color[1:3], 16)
    g = int(color[3:5], 16)
    b = int(color[5:7], 16)
    r = min(255, int(r + (255 - r) * factor))
    g = min(255, int(g + (255 - g) * factor))
    b = min(255, int(b + (255 - b) * factor))
    return f'#{r:02x}{g:02x}{b:02x}'


# ─────────────────────────────────────────────────────────────────
#  TAPE CANVAS
# ─────────────────────────────────────────────────────────────────

class TapeCanvas(tk.Canvas):
    """Animated tape: rounded cells, glow halo on head, head always centred."""

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C['panel'], highlightthickness=0,
                         height=CELL_H + 58, **kw)
        self.cell_data:   list[tuple[int, str]] = []
        self.head_pos:    int                   = 0
        self.changed_pos: int | None            = None

    def render(self, cell_data: list[tuple[int, str]],
               head_pos: int, changed_pos: int | None = None):
        self.cell_data   = cell_data
        self.head_pos    = head_pos
        self.changed_pos = changed_pos
        self.after_idle(self._draw)

    def _draw(self):
        self.delete('all')
        w = self.winfo_width() or DEFAULT_CANVAS_W
        n = len(self.cell_data)
        if not n:
            return
        y0 = 34
        x0 = w // 2 - (n // 2) * CELL_W - CELL_W // 2

        for idx, (pos, sym) in enumerate(self.cell_data):
            x       = x0 + idx * CELL_W
            cx      = x + CELL_W // 2
            is_head = (pos == self.head_pos)
            is_chg  = (self.changed_pos is not None
                       and pos == self.changed_pos and not is_head)

            if is_head:
                _draw_rounded_rect(self, x - 5, y0 - 5, x + CELL_W + 3, y0 + CELL_H + 5,
                    r=CELL_R + 5, fill=C['tape_glow'], outline='')
                fill, sym_col, ol, ow = C['tape_head'], '#ffffff', '#d8caff', 2
            elif is_chg:
                fill, sym_col, ol, ow = C['tape_chg'], C['yellow'], C['yellow'], 1
            else:
                fill, sym_col, ol, ow = C['tape_cell'], C['tape_text'], C['border'], 1

            _draw_rounded_rect(self, x + 2, y0, x + CELL_W - 2, y0 + CELL_H,
                r=CELL_R, fill=fill, outline=ol, width=ow)
            self.create_text(cx, y0 + CELL_H // 2,
                             text=sym, fill=sym_col, font=FONT_MONO_BIG)

            if abs(pos - self.head_pos) <= 4:
                self.create_text(cx, y0 + CELL_H + 14, text=str(pos),
                                 fill=C['accent'] if is_head else C['subtle'],
                                 font=('Segoe UI', 7))

        hx = w // 2
        self.create_polygon(hx - 8, y0 - 8, hx + 8, y0 - 8, hx, y0 - 1,
                            fill=C['accent'], outline='')
        self.create_text(hx, y0 - 20, text='READ / WRITE HEAD',
                         fill=C['muted'], font=('Segoe UI', 7, 'bold'))


# ─────────────────────────────────────────────────────────────────
#  CUSTOM TAB BAR  (pure tk, no ttk, no layout-registration risk)
# ─────────────────────────────────────────────────────────────────

class TabBar(tk.Frame):
    """Lightweight custom tab widget: tk.Button strip + stacked tk.Frame pages."""

    def __init__(self, parent, bg: str = '', **kw):
        bg = bg or C['panel2']
        super().__init__(parent, bg=bg, **kw)
        self._bg   = bg
        self._tabs: list[tuple[tk.Button, tk.Frame]] = []

        self._bar  = tk.Frame(self, bg=bg)
        self._bar.pack(side='top', fill='x')
        tk.Frame(self, bg=C['border'], height=1).pack(side='top', fill='x')
        self._body = tk.Frame(self, bg=bg)
        self._body.pack(fill='both', expand=True)

    def add(self, label: str, frame: tk.Frame):
        idx = len(self._tabs)
        btn = tk.Button(
            self._bar, text=label,
            bg=C['btn'], fg=C['muted'],
            activebackground=self._bg, activeforeground=C['accent'],
            relief='flat', font=FONT_UI_BOLD,
            padx=18, pady=8, bd=0, cursor='hand2',
            command=lambda i=idx: self.select(i),
        )
        btn.pack(side='left')
        frame.place(in_=self._body, x=0, y=0, relwidth=1, relheight=1)
        self._tabs.append((btn, frame))
        if len(self._tabs) == 1:
            self.select(0)

    def select(self, idx: int):
        for i, (btn, frame) in enumerate(self._tabs):
            if i == idx:
                btn.config(bg=self._bg, fg=C['accent'])
                frame.lift()
            else:
                btn.config(bg=C['btn'], fg=C['muted'])


# ─────────────────────────────────────────────────────────────────
#  MAIN APPLICATION
# ─────────────────────────────────────────────────────────────────

class App(tk.Tk):
    """Turing Machine Simulator — Rose Pine dark theme, redesigned UI."""

    _S_READY   = ('  READY',    C['muted'])
    _S_RUNNING = ('  RUNNING',  C['accent2'])
    _S_ACCEPT  = ('  ACCEPTED', C['green'])
    _S_REJECT  = ('  REJECTED', C['red'])

    def __init__(self):
        super().__init__()
        self.title('Turing Machine Simulator')
        self.configure(bg=C['bg'])
        self.resizable(True, True)
        self.minsize(1100, 720)

        self.tm  = TuringMachine()
        self.sim = Simulator(self.tm)
        self._run_thread: threading.Thread | None = None
        self._running    = False
        self._speed_ms   = 300
        self._table_win: tk.Toplevel | None = None
        self._batch_win: tk.Toplevel | None = None

        self._build_ui()
        self._bind_keys()
        self._load_example()
        self._set_status(*self._S_READY)

    # ── Status chip ──────────────────────────────────────────────

    def _set_status(self, label: str, color: str):
        self.status_chip.config(text=label, fg=color)

    # ── Menu bar ─────────────────────────────────────────────────

    def _build_menu(self):
        def _menu(parent):
            return tk.Menu(parent, tearoff=0,
                           bg=C['panel'], fg=C['text'],
                           activebackground=C['accent'],
                           activeforeground=C['panel'])

        bar = tk.Menu(self, bg=C['panel'], fg=C['text'],
                      activebackground=C['accent'], activeforeground=C['panel'],
                      relief='flat', bd=0)

        fm = _menu(bar)
        fm.add_command(label='New / Clear...',          command=self._new_config)
        fm.add_command(label='Open Configuration...',   command=self._load_config)
        fm.add_command(label='Save Configuration...',   command=self._save_config)
        fm.add_separator()
        fm.add_command(label='Export Execution Log...', command=self._export_log)
        fm.add_separator()
        fm.add_command(label='Exit',                    command=self.quit)
        bar.add_cascade(label='File', menu=fm)

        vm = _menu(bar)
        vm.add_command(label='Transition Table   F9',   command=self._show_transition_table)
        vm.add_command(label='Batch Test...',           command=self._show_batch_test)
        bar.add_cascade(label='View', menu=vm)

        em = _menu(bar)
        em.add_command(label='0^n 1^n  Acceptor          (0011)',
                       command=self._example_0n1n)
        em.add_command(label='Binary Increment          (0111)',
                       command=self._example_binary_inc)
        em.add_command(label='Even-length Binary        (0110)',
                       command=self._example_even_length)
        em.add_command(label='Palindrome over {a,b}     (ababa)',
                       command=self._example_palindrome)
        em.add_command(label='Well-balanced Parens      (()()())',
                       command=self._example_brackets)
        bar.add_cascade(label='Examples', menu=em)

        hm = _menu(bar)
        hm.add_command(label='Keyboard Shortcuts', command=self._show_shortcuts)
        hm.add_command(label='About',              command=self._show_about)
        bar.add_cascade(label='Help', menu=hm)

        self.config(menu=bar)

    # ── Full UI assembly ─────────────────────────────────────────

    def _build_ui(self):
        self._build_menu()

        # Status bar packed FIRST so content above expands into it
        self._build_status_bar()

        # Header
        hdr = tk.Frame(self, bg=C['bg'])
        hdr.pack(fill='x', padx=20, pady=(12, 8))

        lhdr = tk.Frame(hdr, bg=C['bg'])
        lhdr.pack(side='left')
        tk.Label(lhdr, text='  TURING  MACHINE  SIMULATOR',
                 bg=C['bg'], fg=C['accent'], font=FONT_TITLE).pack(anchor='w')
        tk.Label(lhdr,
                 text='Deterministic  .  Single-Tape  .  Step-by-Step Execution',
                 bg=C['bg'], fg=C['subtle'], font=FONT_UI_SM).pack(
                     anchor='w', pady=(2, 0))

        chip_f = tk.Frame(hdr, bg=C['panel2'],
                          highlightbackground=C['border'], highlightthickness=1)
        chip_f.pack(side='right', pady=2)
        _lbl, _clr = self._S_READY
        self.status_chip = tk.Label(chip_f, text=_lbl,
                                    bg=C['panel2'], fg=_clr,
                                    font=FONT_UI_BOLD, padx=14, pady=6)
        self.status_chip.pack()

        # Accent separator
        sep = tk.Canvas(self, height=3, bg=C['bg'], highlightthickness=0)
        sep.pack(fill='x')

        def _draw_sep(e=None):
            sep.delete('all')
            w = sep.winfo_width()
            sep.create_rectangle(0, 0, w * 3 // 5, 3, fill=C['accent'],  outline='')
            sep.create_rectangle(w * 3 // 5, 0, w * 4 // 5, 3,
                                 fill=C['panel2'], outline='')
        sep.bind('<Configure>', lambda e: _draw_sep())
        self.after(80, _draw_sep)

        # Main split
        main = tk.Frame(self, bg=C['bg'])
        main.pack(fill='both', expand=True, padx=14, pady=(6, 8))

        left = tk.Frame(main, bg=C['bg'])
        left.pack(side='left', fill='both', expand=True)

        right = tk.Frame(main, bg=C['panel'],
                         highlightbackground=C['border'], highlightthickness=1)
        right.pack(side='right', fill='y', padx=(14, 0))

        self._build_tape_panel(left)
        self._build_hud(left)
        self._build_controls(left)   # always visible, above config tabs

        self.result_banner = tk.Label(left, text='', bg=C['bg'],
                                      font=('Segoe UI', 11, 'bold'),
                                      pady=5, anchor='center')
        self.result_banner.pack(fill='x')

        self._build_config_tabs(left)
        self._build_log(right)

    # ── Tape panel ───────────────────────────────────────────────

    def _build_tape_panel(self, parent):
        card = tk.Frame(parent, bg=C['panel'],
                        highlightbackground=C['border_hi'], highlightthickness=1)
        card.pack(fill='x', pady=(0, 8))

        top = tk.Frame(card, bg=C['panel'])
        top.pack(fill='x', padx=12, pady=(7, 0))
        tk.Label(top, text='T A P E', bg=C['panel'], fg=C['muted'],
                 font=('Segoe UI', 8, 'bold')).pack(side='left')
        self.tape_hdr_lbl = tk.Label(top, text='', bg=C['panel'], fg=C['subtle'],
                                     font=FONT_MONO_SM)
        self.tape_hdr_lbl.pack(side='right', padx=4)

        self.tape_canvas = TapeCanvas(card)
        self.tape_canvas.pack(fill='x', expand=True, padx=6, pady=(2, 6))

    # ── HUD row ──────────────────────────────────────────────────

    def _build_hud(self, parent):
        hud = tk.Frame(parent, bg=C['bg'])
        hud.pack(fill='x', pady=(0, 8))

        for title, attr, color in [
            ('STATE',  'lbl_state',  C['accent']),
            ('HEAD',   'lbl_head',   C['accent2']),
            ('SYMBOL', 'lbl_symbol', C['yellow']),
            ('STEPS',  'lbl_steps',  C['text']),
        ]:
            card = tk.Frame(hud, bg=C['panel2'],
                            highlightbackground=C['border'], highlightthickness=1)
            card.pack(side='left', fill='both', expand=True, padx=(0, 8))
            tk.Frame(card, bg=color, height=3).pack(fill='x')
            tk.Label(card, text=title, bg=C['panel2'],
                     fg=C['subtle'], font=FONT_HUD_LBL).pack(pady=(6, 0))
            val = tk.Label(card, text='--', bg=C['panel2'],
                           fg=color, font=FONT_HUD_VAL)
            val.pack(pady=(2, 7))
            setattr(self, attr, val)

    # ── Controls card ────────────────────────────────────────────

    def _build_controls(self, parent):
        card = tk.Frame(parent, bg=C['panel'],
                        highlightbackground=C['border'], highlightthickness=1)
        card.pack(fill='x', pady=(0, 8))

        btn_row = tk.Frame(card, bg=C['panel'])
        btn_row.pack(fill='x', padx=10, pady=(10, 6))

        self.btn_load  = self._make_btn(btn_row, 'Load',   C['btn'],       self._load_machine)
        self.btn_step  = self._make_btn(btn_row, 'Step',   C['btn_step'],  self._step)
        self.btn_undo  = self._make_btn(btn_row, 'Undo',   C['btn'],       self._undo)
        tk.Frame(btn_row, bg=C['border'], width=1).pack(
            side='left', fill='y', padx=8, pady=3)
        self.btn_run   = self._make_btn(btn_row, 'Run',    C['btn_run'],   self._run)
        self.btn_stop  = self._make_btn(btn_row, 'Stop',   C['btn_stop'],  self._stop)
        self.btn_reset = self._make_btn(btn_row, 'Reset',  C['btn_reset'], self._reset)
        tk.Frame(btn_row, bg=C['border'], width=1).pack(
            side='left', fill='y', padx=8, pady=3)
        self.btn_table = self._make_btn(btn_row, 'Table',  C['btn'],       self._show_transition_table)
        self.btn_batch = self._make_btn(btn_row, 'Batch',  C['btn'],       self._show_batch_test)

        for btn in (self.btn_load, self.btn_step, self.btn_undo,
                    self.btn_run, self.btn_stop, self.btn_reset,
                    self.btn_table, self.btn_batch):
            btn.pack(side='left', padx=3)

        self.btn_stop.config(state='disabled')

        spd = tk.Frame(card, bg=C['panel'])
        spd.pack(fill='x', padx=10, pady=(0, 10))

        tk.Label(spd, text='Speed:', bg=C['panel'],
                 fg=C['muted'], font=FONT_UI_SM).pack(side='left', padx=(0, 6))
        tk.Label(spd, text='Fast', bg=C['panel'],
                 fg=C['subtle'], font=FONT_UI_SM).pack(side='left')
        self.speed_var = tk.IntVar(value=300)
        tk.Scale(spd, from_=50, to=1200, orient='horizontal',
                 variable=self.speed_var, length=170,
                 bg=C['panel'], fg=C['muted'], troughcolor=C['panel2'],
                 highlightthickness=0, sliderrelief='flat',
                 sliderlength=16, width=8, showvalue=False,
                 command=self._on_speed_change).pack(side='left', padx=4)
        tk.Label(spd, text='Slow', bg=C['panel'],
                 fg=C['subtle'], font=FONT_UI_SM).pack(side='left')
        self.spd_lbl = tk.Label(spd, text='300 ms', bg=C['panel'],
                                fg=C['muted'], font=FONT_UI_SM, width=7)
        self.spd_lbl.pack(side='left', padx=(10, 0))


    # ── Config tabs ──────────────────────────────────────────────

    def _build_config_tabs(self, parent):
        tabs = TabBar(parent)
        tabs.pack(fill='both', expand=True, pady=(4, 0))

        # Tab 1: Machine
        tab_m = tk.Frame(tabs._body, bg=C['panel2'])
        grid  = tk.Frame(tab_m, bg=C['panel2'])
        grid.pack(fill='both', expand=True, padx=14, pady=12)

        tk.Label(grid, text='States  (comma-separated)',
                 bg=C['panel2'], fg=C['muted'],
                 font=FONT_UI_SM).grid(row=0, column=0, columnspan=6, sticky='w')
        self.entry_states = self._make_entry(grid)
        self.entry_states.grid(row=1, column=0, columnspan=6,
                               sticky='ew', pady=(3, 10))

        for ci, (lbl, attr, w) in enumerate([
            ('Start state',  'entry_start',  14),
            ('Accept state', 'entry_accept', 20),
            ('Reject state', 'entry_reject', 14),
        ]):
            tk.Label(grid, text=lbl, bg=C['panel2'], fg=C['muted'],
                     font=FONT_UI_SM).grid(row=2, column=ci * 2,
                                            sticky='w', padx=(0, 4))
            e = self._make_entry(grid, width=w)
            e.grid(row=3, column=ci * 2, sticky='ew', padx=(0, 14), pady=(3, 10))
            setattr(self, attr, e)

        tk.Label(grid, text='Input string',
                 bg=C['panel2'], fg=C['muted'],
                 font=FONT_UI_SM).grid(row=4, column=0, columnspan=6, sticky='w')
        self.entry_input = self._make_entry(grid)
        self.entry_input.grid(row=5, column=0, columnspan=6,
                              sticky='ew', pady=(3, 10))

        tk.Label(grid, text='Max steps (loop guard)',
                 bg=C['panel2'], fg=C['muted'],
                 font=FONT_UI_SM).grid(row=6, column=0, columnspan=2, sticky='w')
        self.entry_maxsteps = self._make_entry(grid, width=10)
        self.entry_maxsteps.insert(0, str(Simulator.MAX_STEPS))
        self.entry_maxsteps.grid(row=7, column=0, sticky='w', pady=(3, 4))
        tk.Label(grid, text='steps', bg=C['panel2'], fg=C['subtle'],
                 font=FONT_UI_SM).grid(row=7, column=1, sticky='w', padx=(6, 0))

        for c in range(6):
            grid.columnconfigure(c, weight=1)

        tabs.add('  Machine  ', tab_m)

        # Tab 2: Transitions
        tab_t = tk.Frame(tabs._body, bg=C['panel2'])

        hint = tk.Frame(tab_t, bg=C['panel2'])
        hint.pack(fill='x', padx=12, pady=(8, 4))
        tk.Label(hint, text='Format:  state, sym  ->  new_sym, Dir, next_state',
                 bg=C['panel2'], fg=C['subtle'],
                 font=('Segoe UI', 8), anchor='w').pack(side='left')
        tk.Label(hint, text='   # comment',
                 bg=C['panel2'], fg=C['subtle'],
                 font=('Segoe UI', 8)).pack(side='right')

        self.txt_transitions = scrolledtext.ScrolledText(
            tab_t, bg=C['panel'], fg=C['text'],
            insertbackground=C['accent'],
            relief='flat', font=FONT_MONO,
            highlightbackground=C['border_hi'], highlightthickness=1,
            padx=10, pady=8,
        )
        self.txt_transitions.pack(fill='both', expand=True, padx=8, pady=(0, 8))

        for tag, col, extra in [
            ('hl_comment',   C['subtle'],  {}),
            ('hl_state',     C['accent'],  {}),
            ('hl_symbol',    C['yellow'],  {}),
            ('hl_arrow',     C['subtle'],  {}),
            ('hl_direction', C['accent2'], {}),
            ('hl_error',     C['red'],     {'underline': True}),
        ]:
            self.txt_transitions.tag_config(tag, foreground=col, **extra)

        self.txt_transitions.bind('<KeyRelease>',
                                  lambda _e: self._highlight_transitions())
        self.txt_transitions.bind('<<Paste>>',
                                  lambda _e: self.after(10, self._highlight_transitions))

        tabs.add('  Transitions  ', tab_t)

    # ── Execution log ────────────────────────────────────────────

    def _build_log(self, parent):
        hdr = tk.Frame(parent, bg=C['panel'])
        hdr.pack(fill='x')

        tk.Label(hdr, text='EXECUTION  LOG',
                 bg=C['panel'], fg=C['accent'],
                 font=('Segoe UI', 8, 'bold')).pack(side='left', padx=12, pady=8)

        exp = tk.Label(hdr, text='export', bg=C['panel'],
                       fg=C['muted'], cursor='hand2', font=FONT_UI_SM)
        exp.pack(side='right', padx=6)
        exp.bind('<Button-1>', lambda _e: self._export_log())

        clr = tk.Label(hdr, text='clear', bg=C['panel'],
                       fg=C['muted'], cursor='hand2', font=FONT_UI_SM)
        clr.pack(side='right', padx=2)
        clr.bind('<Button-1>', lambda _e: self._log_clear())

        tk.Frame(parent, bg=C['border'], height=1).pack(fill='x')

        self.log_box = scrolledtext.ScrolledText(
            parent, width=26,
            bg=C['panel'], fg=C['text'],
            insertbackground=C['text'],
            relief='flat', font=('Consolas', 8),
            state='disabled', highlightthickness=0,
            padx=8, pady=6,
        )
        self.log_box.pack(fill='both', expand=True)

        for tag, col in [
            ('accept',  C['green']),
            ('reject',  C['red']),
            ('step',    C['accent']),
            ('info',    C['muted']),
            ('timeout', C['yellow']),
        ]:
            self.log_box.tag_config(tag, foreground=col)

    # ── Status bar ───────────────────────────────────────────────

    def _build_status_bar(self):
        bar = tk.Frame(self, bg=C['panel2'], padx=14, pady=5)
        bar.pack(side='bottom', fill='x')
        for key, action in [
            ('F5',     'Run'),
            ('F6',     'Step'),
            ('Esc',    'Stop'),
            ('Ctrl+L', 'Load'),
            ('Ctrl+R', 'Reset'),
            ('Ctrl+Z', 'Undo'),
            ('F9',     'Table'),
        ]:
            tk.Label(bar, text=key, bg=C['panel2'],
                     fg=C['accent'], font=('Consolas', 8, 'bold')).pack(side='left')
            tk.Label(bar, text=f' {action}', bg=C['panel2'],
                     fg=C['muted'], font=FONT_UI_SM).pack(side='left', padx=(0, 14))

    # ── Widget factories ─────────────────────────────────────────

    def _make_entry(self, parent, **kw):
        return tk.Entry(parent,
                        bg=C['panel'], fg=C['text'],
                        insertbackground=C['accent'],
                        relief='flat', font=FONT_MONO,
                        highlightbackground=C['border'],
                        highlightthickness=1,
                        selectbackground=C['accent'],
                        selectforeground=C['panel'], **kw)

    def _make_btn(self, parent, text: str, color: str, command):
        hover = _lighten(color)
        btn = tk.Button(parent, text=text, bg=color, fg=C['text'],
                        activebackground=hover, activeforeground=C['text'],
                        relief='flat', font=FONT_BTN,
                        cursor='hand2', padx=12, pady=7,
                        command=command, bd=0)
        btn.bind('<Enter>', lambda _e, b=btn, h=hover: b.config(bg=h))
        btn.bind('<Leave>', lambda _e, b=btn, c=color: b.config(bg=c))
        return btn

    # ── Initial render ───────────────────────────────────────────

    def _initial_render(self):
        half  = TAPE_CELLS // 2
        cells = [(i, '_') for i in range(-half, half + 1)]
        self.tape_canvas.render(cells, head_pos=0)

    # ── Keyboard shortcuts ───────────────────────────────────────

    def _bind_keys(self):
        self.bind('<F5>',        lambda _e: self._run())
        self.bind('<F6>',        lambda _e: self._step())
        self.bind('<Escape>',    lambda _e: self._stop())
        self.bind('<Control-l>', lambda _e: self._load_machine())
        self.bind('<Control-L>', lambda _e: self._load_machine())
        self.bind('<Control-r>', lambda _e: self._reset())
        self.bind('<Control-R>', lambda _e: self._reset())
        self.bind('<Control-z>', lambda _e: self._undo())
        self.bind('<Control-Z>', lambda _e: self._undo())
        self.bind('<F9>',        lambda _e: self._show_transition_table())
        for w in (self.entry_states, self.entry_start,
                  self.entry_accept, self.entry_reject, self.entry_input):
            w.bind('<Return>', lambda _e: self._load_machine())


    # ── Example loading ──────────────────────────────────────────

    def _clear_and_load_example(self, states, start, accept, reject,
                                 input_str, transitions):
        for entry in (self.entry_states, self.entry_start, self.entry_accept,
                      self.entry_reject, self.entry_input):
            entry.delete(0, 'end')
        self.txt_transitions.delete('1.0', 'end')
        self.entry_states.insert(0, states)
        self.entry_start .insert(0, start)
        self.entry_accept.insert(0, accept)
        self.entry_reject.insert(0, reject)
        self.entry_input .insert(0, input_str)
        self.txt_transitions.insert('1.0', transitions)
        self._highlight_transitions()

    def _load_example(self):
        self._example_0n1n()

    # ── Built-in examples ────────────────────────────────────────

    def _example_0n1n(self):
        self._clear_and_load_example(
            states='q0,q1,q2,qaccept,qreject',
            start='q0', accept='qaccept', reject='qreject',
            input_str='0011',
            transitions=(
                '# Accepts strings of the form 0^n 1^n  (n >= 1)\n'
                '# e.g. 01, 0011, 000111\n'
                '# q0: find a 0, mark it X\n'
                'q0,0 -> X,R,q1\n'
                'q0,Y -> Y,R,q0\n'
                'q0,_ -> _,R,qaccept\n'
                '# q1: scan right past 0s and Ys to find a 1\n'
                'q1,0 -> 0,R,q1\n'
                'q1,Y -> Y,R,q1\n'
                'q1,1 -> Y,L,q2\n'
                'q1,_ -> _,R,qreject\n'
                '# q2: scan left back to leftmost X\n'
                'q2,0 -> 0,L,q2\n'
                'q2,Y -> Y,L,q2\n'
                'q2,X -> X,R,q0\n'
            ),
        )

    def _example_binary_inc(self):
        self._clear_and_load_example(
            states='q0,q1,qacc',
            start='q0', accept='qacc', reject='',
            input_str='0111',
            transitions=(
                '# Increments a binary number on the tape\n'
                '# Input 0111 -> tape becomes 1000, halts in qacc\n'
                '# q0: scan right to find the end\n'
                'q0,0 -> 0,R,q0\n'
                'q0,1 -> 1,R,q0\n'
                'q0,_ -> _,L,q1\n'
                '# q1: increment from the rightmost bit\n'
                'q1,0 -> 1,R,qacc\n'
                'q1,1 -> 0,L,q1\n'
                'q1,_ -> 1,R,qacc\n'
            ),
        )

    def _example_even_length(self):
        self._clear_and_load_example(
            states='q_even,q_odd,qacc,qrej',
            start='q_even', accept='qacc', reject='qrej',
            input_str='0110',
            transitions=(
                '# Accepts binary strings of even length\n'
                'q_even,0 -> 0,R,q_odd\n'
                'q_even,1 -> 1,R,q_odd\n'
                'q_even,_ -> _,R,qacc\n'
                'q_odd,0  -> 0,R,q_even\n'
                'q_odd,1  -> 1,R,q_even\n'
                'q_odd,_  -> _,R,qrej\n'
            ),
        )

    def _example_palindrome(self):
        self._clear_and_load_example(
            states='q0,qa_r,qb_r,qa_c,qb_c,q_ret,qacc,qrej',
            start='q0', accept='qacc', reject='qrej',
            input_str='ababa',
            transitions=(
                '# Accepts palindromes over {a,b}  e.g. a, aba, abba, ababa\n'
                '# Strategy: erase matching outermost pair, repeat\n'
                'q0,a   -> X,R,qa_r\n'
                'q0,b   -> X,R,qb_r\n'
                'q0,X   -> X,R,q0\n'
                'q0,_   -> _,R,qacc\n'
                '# qa_r: heading right (remembered left = a)\n'
                'qa_r,a -> a,R,qa_r\n'
                'qa_r,b -> b,R,qa_r\n'
                'qa_r,X -> X,R,qa_r\n'
                'qa_r,_ -> _,L,qa_c\n'
                '# qa_c: check rightmost unmatched symbol is a\n'
                'qa_c,a -> X,L,q_ret\n'
                'qa_c,b -> b,R,qrej\n'
                'qa_c,X -> X,L,qa_c\n'
                'qa_c,_ -> _,R,qacc\n'
                '# qb_r: heading right (remembered left = b)\n'
                'qb_r,a -> a,R,qb_r\n'
                'qb_r,b -> b,R,qb_r\n'
                'qb_r,X -> X,R,qb_r\n'
                'qb_r,_ -> _,L,qb_c\n'
                '# qb_c: check rightmost unmatched symbol is b\n'
                'qb_c,b -> X,L,q_ret\n'
                'qb_c,a -> a,R,qrej\n'
                'qb_c,X -> X,L,qb_c\n'
                'qb_c,_ -> _,R,qacc\n'
                '# q_ret: go back left to restart\n'
                'q_ret,a -> a,L,q_ret\n'
                'q_ret,b -> b,L,q_ret\n'
                'q_ret,X -> X,L,q_ret\n'
                'q_ret,_ -> _,R,q0\n'
            ),
        )

    def _example_brackets(self):
        self._clear_and_load_example(
            states='q0,q1,q2,q_chk,qacc,qrej',
            start='q0', accept='qacc', reject='qrej',
            input_str='(()())',
            transitions=(
                '# Accepts well-balanced parentheses  e.g. (), (()), ()()\n'
                '# Strategy: find innermost ), erase it and its matching (\n'
                'q0,( -> (,R,q0\n'
                'q0,) -> X,L,q1\n'
                'q0,X -> X,R,q0\n'
                'q0,_ -> _,L,q_chk\n'
                '# q1: scan left for matching (\n'
                'q1,( -> X,L,q2\n'
                'q1,) -> ),R,qrej\n'
                'q1,X -> X,L,q1\n'
                'q1,_ -> _,R,qrej\n'
                '# q2: return to left end and restart\n'
                'q2,( -> (,L,q2\n'
                'q2,) -> ),L,q2\n'
                'q2,X -> X,L,q2\n'
                'q2,_ -> _,R,q0\n'
                '# q_chk: verify no unmatched ( remains\n'
                'q_chk,( -> (,R,qrej\n'
                'q_chk,X -> X,L,q_chk\n'
                'q_chk,_ -> _,R,qacc\n'
            ),
        )


    # ── Event handlers ───────────────────────────────────────────

    def _on_speed_change(self, val):
        self._speed_ms = int(float(val))
        if hasattr(self, 'spd_lbl'):
            self.spd_lbl.config(text=f'{self._speed_ms} ms')

    def _load_machine(self):
        states_raw = self.entry_states.get().strip()
        if not states_raw:
            messagebox.showerror('Config Error', 'Please enter at least one state.')
            return
        self.tm.states = {s.strip() for s in states_raw.split(',')}

        start = self.entry_start.get().strip()
        if not start:
            messagebox.showerror('Config Error', 'Please enter a start state.')
            return
        self.tm.start_state = start

        accept_raw = self.entry_accept.get().strip()
        self.tm.accept_states = (
            {s.strip() for s in accept_raw.split(',')} if accept_raw else set())
        self.tm.reject_state = self.entry_reject.get().strip()

        tr_text = self.txt_transitions.get('1.0', 'end')
        errors  = self.tm.parse_transitions(tr_text)
        if errors:
            messagebox.showerror('Transition Error', '\n'.join(errors[:10]))
            return

        issues = self.tm.validate()
        if issues:
            if not messagebox.askyesno(
                    'Validation Warnings',
                    'Warnings:\n' + '\n'.join(issues) + '\n\nContinue anyway?'):
                return

        input_str = self.entry_input.get().strip()
        self.sim  = Simulator(self.tm)
        try:
            ms = int(self.entry_maxsteps.get().strip())
            if ms > 0:
                self.sim.MAX_STEPS = ms
        except ValueError:
            pass

        self.sim.load(input_str)
        self.title(f'Turing Machine Simulator -- "{input_str}"')
        self._log_clear()
        self._log(
            f"Loaded  |  input: '{input_str}'  |  {len(self.tm.transitions)} transitions",
            'info')
        self.result_banner.config(text='', bg=C['bg'])
        self._set_status(*self._S_READY)
        self._refresh_ui()
        if self._table_win and self._table_win.winfo_exists():
            self._show_transition_table()

    def _step(self):
        if self._running:
            messagebox.showwarning('Running', 'Stop the auto-run first.')
            return
        if self.sim.halted:
            messagebox.showinfo('Halted', 'Machine has halted. Press Reset to restart.')
            return
        if not self.tm.start_state:
            messagebox.showwarning('Not Loaded', 'Press Load first.')
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
            messagebox.showinfo('Halted', 'Machine has halted. Press Reset first.')
            return
        if not self.tm.start_state:
            messagebox.showwarning('Not Loaded', 'Press Load first.')
            return
        self._running = True
        self._set_run_mode(True)
        self._run_thread = threading.Thread(target=self._run_loop, daemon=True)
        self._run_thread.start()

    def _run_loop(self):
        while self._running and not self.sim.halted:
            status = self.sim.step()
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
        self.sim.load(self.entry_input.get().strip())
        self.result_banner.config(text='', bg=C['bg'])
        self._log_clear()
        self._log('Reset -- ready.', 'info')
        self._set_status(*self._S_READY)
        self._refresh_ui()

    def _set_run_mode(self, running: bool):
        idle = 'normal' if not running else 'disabled'
        stop = 'normal' if running     else 'disabled'
        for btn in (self.btn_load, self.btn_step, self.btn_undo,
                    self.btn_run, self.btn_reset, self.btn_table, self.btn_batch):
            btn.config(state=idle)
        self.btn_stop.config(state=stop)
        if running:
            self._set_status(*self._S_RUNNING)
        elif not self.sim.halted:
            self._set_status(*self._S_READY)

    def _undo(self):
        if self._running:
            messagebox.showwarning('Running', 'Stop the auto-run first.')
            return
        if not self.tm.start_state:
            messagebox.showwarning('Not Loaded', 'Press Load first.')
            return
        if not self.sim.undo():
            messagebox.showinfo('Undo', 'Nothing to undo -- already at initial state.')
            return
        self.result_banner.config(text='', bg=C['bg'])
        self._set_status(*self._S_READY)
        self._refresh_ui()
        self._log(f'  Undo -- back to step {self.sim.steps}', 'info')

    # ── UI update helpers ────────────────────────────────────────

    def _refresh_ui(self):
        head    = self.sim.tape.head
        state   = self.sim.current_state or '--'
        symbol  = self.sim.tape.read()
        steps   = self.sim.steps
        changed = self.sim.last_written_pos
        content = self.sim.tape.get_tape_content()

        self.tape_canvas.render(
            self.sim.tape.get_visible_slice(head, TAPE_CELLS), head, changed)
        self.tape_hdr_lbl.config(text=f'tape: {content}')

        self.lbl_state .config(text=state)
        self.lbl_head  .config(text=str(head))
        self.lbl_symbol.config(text=symbol)
        self.lbl_steps .config(text=str(steps))

        if state in self.tm.accept_states:
            self.lbl_state.config(fg=C['green'])
        elif state == self.tm.reject_state and self.tm.reject_state:
            self.lbl_state.config(fg=C['red'])
        else:
            self.lbl_state.config(fg=C['accent'])

    def _show_result(self, status: str):
        tape = self.sim.tape.get_tape_content()
        n    = self.sim.steps
        if status == 'accepted':
            self.result_banner.config(
                text=f'  ACCEPTED  after {n} steps   |   tape: {tape}  ',
                bg=C['green'], fg='white')
            self._set_status(*self._S_ACCEPT)
        elif status == 'timeout':
            self.result_banner.config(
                text=f'  TIMEOUT  -- exceeded {self.sim.MAX_STEPS} steps  ',
                bg=C['yellow'], fg=C['panel2'])
            self._set_status(*self._S_REJECT)
        else:
            reason = (f'no rule for ({self.sim.current_state}, {self.sim.tape.read()})'
                      if status == 'no_rule' else status)
            self.result_banner.config(
                text=f'  REJECTED  ({reason})  after {n} steps   |   tape: {tape}  ',
                bg=C['red'], fg='white')
            self._set_status(*self._S_REJECT)

    def _log(self, msg: str, tag: str = ''):
        self.log_box.config(state='normal')
        self.log_box.insert('end', msg + '\n', tag)
        self.log_box.see('end')
        self.log_box.config(state='disabled')

    def _log_step(self, status: str):
        steps = self.sim.steps
        tape  = self.sim.tape.get_tape_content()
        rule  = self.sim.last_rule

        if rule:
            q, sym, wsym, d, nq = rule
            self._log(f'[{steps:>4}]  {q} ({sym})->({wsym},{d})-> {nq}', 'step')

        if status == 'accepted':
            self._log('       ACCEPTED', 'accept')
            self._log(f'       tape: {tape}', 'accept')
        elif status == 'timeout':
            self._log(f'       TIMEOUT (>{self.sim.MAX_STEPS} steps)', 'timeout')
            self._log(f'       tape: {tape}', 'timeout')
        elif status not in ('running',):
            self._log(f'       REJECTED  ({status})', 'reject')
            self._log(f'       tape: {tape}', 'reject')

    def _log_clear(self):
        self.log_box.config(state='normal')
        self.log_box.delete('1.0', 'end')
        self.log_box.config(state='disabled')


    # ── File operations ──────────────────────────────────────────

    def _new_config(self):
        if not messagebox.askyesno('New', 'Clear all configuration and start fresh?'):
            return
        for entry in (self.entry_states, self.entry_start, self.entry_accept,
                      self.entry_reject, self.entry_input):
            entry.delete(0, 'end')
        self.txt_transitions.delete('1.0', 'end')
        self.result_banner.config(text='', bg=C['bg'])
        self._log_clear()
        self._log('New configuration -- fill in Machine tab then press Load.', 'info')
        self._set_status(*self._S_READY)

    def _save_config(self):
        path = filedialog.asksaveasfilename(
            defaultextension='.json',
            filetypes=[('JSON files', '*.json'), ('All files', '*.*')],
            title='Save Machine Configuration',
        )
        if not path:
            return
        config = {
            'states':        self.entry_states.get().strip(),
            'start_state':   self.entry_start.get().strip(),
            'accept_states': self.entry_accept.get().strip(),
            'reject_state':  self.entry_reject.get().strip(),
            'input_string':  self.entry_input.get().strip(),
            'max_steps':     self.entry_maxsteps.get().strip(),
            'transitions':   self.txt_transitions.get('1.0', 'end').rstrip('\n'),
        }
        try:
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2)
            self._log(f'Config saved -> {path}', 'info')
        except OSError as e:
            messagebox.showerror('Save Error', str(e))

    def _load_config(self):
        path = filedialog.askopenfilename(
            filetypes=[('JSON files', '*.json'), ('All files', '*.*')],
            title='Open Machine Configuration',
        )
        if not path:
            return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                config = json.load(f)
        except (OSError, json.JSONDecodeError) as e:
            messagebox.showerror('Load Error', str(e))
            return
        for entry, key in [
            (self.entry_states,   'states'),
            (self.entry_start,    'start_state'),
            (self.entry_accept,   'accept_states'),
            (self.entry_reject,   'reject_state'),
            (self.entry_input,    'input_string'),
            (self.entry_maxsteps, 'max_steps'),
        ]:
            entry.delete(0, 'end')
            entry.insert(0, config.get(key, ''))
        self.txt_transitions.delete('1.0', 'end')
        self.txt_transitions.insert('1.0', config.get('transitions', ''))
        self._highlight_transitions()
        self._log(f'Config loaded <- {path}', 'info')

    def _export_log(self):
        path = filedialog.asksaveasfilename(
            defaultextension='.txt',
            filetypes=[('Text files', '*.txt'), ('All files', '*.*')],
            title='Export Execution Log',
        )
        if not path:
            return
        try:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(self.log_box.get('1.0', 'end'))
            messagebox.showinfo('Exported', f'Log saved to:\n{path}')
        except OSError as e:
            messagebox.showerror('Export Error', str(e))

    # ── Transition table viewer ──────────────────────────────────

    def _show_transition_table(self):
        if not self.tm.transitions:
            messagebox.showinfo('Table', 'No transitions loaded -- press Load first.')
            return
        if self._table_win and self._table_win.winfo_exists():
            self._table_win.lift()
        else:
            self._table_win = tk.Toplevel(self)
            self._table_win.title('Transition Table  delta(state, symbol)')
            self._table_win.configure(bg=C['bg'])
            self._table_win.geometry('680x420')
            self._table_win.resizable(True, True)

            self._table_text = tk.Text(
                self._table_win, bg=C['panel'], fg=C['text'],
                font=('Courier New', 10), relief='flat',
                wrap='none', state='disabled', highlightthickness=0,
            )
            sb_x = tk.Scrollbar(self._table_win, orient='horizontal',
                                 command=self._table_text.xview)
            sb_y = tk.Scrollbar(self._table_win, orient='vertical',
                                 command=self._table_text.yview)
            self._table_text.configure(xscrollcommand=sb_x.set,
                                        yscrollcommand=sb_y.set)
            sb_y.pack(side='right',  fill='y')
            sb_x.pack(side='bottom', fill='x')
            self._table_text.pack(fill='both', expand=True, padx=4, pady=4)

            for tag, col, bold in [
                ('hdr',   C['accent'], True),
                ('state', C['accent'], False),
                ('rule',  C['yellow'], False),
                ('empty', C['muted'],  False),
                ('sep',   C['border'], False),
            ]:
                fnt = ('Courier New', 10, 'bold') if bold else ('Courier New', 10)
                self._table_text.tag_config(tag, foreground=col, font=fnt)

        self._render_transition_table()

    def _render_transition_table(self):
        tm      = self.tm
        states  = sorted(tm.states)
        symbols = sorted({sym for (_, sym) in tm.transitions})

        sw = max((len(s) for s in states),  default=5) + 2
        cw = max(
            max((len(f'{w},{d},{n}')
                 for (w, d, n) in tm.transitions.values()), default=7),
            max((len(sym) for sym in symbols), default=3),
        ) + 2

        pad = lambda s, w: s.center(w)
        sep = '-' * sw + '+' + ('-' * cw + '+') * len(symbols)

        t = self._table_text
        t.config(state='normal')
        t.delete('1.0', 'end')
        t.insert('end', pad('delta', sw) + '|' +
                 '|'.join(pad(s, cw) for s in symbols) + '\n', 'hdr')
        t.insert('end', sep + '\n', 'sep')

        for state in states:
            t.insert('end', pad(state, sw), 'state')
            t.insert('end', '|', 'sep')
            for sym in symbols:
                rule = tm.transitions.get((state, sym))
                if rule:
                    t.insert('end', pad(f'{rule[0]},{rule[1]},{rule[2]}', cw), 'rule')
                else:
                    t.insert('end', pad('--', cw), 'empty')
                t.insert('end', '|', 'sep')
            t.insert('end', '\n')
            t.insert('end', sep + '\n', 'sep')

        t.config(state='disabled')

    # ── Batch test ───────────────────────────────────────────────

    def _show_batch_test(self):
        if not self.tm.start_state:
            messagebox.showwarning('Not Loaded', 'Press Load first.')
            return
        if self._batch_win and self._batch_win.winfo_exists():
            self._batch_win.lift()
            return

        self._batch_win = tk.Toplevel(self)
        self._batch_win.title('Batch Test')
        self._batch_win.configure(bg=C['bg'])
        self._batch_win.geometry('540x500')
        self._batch_win.resizable(True, True)

        tk.Label(self._batch_win, text='BATCH TEST',
                 bg=C['bg'], fg=C['accent'],
                 font=FONT_UI_BOLD).pack(anchor='w', padx=14, pady=(12, 4))
        tk.Label(self._batch_win,
                 text='Enter one input string per line (blank line = empty tape):',
                 bg=C['bg'], fg=C['muted'],
                 font=FONT_UI_SM).pack(anchor='w', padx=14)

        inp = scrolledtext.ScrolledText(
            self._batch_win, height=7,
            bg=C['panel'], fg=C['text'], insertbackground=C['accent'],
            relief='flat', font=FONT_MONO,
            highlightbackground=C['border'], highlightthickness=1,
            padx=8, pady=6)
        inp.pack(fill='x', padx=14, pady=6)

        out = scrolledtext.ScrolledText(
            self._batch_win, height=14,
            bg=C['panel'], fg=C['text'],
            relief='flat', font=('Consolas', 9),
            highlightthickness=0, padx=8, pady=6, state='disabled')

        def _run():
            lines = inp.get('1.0', 'end').splitlines()
            out.config(state='normal')
            out.delete('1.0', 'end')
            out.insert('end', f"{'INPUT':<22}  {'RESULT':<12}  STEPS\n", 'hdr')
            out.insert('end', '-' * 46 + '\n', 'hdr')
            for line in lines:
                stripped = line.strip()
                sim = Simulator(self.tm)
                sim.MAX_STEPS = self.sim.MAX_STEPS
                sim.load(stripped)
                status = sim.run_to_halt()
                tag    = 'accept' if status == 'accepted' else 'reject'
                icon   = 'OK' if status == 'accepted' else 'XX'
                disp   = f'"{stripped}"' if stripped else '(empty)'
                out.insert('end',
                           f'{disp:<22}  {icon} {status:<11}  {sim.steps}\n', tag)
            out.config(state='disabled')

        self._make_btn(
            self._batch_win, 'Run Batch', C['btn_run'], _run,
        ).pack(padx=14, pady=(0, 6), anchor='w')

        tk.Frame(self._batch_win, bg=C['border'], height=1).pack(fill='x', padx=14)

        out.pack(fill='both', expand=True, padx=14, pady=(6, 14))
        for tag, col in [('accept', C['green']),
                         ('reject', C['red']),
                         ('hdr',    C['accent'])]:
            out.tag_config(tag, foreground=col)

    # ── Help dialogs ─────────────────────────────────────────────

    def _show_shortcuts(self):
        win = tk.Toplevel(self)
        win.title('Keyboard Shortcuts')
        win.configure(bg=C['bg'])
        win.resizable(False, False)
        for key, desc in [
            ('F5',       'Run machine (animated)'),
            ('F6',       'Single step'),
            ('Escape',   'Stop auto-run'),
            ('Ctrl + L', 'Load machine from config fields'),
            ('Ctrl + R', 'Reset tape to initial input'),
            ('Ctrl + Z', 'Undo last step'),
            ('F9',       'Open transition table viewer'),
            ('Return',   'Load machine (when in a config entry field)'),
        ]:
            row = tk.Frame(win, bg=C['bg'])
            row.pack(fill='x', padx=20, pady=3)
            tk.Label(row, text=key, bg=C['bg'], fg=C['accent'],
                     font=('Consolas', 9, 'bold'), width=14, anchor='w').pack(side='left')
            tk.Label(row, text=desc, bg=C['bg'], fg=C['text'],
                     font=FONT_UI, anchor='w').pack(side='left')
        tk.Frame(win, bg=C['bg'], height=10).pack()

    def _show_about(self):
        messagebox.showinfo(
            'About',
            'Turing Machine Simulator\n\n'
            'A deterministic, single-tape TM simulator.\n\n'
            'Features:\n'
            '  * Step-by-step and animated execution\n'
            '  * Unlimited undo / history  (Ctrl+Z)\n'
            '  * Syntax-highlighted transition editor\n'
            '  * Transition table viewer  (F9)\n'
            '  * Batch test multiple inputs at once\n'
            '  * Configurable step limit per machine\n'
            '  * Save / load configurations  (JSON)\n'
            '  * Export execution log to .txt\n'
            '  * 5 built-in example machines\n\n'
            'Built with Python + Tkinter  --  Rose Pine theme',
        )

    # ── Syntax highlighting ──────────────────────────────────────

    _TRANSITION_RE = re.compile(
        r'^(\s*)(\S+)(\s*,\s*)(\S+)(\s*->\s*)(\S+)(\s*,\s*)([LRSlrs])(\s*,\s*)(\S+)(\s*)$'
    )

    def _highlight_transitions(self):
        t = self.txt_transitions
        for tag in ('hl_comment', 'hl_state', 'hl_symbol',
                    'hl_arrow', 'hl_direction', 'hl_error'):
            t.tag_remove(tag, '1.0', 'end')

        for lineno, raw in enumerate(t.get('1.0', 'end').splitlines(), 1):
            ls = f'{lineno}.0'
            le = f'{lineno}.end'
            stripped = raw.strip()
            if not stripped:
                continue
            if stripped.startswith('#'):
                t.tag_add('hl_comment', ls, le)
                continue
            m = self._TRANSITION_RE.match(raw)
            if not m:
                t.tag_add('hl_error', ls, le)
                continue
            col = 0
            for i, chunk in enumerate(m.groups()):
                start = f'{lineno}.{col}'
                end   = f'{lineno}.{col + len(chunk)}'
                if   i == 1: t.tag_add('hl_state',     start, end)
                elif i == 3: t.tag_add('hl_symbol',    start, end)
                elif i == 4: t.tag_add('hl_arrow',     start, end)
                elif i == 5: t.tag_add('hl_symbol',    start, end)
                elif i == 7: t.tag_add('hl_direction', start, end)
                elif i == 9: t.tag_add('hl_state',     start, end)
                col += len(chunk)


# ─────────────────────────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    app = App()
    app.after(100, app._initial_render)
    app.mainloop()
