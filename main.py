import json
import tkinter as tk
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
#  FRONTEND: Tkinter GUI
# ─────────────────────────────────────────────────────────────────

# Colour palette — dark terminal aesthetic
C = {
    'bg':          '#0d1117',
    'panel':       '#161b22',
    'border':      '#30363d',
    'text':        '#e6edf3',
    'muted':       '#8b949e',
    'accent':      '#58a6ff',
    'green':       '#3fb950',
    'red':         '#f85149',
    'yellow':      '#d29922',
    'tape_cell':   '#21262d',
    'tape_head':   '#388bfd',
    'tape_changed':'#d29922',
    'tape_text':   '#e6edf3',
    'btn':         '#21262d',
    'btn_hover':   '#30363d',
    'btn_run':     '#238636',
    'btn_step':    '#1f6feb',
    'btn_reset':   '#6e7681',
}

FONT_MONO  = ('Courier New', 11)
FONT_MONO_BIG = ('Courier New', 14, 'bold')
FONT_TITLE = ('Courier New', 18, 'bold')
FONT_LABEL = ('Courier New', 10)
FONT_BTN   = ('Courier New', 11, 'bold')

TAPE_CELLS     = 21   # visible tape cells (odd number keeps head centred)
CELL_W         = 44
CELL_H         = 54


class TapeCanvas(tk.Canvas):
    """Custom canvas that draws the tape cells."""

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=C['bg'], highlightthickness=0,
                         height=CELL_H + 40, **kw)
        self.cell_data: list[tuple[int, str]] = []
        self.head_pos: int = 0
        self.changed_pos: int | None = None

    def render(self, cell_data: list[tuple[int, str]],
               head_pos: int, changed_pos: int | None = None):
        self.cell_data = cell_data
        self.head_pos = head_pos
        self.changed_pos = changed_pos
        self.after_idle(self._draw)

    def _draw(self):
        self.delete('all')
        w = self.winfo_width()
        n = len(self.cell_data)
        total_w = n * CELL_W
        x0 = (w - total_w) // 2          # Centre the tape in canvas
        y0 = 22                           # top of cells

        for idx, (pos, sym) in enumerate(self.cell_data):
            x = x0 + idx * CELL_W
            is_head = (pos == self.head_pos)
            is_changed = (pos == self.changed_pos)

            # Cell fill
            if is_head:
                fill = C['tape_head']
            elif is_changed:
                fill = C['tape_changed']
            else:
                fill = C['tape_cell']

            # Draw cell rectangle
            self.create_rectangle(x, y0, x + CELL_W - 2, y0 + CELL_H,
                                  fill=fill, outline=C['border'], width=1)

            # Symbol
            txt_color = '#ffffff' if (is_head or is_changed) else C['tape_text']
            self.create_text(x + CELL_W // 2, y0 + CELL_H // 2,
                             text=sym, fill=txt_color,
                             font=FONT_MONO_BIG)

            # Position index (small, below cell)
            self.create_text(x + CELL_W // 2, y0 + CELL_H + 10,
                             text=str(pos), fill=C['muted'],
                             font=('Courier New', 8))

        # Head arrow above the centre cell
        cx = x0 + (n // 2) * CELL_W + CELL_W // 2
        self.create_text(cx, y0 - 10, text='▼',
                         fill=C['tape_head'], font=('Courier New', 14, 'bold'))


class App(tk.Tk):
    """Main application window."""

    def __init__(self):
        super().__init__()
        self.title("Turing Machine Simulator")
        self.configure(bg=C['bg'])
        self.resizable(True, True)
        self.minsize(900, 720)

        self.tm = TuringMachine()
        self.sim = Simulator(self.tm)
        self._run_thread: threading.Thread | None = None
        self._running = False
        self._speed_ms = 400   # ms between steps during Run
        self._table_win: tk.Toplevel | None = None   # Transition table window

        self._build_ui()
        self._load_example()   # Pre-fill with a working example

    # ── UI construction ───────────────────────────────────────────

    def _build_menu(self):
        """Create the top menu bar, housing File and View actions."""
        menubar = tk.Menu(self, bg=C['panel'], fg=C['text'],
                          activebackground=C['accent'], activeforeground='white',
                          relief='flat', bd=0)

        file_menu = tk.Menu(menubar, tearoff=0,
                            bg=C['panel'], fg=C['text'],
                            activebackground=C['accent'], activeforeground='white')
        file_menu.add_command(label="Open Configuration…", command=self._load_config)
        file_menu.add_command(label="Save Configuration…", command=self._save_config)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        view_menu = tk.Menu(menubar, tearoff=0,
                            bg=C['panel'], fg=C['text'],
                            activebackground=C['accent'], activeforeground='white')
        view_menu.add_command(label="Transition Table", command=self._show_transition_table)
        menubar.add_cascade(label="View", menu=view_menu)

        self.config(menu=menubar)

    def _build_ui(self):
        # ── Menu bar ──────────────────────────────────────────────
        self._build_menu()

        # ── Title bar ────────────────────────────────────────────
        title_frame = tk.Frame(self, bg=C['bg'], pady=10)
        title_frame.pack(fill='x')
        tk.Label(title_frame, text="◈  TURING MACHINE SIMULATOR",
                 bg=C['bg'], fg=C['accent'],
                 font=FONT_TITLE).pack()
        tk.Label(title_frame, text="Deterministic · Single-Tape · Step-by-Step",
                 bg=C['bg'], fg=C['muted'], font=FONT_LABEL).pack()

        # ── Separator ────────────────────────────────────────────
        tk.Frame(self, bg=C['border'], height=1).pack(fill='x')

        # ── Main layout (left panel + right log) ─────────────────
        main = tk.Frame(self, bg=C['bg'])
        main.pack(fill='both', expand=True, padx=16, pady=10)

        left  = tk.Frame(main, bg=C['bg'])
        left.pack(side='left', fill='both', expand=True)

        right = tk.Frame(main, bg=C['panel'], bd=0,
                         highlightbackground=C['border'], highlightthickness=1)
        right.pack(side='right', fill='y', padx=(12, 0), ipadx=4)

        # ── Tape display ─────────────────────────────────────────
        tape_frame = tk.LabelFrame(left, text=" TAPE ", bg=C['bg'], fg=C['accent'],
                                   font=FONT_LABEL, bd=1,
                                   highlightbackground=C['border'])
        tape_frame.pack(fill='x', pady=(0, 8))

        self.tape_canvas = TapeCanvas(tape_frame, width=TAPE_CELLS * CELL_W + 20)
        self.tape_canvas.pack(fill='x', expand=True, padx=8, pady=8)

        # ── Status bar ───────────────────────────────────────────
        status_frame = tk.Frame(left, bg=C['panel'],
                                highlightbackground=C['border'], highlightthickness=1)
        status_frame.pack(fill='x', pady=(0, 8))

        for col in range(4):
            status_frame.columnconfigure(col, weight=1)

        for col, label in enumerate(("STATE", "HEAD", "SYMBOL", "STEPS")):
            tk.Label(status_frame, text=label, bg=C['panel'],
                     fg=C['muted'], font=FONT_LABEL).grid(row=0, column=col, padx=8, pady=4)

        self.lbl_state  = tk.Label(status_frame, text="—", bg=C['panel'],
                                   fg=C['accent'], font=FONT_MONO_BIG)
        self.lbl_head   = tk.Label(status_frame, text="0", bg=C['panel'],
                                   fg=C['text'],   font=FONT_MONO_BIG)
        self.lbl_symbol = tk.Label(status_frame, text="_", bg=C['panel'],
                                   fg=C['text'],   font=FONT_MONO_BIG)
        self.lbl_steps  = tk.Label(status_frame, text="0", bg=C['panel'],
                                   fg=C['text'],   font=FONT_MONO_BIG)

        self.lbl_state .grid(row=1, column=0, padx=8, pady=(0, 6))
        self.lbl_head  .grid(row=1, column=1, padx=8, pady=(0, 6))
        self.lbl_symbol.grid(row=1, column=2, padx=8, pady=(0, 6))
        self.lbl_steps .grid(row=1, column=3, padx=8, pady=(0, 6))

        # ── Result banner ─────────────────────────────────────────
        self.result_banner = tk.Label(left, text="", bg=C['bg'],
                                      font=('Courier New', 15, 'bold'))
        self.result_banner.pack(fill='x', pady=(0, 8))

        # ── Configuration section ─────────────────────────────────
        cfg_frame = tk.LabelFrame(left, text=" CONFIGURATION ",
                                  bg=C['bg'], fg=C['accent'],
                                  font=FONT_LABEL, bd=1,
                                  highlightbackground=C['border'])
        cfg_frame.pack(fill='x', pady=(0, 8))

        # Row 0: States / Start / Accept / Reject
        row0 = tk.Frame(cfg_frame, bg=C['bg'])
        row0.pack(fill='x', padx=8, pady=4)

        fields = [
            ("States", 'entry_states', 20),
            ("Start",  'entry_start',   8),
            ("Accept", 'entry_accept',  8),
            ("Reject", 'entry_reject',  8),
        ]
        for label, attr, w in fields:
            col = tk.Frame(row0, bg=C['bg'])
            col.pack(side='left', padx=4)
            tk.Label(col, text=label, bg=C['bg'], fg=C['muted'],
                     font=FONT_LABEL).pack(anchor='w')
            e = tk.Entry(col, width=w, bg=C['panel'], fg=C['text'],
                         insertbackground=C['text'], relief='flat',
                         font=FONT_MONO,
                         highlightbackground=C['border'], highlightthickness=1)
            e.pack()
            setattr(self, attr, e)

        # Row 1: Input string
        row1 = tk.Frame(cfg_frame, bg=C['bg'])
        row1.pack(fill='x', padx=8, pady=4)
        tk.Label(row1, text="Input:", bg=C['bg'], fg=C['muted'],
                 font=FONT_LABEL).pack(side='left', padx=4)
        self.entry_input = tk.Entry(row1, width=34, bg=C['panel'],
                                    fg=C['text'], insertbackground=C['text'],
                                    relief='flat', font=FONT_MONO,
                                    highlightbackground=C['border'], highlightthickness=1)
        self.entry_input.pack(side='left', padx=4)

        # ── Transition editor ─────────────────────────────────────
        tr_frame = tk.LabelFrame(left, text=" TRANSITIONS  (state,sym → sym,Dir,state) ",
                                 bg=C['bg'], fg=C['accent'],
                                 font=FONT_LABEL, bd=1,
                                 highlightbackground=C['border'])
        tr_frame.pack(fill='both', expand=True, pady=(0, 8))

        self.txt_transitions = scrolledtext.ScrolledText(
            tr_frame, width=55, height=8,
            bg=C['panel'], fg=C['text'],
            insertbackground=C['text'],
            relief='flat', font=FONT_MONO,
            highlightbackground=C['border'], highlightthickness=1
        )
        self.txt_transitions.pack(fill='both', expand=True, padx=8, pady=8)

        # Syntax-highlight colour tags
        self.txt_transitions.tag_config('hl_comment',   foreground=C['muted'])
        self.txt_transitions.tag_config('hl_state',     foreground=C['accent'])
        self.txt_transitions.tag_config('hl_symbol',    foreground=C['yellow'])
        self.txt_transitions.tag_config('hl_arrow',     foreground=C['muted'])
        self.txt_transitions.tag_config('hl_direction', foreground=C['green'])
        self.txt_transitions.tag_config('hl_error',     foreground=C['red'])

        self.txt_transitions.bind('<KeyRelease>',   lambda _e: self._highlight_transitions())
        self.txt_transitions.bind('<<Paste>>',      lambda _e: self.after(10, self._highlight_transitions))

        # ── Buttons ───────────────────────────────────────────────
        btn_frame = tk.Frame(left, bg=C['bg'])
        btn_frame.pack(fill='x', pady=(0, 4))

        self.btn_load  = self._make_btn(btn_frame, "⬆  LOAD",  C['btn'],       self._load_machine)
        self.btn_step  = self._make_btn(btn_frame, "▶  STEP",  C['btn_step'],  self._step)
        self.btn_undo  = self._make_btn(btn_frame, "◀  UNDO",  C['btn'],       self._undo)

        # Visual divider between configure/step group and run group
        tk.Frame(btn_frame, bg=C['border'], width=1).pack(side='left', fill='y', padx=6, pady=4)

        self.btn_run   = self._make_btn(btn_frame, "⏩  RUN",   C['btn_run'],   self._run)
        self.btn_stop  = self._make_btn(btn_frame, "⏹  STOP",  C['yellow'],    self._stop)
        self.btn_reset = self._make_btn(btn_frame, "↺  RESET", C['btn_reset'], self._reset)

        for btn in (self.btn_load, self.btn_step, self.btn_undo,
                    self.btn_run, self.btn_stop, self.btn_reset):
            btn.pack(side='left', padx=3, pady=2)

        self.btn_stop.config(state='disabled')

        # Speed control — compact inline strip
        spd_frame = tk.Frame(left, bg=C['bg'])
        spd_frame.pack(fill='x')
        tk.Label(spd_frame, text="Speed:", bg=C['bg'],
                 fg=C['muted'], font=FONT_LABEL).pack(side='left', padx=4)
        self.speed_var = tk.IntVar(value=400)
        speed_scale = tk.Scale(spd_frame, from_=50, to=1000,
                               orient='horizontal', variable=self.speed_var,
                               bg=C['bg'], fg=C['text'], troughcolor=C['panel'],
                               highlightthickness=0, length=160,
                               command=self._on_speed_change,
                               showvalue=True)
        speed_scale.pack(side='left')

        # ── Right panel: Execution log ─────────────────────────────
        tk.Label(right, text="EXECUTION LOG", bg=C['panel'],
                 fg=C['accent'], font=FONT_LABEL).pack(padx=8, pady=(8, 2))
        tk.Frame(right, bg=C['border'], height=1).pack(fill='x', padx=4)

        self.log_box = scrolledtext.ScrolledText(
            right, width=26, height=30,
            bg=C['panel'], fg=C['text'],
            insertbackground=C['text'],
            relief='flat', font=('Courier New', 9),
            state='disabled',
            highlightthickness=0
        )
        self.log_box.pack(fill='both', expand=True, padx=4, pady=4)

        # Tag colours in log
        self.log_box.tag_config('accept', foreground=C['green'])
        self.log_box.tag_config('reject', foreground=C['red'])
        self.log_box.tag_config('step',   foreground=C['accent'])
        self.log_box.tag_config('info',   foreground=C['muted'])

    def _make_btn(self, parent, text, color, command):
        btn = tk.Button(parent, text=text, bg=color, fg='white',
                        activebackground=C['btn_hover'], activeforeground='white',
                        relief='flat', font=FONT_BTN, cursor='hand2',
                        padx=10, pady=6, command=command, bd=0)
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
        self._speed_ms = int(val)

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
        self._refresh_ui()

    def _set_run_mode(self, running: bool):
        """Enable/disable buttons appropriately during auto-run."""
        idle_state  = 'normal' if not running else 'disabled'
        stop_state  = 'normal' if running     else 'disabled'
        for btn in (self.btn_load, self.btn_step, self.btn_undo,
                    self.btn_run, self.btn_reset):
            btn.config(state=idle_state)
        self.btn_stop.config(state=stop_state)

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
        elif status == 'timeout':
            self.result_banner.config(
                text=f"  ⚠  TIMEOUT  — exceeded {self.sim.MAX_STEPS} steps  ",
                bg=C['yellow'], fg='white')
        elif status == 'no_rule':
            self.result_banner.config(
                text=f"  ✘  REJECTED  (no rule) after {self.sim.steps} steps  ",
                bg=C['red'], fg='white')
        else:
            self.result_banner.config(
                text=f"  ✘  REJECTED  after {self.sim.steps} steps  ",
                bg=C['red'], fg='white')

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
        self._refresh_ui()
        steps = self.sim.steps
        self._log(f"[{steps:>5}] ↩ UNDO — back to step {steps}", 'info')

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
        app.tape_canvas.render(
            [(i, '_') for i in range(-TAPE_CELLS // 2, TAPE_CELLS // 2 + 1)],
            head_pos=0
        )
    app.after(100, _initial_render)

    app.mainloop()