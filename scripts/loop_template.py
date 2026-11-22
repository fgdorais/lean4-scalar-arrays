# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""
The template for `ScalarArray/Loop.lean` and `ScalarArray/UInt16/Loops.lean`, used by
`generate.py`: the loops in continuation-passing style with `MIN_ARITY` to `MAX_ARITY` variables.
The loops with one variable, `Tail.forIn` and `Tail.forInRev`, are written by hand in the `Program`
template, with the lemmas that run them. `maxLoopVars` in
`ScalarArray/Notation.lean` is `MAX_ARITY`.
"""

MIN_ARITY = 2
MAX_ARITY = 8

SUB = '₀₁₂₃₄₅₆₇₈₉'

HEADER = '''/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

'''


def sub(i):
    return ''.join(SUB[int(d)] for d in str(i))


def names(base, n):
    return [f'{base}{sub(i)}' for i in range(1, n + 1)]


def spaced(xs):
    return ' '.join(xs)


def universes(n):
    """The binders `{β₁ : Type v₁} …`, in groups that fit in 100 columns."""
    return [f'{{β{sub(i)} : Type v{sub(i)}}}' for i in range(1, n + 1)]


def arrow(n, last):
    """`β₁ → … → βₙ → last`."""
    return ' → '.join(names('β', n) + [last])


def wrap(prefix, items, indent, width=100):
    """`prefix` followed by `items` separated by spaces, broken into lines of at most `width`."""
    lines = []
    line = prefix
    for item in items:
        if len(line) + 1 + len(item) > width and line.strip():
            lines.append(line)
            line = ' ' * indent + item
        else:
            line = f'{line} {item}' if line.strip() else line + item
    lines.append(line)
    return '\n'.join(lines)


def fold(text, width=100):
    """
    Breaks the code lines of `text` longer than `width`, after an arrow if possible, else at a
    space. Comments are left alone.
    """
    out = []
    in_doc = False
    for line in text.split('\n'):
        if line.startswith('/-'):
            in_doc = not line.rstrip().endswith('-/')
        elif in_doc:
            in_doc = not line.rstrip().endswith('-/')
        else:
            while len(line) > width:
                indent = len(line) - len(line.lstrip())
                cont = ' ' * (4 if indent == 0 else indent + 2)
                i = line.rfind(' → ', 0, width - 1)
                if i > indent:
                    head, rest = line[:i + 2], line[i + 3:]
                else:
                    i = line.rfind(' ', indent + 1, width + 1)
                    head, rest = line[:i], line[i + 1:]
                out.append(head)
                line = cont + rest
        out.append(line)
    return '\n'.join(out)


def inits(n):
    return [f'(init{sub(i)} : β{sub(i)})' for i in range(1, n + 1)]


def bs(n):
    return [f'(b{sub(i)} : β{sub(i)})' for i in range(1, n + 1)]


def kernel(n, up):
    b = spaced(names('b', n))
    k = arrow(n, 'σ → γ')
    name = f'forUp{n}' if up else f'forDown{n}'
    binders = wrap(f'public def {name} {{σ : Type u}} {{γ : Type w}}', universes(n), 4)
    if up:
        index = '(j : USize) (hlo : lo.toNat ≤ j.toNat)'
        step = (f'  if hj : j < hi then\n'
                f'    body j hlo hj (fun {b} s =>\n'
                f'        {name} lo hi body k (j + 1) (le_succ hlo hj) {b} s)\n'
                f'      {b} s\n')
        measure = ('termination_by hi.toNat - j.toNat\n'
                   'decreasing_by exact sub_toNat_add_one_lt hj\n')
        doc = (f'/--\nThe loop with {n} variables up from `j` to `hi - 1`: the body gets the '
               f'next step as `next`, and the\nloop ends with `k`. It is specified by '
               f'`{name}_eq`.\n-/\n')
    else:
        index = '(j : USize) (hj : j.toNat ≤ hi.toNat)'
        step = (f'  if h : lo < j then\n'
                f'    body (j - 1) (le_pred h) (pred_lt hj h) (fun {b} s =>\n'
                f'        {name} lo hi body k (j - 1) (Nat.le_of_lt (pred_lt hj h)) {b} s)\n'
                f'      {b} s\n')
        measure = ('termination_by j.toNat\n'
                   'decreasing_by exact toNat_sub_one_lt_of_lt h\n')
        doc = (f'/--\nThe loop with {n} variables down from `j - 1` to `lo`: the body gets the '
               f'next step as `next`,\nand the loop ends with `k`. It is specified by '
               f'`{name}_eq`.\n-/\n')
    args = wrap('    ', [index] + bs(n) + ['(s : σ) : γ :=' ], 4)
    return (doc + '@[specialize]\n' + binders + '\n'
            + '    (lo hi : USize)\n'
            + '    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →\n'
            + f'      ({k}) →\n'
            + f'      {k})\n'
            + f'    (k : {k})\n'
            + args + '\n' + step
            + '  else\n'
            + f'    k {b} s\n'
            + measure)


def kernel_eq(n, up):
    b = spaced(names('b', n))
    k = arrow(n, 'σ → γ')
    name = f'forUp{n}' if up else f'forDown{n}'
    binders = wrap(f'public theorem {name}_eq {{σ : Type u}} {{γ : Type w}}', universes(n), 4)
    if up:
        index = '(j : USize) (hlo : lo.toNat ≤ j.toNat)'
        lhs = f'    {name} lo hi body k j hlo {b} s =\n'
        rhs = (f'      if hj : j < hi then\n'
               f'        body j hlo hj (fun {b} s =>\n'
               f'            {name} lo hi body k (j + 1) (le_succ hlo hj) {b} s)\n'
               f'          {b} s\n')
        cond = 'j < hi'
    else:
        index = '(j : USize) (hj : j.toNat ≤ hi.toNat)'
        lhs = f'    {name} lo hi body k j hj {b} s =\n'
        rhs = (f'      if h : lo < j then\n'
               f'        body (j - 1) (le_pred h) (pred_lt hj h) (fun {b} s =>\n'
               f'            {name} lo hi body k (j - 1) (Nat.le_of_lt (pred_lt hj h)) {b} s)\n'
               f'          {b} s\n')
        cond = 'lo < j'
    args = wrap('    ', [index] + bs(n) + ['(s : σ) :'], 4)
    return (f'/-- One step of `{name}`. -/\n' + binders + '\n'
            + '    (lo hi : USize)\n'
            + '    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →\n'
            + f'      ({k}) →\n'
            + f'      {k})\n'
            + f'    (k : {k})\n'
            + args + '\n' + lhs + rhs
            + f'      else k {b} s := by\n'
            + f'  rw [{name}]\n')


def loop_module():
    """`ScalarArray/Loop.lean`: the loops over any state, which each array's loops wrap."""
    out = [HEADER, '''public import Init
import all ScalarArray.Internal

/-!
# Loops with several variables

The loops in continuation-passing style of the arrays' tail programs with %d to %d variables,
`XArray.InPlace.Tail.forIn%d`, … and `XArray.InPlace.Tail.forInRev%d`, …, over any state `σ`: each
array's loops wrap these, with its own state. They are for internal use: the arrays' loops are the
API. Each variable is an argument of the loop, so that scalars stay unboxed.

This module is generated by `scripts/generate.py`, from `scripts/loop_template.py`.
-/

namespace ScalarArray.Loop

/-- The index of a step of `forUp`: `lo ≤ j + 1` when `lo ≤ j < hi`. -/
public theorem le_succ {lo j hi : USize} (h : lo.toNat ≤ j.toNat) (hj : j < hi) :
    lo.toNat ≤ (j + 1).toNat := by
  grind

/-- The index of a step of `forDown`: `j - 1 < hi` when `lo < j ≤ hi`. -/
public theorem pred_lt {lo hi j : USize} (hj : j.toNat ≤ hi.toNat) (h : lo < j) :
    (j - 1).toNat < hi.toNat := by
  grind

/-- The index of a step of `forDown`: `lo ≤ j - 1` when `lo < j`. -/
public theorem le_pred {lo j : USize} (h : lo < j) : lo.toNat ≤ (j - 1).toNat := by
  grind
''' % (MIN_ARITY, MAX_ARITY, MIN_ARITY, MIN_ARITY)]
    for n in range(MIN_ARITY, MAX_ARITY + 1):
        out.append(f'\n/-! ## {n} variables -/\n')
        out.append('\n' + kernel(n, True))
        out.append('\n' + kernel_eq(n, True))
        out.append('\n' + kernel(n, False))
        out.append('\n' + kernel_eq(n, False))
    out.append('\nend ScalarArray.Loop\n')
    return fold(''.join(out))


def wrapper(n, up, start):
    """`Tail.forInN` or `Tail.forInRevN`, from `j₀` if `start`."""
    b = spaced(names('b', n))
    i = spaced(names('init', n))
    k = arrow(n, 'Tail n γ')
    kern = f'forUp{n}' if up else f'forDown{n}'
    name = (f'forIn{n}' if up else f'forInRev{n}') + ('From' if start else '')
    binders = wrap(f'public def {name}', universes(n), 4)
    if start:
        h = '(h : lo.toNat ≤ j₀.toNat)' if up else '(h : j₀.toNat ≤ hi.toNat)'
        args = wrap('    ', ['(lo hi j₀ : USize)', h] + inits(n), 4)
        if up:
            doc = (f'/-- `Tail.forIn{n}` from `j₀` instead of `lo`. It is specified by '
                   f'`Tail.forIn{n}From_eq`. -/\n')
        else:
            doc = (f'/--\n`Tail.forInRev{n}` from `j₀ - 1` down to `lo` instead of from `hi - 1`. '
                   f'It is specified by\n`Tail.forInRev{n}From_eq`.\n-/\n')
        body = (f'  ⟨Loop.{kern} lo hi\n'
                f'    (fun j hlo hj next {b} s =>\n'
                f'      (body j hlo hj (fun {b} => ⟨next {b}⟩) {b}).fn s)\n'
                f'    (fun {b} s => (k {b}).fn s) j₀ h {i}⟩\n')
        attrs = '@[inline]\n'
    else:
        args = wrap('    ', ['(lo hi : USize)'] + inits(n), 4)
        if up:
            doc = (f'/-- `Tail.forIn` with {n} variables, which the loop keeps as {n} arguments. '
                   f'-/\n')
            body = f'  forIn{n}From lo hi lo (Nat.le_refl _) {i} body k\n'
        else:
            doc = f'/-- `Tail.forIn{n}` from `hi - 1` down to `lo`. -/\n'
            body = f'  forInRev{n}From lo hi hi (Nat.le_refl _) {i} body k\n'
        attrs = '@[inline, expose]\n'
    return (doc + attrs + binders + '\n' + args + '\n'
            + '    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →\n'
            + f'      ({k}) → {k})\n'
            + f'    (k : {k}) : Tail n γ :=\n'
            + body)


def wrapper_eq(n, up, start):
    i = spaced(names('init', n))
    b = spaced(names('b', n))
    k = arrow(n, 'Tail n γ')
    kern = f'forUp{n}' if up else f'forDown{n}'
    base = f'forIn{n}' if up else f'forInRev{n}'
    if start:
        h = '(hlo : lo.toNat ≤ j.toNat)' if up else '(hj : j.toNat ≤ hi.toNat)'
        binders = wrap(f'public theorem {base}From_eq', universes(n), 4)
        args = wrap('    ', ['(lo hi j : USize)', h] + inits(n), 4)
        if up:
            stmt = (f'    {base}From lo hi j hlo {i} body k =\n'
                    f'      if hj : j < hi then\n'
                    f'        body j hlo hj\n'
                    f'          (fun {b} =>\n'
                    f'            {base}From lo hi (j + 1) (forIn_le_succ hlo hj) {b} body k)\n'
                    f'          {i}\n'
                    f'      else k {i} := by\n')
            proof = (f'  apply fn_inj; funext s\n'
                     f'  show Loop.{kern} lo hi _ _ j hlo {i} s = _\n'
                     f'  rw [Loop.{kern}_eq]\n'
                     f'  by_cases hj : j < hi\n'
                     f'  · simp only [hj, ↓reduceDIte]; rfl\n'
                     f'  · simp only [hj, ↓reduceDIte]\n')
        else:
            stmt = (f'    {base}From lo hi j hj {i} body k =\n'
                    f'      if h : lo < j then\n'
                    f'        body (j - 1) (forInRev_le_pred h) (forInRev_pred_lt hj h)\n'
                    f'          (fun {b} =>\n'
                    f'            {base}From lo hi (j - 1) (Nat.le_of_lt (forInRev_pred_lt hj h))'
                    f' {b}\n'
                    f'              body k)\n'
                    f'          {i}\n'
                    f'      else k {i} := by\n')
            proof = (f'  apply fn_inj; funext s\n'
                     f'  show Loop.{kern} lo hi _ _ j hj {i} s = _\n'
                     f'  rw [Loop.{kern}_eq]\n'
                     f'  by_cases h : lo < j\n'
                     f'  · simp only [h, ↓reduceDIte]; rfl\n'
                     f'  · simp only [h, ↓reduceDIte]\n')
        doc = f'/-- One step of `Tail.{base}From`. -/\n'
    else:
        binders = wrap(f'@[simp] public theorem {base}_eq', universes(n), 4)
        args = wrap('    ', ['(lo hi : USize)'] + inits(n), 4)
        j0 = 'lo' if up else 'hi'
        stmt = (f'    {base} lo hi {i} body k =\n'
                f'      {base}From lo hi {j0} (Nat.le_refl _) {i} body k := by\n')
        proof = '  rfl\n'
        doc = ''
    return (doc + binders + '\n' + args + '\n'
            + '    (body : (j : USize) → lo.toNat ≤ j.toNat → j.toNat < hi.toNat →\n'
            + f'      ({k}) → {k})\n'
            + f'    (k : {k}) :\n'
            + stmt + proof)


def loops_module():
    """`ScalarArray/UInt16/Loops.lean`, the template of each array's loops with several
    variables."""
    lo, hi = MIN_ARITY, MAX_ARITY
    doc = (f'The loops in continuation-passing style of `UInt16Array.InPlace.Tail` with {lo} to '
           f'{hi} variables:\n`Tail.forIn{lo}`, … `Tail.forIn{hi}`, and `Tail.forInRev{lo}`, … '
           f'`Tail.forInRev{hi}` downward. Like\n`Tail.forIn`, each variable is an argument of '
           f'the loop, so scalars stay unboxed, and nested loops\nallocate nothing. They wrap '
           f'the loops of `ScalarArray.Loop`, and they are specified by their\none-step '
           f'equations, `Tail.forIn{lo}From_eq`, …')
    out = [HEADER, f'''public import ScalarArray.UInt16.Program
public import ScalarArray.Loop
import all ScalarArray.UInt16.Program

/-!
# Loops with several variables on `UInt16Array`

{doc}

This module is generated by `scripts/generate.py`, from `scripts/loop_template.py`.
-/

namespace ScalarArray.UInt16Array.InPlace.Tail

variable {{n : Nat}} {{γ : Type w}}
''']
    for n in range(MIN_ARITY, MAX_ARITY + 1):
        out.append(f'\n/-! ## {n} variables -/\n')
        for up in (True, False):
            out.append('\n' + wrapper(n, up, True))
            out.append('\n' + wrapper(n, up, False))
        for up in (True, False):
            out.append('\n' + wrapper_eq(n, up, True))
            out.append('\n' + wrapper_eq(n, up, False))
    out.append('\nend ScalarArray.UInt16Array.InPlace.Tail\n')
    return fold(''.join(out))
