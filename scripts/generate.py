#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""
Generates the array modules and their tests from the `UInt16` versions.

`ScalarArray/UInt16.lean`, `ScalarArrayTest/UInt16.lean` and their parts in `ScalarArray/UInt16/`
and `ScalarArrayTest/UInt16/` are the templates: make changes there, then run this script from
anywhere to regenerate the other types, the root import lists and `.gitattributes`, which marks the
generated files so that GitHub collapses them in diffs.
`ScalarArray/Bytes.lean` and its tests come from `bytes_template.py`. That module is experimental,
so the root `ScalarArray.lean` does not import it.
With `--check`, it changes nothing and exits with status 1 if any generated file is out of date.
"""

import pathlib
import sys

sys.dont_write_bytecode = True
import bytes_template  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent

WORD = '(System.Platform.numBits / 8).toUInt32'
# Each entry: type name, element type, C element type, element size expression, element size in
# prose, a large test value, and the `Nat` conversion function.
WORD_PROSE = 'one machine word per element'
BIG = '18446744073709551615'
SMALL = '-9223372036854775808'
types = [
  ('UInt8',   'UInt8',   'uint8_t',  '1',  '1 byte per element',  '255',         'toUInt8'),
  ('UInt16',  'UInt16',  'uint16_t', '2',  '2 bytes per element', '65535',       'toUInt16'),
  ('UInt32',  'UInt32',  'uint32_t', '4',  '4 bytes per element', '4294967295',  'toUInt32'),
  ('UInt64',  'UInt64',  'uint64_t', '8',  '8 bytes per element', BIG,           'toUInt64'),
  ('USize',   'USize',   'size_t',   WORD, WORD_PROSE,            BIG,           'toUSize'),
  ('Int8',    'Int8',    'uint8_t',  '1',  '1 byte per element',  '-128',        'toInt8'),
  ('Int16',   'Int16',   'uint16_t', '2',  '2 bytes per element', '-32768',      'toInt16'),
  ('Int32',   'Int32',   'uint32_t', '4',  '4 bytes per element', '-2147483648', 'toInt32'),
  ('Int64',   'Int64',   'uint64_t', '8',  '8 bytes per element', SMALL,         'toInt64'),
  ('ISize',   'ISize',   'size_t',   WORD, WORD_PROSE,            SMALL,         'toISize'),
  ('Float32', 'Float32', 'float',    '4',  '4 bytes per element', '-1.5e38',     'toFloat32'),
  ('Float64', 'Float',   'double',   '8',  '8 bytes per element', '-1.5e300',    'toFloat'),
]

# The float types have no `DecidableEq` or `Hashable`: they get a `BEq` instance instead.
FLOAT_EQ_OLD = """/-- Decides equality by comparing the two arrays' memory. -/
@[extern "lean_sarray_dec_eq", expose]
public def decEq (a b : @& UInt16Array) : Decidable (a = b) :=
  decidable_of_iff (a.toArray = b.toArray)
    ⟨fun h => by rw [← mk_toArray a, h, mk_toArray], fun h => h ▸ rfl⟩

public instance : DecidableEq UInt16Array := decEq

private theorem beq_eq_beq_toArray (a b : UInt16Array) : (a == b) = (a.toArray == b.toArray) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨congrArg toArray, toArray_injective⟩

/-- The same hash as `a.toArray`. -/
public def hash (a : @& UInt16Array) : UInt64 :=
  Hashable.hash a.toArray

public def hashImpl (a : @& UInt16Array) : UInt64 :=
  a.foldl (fun r x => mixHash r (Hashable.hash x)) 7

@[csimp] public theorem hash_eq_hashImpl : @hash = @hashImpl := by rfl

public instance : Hashable UInt16Array := ⟨hash⟩

public theorem hash_eq_hash_toArray (a : UInt16Array) :
    Hashable.hash a = Hashable.hash a.toArray := by
  rfl
"""
FLOAT_EQ_NEW = """/--
Compares the elements with `==`, like `Array`. Floating-point equality is not decidable equality:
`NaN` is not equal to itself and `0.0 == -0.0`.
-/
public def beq (a b : @& UInt16Array) : Bool :=
  a.toArray == b.toArray

@[noinline]
private def beqSlow (a b : @& UInt16Array) : Bool :=
  a.beq b

public def beqImpl (a b : @& UInt16Array) : Bool :=
  if a.size < USize.size ∧ b.size < USize.size then
    if h : a.usize = b.usize then loop a.usize a.toNat_usize_le (h ▸ b.toNat_usize_le) 0 else false
  else beqSlow a b
where
  loop (stop : USize) (ha : stop.toNat ≤ a.size) (hb : stop.toNat ≤ b.size) (i : USize) : Bool :=
    if h : i < stop then
      a.uget i (toNat_lt_of_lt h ha) == b.uget i (toNat_lt_of_lt h hb) && loop stop ha hb (i + 1)
    else true
  termination_by stop.toNat - i.toNat
  decreasing_by exact sub_toNat_add_one_lt h

private theorem beqImpl_loop (a b : UInt16Array) (stop : USize) (ha : stop.toNat ≤ a.size)
    (hb : stop.toNat ≤ b.size) (i : USize) :
    beqImpl.loop a b stop ha hb i = true ↔ ∀ (k : Nat) (_ : i.toNat ≤ k) (hk : k < stop.toNat),
      (a.toArray[k]'(by rw [size_toArray']; lia) ==
        b.toArray[k]'(by rw [size_toArray']; lia)) = true := by
  fun_induction beqImpl.loop a b stop ha hb i with
  | case1 i hi ih =>
    have := USize.lt_iff_toNat_lt.1 hi
    rw [Bool.and_eq_true, ih]
    simp only [uget, Array.uget, toNat_add_one_of_lt hi]
    constructor
    · rintro ⟨h0, h⟩ k hik hk
      by_cases hk' : k = i.toNat
      · subst hk'; exact h0
      · exact h k (by lia) hk
    · intro h
      exact ⟨h _ (Nat.le_refl _) this, fun k hik hk => h k (by lia) hk⟩
  | case2 i hi =>
    have := USize.le_iff_toNat_le.1 (USize.not_lt.1 hi)
    simp only [true_iff]
    intro k hik hk
    lia

@[csimp] public theorem beq_eq_beqImpl : @beq = @beqImpl := by
  funext a b
  simp only [beqImpl]
  split
  · rename_i hsize
    have ha := toNat_toUSize_of_le hsize.1 (Nat.le_refl _)
    have hb := toNat_toUSize_of_le hsize.2 (Nat.le_refl _)
    have husize : a.usize = b.usize ↔ a.size = b.size := by
      rw [← USize.toNat_inj, usize, usize, ha, hb]
    rw [beq, Array.beq_eq_decide]
    have hdata : a.toArray.size = b.toArray.size ↔ a.size = b.size := .rfl
    by_cases h : a.size = b.size
    · rw [dite_eq_left (husize.2 h), dite_eq_left (hdata.2 h), Bool.eq_iff_iff, decide_eq_true_eq,
        beqImpl_loop]
      simp only [usize, ha, USize.toNat_zero, Nat.zero_le, forall_const]
      exact ⟨fun h' k hk => h' k hk, fun h' k hk => h' k hk⟩
    · rw [dite_eq_right fun h' => h (husize.1 h'), dite_eq_right fun h' => h (hdata.1 h')]
  · rfl

public instance : BEq UInt16Array := ⟨beq⟩

private theorem beq_eq_beq_toArray (a b : UInt16Array) : (a == b) = (a.toArray == b.toArray) := rfl
"""
# The parts of each array module and of its tests, in import order. The float types leave out
# `Decidable`: the lemmas and instances that need decidable equality or hashing, and their tests.
PARTS = ['Basic', 'Array', 'Slice', 'Lemmas', 'InPlace', 'Decidable']
# Left out of the `USize` and `ISize` tests: `decide` can't evaluate their literals, since
# `System.Platform.numBits` is opaque.
WORD_TEST_DECIDE = ('-- `decide` evaluates', '-- Lemmas that need decidable equality')


def sub(s, pairs):
    for a, b in pairs:
        assert a in s, f"template text not found: {a!r}"
        s = s.replace(a, b)
    return s


def sub_all(files, pairs):
    """`sub` on several files at once: each text must be found in at least one of them."""
    for a, b in pairs:
        assert any(a in s for s in files.values()), f"template text not found: {a!r}"
        files = {path: s.replace(a, b) for path, s in files.items()}
    return files


def cut(s, span):
    start, stop = span
    i = s.find(start)
    assert i >= 0 and s.count(start) == 1, f"template text not found: {start!r}"
    j = s.find(stop, i)
    assert j >= 0, f"template text not found: {stop!r}"
    return s[:i] + s[j:]


def generate():
    """Returns a map from paths relative to the repository root to their generated contents."""
    src = {'': (ROOT / 'ScalarArray/UInt16.lean').read_text()}
    src.update({p: (ROOT / f'ScalarArray/UInt16/{p}.lean').read_text() for p in PARTS})
    tst = {'': (ROOT / 'ScalarArrayTest/UInt16.lean').read_text()}
    tst.update({p: (ROOT / f'ScalarArrayTest/UInt16/{p}.lean').read_text() for p in PARTS})
    files = {}
    for name, elem, ctype, alloc, per_elem, big, conv in types:
        is_float = name.startswith('Float')
        s = dict(src)
        if is_float:
            del s['Decidable']
            s = sub_all(s, [
                (FLOAT_EQ_OLD, FLOAT_EQ_NEW),
                ('/-! ## Equality and hashing -/', '/-! ## Equality -/'),
                ('public import ScalarArray.UInt16.Decidable\n', ''),
            ])
        s = sub_all(s, [
            # Module names first: `Float64Array` lives in `ScalarArray.Float64`, not
            # `ScalarArray.Float`.
            ('ScalarArray.UInt16.', f'ScalarArray.{name}.'),
            ('UInt16Array', name + 'Array'),
            ('allocate 2 ', f'allocate {alloc} '),
            ('2 bytes per element', per_elem),
            ('uint16_t', ctype),
            ('UInt16', elem),
        ])
        if name == 'Float64':
            s = sub_all(s, [('it otherwise, like `Array` and `ByteArray`.\n',
                             'it otherwise, like `Array` and `ByteArray`.\n\n'
                             '`Float64Array` has the same runtime representation as the core '
                             '`FloatArray`, with the same API\n'
                             'as the other arrays in this library.\n')])
        for part, text in s.items():
            files[f'ScalarArray/{name}{"/" + part if part else ""}.lean'] = text
        t = dict(tst)
        if is_float:
            del t['Decidable']
            t = sub_all(t, [('import ScalarArrayTest.UInt16.Decidable\n', '')])
        if alloc == WORD:
            t['Decidable'] = cut(t['Decidable'], WORD_TEST_DECIDE)
        t = sub_all(t, [
            ('ScalarArrayTest.UInt16.', f'ScalarArrayTest.{name}.'),
            ('import ScalarArray.UInt16\n', f'import ScalarArray.{name}\n'),
            ('elemSize : UInt32 := 2', f'elemSize : UInt32 := {alloc}'),
            ('UInt16Array', name + 'Array'),
            ('toUInt16', conv),
            ('big : UInt16 := 65535', f'big : UInt16 := {big}'),
            ('UInt16', elem),
        ])
        for part, text in t.items():
            files[f'ScalarArrayTest/{name}{"/" + part if part else ""}.lean'] = text
    names = [t[0] for t in types]
    root = (ROOT / 'ScalarArray.lean').read_text()
    head = root.split('public import ScalarArray.')[0]
    doc = '\n/-!' + root.split('\n/-!', 1)[1]
    files['ScalarArray.lean'] = (
        head + ''.join(f'public import ScalarArray.{n}\n' for n in names)
        + 'public import ScalarArray.Conversions\n' + doc)
    files['ScalarArray/Bytes.lean'] = bytes_template.module()
    files['ScalarArrayTest/Bytes.lean'] = bytes_template.tests()
    test_root = (ROOT / 'ScalarArrayTest.lean').read_text()
    files['ScalarArrayTest.lean'] = (
        test_root.split('import ')[0]
        + ''.join(f'import ScalarArrayTest.{n}\n' for n in names)
        + 'import ScalarArrayTest.Float\n'
        + 'import ScalarArrayTest.Conversions\n'
        + 'import ScalarArrayTest.Bytes\n')
    files['.gitattributes'] = (
        '# Files generated by `scripts/generate.py`, from the `UInt16` templates and\n'
        '# `bytes_template.py`. GitHub collapses them in diffs.\n'
        + ''.join(f'{d}/{n}.lean linguist-generated\n{d}/{n}/** linguist-generated\n'
                  for d in ['ScalarArray', 'ScalarArrayTest'] for n in names if n != 'UInt16')
        + 'ScalarArray/Bytes.lean linguist-generated\n'
        + 'ScalarArrayTest/Bytes.lean linguist-generated\n')
    return files


def main():
    check = sys.argv[1:] == ['--check']
    stale = []
    for path, contents in generate().items():
        file = ROOT / path
        if not file.exists() or file.read_text() != contents:
            stale.append(path)
            if not check:
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text(contents)
    if check and stale:
        print('Out of date; run scripts/generate.py:', *stale, sep='\n  ')
        sys.exit(1)


if __name__ == '__main__':
    main()
