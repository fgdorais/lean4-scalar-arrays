#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""
Generates the array modules and their tests from the `UInt16` versions.

`ScalarArray/UInt16.lean` and `ScalarArrayTest/UInt16.lean` are the templates: make changes there,
then run this script from anywhere to regenerate the other types and the root import lists.
With `--check`, it changes nothing and exits with status 1 if any generated file is out of date.
"""

import pathlib
import sys

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
  decidable_of_iff (a.data = b.data) ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

public instance : DecidableEq UInt16Array := decEq

private unsafe def hashImpl (a : @& UInt16Array) : UInt64 :=
  foldlMImpl (m := Id) (fun r x => mixHash r (Hashable.hash x)) 7 a

/-- The same hash as `a.data`. -/
@[implemented_by hashImpl]
public def hash (a : @& UInt16Array) : UInt64 :=
  Hashable.hash a.data

public instance : Hashable UInt16Array := ⟨hash⟩

public theorem hash_eq_hash_data (a : UInt16Array) : Hashable.hash a = Hashable.hash a.data := by
  rfl
"""
FLOAT_EQ_NEW = """private unsafe def beqImpl (a b : @& UInt16Array) : Bool :=
  a.usize == b.usize && loop 0
where
  loop (i : USize) : Bool :=
    if h : i.toNat < a.size then
      if h' : i.toNat < b.size then a.uget i h == b.uget i h' && loop (i + 1) else false
    else
      true

/--
Compares the elements with `==`, like `Array`. Floating-point equality is not decidable equality:
`NaN` is not equal to itself and `0.0 == -0.0`.
-/
@[implemented_by beqImpl]
public def beq (a b : @& UInt16Array) : Bool :=
  a.data == b.data

public instance : BEq UInt16Array := ⟨beq⟩
"""
# Also left out for the float types, from the first line up to, but not including, the second: the
# lemmas and instances that need decidable equality or hashing, and their tests.
FLOAT_DEC = ('/-! ### Decidable membership and slice hashing -/\n',
             '/-! ### End of the part left out of the float types -/\n')
FLOAT_TEST_DEC = ('/-! Decidable equality and hashing -/\n', '/-! Iteration -/\n')
# Left out of the `USize` and `ISize` tests: `decide` can't evaluate their literals, since
# `System.Platform.numBits` is opaque.
WORD_TEST_DECIDE = ('-- `decide` evaluates', '-- Lemmas that need decidable equality')


def sub(s, pairs):
    for a, b in pairs:
        assert a in s, f"template text not found: {a!r}"
        s = s.replace(a, b)
    return s


def cut(s, span):
    start, stop = span
    i = s.find(start)
    assert i >= 0 and s.count(start) == 1, f"template text not found: {start!r}"
    j = s.find(stop, i)
    assert j >= 0, f"template text not found: {stop!r}"
    return s[:i] + s[j:]


def generate():
    """Returns a map from paths relative to the repository root to their generated contents."""
    src = (ROOT / 'ScalarArray/UInt16.lean').read_text()
    tst = (ROOT / 'ScalarArrayTest/UInt16.lean').read_text()
    files = {}
    for name, elem, ctype, alloc, per_elem, big, conv in types:
        is_float = name.startswith('Float')
        s = src
        if is_float:
            s = sub(s, [(FLOAT_EQ_OLD, FLOAT_EQ_NEW),
                        ('/-! ## Equality and hashing -/', '/-! ## Equality -/')])
            s = cut(s, FLOAT_DEC)
        s = sub(s, [
            ('UInt16Array', name + 'Array'),
            ('allocate 2 ', f'allocate {alloc} '),
            ('2 bytes per element', per_elem),
            ('uint16_t', ctype),
            ('UInt16', elem),
        ])
        if name == 'Float64':
            s = sub(s, [('it otherwise, like `Array` and `ByteArray`.\n',
                         'it otherwise, like `Array` and `ByteArray`.\n\n'
                         '`Float64Array` has the same runtime representation as the core '
                         '`FloatArray`, with the same API\n'
                         'as the other arrays in this library.\n')])
        files[f'ScalarArray/{name}.lean'] = s
        t = cut(tst, FLOAT_TEST_DEC) if is_float else tst
        if alloc == WORD:
            t = cut(t, WORD_TEST_DECIDE)
        t = sub(t, [
            ('import ScalarArray.UInt16', 'import ScalarArray.' + name),
            ('elemSize : UInt32 := 2', f'elemSize : UInt32 := {alloc}'),
            ('UInt16Array', name + 'Array'),
            ('toUInt16', conv),
            ('big : UInt16 := 65535', f'big : UInt16 := {big}'),
            ('UInt16', elem),
        ])
        files[f'ScalarArrayTest/{name}.lean'] = t
    names = [t[0] for t in types]
    root = (ROOT / 'ScalarArray.lean').read_text()
    head = root.split('public import ScalarArray.')[0]
    doc = '\n/-!' + root.split('\n/-!', 1)[1]
    files['ScalarArray.lean'] = (
        head + ''.join(f'public import ScalarArray.{n}\n' for n in names)
        + 'public import ScalarArray.Conversions\n' + doc)
    test_root = (ROOT / 'ScalarArrayTest.lean').read_text()
    files['ScalarArrayTest.lean'] = (
        test_root.split('import ')[0]
        + ''.join(f'import ScalarArrayTest.{n}\n' for n in names)
        + 'import ScalarArrayTest.Float\n'
        + 'import ScalarArrayTest.Conversions\n')
    return files


def main():
    check = sys.argv[1:] == ['--check']
    stale = []
    for path, contents in generate().items():
        file = ROOT / path
        if not file.exists() or file.read_text() != contents:
            stale.append(path)
            if not check:
                file.write_text(contents)
    if check and stale:
        print('Out of date; run scripts/generate.py:', *stale, sep='\n  ')
        sys.exit(1)


if __name__ == '__main__':
    main()
