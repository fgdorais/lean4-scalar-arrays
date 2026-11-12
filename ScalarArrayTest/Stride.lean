/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray.Stride
import ScalarArrayTest.Util
meta import ScalarArray.Stride
meta import ScalarArrayTest.Util

open ScalarArray

/-!
Tests for `ScalarArray.Stride`, `ScalarArray.iterRange` and `ScalarArray.iterRangeRev`.
-/

/-! `iterRange` and `iterRangeRev` -/

-- The steps from `lo` up to `hi - 1`, in this order.
#guard iterRange (fun i (l : List Nat) => i :: l) 2 5 [] == [4, 3, 2]
#guard iterRangeRev (fun i (l : List Nat) => i :: l) 2 5 [] == [2, 3, 4]

-- An empty range.
#guard iterRange (fun i (l : List Nat) => i :: l) 5 2 [] == []
#guard iterRangeRev (fun i (l : List Nat) => i :: l) 5 5 [] == []

/-! `Stride` -/

#guard (Stride.idx ⟨3, 4⟩ 5) == 23
#guard (Stride.shift ⟨3, 4⟩ 2) == ⟨11, 4⟩

-- The last of `n` steps must be in bounds.
#guard decide (Stride.Fits ⟨1, 2⟩ 3 6)
#guard !decide (Stride.Fits ⟨1, 2⟩ 3 5)

-- A zero stride fits only one step, and no step always fits.
#guard decide (Stride.Fits ⟨7, 0⟩ 1 8)
#guard !decide (Stride.Fits ⟨7, 0⟩ 2 8)
#guard decide (Stride.Fits ⟨100, 0⟩ 0 8)

example (s : Stride) (k i : Nat) : (s.shift k).idx i = s.idx (k + i) := by simp

example (s : Stride) (h : s.Fits 4 10) : s.Fits 2 10 := h.mono (by decide)
