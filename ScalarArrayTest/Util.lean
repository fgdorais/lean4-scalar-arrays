/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all ScalarArray.Internal

/-!
Helpers that inspect the runtime representation of a scalar array. Their Lean definitions are
placeholders; only the compiled implementations are meaningful, which is what `#guard` runs.
-/

namespace ScalarArrayTest

private unsafe def rawElemSizeImpl (a : α) : UInt32 := (unsafeCast a : ScalarArray).elemSize

/-- The element size recorded in the runtime header of a scalar array. -/
@[implemented_by rawElemSizeImpl]
public def rawElemSize (_ : α) : UInt32 := 0

private unsafe def rawCapacityImpl (a : α) : Nat := (unsafeCast a : ScalarArray).capacity.toNat

/-- The capacity recorded in the runtime header of a scalar array. -/
@[implemented_by rawCapacityImpl]
public def rawCapacity (_ : α) : Nat := 0

end ScalarArrayTest
