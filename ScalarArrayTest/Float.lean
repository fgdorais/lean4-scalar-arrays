/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ScalarArray.Float32
import ScalarArray.Float64

open ScalarArray

/-! Special floating-point values must round-trip bit for bit. -/

def float32Specials : Array Float32 :=
  #[0.0, -0.0, 0.0 / 0.0, -(0.0 / 0.0), 1.0 / 0.0, -1.0 / 0.0, 1.0e-45, 3.4028235e38, 0.1]

def float64Specials : Array Float :=
  #[0.0, -0.0, 0.0 / 0.0, -(0.0 / 0.0), 1.0 / 0.0, -1.0 / 0.0, 5.0e-324, 1.7976931348623157e308,
    0.1]

#guard (Float32Array.mk float32Specials).data.map Float32.toBits ==
  float32Specials.map Float32.toBits
#guard (Float64Array.mk float64Specials).data.map Float.toBits == float64Specials.map Float.toBits

#guard Id.run do
  let mut a := Float32Array.emptyWithCapacity 1
  for x in float32Specials do
    a := a.push x
  return a.data.map Float32.toBits == float32Specials.map Float32.toBits

#guard Id.run do
  let mut a := Float64Array.mk (Array.replicate float64Specials.size 1.0)
  for h : i in [0:float64Specials.size] do
    a := a.set! i float64Specials[i]
  return a.data.map Float.toBits == float64Specials.map Float.toBits

-- `0.1` is not exactly representable, so a `Float32Array` must round it to single precision.
#guard (Float32Array.mk #[0.1])[0]!.toFloat != (0.1 : Float)
#guard (Float32Array.mk #[0.1])[0]! == (0.1 : Float32)

/-! `==` on float arrays compares elements with floating-point `==`, like `Array Float`. -/

#guard Float32Array.mk #[0.0 / 0.0] != Float32Array.mk #[0.0 / 0.0]
#guard Float64Array.mk #[0.0 / 0.0] != Float64Array.mk #[0.0 / 0.0]
#guard Float32Array.mk #[0.0] == Float32Array.mk #[-0.0]
#guard Float64Array.mk #[0.0] == Float64Array.mk #[-0.0]
#guard !(Float32Array.mk #[0.0 / 0.0]).contains (0.0 / 0.0)
#guard !(Float64Array.mk #[0.0 / 0.0]).contains (0.0 / 0.0)
#guard (Float64Array.mk #[1.0, 2.0] == Float64Array.mk #[1.0, 2.0]) ==
  (#[(1.0 : Float), 2.0] == #[1.0, 2.0])
