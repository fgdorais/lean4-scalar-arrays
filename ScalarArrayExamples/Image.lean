/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ScalarArray
import ScalarArray.Notation
meta import ScalarArray

/-!
# Grayscale images on `UInt8Array`

An 8-bit grayscale image is a `UInt8Array` of pixels, one byte each, stored row by row. This
example shows the main ways to work on such an array:

* `inplace` loops for pixel-wise updates, such as brightening with clamping;
* `Std.Iterators` combinators, which build a new array;
* folds, here for a histogram kept in a second array;
* writable slices for work on one row at a time, such as a mirror image or a blur;
* the free conversion to core's `ByteArray`, here to write the image as a PGM file.
-/

open ScalarArray

namespace Image

/-- A grayscale image: `width` pixels per row, and `pixels.size / width` rows. -/
structure Image where
  /-- The number of pixels in each row. -/
  width : Nat
  /-- The pixels, row by row. -/
  pixels : UInt8Array
deriving BEq

/-- The rows of the image, as lists, to show it. -/
def Image.rows (img : Image) : List (List UInt8) :=
  (List.range (img.pixels.size / img.width)).map fun r =>
    img.pixels[r * img.width...(r + 1) * img.width].toList

/-- A horizontal gradient, from black on the left to `max` on the right. -/
def gradient (width height : Nat) (max : UInt8) : Image where
  width
  pixels := UInt8Array.ofFn (n := width * height) fun i =>
    (i.val % width * max.toNat / (width - 1)).toUInt8

/-- A small test image. -/
def test : Image := gradient 4 3 240

#guard test.rows == [[0, 80, 160, 240], [0, 80, 160, 240], [0, 80, 160, 240]]

/-! ## Pixel-wise updates -/

/--
Brightens every pixel by `d`, clamping at white.

The `inplace` loop reads and writes the pixels in place, with `USize` indices, and the index bounds
are proved from the loop's range, `0...a.usize`.
-/
def brighten (d : UInt8) (img : Image) : Image :=
  { img with pixels := (inplace img.pixels do
      for j in 0...img.pixels.usize do
        let x := img.pixels[j]
        img.pixels[j] := if x > 255 - d then 255 else x + d) }

#guard (brighten 50 test).rows.head! == [50, 130, 210, 255]

/--
The negative image.

An iterator combinator makes a new array, which is simplest when the old one is still needed.
-/
def invert (img : Image) : Image :=
  { img with pixels := (img.pixels.iter.map (255 - ·)).toUInt8Array }

#guard (invert test).rows.head! == [255, 175, 95, 15]

/-! ## Statistics -/

/--
The number of pixels of each of the 256 gray levels.

The counts are in a `UInt32Array` that the fold keeps unshared, so each `set!` updates it in place.
-/
def histogram (img : Image) : UInt32Array :=
  img.pixels.foldl (init := UInt32Array.replicate 256 0) fun h x =>
    h.set! x.toNat (h[x.toNat]! + 1)

#guard (histogram test)[80]! == 3
#guard (histogram test).foldl (· + ·) 0 == 12

/-- The mean gray level, rounded down. -/
def mean (img : Image) : Nat :=
  img.pixels.foldl (fun s x => s + x.toNat) 0 / img.pixels.size

#guard mean test == 120

/-- Turns every pixel at least `t` white and the others black. -/
def threshold (t : UInt8) (img : Image) : Image :=
  { img with pixels := (img.pixels.iter.map fun x => if x ≥ t then 255 else 0).toUInt8Array }

#guard (threshold (mean test).toUInt8 test).rows.head! == [0, 0, 255, 255]

/-! ## Rows

A row is the slice `pixels[r * width...(r + 1) * width]`. Taking it from an array that is not used
afterwards and writing to it updates the array in place, and `Slice.array` gives it back.
-/

/-- The mirror image, reversing each row in place. -/
def mirror (img : Image) : Image := Id.run do
  let mut px := img.pixels
  for r in 0...px.size / img.width do
    px := px[r * img.width...(r + 1) * img.width].reverse.array
  return { img with pixels := px }

#guard (mirror test).rows.head! == [240, 160, 80, 0]
#guard mirror (mirror test) == test

/--
Blurs a row, replacing each pixel but the first and last with the mean of itself and its two
neighbors.

The `inplace` loop works on the slice. At step `j` it reads the pixel `s[j]` and writes the blurred
pixel `s[j - 1]`, which the earlier steps have not touched. The loop variables `l` and `m` hold the
old values of the two pixels before `s[j]`, since `s[j - 2]` has already been overwritten. The sums
are in `UInt16`, so that nothing overflows. The hypothesis `h` proves the bounds of `s[0]` and
`s[1]`, and the loop range those of `s[j]` and `s[j - 1]`.
-/
def blurRow (s : UInt8Array.Slice) (h : 2 ≤ s.size) : UInt8Array.Slice :=
  inplace s do
    for j in 2...s.usize with (l := s[0]) (m := s[1]) do
      let r := s[j]
      s[j - 1] := ((l.toUInt16 + m.toUInt16 + r.toUInt16) / 3).toUInt8
      l := m
      m := r

/-- Blurs every row of the image. -/
def blur (img : Image) : Image := Id.run do
  let mut px := img.pixels
  for r in 0...px.size / img.width do
    let s := px[r * img.width...(r + 1) * img.width]
    if h : 2 ≤ s.size then
      px := (blurRow s h).array
  return { img with pixels := px }

#guard (blur (threshold 100 test)).rows.head! == [0, 85, 170, 255]

/-! ## Saving

`UInt8Array.toByteArray` converts to core's `ByteArray` without copying, so the pixels can go to any
function that takes bytes, such as `IO.FS.writeBinFile`. Here they make a binary PGM image, a short
text header followed by the pixels.
-/

/-- The image in the binary PGM format. -/
def toPGM (img : Image) : ByteArray :=
  s!"P5\n{img.width} {img.pixels.size / img.width}\n255\n".toUTF8 ++ img.pixels.toByteArray

#guard (toPGM test).size == "P5\n4 3\n255\n".length + 12
#guard (toPGM test).extract 11 15 == ByteArray.mk #[0, 80, 160, 240]

/-- Writes the image to a PGM file. -/
def save (img : Image) (path : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile path (toPGM img)

end Image
