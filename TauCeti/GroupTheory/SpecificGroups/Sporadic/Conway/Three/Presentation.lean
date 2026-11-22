/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.BitField
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Conway.Three.Basic

/-!
# Djoković's presentation of the third Conway group holds in the ATLAS model

The presentation selected for `Co₃` is Djoković's presentation (13.1) on seven involutions
`a, b, c, d, e, f, g` with twenty-four relators (`TauCeti.Sporadic.co3Presentation`). It is not on
the ATLAS standard generators: the file generators `Co3.a` and `Co3.b` of the degree-276 model
have orders `3` and `4`. This file gives seven involutions `Co3.imageA`, …, `Co3.imageG` of the
276 points that satisfy all twenty-four relators and generate exactly the model `Co3`, and
deduces that the presented group `SporadicName.Co3.Group` maps onto the model. In particular
the presented group is nontrivial.

Each image is given by its table of forward images, so that the relators compute directly. Five
of them are also written as words in the file generators (`Co3.imageA_eq`, `Co3.imageB_eq`,
`Co3.imageC_eq`, `Co3.imageD_eq`, `Co3.imageG_eq`), and the other two are determined by these
through the relators `e(abc)³` and `f(ag)³` (`Co3.imageE_eq`, `Co3.imageF_eq`); this puts all seven
in the model. Conversely `Co3.a_eq` and `Co3.b_eq` write the two file generators as words in the
seven images, so the images generate the whole model.

The seven permutations were found by a computer search in the model, along the lines of the
comparison recorded in the module `TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three`:
`a`, `b`, `c`, `e`, `f` and `g` among the involutions centralizing an involution with 36 fixed
points, and `d` among the involutions commuting with `a`, `b` and `g`. Nothing about that search
is used: the relators and both directions of generation are checked here. Products follow
Mathlib's convention `(σ * τ) x = σ (τ x)`. Because the seven images are involutions, reading a
relator in the other direction gives the inverse permutation, so the relators hold in either
convention.

No order of the model or of the presented group is asserted here, and the surjection is not
shown to be injective.

The lift and range arguments use `GroupPresentation.homEquiv` and
`GroupPresentation.exists_surjective_of_closure_range_eq`.

## Main declarations

* `TauCeti.Sporadic.Co3.imageA`, …, `TauCeti.Sporadic.Co3.imageG`: the images of the seven
  generators, with `TauCeti.Sporadic.Co3.presentationImage` the resulting assignment.
* `TauCeti.Sporadic.Co3.lift_presentationImage_toFreeGroup_eq_one`: the twenty-four relators hold.
* `TauCeti.Sporadic.Co3.closure_range_presentationImage`: the images generate the model.
* `TauCeti.Sporadic.Co3.presentationHom`, `TauCeti.Sporadic.Co3.range_presentationHom`: the
  homomorphism from the presented group and its range.
* `TauCeti.Sporadic.exists_surjective_Co3`: the presented group maps onto the model.

## References

* D. Ž. Djoković, *Presentations of some finite simple groups*, J. Austral. Math. Soc. Ser. A
  **45** (1988), 143--168, presentation (13.1), p. 162,
  <https://doi.org/10.1017/S1446788700030068>.
* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `Co3G1-p276B0`, <https://brauer.maths.qmul.ac.uk/Atlas/v3/>.
-/

public section

namespace TauCeti.Sporadic

namespace Co3

/-! ### Images of Djoković's generators -/

/- Each image is given by the table of its images: 23 rows of 12 entries, entry `i` (counted from
zero along the rows) being the image of the point `i`. The table is packed into the natural number
having these entries as its digits in base `512`, so that the image of `i` is field `i` of width
`9` of that number. The kernel reads such a field by binary arithmetic in one step, whereas a
lookup in a list or an array costs one reduction for every position passed. The bodies are
exposed so that importing modules can compute with the seven permutations. -/

/-- The image of the generator `a` of presentation (13.1), of index zero.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageA : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[0, 1, 73, 159, 55, 33, 38, 188, 118, 260, 124, 107],
     [61, 244, 70, 15, 143, 17, 71, 84, 67, 35, 195, 53],
     [39, 157, 43, 258, 246, 29, 132, 31, 129, 5, 52, 21],
     [98, 257, 6, 24, 243, 175, 42, 26, 64, 149, 144, 54],
     [189, 169, 100, 51, 34, 23, 47, 4, 233, 123, 252, 59],
     [198, 12, 164, 268, 44, 168, 227, 20, 162, 171, 14, 18],
     [155, 2, 74, 212, 76, 111, 102, 158, 80, 240, 82, 104],
     [19, 253, 86, 179, 128, 250, 90, 215, 110, 152, 139, 112],
     [209, 134, 36, 181, 50, 101, 78, 103, 83, 261, 192, 11],
     [270, 208, 92, 77, 95, 130, 176, 138, 249, 272, 8, 242],
     [120, 267, 254, 57, 10, 150, 126, 205, 88, 32, 113, 216],
     [30, 220, 97, 135, 247, 275, 115, 94, 165, 194, 201, 16],
     [46, 151, 259, 147, 148, 45, 125, 145, 93, 203, 154, 72],
     [224, 25, 79, 3, 211, 161, 68, 163, 62, 140, 239, 190],
     [65, 49, 202, 69, 228, 255, 193, 41, 114, 217, 178, 87],
     [269, 99, 199, 262, 207, 229, 221, 236, 7, 48, 167, 235],
     [106, 174, 141, 22, 264, 238, 60, 182, 248, 142, 170, 153],
     [204, 127, 206, 184, 109, 96, 214, 160, 75, 234, 210, 91],
     [131, 177, 271, 219, 133, 186, 251, 226, 156, 225, 223, 66],
     [172, 185, 230, 274, 232, 56, 213, 191, 187, 237, 197, 166],
     [81, 263, 119, 40, 13, 245, 28, 136, 200, 116, 89, 222],
     [58, 85, 122, 173, 256, 37, 27, 146, 9, 105, 183, 241],
     [196, 273, 266, 121, 63, 180, 108, 218, 117, 265, 231, 137]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-- The image of the generator `b` of presentation (13.1), of index one.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageB : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[34, 234, 32, 214, 170, 46, 206, 175, 223, 271, 138, 11],
     [77, 229, 196, 15, 16, 242, 53, 144, 81, 116, 97, 66],
     [194, 25, 134, 102, 124, 107, 249, 250, 2, 84, 0, 132],
     [36, 215, 38, 139, 219, 83, 98, 195, 154, 45, 5, 114],
     [111, 91, 248, 235, 52, 18, 233, 275, 176, 62, 58, 79],
     [160, 189, 57, 63, 64, 129, 23, 262, 182, 193, 72, 227],
     [70, 168, 216, 212, 252, 12, 231, 59, 157, 20, 272, 41],
     [33, 255, 86, 150, 237, 89, 90, 49, 110, 125, 141, 127],
     [261, 22, 42, 239, 201, 207, 27, 167, 188, 156, 171, 29],
     [166, 123, 92, 48, 197, 185, 47, 246, 21, 117, 228, 119],
     [120, 256, 145, 109, 28, 93, 126, 95, 128, 65, 244, 131],
     [35, 133, 26, 247, 136, 202, 10, 39, 199, 94, 200, 163],
     [19, 122, 253, 147, 149, 148, 87, 153, 179, 151, 44, 264],
     [105, 80, 158, 269, 60, 161, 165, 143, 208, 162, 108, 103],
     [73, 257, 4, 106, 226, 259, 192, 7, 56, 217, 265, 152],
     [210, 270, 68, 240, 184, 113, 260, 211, 104, 61, 190, 191],
     [174, 69, 24, 43, 14, 112, 236, 140, 142, 100, 137, 254],
     [241, 238, 6, 101, 164, 224, 180, 187, 75, 213, 3, 37],
     [74, 177, 221, 40, 225, 218, 245, 8, 209, 220, 172, 71],
     [118, 13, 230, 78, 232, 54, 1, 51, 198, 88, 205, 99],
     [183, 204, 17, 243, 130, 222, 115, 135, 50, 30, 31, 251],
     [76, 146, 203, 85, 121, 169, 274, 173, 186, 96, 67, 263],
     [155, 178, 268, 267, 266, 159, 181, 9, 82, 273, 258, 55]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-- The image of the generator `c` of presentation (13.1), of index two.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageC : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[1, 0, 73, 52, 18, 175, 160, 254, 118, 208, 259, 16],
     [179, 157, 270, 237, 11, 51, 4, 19, 115, 35, 213, 202],
     [153, 244, 180, 258, 32, 29, 45, 31, 28, 41, 159, 21],
     [98, 123, 211, 203, 236, 33, 120, 269, 113, 30, 139, 227],
     [125, 199, 229, 17, 3, 170, 66, 71, 193, 257, 142, 80],
     [60, 87, 165, 63, 130, 85, 54, 138, 162, 176, 108, 55],
     [111, 2, 204, 274, 154, 155, 102, 248, 59, 255, 90, 83],
     [84, 65, 256, 61, 273, 184, 82, 271, 226, 166, 144, 112],
     [167, 119, 36, 264, 185, 101, 78, 103, 104, 105, 275, 143],
     [70, 260, 223, 72, 95, 44, 171, 20, 220, 121, 8, 97],
     [42, 117, 188, 37, 146, 48, 126, 127, 265, 246, 64, 131],
     [149, 249, 242, 135, 136, 192, 67, 46, 164, 141, 58, 107],
     [94, 145, 124, 147, 225, 132, 189, 151, 239, 24, 76, 77],
     [222, 13, 200, 34, 6, 178, 68, 163, 140, 62, 93, 96],
     [253, 182, 53, 114, 228, 240, 233, 5, 69, 217, 161, 12],
     [26, 196, 169, 262, 89, 100, 221, 243, 122, 150, 209, 214],
     [137, 56, 194, 234, 181, 197, 198, 49, 158, 252, 23, 39],
     [74, 205, 206, 250, 9, 190, 235, 38, 231, 22, 191, 218],
     [216, 177, 215, 219, 116, 186, 156, 110, 251, 148, 92, 47],
     [172, 50, 232, 212, 230, 174, 195, 210, 40, 15, 238, 152],
     [173, 241, 134, 187, 25, 245, 129, 247, 79, 133, 207, 224],
     [201, 168, 7, 81, 86, 57, 27, 10, 109, 261, 183, 263],
     [99, 128, 266, 272, 268, 43, 14, 91, 267, 88, 75, 106]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-- The image of the generator `d` of presentation (13.1), of index three.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageD : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[42, 178, 73, 159, 12, 19, 6, 7, 67, 192, 246, 131],
     [4, 197, 165, 15, 16, 17, 257, 5, 118, 94, 96, 49],
     [30, 25, 156, 258, 124, 74, 24, 59, 168, 84, 98, 139],
     [52, 71, 38, 132, 149, 41, 0, 224, 44, 243, 144, 56],
     [137, 23, 100, 245, 36, 169, 233, 61, 47, 179, 184, 31],
     [122, 55, 152, 63, 64, 129, 91, 8, 264, 221, 140, 37],
     [199, 2, 29, 212, 101, 170, 231, 250, 80, 228, 82, 83],
     [33, 259, 86, 123, 167, 158, 126, 66, 110, 164, 21, 185],
     [22, 261, 34, 181, 50, 76, 274, 237, 104, 134, 260, 216],
     [166, 150, 92, 202, 229, 127, 176, 138, 141, 117, 20, 119],
     [161, 247, 60, 87, 28, 208, 90, 113, 190, 65, 205, 11],
     [39, 133, 105, 256, 267, 48, 115, 35, 70, 116, 200, 143],
     [46, 160, 253, 230, 219, 40, 109, 211, 62, 187, 154, 182],
     [26, 157, 89, 3, 145, 120, 196, 163, 93, 14, 108, 88],
     [32, 53, 77, 186, 240, 255, 271, 175, 114, 217, 1, 57],
     [210, 99, 155, 226, 58, 95, 171, 153, 188, 275, 128, 251],
     [9, 218, 249, 209, 162, 13, 254, 72, 142, 248, 111, 236],
     [204, 130, 206, 252, 125, 195, 180, 151, 75, 273, 269, 227],
     [107, 177, 193, 148, 220, 69, 235, 262, 43, 225, 183, 215],
     [81, 112, 147, 78, 232, 54, 265, 222, 203, 103, 244, 270],
     [172, 241, 242, 45, 238, 51, 10, 121, 201, 194, 79, 191],
     [207, 146, 198, 173, 135, 18, 27, 85, 106, 97, 223, 263],
     [68, 234, 266, 136, 268, 214, 239, 174, 272, 213, 102, 189]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-- The image of the generator `e` of presentation (13.1), of index four.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageE : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[17, 51, 262, 97, 69, 203, 40, 139, 172, 140, 124, 11],
     [264, 201, 189, 161, 16, 0, 176, 145, 129, 21, 214, 233],
     [41, 58, 269, 102, 138, 29, 30, 31, 67, 153, 242, 35],
     [36, 257, 243, 175, 6, 24, 42, 180, 79, 45, 254, 227],
     [70, 91, 185, 1, 119, 56, 66, 171, 53, 123, 25, 154],
     [198, 196, 109, 63, 158, 81, 54, 32, 221, 4, 48, 114],
     [111, 183, 204, 212, 80, 155, 258, 44, 76, 65, 256, 194],
     [151, 255, 90, 181, 265, 89, 86, 49, 110, 166, 188, 112],
     [156, 3, 98, 179, 229, 101, 27, 245, 141, 261, 275, 107],
     [125, 62, 92, 72, 95, 248, 71, 246, 116, 267, 228, 52],
     [120, 272, 144, 57, 10, 108, 126, 197, 273, 20, 200, 263],
     [132, 133, 159, 135, 136, 192, 28, 7, 9, 104, 244, 143],
     [122, 19, 259, 147, 148, 149, 270, 84, 239, 33, 59, 77],
     [96, 252, 64, 134, 236, 15, 186, 163, 208, 260, 93, 222],
     [240, 215, 193, 55, 8, 253, 202, 39, 18, 217, 237, 99],
     [43, 87, 218, 73, 184, 50, 162, 211, 94, 14, 251, 213],
     [137, 170, 83, 210, 61, 127, 60, 271, 130, 13, 174, 5],
     [74, 238, 219, 207, 164, 224, 195, 187, 75, 191, 22, 169],
     [241, 177, 182, 206, 220, 68, 167, 226, 209, 225, 223, 47],
     [118, 100, 232, 274, 230, 23, 235, 234, 160, 178, 205, 152],
     [168, 216, 34, 38, 142, 103, 115, 247, 113, 249, 250, 190],
     [157, 173, 46, 85, 82, 37, 78, 146, 165, 105, 2, 131],
     [12, 88, 266, 117, 268, 26, 150, 199, 121, 128, 231, 106]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-- The image of the generator `f` of presentation (13.1), of index five.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageF : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[0, 51, 73, 138, 153, 171, 41, 44, 152, 13, 105, 11],
     [187, 9, 200, 206, 143, 17, 87, 186, 164, 89, 193, 49],
     [40, 119, 155, 100, 97, 101, 149, 147, 109, 69, 252, 250],
     [184, 57, 175, 243, 24, 6, 42, 72, 7, 132, 255, 227],
     [113, 23, 258, 1, 58, 169, 66, 203, 215, 37, 52, 230],
     [146, 236, 67, 220, 188, 125, 54, 62, 151, 33, 248, 179],
     [43, 2, 76, 177, 74, 269, 185, 139, 204, 108, 86, 117],
     [221, 254, 82, 18, 273, 21, 256, 233, 92, 118, 158, 231],
     [218, 28, 207, 114, 27, 29, 229, 237, 272, 10, 238, 107],
     [81, 32, 110, 180, 274, 48, 99, 159, 247, 83, 93, 25],
     [148, 141, 253, 257, 261, 65, 135, 137, 265, 208, 189, 131],
     [45, 268, 246, 126, 249, 127, 3, 79, 201, 121, 165, 16],
     [173, 162, 60, 31, 120, 30, 168, 68, 8, 4, 232, 26],
     [182, 242, 94, 115, 196, 219, 145, 266, 20, 142, 228, 213],
     [150, 53, 214, 5, 239, 144, 195, 38, 181, 75, 245, 71],
     [111, 176, 156, 262, 36, 78, 19, 12, 64, 130, 234, 222],
     [197, 22, 267, 174, 160, 192, 259, 224, 14, 140, 210, 55],
     [80, 275, 15, 98, 129, 271, 202, 264, 217, 167, 170, 56],
     [216, 212, 96, 161, 63, 84, 191, 226, 199, 225, 223, 47],
     [166, 102, 59, 95, 154, 91, 190, 251, 61, 103, 106, 172],
     [270, 241, 157, 39, 260, 178, 134, 116, 70, 136, 35, 235],
     [34, 122, 85, 46, 90, 123, 50, 198, 244, 124, 183, 263],
     [211, 128, 163, 194, 133, 77, 240, 209, 104, 88, 112, 205]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-- The image of the generator `g` of presentation (13.1), of index six.
Entry `i` of the table is the image of the point `i`. -/
@[expose] def imageG : Equiv.Perm (Fin 276) :=
  let t : ℕ := Nat.ofDigits 512
    [[216, 51, 53, 68, 105, 55, 41, 44, 114, 201, 153, 11],
     [134, 140, 122, 117, 133, 241, 32, 61, 93, 135, 218, 23],
     [40, 119, 77, 209, 84, 98, 149, 132, 18, 124, 74, 250],
     [184, 240, 232, 59, 24, 6, 107, 274, 7, 147, 275, 223],
     [127, 49, 174, 1, 58, 2, 54, 5, 262, 270, 52, 39],
     [165, 19, 181, 63, 86, 108, 66, 176, 3, 261, 197, 172],
     [112, 169, 34, 217, 252, 26, 210, 139, 157, 125, 188, 206],
     [28, 238, 64, 109, 167, 126, 158, 91, 110, 20, 256, 111],
     [193, 221, 29, 152, 271, 207, 224, 237, 272, 4, 254, 42],
     [65, 87, 92, 95, 72, 137, 8, 211, 247, 15, 164, 25],
     [136, 141, 14, 150, 33, 81, 89, 48, 191, 166, 173, 131],
     [31, 16, 12, 21, 120, 113, 151, 79, 13, 121, 146, 268],
     [189, 196, 142, 45, 249, 30, 123, 138, 99, 10, 175, 269],
     [170, 80, 90, 264, 162, 267, 160, 266, 118, 60, 129, 88],
     [257, 73, 156, 203, 71, 130, 50, 154, 67, 212, 245, 239],
     [231, 62, 214, 215, 36, 202, 236, 246, 82, 144, 251, 128],
     [248, 96, 219, 258, 145, 70, 260, 229, 253, 9, 185, 171],
     [242, 255, 83, 101, 228, 27, 78, 115, 177, 273, 182, 183],
     [0, 75, 22, 194, 220, 97, 265, 47, 102, 225, 227, 226],
     [208, 199, 243, 180, 38, 233, 235, 234, 186, 103, 85, 179],
     [37, 17, 204, 230, 259, 178, 187, 116, 192, 148, 35, 190],
     [76, 200, 106, 205, 94, 168, 195, 244, 198, 69, 56, 263],
     [159, 222, 163, 161, 143, 155, 57, 100, 104, 213, 43, 46]].flatten
  Function.Involutive.toPerm (fun i : Fin 276 ↦ Fin.ofNat 276 (Nat.bitField 9 t i))
    (by unfold Function.Involutive; decide +kernel)

/-! ### The images as words in the file generators, and conversely -/

/-- The image of the generator `a` as a word in the file generators. -/
theorem imageA_eq :
    imageA = a * b⁻¹ * a * b * a * b⁻¹ * a * b * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a * b * b * a⁻¹ * b * a *
      b * a⁻¹ * b * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ := by
  decide +kernel

/-- The image of the generator `b` as a word in the file generators. -/
theorem imageB_eq :
    imageB = a * b⁻¹ * a⁻¹ * b * a⁻¹ * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a * b *
      a⁻¹ * b * a * b⁻¹ * a⁻¹ * b * a * b * b * a⁻¹ * b⁻¹ * a * b * a * b * b * a⁻¹ := by
  decide +kernel

/-- The image of the generator `c` as a word in the file generators. -/
theorem imageC_eq :
    imageC = b * a * b * a * b * a * b * b * a * b * a * b * a⁻¹ * b * b * a * b⁻¹ * a⁻¹ * b⁻¹ *
      a⁻¹ * b * b * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ := by
  decide +kernel

/-- The image of the generator `d` as a word in the file generators. -/
theorem imageD_eq :
    imageD = b⁻¹ * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b⁻¹ * a * b⁻¹ * a * b⁻¹ * a * b *
      b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a * b * a * b * a * b⁻¹ * a⁻¹ * b := by
  decide +kernel

/-- The image of the generator `g` as a word in the file generators. -/
theorem imageG_eq :
    imageG = b * a⁻¹ * b * a * b * a⁻¹ * b * b * a⁻¹ * b⁻¹ * a * b⁻¹ * a⁻¹ * b * b * a * b * a⁻¹ *
      b * a⁻¹ * b⁻¹ * a * b⁻¹ * a⁻¹ * b * a * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b := by
  decide +kernel

/-- The image of the generator `e` in terms of the images of `a`, `b` and `c`: the relator
`e(abc)³` of presentation (13.1), solved for the involution `e`. -/
theorem imageE_eq : imageE = (imageA * imageB * imageC) ^ 3 := by
  decide +kernel

/-- The image of the generator `f` in terms of the images of `a` and `g`: the relator `f(ag)³` of
presentation (13.1), solved for the involution `f`. -/
theorem imageF_eq : imageF = (imageA * imageG) ^ 3 := by
  decide +kernel

/-- The first file generator as a word in the seven images. -/
theorem a_eq :
    a = imageB * imageC * imageG * imageB * imageF * imageC * imageA * imageG * imageD * imageE *
      imageC * imageD * imageB * imageF * imageB * imageC * imageG * imageA * imageB * imageC *
      imageG * imageD * imageC * imageG * imageD * imageC * imageA * imageB := by
  decide +kernel

/-- The second file generator as a word in the seven images. -/
theorem b_eq :
    b = imageC * imageG * imageD * imageC * imageA * imageB * imageF * imageC * imageA * imageG *
      imageC * imageB * imageA * imageF * imageE * imageD * imageC * imageB * imageF * imageD *
      imageB * imageC * imageA * imageG * imageB * imageA := by
  decide +kernel

/-! ### The assignment and the relators -/

/-- The seven-generator assignment for presentation (13.1): the generators of index `0`, …, `6`
go to `imageA`, …, `imageG`. -/
def presentationImage (i : Fin SporadicName.Co3.presentation.generatorCount) :
    Equiv.Perm (Fin 276) :=
  [imageA, imageB, imageC, imageD, imageE, imageF, imageG].getD i 1

/-- The explicit assignment underlying `presentationImage`. -/
@[simp]
theorem presentationImage_apply (i : Fin SporadicName.Co3.presentation.generatorCount) :
    presentationImage i = [imageA, imageB, imageC, imageD, imageE, imageF, imageG].getD i 1 :=
  (rfl)

/-- The assignment has precisely the seven chosen images as its values. -/
theorem range_presentationImage :
    Set.range presentationImage =
      {imageA, imageB, imageC, imageD, imageE, imageF, imageG} := by
  have h : SporadicName.Co3.presentation.generatorCount = 7 := by simp
  ext σ
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hk' : k < 7 := h ▸ hk
    interval_cases k <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨⟨0, by omega⟩, rfl⟩, ⟨⟨1, by omega⟩, rfl⟩, ⟨⟨2, by omega⟩, rfl⟩,
      ⟨⟨3, by omega⟩, rfl⟩, ⟨⟨4, by omega⟩, rfl⟩, ⟨⟨5, by omega⟩, rfl⟩, ⟨⟨6, by omega⟩, rfl⟩]

/- The relators in the four blocks of presentation (13.1): the seven generators are involutions,
seven pairs of them commute, three pairs have a product of order three, and seven mixed words
are trivial. Separate closed checks keep each computation small. -/
private theorem relators_sq :
    imageA ^ 2 = 1 ∧ imageB ^ 2 = 1 ∧ imageC ^ 2 = 1 ∧ imageD ^ 2 = 1 ∧ imageE ^ 2 = 1 ∧
      imageF ^ 2 = 1 ∧ imageG ^ 2 = 1 := by
  decide +kernel

private theorem relators_commute :
    (imageA * imageC) ^ 2 = 1 ∧ (imageA * imageD) ^ 2 = 1 ∧ (imageA * imageE) ^ 2 = 1 ∧
      (imageB * imageD) ^ 2 = 1 ∧ (imageC * imageE) ^ 2 = 1 ∧ (imageD * imageG) ^ 2 = 1 ∧
      (imageE * imageG) ^ 2 = 1 := by
  decide +kernel

private theorem relators_cube :
    (imageA * imageB) ^ 3 = 1 ∧ (imageC * imageD) ^ 3 = 1 ∧ (imageD * imageE) ^ 3 = 1 := by
  decide +kernel

private theorem relators_mixed :
    imageF * (imageA * imageG) ^ 3 = 1 ∧ imageG * (imageB * imageF) ^ 3 = 1 ∧
      (imageC * imageF * imageG) ^ 3 = 1 ∧ imageE * (imageA * imageB * imageC) ^ 3 = 1 ∧
      imageE * (imageA * imageC * imageG) ^ 4 = 1 ∧
      (imageB * imageC * imageF * imageC * imageF) ^ 3 = 1 ∧
      imageE * (imageA * imageB * imageC * imageF) ^ 7 = 1 := by
  decide +kernel

/-- All twenty-four transcribed relators of presentation (13.1) hold at the chosen images. -/
theorem lift_presentationImage_toFreeGroup_eq_one :
    ∀ t ∈ SporadicName.Co3.presentation.transcribed,
      FreeGroup.lift presentationImage t.toFreeGroup = 1 := by
  -- Abstract the presentation first, because it occurs in the generator index type.
  suffices key : ∀ P : GroupPresentation, P = co3Presentation → ∀ t ∈ P.transcribed,
      FreeGroup.lift (fun i : Fin P.generatorCount ↦
        [imageA, imageB, imageC, imageD, imageE, imageF, imageG].getD i 1) t.toFreeGroup = 1 from
    key _ SporadicName.presentation_Co3
  rintro P rfl
  obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := relators_sq
  obtain ⟨hAC, hAD, hAE, hBD, hCE, hDG, hEG⟩ := relators_commute
  obtain ⟨hAB, hCD, hDE⟩ := relators_cube
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := relators_mixed
  simp only [co3Presentation_transcribed, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Relator.lift_toFreeGroup, Relator.eval_mul, Relator.eval_pow,
    Relator.eval_gen, List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨hA, hB, hC, hD, hE, hF, hG, hAC, hAD, hAE, hBD, hCE, hDG, hEG, hAB, hCD, hDE,
    h1, h2, h3, h4, h5, h6, h7⟩

/-! ### Generation and the surjection -/

/-- The seven images generate exactly the ATLAS model. -/
theorem closure_range_presentationImage :
    Subgroup.closure (Set.range presentationImage) = Co3 := by
  rw [range_presentationImage, Co3_def]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    have ha : a ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
    -- The five images given as words in `a` and `b`; a word is peeled from the right.
    have hw : imageA ∈ Subgroup.closure {a, b} ∧ imageB ∈ Subgroup.closure {a, b} ∧
        imageC ∈ Subgroup.closure {a, b} ∧ imageD ∈ Subgroup.closure {a, b} ∧
        imageG ∈ Subgroup.closure {a, b} := by
      simp only [imageA_eq, imageB_eq, imageC_eq, imageD_eq, imageG_eq, mul_mem_cancel_right ha,
        mul_mem_cancel_right hb, mul_mem_cancel_right (inv_mem ha),
        mul_mem_cancel_right (inv_mem hb), inv_mem_iff, ha, hb, and_self]
    obtain ⟨hA, hB, hC, hD, hG⟩ := hw
    rintro σ (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hA
    · exact hB
    · exact hC
    · exact hD
    · rw [imageE_eq]
      exact pow_mem (mul_mem (mul_mem hA hB) hC) 3
    · rw [imageF_eq]
      exact pow_mem (mul_mem hA hG) 3
    · exact hG
  · refine (Subgroup.closure_le _).mpr ?_
    have h : ∀ σ ∈ ({imageA, imageB, imageC, imageD, imageE, imageF, imageG} :
        Set (Equiv.Perm (Fin 276))), σ ∈ Subgroup.closure
          ({imageA, imageB, imageC, imageD, imageE, imageF, imageG} :
            Set (Equiv.Perm (Fin 276))) :=
      fun _ hσ ↦ Subgroup.subset_closure hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
    obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ := h
    rintro σ (rfl | rfl) <;>
    · simp only [SetLike.mem_coe, a_eq, b_eq, mul_mem_cancel_right hA, mul_mem_cancel_right hB,
        mul_mem_cancel_right hC, mul_mem_cancel_right hD, mul_mem_cancel_right hE,
        mul_mem_cancel_right hF, mul_mem_cancel_right hG, hB, hC]

/-- The homomorphism from the presented group extending the chosen assignment. -/
def presentationHom : SporadicName.Co3.Group →* Equiv.Perm (Fin 276) :=
  SporadicName.Co3.presentation.homEquiv.symm
    ⟨presentationImage, lift_presentationImage_toFreeGroup_eq_one⟩

/-- The homomorphism sends each generator of the presented group to its chosen image. -/
@[simp]
theorem presentationHom_of (i : Fin SporadicName.Co3.presentation.generatorCount) :
    presentationHom (PresentedGroup.of i) = presentationImage i :=
  GroupPresentation.homEquiv_symm_apply_of _ _ i

/-- The range of the presented-group homomorphism is exactly the ATLAS model. -/
theorem range_presentationHom : presentationHom.range = Co3 :=
  (GroupPresentation.range_homEquiv_symm _ _).trans closure_range_presentationImage

end Co3

/-- The presented third Conway group maps onto its ATLAS degree-276 permutation model. -/
theorem exists_surjective_Co3 :
    ∃ f : SporadicName.Co3.Group →* Co3, Function.Surjective f :=
  SporadicName.Co3.presentation.exists_surjective_of_closure_range_eq
    ⟨Co3.presentationImage, Co3.lift_presentationImage_toFreeGroup_eq_one⟩
    Co3.closure_range_presentationImage

/-- The presented group is nontrivial because it surjects onto the model. -/
instance : Nontrivial SporadicName.Co3.Group :=
  exists_surjective_Co3.choose_spec.nontrivial

end TauCeti.Sporadic
