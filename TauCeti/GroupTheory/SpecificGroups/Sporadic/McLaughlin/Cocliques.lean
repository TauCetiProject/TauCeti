/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.McLaughlin.Orbits
import Mathlib.Data.Nat.Bitwise

/-!
# Cocliques and the fifth basic orbit of the McLaughlin permutation model

The orbit of `4` under the pointwise stabilizer of `{0, 1, 2, 3}` in the ATLAS model `McL` is
`{4, 37, 40, 102, 119}`, so this fifth basic orbit has length `5` and the pointwise stabilizer of
`{0, 1, 2, 3}` has order `10`.

The McLaughlin graph (`McL.related`) does not suffice for the upper bound: an automorphism of the
graph outside the model fixes `0, 1, 2, 3` and sends `4` to `70`. The invariant that separates the
two is a family of `2025` sets, listed here, that every element of `McL` permutes. Each set is the
set of common non-neighbours of seven listed points, and the list is arranged in orbits of the
second file generator `b`: entry `5 * q + r` is the image under `b ^ r` of entry `5 * q`, so `b`
permutes the list because `b ^ 5 = 1`. A table records how the first generator `a` permutes it.
For each entry, a kernel-checked bit-mask computation shows that every neighbour of the image
under `a` of one of its seven points is a neighbour of one of the seven points of the tabulated
image; since `a` preserves adjacency, the image under `a` of the entry contains the tabulated
image, and since `a` and the table are involutions, the two are equal. The sets are the `2025`
cocliques of size `22` of one class of the graph, which the automorphism above moves to a
disjoint class; the proofs do not use this description.

The separating property of a point `y` is the existence of a listed coclique through `0` and `3`
all of whose common neighbours of `1` and `2` are adjacent to `y`. It is invariant under the
pointwise stabilizer of `{0, 1, 2, 3}`, it fails for `4`, and an explicit coclique witnesses it for
each of the ten points outside `{4, 37, 40, 102, 119}` that are adjacent to `0`, `1` and `3` but
not to `2`. Conversely the powers of an explicit element of the stabilizer move `4` around
`{4, 37, 40, 102, 119}`.

The cocliques were found by a computer search, and the element of the stabilizer from a collision of
images of `(0, 1, 2, 3)` under words in the generators. Only the kernel-checked evaluations below
enter the proofs.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `McLG1-p275B0`, <https://brauer.maths.qmul.ac.uk/Atlas/v3/>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge University Press, 2003, §4.1.
-/

public section

open MulAction

namespace TauCeti.Sporadic.McL

/-! ### Common non-neighbours -/

/-- The points adjacent to no point of `K` in the McLaughlin graph. -/
private def nonNeighbors (K : List (Fin 275)) : Set (Fin 275) :=
  {x | ∀ s ∈ K, related s x = false}

private theorem image_nonNeighbors {g : Equiv.Perm (Fin 275)} (hg : g ∈ McL)
    (K : List (Fin 275)) : ⇑g '' nonNeighbors K = nonNeighbors (K.map g) := by
  ext x
  simp only [nonNeighbors, Set.mem_image, Set.mem_ofPred_eq, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨y, hy, rfl⟩ s hs
    rw [related_apply hg]
    exact hy s hs
  · intro hx
    refine ⟨g⁻¹ x, fun s hs ↦ ?_, by simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]⟩
    rw [← related_apply hg s, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    exact hx s hs

/-! ### A family of `2025` cocliques -/

/- Seven points of the coclique `5 * q`, which consists of their common non-neighbours. -/
private def keyTable (q : ℕ) : List (Fin 275) :=
  (#[
    #[[4, 6, 30, 33, 43, 156, 178], [17, 22, 23, 24, 130, 162, 33], [4, 25, 30, 39, 50, 160, 207],
      [13, 48, 58, 70, 77, 118, 126], [7, 12, 15, 30, 34, 49, 73], [11, 22, 27, 49, 58, 202, 206],
      [14, 24, 38, 48, 109, 178, 51], [0, 3, 14, 22, 29, 198, 210], [5, 11, 29, 54, 81, 146, 175],
      [11, 23, 33, 45, 47, 194, 218], [14, 20, 22, 37, 74, 162, 170], [0, 15, 22, 32, 42, 101, 223],
      [0, 8, 9, 19, 39, 80, 87], [2, 8, 28, 44, 94, 183, 59], [7, 15, 22, 24, 59, 192, 46],
      [1, 19, 35, 38, 41, 55, 115], [12, 27, 55, 83, 192, 203, 105], [17, 19, 35, 53, 54, 117, 153],
      [13, 24, 37, 40, 70, 120, 172], [6, 19, 32, 50, 70, 145, 191], [0, 9, 13, 22, 26, 160, 184],
      [0, 34, 39, 56, 59, 191, 229], [15, 22, 39, 48, 128, 184, 49], [5, 14, 52, 58, 63, 74, 127],
      [5, 10, 23, 29, 33, 130, 151]],
    #[[3, 22, 23, 29, 33, 58, 157], [12, 15, 20, 28, 41, 106, 174], [6, 7, 8, 15, 19, 30, 108],
      [0, 8, 12, 21, 46, 174, 200], [1, 23, 24, 28, 59, 138, 71], [26, 27, 32, 49, 79, 124, 184],
      [37, 51, 85, 92, 102, 159, 95], [0, 8, 22, 29, 30, 81, 156], [45, 53, 60, 72, 80, 194, 226],
      [7, 9, 17, 18, 19, 154, 208], [7, 22, 26, 46, 60, 124, 234], [7, 9, 19, 20, 60, 66, 150],
      [1, 7, 30, 46, 217, 236, 59], [0, 20, 29, 34, 44, 137, 236], [3, 14, 31, 58, 61, 223, 237],
      [2, 15, 28, 32, 36, 37, 172], [2, 18, 21, 46, 62, 168, 235], [8, 13, 40, 46, 52, 128, 235],
      [1, 28, 29, 38, 44, 206, 210], [6, 19, 35, 38, 39, 65, 214], [27, 41, 45, 49, 55, 82, 179],
      [9, 48, 53, 60, 80, 118, 132], [1, 5, 31, 41, 55, 173, 239], [0, 19, 30, 34, 53, 121, 136],
      [14, 20, 29, 35, 61, 103, 240]],
    #[[0, 12, 15, 20, 22, 170, 212], [8, 9, 13, 28, 37, 177, 211], [15, 38, 48, 50, 57, 135, 212],
      [0, 15, 19, 20, 32, 63, 222], [26, 37, 49, 51, 60, 211, 54], [10, 19, 60, 71, 80, 138, 161],
      [8, 13, 20, 30, 32, 40, 240], [11, 26, 27, 50, 82, 101, 132], [9, 20, 22, 29, 118, 208, 51],
      [3, 14, 25, 51, 95, 207, 221], [13, 24, 49, 51, 131, 210, 100], [3, 5, 14, 17, 24, 149, 201],
      [11, 25, 26, 30, 33, 40, 221], [12, 13, 30, 52, 53, 132, 203], [29, 45, 60, 64, 66, 117, 236],
      [12, 13, 26, 37, 46, 205, 213], [1, 5, 18, 44, 56, 104, 107], [11, 27, 41, 45, 52, 58, 172],
      [3, 11, 22, 25, 29, 84, 207], [17, 19, 38, 44, 63, 162, 212], [3, 9, 10, 14, 17, 51, 98],
      [22, 29, 39, 59, 66, 72, 164], [28, 35, 41, 54, 81, 112, 209], [33, 45, 49, 56, 58, 155, 194],
      [10, 16, 18, 56, 70, 86, 88]],
    #[[1, 9, 17, 19, 29, 143, 152], [9, 10, 19, 25, 191, 222, 39], [0, 25, 26, 27, 56, 69, 97],
      [3, 24, 30, 48, 72, 194, 195], [1, 5, 17, 24, 53, 199, 228], [4, 11, 24, 33, 51, 110, 170],
      [1, 2, 6, 16, 28, 181, 206], [6, 10, 19, 38, 39, 65, 177], [7, 20, 41, 44, 196, 203, 64],
      [4, 7, 13, 26, 30, 78, 196], [15, 24, 30, 33, 197, 229, 42], [11, 15, 29, 30, 50, 59, 82],
      [20, 25, 32, 33, 61, 82, 207], [40, 50, 61, 70, 108, 117, 166], [1, 6, 28, 30, 41, 243, 34],
      [5, 10, 14, 64, 65, 224, 91], [19, 32, 34, 39, 61, 143, 41], [9, 16, 26, 50, 84, 191, 51],
      [13, 18, 24, 59, 78, 126, 242], [1, 5, 10, 19, 142, 153, 29], [2, 8, 17, 37, 57, 145, 200],
      [17, 22, 48, 51, 60, 122, 156], [9, 14, 17, 22, 66, 220, 244], [9, 10, 14, 16, 31, 66, 97],
      [8, 9, 19, 20, 39, 80, 122]],
    #[[0, 9, 19, 26, 101, 169, 42], [20, 25, 26, 27, 50, 109, 222], [27, 32, 36, 41, 86, 99, 56],
      [2, 16, 17, 18, 97, 245, 84], [16, 24, 38, 41, 49, 123, 245], [10, 19, 39, 43, 55, 94, 169],
      [13, 14, 24, 28, 51, 131, 210], [2, 9, 26, 53, 97, 105, 114], [20, 50, 51, 58, 80, 130, 212],
      [3, 5, 14, 24, 138, 201, 42], [35, 53, 71, 80, 88, 104, 219], [2, 9, 18, 19, 32, 44, 88],
      [3, 11, 61, 64, 84, 147, 221], [3, 5, 11, 25, 31, 127, 182], [20, 27, 28, 31, 35, 41, 119],
      [11, 28, 46, 52, 92, 142, 146], [40, 61, 69, 95, 121, 221, 226], [0, 3, 58, 59, 80, 132, 191],
      [1, 18, 19, 26, 53, 187, 242], [14, 27, 35, 38, 51, 80, 242], [5, 11, 31, 38, 58, 246, 41],
      [1, 24, 38, 51, 186, 197, 57], [1, 2, 5, 18, 24, 187, 243], [2, 11, 26, 32, 40, 187, 236],
      [9, 19, 30, 32, 65, 246, 42]],
    #[[10, 17, 35, 45, 55, 80, 228], [0, 3, 9, 35, 53, 111, 234], [35, 36, 61, 67, 92, 111, 117],
      [8, 9, 21, 34, 35, 112, 117], [39, 52, 61, 64, 72, 179, 190], [7, 9, 13, 18, 46, 107, 176],
      [0, 44, 53, 78, 82, 97, 169], [10, 34, 39, 48, 49, 72, 155], [30, 40, 68, 72, 76, 178, 186],
      [3, 5, 10, 25, 31, 182, 68], [5, 21, 29, 31, 52, 68, 77], [19, 30, 35, 60, 64, 72, 122],
      [29, 30, 42, 47, 48, 146, 248], [1, 2, 5, 11, 38, 185, 203], [2, 9, 42, 46, 145, 150, 57],
      [3, 5, 53, 80, 97, 224, 108], [40, 46, 52, 53, 69, 224, 238], [1, 9, 19, 30, 35, 203, 211],
      [6, 10, 16, 17, 155, 208, 38], [21, 23, 46, 48, 75, 163, 235], [1, 10, 16, 38, 49, 104, 211],
      [5, 38, 41, 45, 54, 103, 117], [10, 34, 48, 68, 71, 77, 211], [1, 19, 26, 34, 41, 103, 189],
      [7, 16, 26, 49, 102, 177, 214]],
    #[[10, 31, 36, 38, 56, 116, 142], [34, 45, 50, 61, 85, 128, 236], [3, 11, 25, 58, 156, 238, 61],
      [18, 25, 32, 56, 187, 238, 69], [13, 30, 34, 46, 47, 128, 229],
      [11, 46, 52, 75, 76, 190, 215], [0, 9, 28, 29, 30, 52, 250], [6, 31, 58, 62, 182, 236, 76],
      [14, 29, 38, 39, 84, 208, 44], [13, 18, 46, 75, 77, 172, 182], [0, 13, 30, 46, 57, 129, 135],
      [14, 28, 38, 42, 57, 65, 103], [13, 25, 30, 50, 51, 58, 242], [3, 10, 35, 45, 64, 247, 250],
      [3, 9, 25, 29, 30, 64, 224], [1, 2, 9, 21, 89, 169, 28], [3, 17, 29, 78, 84, 155, 198],
      [1, 43, 55, 97, 101, 133, 251], [1, 6, 10, 16, 17, 43, 155], [1, 3, 29, 30, 35, 60, 155],
      [7, 8, 12, 39, 55, 117, 183], [6, 7, 15, 39, 67, 188, 209], [4, 24, 30, 51, 54, 146, 178],
      [2, 6, 7, 9, 37, 57, 79], [9, 14, 29, 57, 96, 164, 166]],
    #[[14, 28, 29, 31, 138, 185, 35], [9, 10, 16, 39, 48, 159, 211], [2, 11, 15, 24, 38, 116, 201],
      [10, 14, 17, 37, 67, 173, 188], [7, 8, 9, 17, 22, 94, 223],
      [97, 114, 120, 123, 200, 240, 135], [31, 35, 55, 64, 93, 114, 248],
      [10, 35, 36, 38, 48, 130, 166], [1, 3, 9, 10, 17, 51, 233], [14, 57, 62, 67, 167, 213, 73],
      [11, 26, 27, 28, 47, 129, 175], [15, 22, 23, 33, 49, 124, 202],
      [11, 15, 29, 38, 72, 129, 138], [1, 16, 26, 28, 34, 169, 199], [24, 26, 33, 51, 71, 162, 175],
      [27, 28, 35, 36, 38, 220, 240], [11, 27, 38, 56, 84, 159, 245],
      [12, 14, 22, 27, 109, 230, 63], [0, 18, 46, 79, 111, 202, 88], [1, 18, 24, 26, 42, 131, 252],
      [17, 24, 38, 72, 115, 165, 200], [16, 18, 56, 75, 78, 111, 113],
      [10, 38, 42, 48, 49, 148, 159], [1, 3, 11, 29, 45, 97, 252], [17, 22, 42, 43, 67, 156, 213]],
    #[[3, 14, 17, 21, 35, 147, 166], [12, 22, 46, 48, 49, 72, 83], [3, 10, 14, 21, 29, 48, 190],
      [5, 10, 19, 61, 63, 77, 121], [3, 9, 22, 25, 114, 146, 201], [9, 32, 34, 46, 52, 182, 253],
      [11, 22, 26, 32, 118, 134, 33], [3, 5, 10, 18, 25, 127, 182], [0, 9, 48, 50, 145, 222, 75],
      [8, 32, 34, 36, 63, 112, 216], [3, 9, 10, 17, 98, 233, 18], [3, 45, 52, 61, 80, 234, 238],
      [0, 8, 9, 22, 32, 240, 253], [18, 32, 61, 70, 107, 141, 242], [60, 80, 92, 95, 97, 114, 171],
      [18, 37, 40, 46, 67, 74, 249], [10, 36, 45, 69, 88, 95, 171], [10, 29, 33, 34, 45, 98, 252],
      [11, 26, 42, 54, 69, 152, 172], [15, 22, 26, 37, 94, 159, 201], [0, 3, 22, 48, 193, 209, 78],
      [10, 17, 21, 23, 37, 42, 71], [23, 28, 31, 36, 76, 77, 167], [4, 12, 20, 27, 43, 91, 206],
      [4, 8, 15, 50, 54, 82, 94]],
    #[[6, 8, 20, 28, 29, 228, 254], [35, 45, 51, 54, 73, 196, 210], [23, 45, 48, 58, 63, 153, 230],
      [0, 15, 29, 39, 56, 156, 231], [13, 34, 49, 70, 85, 104, 126], [15, 20, 58, 61, 73, 157, 237],
      [6, 8, 15, 34, 36, 136, 211], [0, 21, 28, 34, 44, 104, 169], [13, 48, 50, 51, 80, 167, 240],
      [20, 27, 61, 63, 80, 112, 171], [12, 20, 34, 35, 57, 117, 239], [6, 44, 58, 70, 108, 223, 78],
      [14, 20, 28, 29, 31, 127, 138], [13, 14, 20, 37, 57, 226, 243], [0, 8, 21, 44, 78, 96, 238],
      [6, 10, 16, 34, 39, 56, 239], [12, 14, 16, 35, 39, 198, 237], [29, 31, 39, 76, 83, 111, 160],
      [14, 16, 17, 24, 37, 51, 181], [1, 21, 28, 43, 62, 78, 199], [20, 33, 34, 37, 60, 197, 226],
      [26, 27, 32, 43, 69, 81, 158], [1, 16, 34, 35, 41, 45, 104], [0, 9, 14, 20, 84, 246, 28],
      [3, 9, 18, 53, 95, 182, 191]],
    #[[20, 30, 41, 52, 58, 102, 218], [1, 9, 26, 28, 42, 51, 220], [0, 12, 13, 34, 247, 255, 46],
      [41, 63, 66, 74, 79, 99, 150], [1, 7, 24, 26, 33, 139, 226], [6, 34, 45, 47, 48, 208, 249],
      [12, 26, 53, 60, 66, 173, 239], [13, 27, 32, 47, 49, 113, 250], [9, 13, 14, 16, 95, 239, 48],
      [21, 34, 45, 47, 52, 140, 196], [1, 30, 42, 43, 69, 250, 49], [22, 26, 33, 37, 42, 51, 207],
      [16, 18, 26, 34, 79, 172, 255], [5, 10, 14, 18, 65, 185, 224], [16, 35, 50, 53, 54, 133, 143],
      [5, 10, 38, 45, 61, 72, 115], [10, 19, 34, 35, 88, 256, 43], [12, 16, 27, 35, 39, 189, 198],
      [12, 40, 54, 72, 73, 221, 256], [13, 27, 80, 83, 88, 225, 240],
      [36, 40, 95, 100, 166, 256, 110], [35, 45, 48, 50, 52, 119, 239],
      [8, 29, 35, 52, 71, 203, 256], [12, 34, 36, 40, 47, 148, 189],
      [13, 34, 39, 44, 65, 136, 239]],
    #[[16, 45, 73, 76, 90, 175, 250], [10, 25, 69, 93, 194, 241, 95], [0, 12, 14, 35, 48, 71, 164],
      [12, 34, 63, 66, 109, 252, 71], [10, 16, 36, 38, 54, 56, 116], [34, 36, 40, 50, 52, 116, 240],
      [8, 17, 48, 53, 70, 111, 117], [34, 45, 52, 53, 66, 242, 253], [0, 21, 29, 56, 66, 116, 185],
      [45, 47, 48, 75, 95, 157, 194], [10, 48, 54, 68, 70, 133, 256], [8, 12, 21, 35, 36, 174, 200],
      [27, 35, 36, 38, 179, 240, 39], [12, 30, 35, 41, 54, 68, 106], [1, 26, 30, 49, 60, 132, 138],
      [11, 38, 45, 50, 51, 54, 257], [1, 21, 35, 45, 53, 239, 248], [46, 48, 53, 57, 60, 154, 200],
      [1, 16, 21, 28, 31, 56, 160], [6, 30, 47, 50, 93, 187, 236], [16, 26, 27, 51, 75, 160, 233],
      [11, 27, 36, 45, 47, 90, 257], [27, 36, 45, 47, 119, 257, 50], [51, 57, 60, 78, 97, 198, 257],
      [0, 12, 27, 28, 104, 160, 252]],
    #[[15, 23, 36, 38, 48, 92, 120], [0, 26, 53, 60, 78, 230, 255], [4, 15, 20, 26, 32, 124, 148],
      [3, 30, 33, 51, 100, 156, 60], [6, 10, 33, 37, 42, 140, 182], [0, 9, 19, 20, 25, 84, 246],
      [20, 30, 40, 57, 62, 243, 258], [11, 25, 29, 31, 50, 61, 97], [9, 35, 50, 51, 57, 88, 234],
      [2, 9, 18, 26, 32, 78, 88], [3, 11, 25, 69, 81, 156, 238], [9, 10, 19, 25, 222, 258, 29],
      [0, 26, 34, 46, 47, 71, 253], [0, 20, 34, 35, 50, 207, 216], [8, 35, 57, 100, 105, 126, 237],
      [1, 2, 26, 28, 46, 79, 85], [2, 21, 42, 54, 57, 146, 248], [0, 15, 26, 28, 42, 153, 222],
      [0, 50, 56, 78, 133, 205, 88], [0, 25, 82, 96, 97, 125, 135], [7, 15, 20, 26, 57, 96, 101],
      [0, 12, 20, 26, 114, 189, 27], [14, 16, 27, 38, 39, 79, 245], [77, 79, 91, 95, 99, 184, 208],
      [38, 55, 70, 80, 117, 119, 211]],
    #[[4, 12, 15, 20, 39, 124, 148], [12, 40, 57, 76, 93, 175, 259], [5, 14, 38, 61, 97, 172, 190],
      [16, 18, 53, 66, 75, 111, 113], [4, 16, 26, 27, 41, 115, 257], [2, 31, 41, 74, 79, 84, 114],
      [0, 26, 50, 53, 57, 146, 174], [5, 41, 44, 55, 63, 65, 199], [0, 19, 30, 35, 39, 242, 260],
      [24, 86, 105, 108, 123, 212, 226], [0, 27, 32, 61, 69, 216, 234],
      [12, 20, 27, 35, 41, 119, 188], [5, 25, 40, 52, 61, 204, 224], [12, 35, 53, 55, 69, 210, 260],
      [8, 17, 35, 43, 67, 198, 260], [13, 18, 70, 87, 91, 149, 231], [0, 14, 27, 35, 44, 225, 256],
      [39, 41, 58, 61, 68, 155, 186], [1, 3, 5, 10, 21, 23, 261], [4, 11, 56, 59, 76, 168, 175],
      [1, 3, 5, 18, 21, 168, 261], [5, 11, 24, 40, 54, 131, 197], [5, 10, 54, 55, 69, 161, 230],
      [12, 15, 24, 54, 72, 152, 169], [26, 37, 74, 95, 109, 134, 230]],
    #[[36, 46, 95, 96, 107, 233, 253], [18, 26, 33, 56, 245, 261, 66],
      [12, 21, 34, 68, 76, 137, 155], [12, 37, 60, 95, 105, 164, 247],
      [3, 45, 53, 68, 95, 179, 261], [11, 15, 24, 26, 46, 49, 261], [3, 31, 59, 61, 68, 128, 261],
      [3, 10, 18, 61, 95, 110, 261], [26, 60, 69, 79, 93, 170, 236], [12, 40, 53, 68, 95, 146, 205],
      [4, 16, 24, 70, 109, 159, 193], [46, 65, 77, 79, 104, 121, 262],
      [9, 25, 67, 95, 99, 114, 227], [0, 3, 21, 46, 52, 137, 160], [36, 46, 47, 48, 52, 83, 141],
      [4, 8, 12, 13, 28, 37, 211], [12, 27, 36, 39, 55, 83, 192], [0, 8, 35, 48, 60, 92, 144],
      [12, 14, 21, 28, 52, 83, 35], [12, 35, 55, 60, 79, 209, 211], [0, 12, 21, 47, 48, 68, 257],
      [10, 36, 37, 77, 79, 159, 88], [0, 8, 12, 20, 30, 114, 189], [1, 5, 10, 19, 142, 219, 55],
      [18, 44, 61, 96, 97, 111, 166]],
    #[[11, 32, 46, 47, 101, 238, 62], [5, 10, 18, 33, 183, 231, 56], [1, 10, 33, 34, 45, 100, 252],
      [5, 11, 45, 56, 69, 190, 61], [18, 21, 34, 37, 46, 96, 199], [34, 35, 36, 41, 45, 104, 52],
      [1, 5, 11, 33, 103, 115, 41], [0, 32, 44, 50, 58, 136, 264], [3, 5, 11, 29, 52, 59, 72],
      [0, 18, 34, 56, 61, 155, 231], [11, 40, 50, 59, 85, 167, 246], [1, 11, 46, 69, 199, 264, 72],
      [4, 7, 8, 13, 37, 177, 211], [6, 7, 9, 60, 78, 223, 236], [44, 45, 50, 53, 78, 140, 198],
      [1, 5, 45, 53, 75, 76, 195], [2, 4, 16, 31, 55, 227, 259], [16, 50, 57, 93, 95, 120, 256],
      [2, 5, 31, 97, 201, 223, 108], [13, 16, 24, 48, 53, 182, 211], [1, 3, 9, 30, 53, 78, 133],
      [14, 25, 27, 43, 96, 131, 244], [6, 9, 10, 21, 48, 182, 248], [6, 9, 10, 16, 17, 43, 208],
      [8, 13, 44, 50, 70, 227, 265]],
    #[[11, 31, 36, 45, 52, 182, 238], [9, 25, 26, 30, 236, 241, 42], [5, 24, 33, 41, 58, 70, 109],
      [0, 27, 43, 47, 56, 163, 230],
      [0, 27, 35, 69, 79, 246, 255]]] : Array (Array (List (Fin 275))))
    |>.getD (q / 25) #[]
    |>.getD (q % 25) []

/- The seven key points of the coclique `i`, moved by `b ^ (i % 5)`. -/
private def key (i : ℕ) : List (Fin 275) := (keyTable (i / 5)).map ⇑(b ^ (i % 5))

/-- The `i`-th listed coclique, for `i < 2025`. -/
private def coclique (i : ℕ) : Set (Fin 275) := nonNeighbors (key i)

/- Row `r` packs the entries `25 * r, …, 25 * r + 24` of `aTable` in fields of eleven bits. -/
private def aTableRows (r : ℕ) : ℕ :=
  (#[
    #[8100947606180101172966135951923660641903690037330851088475393979077195932013062144,
      58327938552926714935769399480603228145992296947440653166564268332529014804758753698,
      45092826585185909472875550802120765810537992609317240448468658086190767654845739583,
      2950150077927584538732179268100447647717182334724998643414574855553502546186943113,
      36982434308152832270374691508023334081282709145371813808364608993098675984591807112,
      47300997891148906750806783605996293639977305939684913038410469994207873081530369897,
      18996562567636299627531334868908885094879074132659012748500596897723068261103458193,
      26093582081604609786790467250093038469603939259644015943933032999297500351184299070,
      15250525090397203384404673632808892513381893930878601614069842194628799837123698399],
    #[17021967112641481699203650849524117350676482687845175160683446156326440701974938823,
      8122477093591440963958736069571660965364496031948883358882456018736896053289109845,
      37402297906436542354495608364792715025058521401879364049094775950977465362027383938,
      11537309256154514902923974007703061215298764167191477540039522733003531056356763207,
      31515313938587861234035426268571259864822363535384371902909740947877890050919274821,
      21321171653683003171109873100123202990965729149195959662744378863289744301539265436,
      45689610986582966870619621376831695641449950935490396536029693421170976297355101047,
      15644278091588653951818957657410496897416503439136375595676211863603648925728195622,
      9217683753743317330018068104899626664144350543885023055132966234138228098433435654],
    #[43577887485869377703476428585024940240586353971276756803718360883540158489321876418,
      46310146726442674269686354807139652213552585355546780144431890716717122323349197512,
      15971306809627041793585102466462216919253642937102438569341140843294800993461642007,
      47134881942793702851985387624034843227832171297141478595932123748889106774124118822,
      7405912358079044105972374597859022592132909363046915544725318801013959800690717445,
      7599780332339259128959293184731826717129263009616212526583631990528497181414715442,
      44151640081324476669370845619687716643939919484475355281219189422883427125721378041,
      2224664638960572395967577934406893496494446444326386632565185741689708416683003253,
      19959350302050810120826799541280721681314416071142756055974517772701572734185634442],
    #[24171167224127612736521756986154582105631942926693433235315216790659284992175076229,
      48473103191222080195202215059161884155441287017884267639457992527895336905547895804,
      16103915462596354949474087345538708147046350071161064308818160423977406907971024475,
      22951471897585254208916339168303020791158503454666170960970038660449560225607789410,
      50704828113086741677309354862158354590146084572970985358986416064400841233543051862,
      39199670995162294292876374700883078612871791862222099101939100552112392484802681261,
      27550202926406186495968376914987530489753335263767223405891214544295398877463138731,
      41870146097123380584720914083998738980064362881760747213428293164911300340980073146,
      16049740808801890375506529251204057726687622569611893634632005624615064657555811096],
    #[10377883255321694812721220695705600068475201097134841091025614522576305145620274052,
      58798107218188517756907437982091683024863138936037713690322202464201200656308110237,
      56630877631344693527685460489000814915758628677602107576556815080170465974763913628,
      10027786026908498929832280724056111392171616308337955649755882214075555706122469044,
      40972564962311561149108390582428104282330959621179129549333473252123655829196692263,
      1237209849399038674193377781494556328802263903253730722960306310477757062000040432,
      16004190150900586291849813227308678869904062139189064499455918041372091161686105796,
      28048383425565426136550840358308267398892950293406275907047653272983346580519072449,
      30564329966600715817988510994164851836963380646006358140640433873094281299774319389],
    #[14938191795244493995129593096888657781350152747010791351981689983186579114647636872,
      12447469901641945344002833351138768222847141175818795086296199014802462521447274741,
      26399034549850682187771211327813723594386801988678044159657520200374828893343326311,
      27837823720357420128562419801318929466331357931789090022338517563281358328898579632,
      30965121385819763076982504163475330235243519931638207520203094525119502518852252755,
      27695045176401227737116996167785266955074178593114431331175451217826278532991925245,
      23264536530976335817068759509467536733382237797100820140874254663372197687417560494,
      56401116677997075258673996443220083498883612037931991556836948183438939313190606919,
      49227192210285214622058561229139823163264865371827930801457544486747589940402734880],
    #[43386162998292452749443982242054100840361180217562050653498574422154788862603246140,
      25034615965003550683226451409751293604480334260008878477600437070789649384177747909,
      58663747500998390026733674380520725140607764615438373407761403166939119312630322058,
      38812106545239149957169578432228064031342137986375081146480709866025788972132558858,
      2007391878036825073741411543124435268861771072874340663164846651963786167289903783,
      26570868067204897053498120444510782435845606808088198625713186284550326813208448451,
      22825141266945139342731073053453583932832790868683174628631071554232992448516123996,
      43403673225724385531983063264338213308791779693171277127471015174676051964831366953,
      22036785413904051838667852174149953898723204022500516641422777197885519290010991209],
    #[47424373362119764533528974418071740608269781229085465895734568535419340369440260233,
      5432211986161335127388378795747436699316433233538357026407542131190854349518730021,
      3939070428496976560891945967824798459735357720304396232564800508376987837637242272,
      18422964991095466806277762545138874569486156024270807256015377517645865657751128398,
      38501729552256192780299687574058970786935709270090451906021223222075396463283395688,
      6582036776670151164657658833201806784726900338746656929551083501267353342883929474,
      6961717201548585427685891633576921831494808255300233528839665819656877836890697421,
      17870615382723187635840225249336649664407327717231653377398677599628799175408950611,
      33209130209163314900387035658889694186444261339392748507868750675466648742113339324],
    #[39297558591080306414643372644576878662761431287896924111594252051614930335057233192,
      4035854016218862372261146432100568469917197052528278996953761517992018536912114692,
      55577602833169416742120348296246415337473864682902537167891736119931334480648238906,
      8778170221652138443686359184742594498239644040978104541795807445326084180606385301,
      43831798292845037372669677008810344243215531446331968028641868021966689361368009240,
      2286017927337958135842334728354099640738139552091218585174571505756966564680758396,
      21162980126190256384494198407220252520819359221657800113818295055988242283128804734,
      13180698087561834044768476360287248277753060957150857420532682615380680191679919857,
      25245566253956468947103586731822047227261687212747366471816732921160332282969837079]]
    : Array (Array ℕ))
    |>.getD (r / 9) #[]
    |>.getD (r % 9) 0

/- The image of the coclique `i` under `a` is the coclique `aTable i`. -/
private def aTable (i : ℕ) : ℕ := (aTableRows (i / 25) >>> (11 * (i % 25))) % 2048

/-! ### Packed lookup tables

The finite checks below run on natural numbers: a permutation is packed into one number with a
field of nine bits per point, and the adjacency rows into one number with a field of `275` bits
per point. The kernel evaluates each packed number once and then reads fields by shifting, which
is much cheaper than repeated lookups in the generator tables. -/

private def aPacked : ℕ :=
  (List.range 275).foldr (fun x acc ↦ acc <<< 9 ||| (a (Fin.ofNat 275 x)).val) 0

private def bPacked : ℕ :=
  (List.range 275).foldr (fun x acc ↦ acc <<< 9 ||| (b (Fin.ofNat 275 x)).val) 0

private def rowsPacked : ℕ :=
  (List.range 275).foldr (fun x acc ↦ acc <<< 275 ||| relationRows (Fin.ofNat 275 x)) 0

private def aNat (x : ℕ) : ℕ := (aPacked >>> (9 * x)) % 512

private def bNat (x : ℕ) : ℕ := (bPacked >>> (9 * x)) % 512

private def rowNat (x : ℕ) : ℕ := (rowsPacked >>> (275 * x)) % 2 ^ 275

private theorem packed_check : (List.range 275).all (fun x ↦
    aNat x == (a (Fin.ofNat 275 x)).val && bNat x == (b (Fin.ofNat 275 x)).val &&
      rowNat x == relationRows (Fin.ofNat 275 x)) = true := by
  decide +kernel

private theorem packed_val (x : Fin 275) :
    aNat x.val = (a x).val ∧ bNat x.val = (b x).val ∧ rowNat x.val = relationRows x := by
  have h := List.all_eq_true.mp packed_check x.val (List.mem_range.mpr x.isLt)
  simpa only [Fin.ofNat_val_eq_self, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

private theorem related_iff_testBit (p x : Fin 275) :
    related p x = (rowNat p.val).testBit x.val := by
  rw [related, (packed_val p).2.2]

private theorem bNat_iterate_val (r : ℕ) (x : Fin 275) : bNat^[r] x.val = ((b ^ r) x).val := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, (packed_val _).2.1, pow_succ', Equiv.Perm.mul_apply]

/-- The union of the neighbourhoods of the points of `K`, as a bit mask. -/
private def neighborMask (K : List ℕ) : ℕ := K.foldr (fun s m ↦ rowNat s ||| m) 0

private theorem mem_nonNeighbors_iff_testBit {K : List (Fin 275)} {x : Fin 275} :
    x ∈ nonNeighbors K ↔ (neighborMask (K.map Fin.val)).testBit x.val = false := by
  induction K with
  | nil => simp [nonNeighbors, neighborMask]
  | cons s K ih =>
    simp only [nonNeighbors, Set.mem_ofPred_eq, List.mem_cons, forall_eq_or_imp] at ih ⊢
    simp only [List.map_cons, neighborMask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_lor, Bool.or_eq_false_iff, ← ih, (packed_val s).2.2, related]

/-- The key points of the coclique `i`, as natural numbers. -/
private def keyNat (i : ℕ) : List ℕ := (keyTable (i / 5)).map fun s ↦ bNat^[i % 5] s.val

private theorem keyNat_eq (i : ℕ) : keyNat i = (key i).map Fin.val := by
  simp only [keyNat, key, List.map_map]
  exact List.map_congr_left fun s _ ↦ bNat_iterate_val _ s

private theorem mem_coclique_iff {i : ℕ} {x : Fin 275} :
    x ∈ coclique i ↔ (neighborMask (keyNat i)).testBit x.val = false := by
  rw [coclique, mem_nonNeighbors_iff_testBit, keyNat_eq]

/-! ### The generators permute the family -/

/- For each `i`, `aTable` is an involution and every neighbour of the image under `a` of a key
point of the coclique `i` is a neighbour of a key point of the coclique `aTable i`. -/
private def aCheck (i : ℕ) : Bool :=
  aTable (aTable i) == i && aTable i < 2025 &&
    (keyNat i).all fun t ↦
      rowNat (aNat t) ||| neighborMask (keyNat (aTable i)) == neighborMask (keyNat (aTable i))

private theorem aCheck_all : (List.range 2025).all aCheck = true := by
  decide +kernel

private theorem a_mul_self : a * a = 1 := by
  ext x
  revert x
  decide +kernel

private theorem b_pow_five : b ^ 5 = 1 := by
  ext x
  revert x
  decide +kernel

private theorem aCheck_spec {i : ℕ} (hi : i < 2025) :
    aTable (aTable i) = i ∧ aTable i < 2025 ∧ coclique (aTable i) ⊆ ⇑a '' coclique i := by
  have h := List.all_eq_true.mp aCheck_all i (List.mem_range.mpr hi)
  simp only [aCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hinv, hlt⟩, hkey⟩ := h
  refine ⟨hinv, hlt, ?_⟩
  intro x hx
  rw [coclique, image_nonNeighbors a_mem]
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  have hmask := hkey t.val (by rw [keyNat_eq]; exact List.mem_map_of_mem ht)
  rw [(packed_val t).1, (packed_val (a t)).2.2] at hmask
  rw [mem_coclique_iff] at hx
  have hbit := congrArg (Nat.testBit · x.val) hmask
  simp only [Nat.testBit_lor, hx, Bool.or_eq_false_iff] at hbit
  rw [related]
  exact hbit.1

private theorem image_a_coclique {i : ℕ} (hi : i < 2025) :
    ⇑a '' coclique i = coclique (aTable i) ∧ aTable i < 2025 := by
  obtain ⟨hinv, hlt, hsub⟩ := aCheck_spec hi
  obtain ⟨-, -, hsub'⟩ := aCheck_spec hlt
  rw [hinv] at hsub'
  have haa (x : Fin 275) : a (a x) = x := by
    rw [← Equiv.Perm.mul_apply, a_mul_self, Equiv.Perm.one_apply]
  refine ⟨subset_antisymm ?_ hsub, hlt⟩
  calc ⇑a '' coclique i ⊆ ⇑a '' (⇑a '' coclique (aTable i)) := Set.image_mono hsub'
    _ = coclique (aTable i) := by simp only [Set.image_image, haa, Set.image_id']

private theorem image_b_coclique (i : ℕ) :
    ⇑b '' coclique i = coclique (i / 5 * 5 + (i % 5 + 1) % 5) := by
  have hq : (i / 5 * 5 + (i % 5 + 1) % 5) / 5 = i / 5 := by omega
  have hr : (i / 5 * 5 + (i % 5 + 1) % 5) % 5 = (i % 5 + 1) % 5 := by omega
  rw [coclique, image_nonNeighbors b_mem, coclique, key, key, hq, hr, List.map_map,
    ← pow_eq_pow_mod (i % 5 + 1) b_pow_five, pow_succ', Equiv.Perm.coe_mul]

private theorem mapsTo_cocliques {g : Equiv.Perm (Fin 275)} (hg : g ∈ McL) :
    Set.MapsTo (⇑g '' ·) (coclique '' Set.Iio 2025) (coclique '' Set.Iio 2025) := by
  rw [McL_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rintro _ ⟨i, hi, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨aTable i, (image_a_coclique hi).2, (image_a_coclique hi).1.symm⟩
    · exact ⟨i / 5 * 5 + (i % 5 + 1) % 5, by simp only [Set.mem_Iio] at hi ⊢; omega,
        (image_b_coclique i).symm⟩
  | one =>
    intro S hS
    simpa using hS
  | mul g h _ _ hg hh =>
    intro S hS
    simpa only [Equiv.Perm.coe_mul, Set.image_comp] using hg (hh hS)
  | inv g _ hg =>
    have hbij := ((Set.finite_Iio 2025).image coclique).injOn_iff_bijOn_of_mapsTo hg |>.mp
      fun _ _ _ _ h ↦ Set.image_injective.mpr g.injective h
    intro S hS
    obtain ⟨T, hT, rfl⟩ := hbij.surjOn hS
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_image_image] using hT

/-! ### The fifth basic orbit -/

/- Every listed coclique through `0` and `3` has a common neighbour of `1` and `2` that is not
adjacent to `4`. -/
private def nearCheck (j : ℕ) : Bool :=
  (neighborMask (keyNat j)).testBit 0 || (neighborMask (keyNat j)).testBit 3 ||
    (List.range 275).any fun z ↦
      !(neighborMask (keyNat j)).testBit z && (rowNat 1).testBit z && (rowNat 2).testBit z &&
        !(rowNat 4).testBit z

private theorem nearCheck_all : (List.range 2025).all nearCheck = true := by
  decide +kernel

/- The witness coclique for each point of the type of `4` outside the fifth basic orbit. -/
private def witness (y : ℕ) : ℕ :=
  ([(36, 716), (70, 716), (117, 1202), (120, 96), (171, 636), (192, 96), (227, 636),
    (245, 1377), (267, 636), (272, 96)] : List (ℕ × ℕ)).lookup y |>.getD 0

/- A point adjacent to `0`, `1` and `3` but not to `2` lies in `{4, 37, 40, 102, 119}`, or its
witness coclique passes through `0` and `3` and all its common neighbours of `1` and `2` are
adjacent to it. -/
private def witnessCheck (y : ℕ) : Bool :=
  !(rowNat 0).testBit y || !(rowNat 1).testBit y || (rowNat 2).testBit y ||
    !(rowNat 3).testBit y || y == 4 || y == 37 || y == 40 || y == 102 || y == 119 ||
    (witness y < 2025 && !(neighborMask (keyNat (witness y))).testBit 0 &&
      !(neighborMask (keyNat (witness y))).testBit 3 &&
      (List.range 275).all fun z ↦
        (neighborMask (keyNat (witness y))).testBit z || !(rowNat 1).testBit z ||
          !(rowNat 2).testBit z || (rowNat y).testBit z)

private theorem witnessCheck_all : (List.range 275).all witnessCheck = true := by
  decide +kernel

private theorem related_eq_testBit {p : Fin 275} {n : ℕ} (hp : p.val = n) (x : Fin 275) :
    related p x = (rowNat n).testBit x.val := by
  rw [related_iff_testBit, hp]

private theorem exists_near {j : ℕ} (hj : j < 2025) (h0 : (0 : Fin 275) ∈ coclique j)
    (h3 : (3 : Fin 275) ∈ coclique j) :
    ∃ z ∈ coclique j, related 1 z = true ∧ related 2 z = true ∧ related 4 z = false := by
  have h := List.all_eq_true.mp nearCheck_all j (List.mem_range.mpr hj)
  have h0' : (neighborMask (keyNat j)).testBit 0 = false := mem_coclique_iff.mp h0
  have h3' : (neighborMask (keyNat j)).testBit 3 = false := mem_coclique_iff.mp h3
  rw [nearCheck, h0', h3', Bool.false_or, Bool.false_or, List.any_eq_true] at h
  obtain ⟨z, hz, hzb⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hzb
  obtain ⟨⟨⟨hm, h1⟩, h2⟩, h4⟩ := hzb
  refine ⟨⟨z, List.mem_range.mp hz⟩, mem_coclique_iff.mpr hm, ?_, ?_, ?_⟩
  · rw [related_eq_testBit rfl]
    exact h1
  · rw [related_eq_testBit rfl]
    exact h2
  · rw [related_eq_testBit rfl]
    exact h4

private theorem exists_witness {y : Fin 275} (h0 : related 0 y = true) (h1 : related 1 y = true)
    (h2 : related 2 y = false) (h3 : related 3 y = true)
    (hy : y ≠ 4 ∧ y ≠ 37 ∧ y ≠ 40 ∧ y ≠ 102 ∧ y ≠ 119) :
    ∃ w < 2025, (0 : Fin 275) ∈ coclique w ∧ (3 : Fin 275) ∈ coclique w ∧
      ∀ z ∈ coclique w, related 1 z = true → related 2 z = true → related y z = true := by
  have h := List.all_eq_true.mp witnessCheck_all y.val (List.mem_range.mpr y.isLt)
  rw [related_eq_testBit (n := 0) rfl] at h0
  rw [related_eq_testBit (n := 1) rfl] at h1
  rw [related_eq_testBit (n := 2) rfl] at h2
  rw [related_eq_testBit (n := 3) rfl] at h3
  have hne (n : Fin 275) (hn : y ≠ n) : (y.val == n.val) = false :=
    beq_false_of_ne (Fin.val_injective.ne hn)
  have e4 : (y.val == 4) = false := hne 4 hy.1
  have e37 : (y.val == 37) = false := hne 37 hy.2.1
  have e40 : (y.val == 40) = false := hne 40 hy.2.2.1
  have e102 : (y.val == 102) = false := hne 102 hy.2.2.2.1
  have e119 : (y.val == 119) = false := hne 119 hy.2.2.2.2
  rw [witnessCheck] at h
  simp only [h0, h1, h2, h3, e4, e37, e40, e102, e119, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hw, hw0⟩, hw3⟩, hz⟩ := h
  refine ⟨witness y.val, hw, mem_coclique_iff.mpr hw0, mem_coclique_iff.mpr hw3, ?_⟩
  intro z hzw hz1 hz2
  rw [mem_coclique_iff] at hzw
  rw [related_eq_testBit (n := 1) rfl] at hz1
  rw [related_eq_testBit (n := 2) rfl] at hz2
  rw [related_iff_testBit]
  simpa only [hzw, hz1, hz2, Bool.not_true, Bool.false_or] using hz z.val z.isLt

/-- An element of `McL` fixing `0, 1, 2, 3` sends `4` into `{4, 37, 40, 102, 119}`. -/
private theorem image_four {g : Equiv.Perm (Fin 275)} (hg : g ∈ McL)
    (hfix : ∀ x : Fin 275, x.val < 4 → g x = x) :
    g 4 = 4 ∨ g 4 = 37 ∨ g 4 = 40 ∨ g 4 = 102 ∨ g 4 = 119 := by
  by_contra hy
  simp only [not_or] at hy
  have hrel (p : Fin 275) (hp : p.val < 4) (z : Fin 275) : related p (g z) = related p z := by
    conv_lhs => rw [← hfix p hp]
    exact related_apply hg p z
  obtain ⟨w, hw, hw0, hw3, hwz⟩ := exists_witness
    ((hrel 0 (by decide) 4).trans (by decide +kernel))
    ((hrel 1 (by decide) 4).trans (by decide +kernel))
    ((hrel 2 (by decide) 4).trans (by decide +kernel))
    ((hrel 3 (by decide) 4).trans (by decide +kernel)) hy
  obtain ⟨j, hj, hji⟩ := mapsTo_cocliques (inv_mem hg) ⟨w, hw, rfl⟩
  have hinv (p : Fin 275) (hp : p.val < 4) : g⁻¹ p = p :=
    Equiv.Perm.inv_eq_iff_eq.mpr (hfix p hp).symm
  have hmem (p : Fin 275) (hp : p.val < 4) (h : p ∈ coclique w) : p ∈ coclique j := by
    rw [hji]
    exact ⟨p, h, hinv p hp⟩
  obtain ⟨z, hz, hz1, hz2, hz4⟩ :=
    exists_near hj (hmem 0 (by decide) hw0) (hmem 3 (by decide) hw3)
  rw [hji] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  have hgg : g (g⁻¹ z') = z' := by rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  have h := hwz z' hz' (by simpa only [hgg] using (hrel 1 (by decide) (g⁻¹ z')).trans hz1)
    (by simpa only [hgg] using (hrel 2 (by decide) (g⁻¹ z')).trans hz2)
  have h4 : related (g 4) z' = false := by
    simpa only [hgg] using (related_apply hg 4 (g⁻¹ z')).trans hz4
  rw [h4] at h
  exact Bool.false_ne_true h

/- An element of the pointwise stabilizer of `{0, 1, 2, 3}` found from two words with the same
images of `0, 1, 2, 3`; its powers send `4` to `40`, `119`, `37` and `102`. -/
private def stabWord : Equiv.Perm (Fin 275) :=
  [b ^ 3, a, b ^ 4, a, b, a, b ^ 4, a, b ^ 2, a, b ^ 3, a, b, a, b, a, b, a, b ^ 3, a, b, a,
    b ^ 4, a, b ^ 4].prod

private theorem stabWord_mem : stabWord ∈
    McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3} : Set (Fin 275)) := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · apply Subgroup.list_prod_mem
    simp [a_mem, b_mem, pow_mem b_mem]
  · have h : stabWord 0 = 0 ∧ stabWord 1 = 1 ∧ stabWord 2 = 2 ∧ stabWord 3 = 3 := by
      decide +kernel
    rw [mem_fixingSubgroup_iff]
    rintro y (rfl | rfl | rfl | rfl) <;> simp [Equiv.Perm.smul_def, h]

private theorem stabWord_pow_apply : stabWord 4 = 40 ∧ (stabWord ^ 2) 4 = 119 ∧
    (stabWord ^ 3) 4 = 37 ∧ (stabWord ^ 4) 4 = 102 := by
  decide +kernel

/-- The orbit of `4` under the pointwise stabilizer of `{0, 1, 2, 3}` in the ATLAS model. -/
theorem orbit_fixing_zero_one_two_three_four :
    orbit ↥(McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3} : Set (Fin 275)))
      (4 : Fin 275) = ({4, 37, 40, 102, 119} : Set (Fin 275)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hfix := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 275))).mp g.property.2
    have h := image_four g.property.1 fun z hz ↦ by
      have : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by omega
      simpa only [Equiv.Perm.smul_def] using
        hfix z (by rcases this with rfl | rfl | rfl | rfl <;> simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, subgroup_smul_def,
      Equiv.Perm.smul_def] using h
  · have hpow (k : ℕ) : ((⟨stabWord, stabWord_mem⟩ ^ k :
        ↥(McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3} : Set (Fin 275)))) •
          (4 : Fin 275)) = (stabWord ^ k) 4 := by
      simp [subgroup_smul_def, Equiv.Perm.smul_def]
    obtain ⟨h1, h2, h3, h4⟩ := stabWord_pow_apply
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact mem_orbit_self _
    · exact mem_orbit_iff.mpr ⟨_, (hpow 3).trans h3⟩
    · exact mem_orbit_iff.mpr ⟨_, (hpow 1).trans (by simpa using h1)⟩
    · exact mem_orbit_iff.mpr ⟨_, (hpow 4).trans h4⟩
    · exact mem_orbit_iff.mpr ⟨_, (hpow 2).trans h2⟩

/-- The fifth basic orbit in the ATLAS McLaughlin model has length five. -/
@[simp] theorem ncard_orbit_fixing_zero_one_two_three_four :
    (orbit ↥(McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3} : Set (Fin 275)))
      (4 : Fin 275)).ncard = 5 := by
  rw [orbit_fixing_zero_one_two_three_four]
  simp

/-- The pointwise stabilizer of `{0, 1, 2, 3}` in the exact ATLAS model has order ten. -/
theorem card_fixing_zero_one_two_three :
    Nat.card ↥(McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275))
      ({0, 1, 2, 3} : Set (Fin 275))) = 10 := by
  have h := Subgroup.relIndex_mul_card (stabilizer (Equiv.Perm (Fin 275)) (4 : Fin 275))
    (McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3} : Set (Fin 275)))
  have hinf : stabilizer (Equiv.Perm (Fin 275)) (4 : Fin 275) ⊓
      (McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3} : Set (Fin 275))) =
      McL ⊓ fixingSubgroup (Equiv.Perm (Fin 275)) ({0, 1, 2, 3, 4} : Set (Fin 275)) := by
    ext g
    simp only [Subgroup.mem_inf, mem_stabilizer_iff, mem_fixingSubgroup_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    tauto
  rw [Subgroup.relIndex, stabilizer_subgroupOf, index_stabilizer,
    ncard_orbit_fixing_zero_one_two_three_four, hinf, card_fixing_zero_one_two_three_four] at h
  omega

end TauCeti.Sporadic.McL
