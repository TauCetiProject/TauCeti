/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Morse.ScalarComposition

/-!
# The sum of two height functions on a product of spheres is a Morse function

On the product `Sⁿ × Sᵐ` of two unit spheres, the sum `sphereHeight v ∘ Prod.fst +
sphereHeight w ∘ Prod.snd` of the height functions in the directions of the unit vectors `v` and
`w` is a Morse function. Its critical points are the four pairs of poles `(±v, ±w)`, and its Morse
index at `(x, y)` is the sum of the indices of the two height functions, so the four critical
points have indices `n + m`, `n`, `m` and `0`. For `n = m = 1` this is the standard Morse function
on the two-torus `S¹ × S¹`, with one critical point of index `2`, two of index `1` and one of
index `0`.

More generally, for a real `ε ≠ 0`, the function `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫` is a Morse function
with the same four critical points, and for `ε > 0` the same Morse indices.

## Main declarations

* `TauCeti.isMorse_sphereHeight_comp_fst_add_comp_snd`: the sum of two height functions is Morse
  on the product of spheres.
* `TauCeti.mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff`: its critical points are the
  pairs of poles.
* `TauCeti.manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd`: its Morse index is the sum of
  the indices of the two height functions.
* `TauCeti.criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd`,
  `TauCeti.isMorse_sphereHeight_comp_fst_add_mul_comp_snd` and
  `TauCeti.manifoldMorseIndex_sphereHeight_comp_fst_add_mul_comp_snd`: the same for
  `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Metric Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {n m : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ E' = m + 1)]

/-- The height in the direction of `w`, multiplied by `ε`, is smooth. -/
theorem contMDiff_mul_comp_sphereHeight (w : sphere (0 : E') 1) (ε : ℝ) :
    ContMDiff (𝓡 m) 𝓘(ℝ) ∞ ((ε * ·) ∘ sphereHeight w) :=
  (contDiff_const.mul contDiff_id).contMDiff.comp (contMDiff_sphereHeight w)

/-- **The critical points** of `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫` on `Sⁿ × Sᵐ`, for `ε ≠ 0`, are the four
pairs of poles. -/
theorem criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd (v : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) {ε : ℝ} (hε : ε ≠ 0) :
    criticalPoints ((𝓡 n).prod (𝓡 m))
        (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd) =
      ({v, -v} : Set (sphere (0 : E) 1)) ×ˢ ({w, -w} : Set (sphere (0 : E') 1)) := by
  ext ⟨x, y⟩
  have hy := (contMDiff_mul_comp_sphereHeight (m := m) w ε y).mdifferentiableAt (by simp)
  rw [mem_criticalPoints, mvfderiv_comp_fst_add_comp_snd_eq_zero_iff
    ((contMDiff_sphereHeight (m := 1) v x).mdifferentiableAt one_ne_zero) hy,
    ← mem_criticalPoints, ← mem_criticalPoints,
    mem_criticalPoints_scalar_comp_iff ((contMDiff_sphereHeight (m := 1) w y).mdifferentiableAt
      one_ne_zero) (by simpa using hε), criticalPoints_sphereHeight, criticalPoints_sphereHeight]
  rfl

/-- `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫` is a Morse function on `Sⁿ × Sᵐ` for `ε ≠ 0`. -/
theorem isMorse_sphereHeight_comp_fst_add_mul_comp_snd (v : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) {ε : ℝ} (hε : ε ≠ 0) :
    IsMorse ((𝓡 n).prod (𝓡 m))
      (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd) :=
  (isMorse_sphereHeight v).comp_fst_add_comp_snd ((isMorse_sphereHeight (n := m) w).scalar_comp
    (fun _ ↦ (contDiff_const.mul contDiff_id).contDiffAt) fun _ ↦ by simpa using hε)

/-- **The Morse indices** of `(x, y) ↦ ⟪x, v⟫ + ε ⟪y, w⟫` on `Sⁿ × Sᵐ`, for `ε > 0`: at a pair of
poles the index is the sum of the indices of the two heights, so the indices at `(v, w)`,
`(v, -w)`, `(-v, w)` and `(-v, -w)` are `n + m`, `n`, `m` and `0`. -/
theorem manifoldMorseIndex_sphereHeight_comp_fst_add_mul_comp_snd (v x : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) {ε : ℝ} (hε : 0 < ε) {y : sphere (0 : E') 1} (hy : y = w ∨ y = -w) :
    manifoldMorseIndex ((𝓡 n).prod (𝓡 m))
        (sphereHeight v ∘ Prod.fst + ((ε * ·) ∘ sphereHeight w) ∘ Prod.snd) (x, y) =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x +
        manifoldMorseIndex (𝓡 m) (sphereHeight w) y := by
  have hyc : y ∈ criticalPoints (𝓡 m) (sphereHeight w) := by
    rw [criticalPoints_sphereHeight]
    exact hy
  rw [manifoldMorseIndex_comp_fst_add_comp_snd
    (contMDiff_sphereHeight (m := 2) v x).contDiffAt_comp_extChartAt_symm
    ((contMDiff_mul_comp_sphereHeight (m := m) w ε).of_le (by simp)
      y).contDiffAt_comp_extChartAt_symm,
    manifoldMorseIndex_scalar_comp_of_pos (φ := (ε * ·)) (contMDiff_sphereHeight (m := 2) w y)
      (contDiff_const.mul contDiff_id).contDiffAt hyc (by simpa using hε)]

/-- **The sum of two height functions is a Morse function on a product of spheres.** -/
theorem isMorse_sphereHeight_comp_fst_add_comp_snd (v : sphere (0 : E) 1)
    (w : sphere (0 : E') 1) :
    IsMorse ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) := by
  simpa [Function.comp_def] using
    isMorse_sphereHeight_comp_fst_add_mul_comp_snd (n := n) (m := m) v w one_ne_zero

/-- The critical points of the sum of two height functions on a product of spheres are the four
pairs of poles. -/
@[simp]
theorem mvfderiv_sphereHeight_comp_fst_add_comp_snd_eq_zero_iff (v x : sphere (0 : E) 1)
    (w y : sphere (0 : E') 1) :
    mvfderiv ((𝓡 n).prod (𝓡 m)) (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) (x, y) =
        0 ↔
      (x = v ∨ x = -v) ∧ (y = w ∨ y = -w) := by
  simpa [mem_criticalPoints, Function.comp_def] using Set.ext_iff.1
    (criticalPoints_sphereHeight_comp_fst_add_mul_comp_snd (n := n) (m := m) v w one_ne_zero)
    (x, y)

/-- The Morse index of the sum of two height functions on a product of spheres is the sum of the
indices of the two height functions; at the four critical points these are `n + m`, `n`, `m` and
`0`. -/
@[simp]
theorem manifoldMorseIndex_sphereHeight_comp_fst_add_comp_snd (v x : sphere (0 : E) 1)
    (w y : sphere (0 : E') 1) :
    manifoldMorseIndex ((𝓡 n).prod (𝓡 m))
        (sphereHeight v ∘ Prod.fst + sphereHeight w ∘ Prod.snd) (x, y) =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x + manifoldMorseIndex (𝓡 m) (sphereHeight w) y :=
  manifoldMorseIndex_comp_fst_add_comp_snd
    (contMDiff_sphereHeight (m := 2) v x).contDiffAt_comp_extChartAt_symm
    (contMDiff_sphereHeight (m := 2) w y).contDiffAt_comp_extChartAt_symm

end TauCeti

end
