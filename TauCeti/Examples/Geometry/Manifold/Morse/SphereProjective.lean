/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Geometry.Manifold.Morse.Projectivization
import TauCeti.Geometry.Manifold.Morse.Reeb
import TauCeti.Geometry.Manifold.Morse.Sphere.Degenerate
import TauCeti.Geometry.Manifold.Morse.Sphere.Saddle
import TauCeti.Geometry.Manifold.Morse.TwoCriticalPoints

/-!
# Examples: Morse functions on the sphere `S²` and the projective line `ℂℙ¹`

This file tests the sphere theorems and the critical counts of Morse functions on three explicit
functions on `S²`, the unit sphere of `EuclideanSpace ℝ (Fin 3)`, and one on `ℂℙ¹`.

* **The height.** The height `h = ⟪·, v⟫` (`TauCeti.sphereHeight`) has exactly two critical
  points, the poles, of indices `0` and `2`, both nondegenerate. So Reeb's theorem for Morse
  functions (`TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`) applies to
  it.
* **A degenerate function with two critical points.** The function `h - h³ / 3` still has only the
  poles as critical points, but both critical Hessians vanish, so it is not a Morse function and
  Reeb's theorem does not apply. The sphere theorem for smooth functions with two possibly
  degenerate critical points (`TauCeti.nonempty_homeomorph_sphere_of_two_criticalPoints`) does.
* **Asymmetric critical counts.** For orthogonal unit vectors `u`, `v` the function
  `f = -(hᵤ² + hᵥ)` has two minima, one saddle and one maximum, so its critical counts in the
  indices `0, 1, 2` are `(2, 1, 1)`, while those of `-f` are `(1, 1, 2) = (c₂, c₁, c₀)`. The
  counts of a single Morse function need not be symmetric under `j ↦ 2 - j`. Both signed counts
  `c₀ - c₁ + c₂` equal `2`, the Euler characteristic of `S²` (`TauCeti.eulerChar_sphere`).
* **The projective line.** The moment function `[z₀ : z₁] ↦ ‖z₁‖² / (‖z₀‖² + ‖z₁‖²)` on `ℂℙ¹`
  (`TauCeti.projectiveMomentFunction` with the weights `(0, 1)`) is well defined, its
  denominator being positive at every nonzero vector. Its critical values are `0` and `1`,
  attained at `[1 : 0]` and `[0 : 1]` with Morse indices `0` and `2`, and it has no other critical
  point.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1 and Remark 1 after it.
-/

open Metric Module Set Projectivization
open scoped Manifold RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-! ### The height on `S²` -/

-- The height on `S²` is a Morse function whose critical points are the two poles, the south pole
-- of index `0` and the north pole of index `2`, both nondegenerate.
example (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    IsMorse (𝓡 2) (sphereHeight v) ∧ criticalPoints (𝓡 2) (sphereHeight v) = {v, -v} ∧
      IsManifoldNondegenerateCriticalPoint (𝓡 2) (sphereHeight v) (-v) ∧
      IsManifoldNondegenerateCriticalPoint (𝓡 2) (sphereHeight v) v ∧
      manifoldMorseIndex (𝓡 2) (sphereHeight v) (-v) = 0 ∧
      manifoldMorseIndex (𝓡 2) (sphereHeight v) v = 2 :=
  ⟨isMorse_sphereHeight v, criticalPoints_sphereHeight v,
    isManifoldNondegenerateCriticalPoint_sphereHeight_neg v,
    isManifoldNondegenerateCriticalPoint_sphereHeight_self v,
    manifoldMorseIndex_sphereHeight_neg v, manifoldMorseIndex_sphereHeight_self v⟩

-- So the height has exactly two critical points, and Reeb's theorem for Morse functions applies
-- to it.
example (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1))) 1) :=
  (isMorse_sphereHeight v).nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two <| by
    rw [totalCriticalCount_def, criticalPoints_sphereHeight,
      encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]

/-! ### The degenerate function `h - h³ / 3` on `S²` -/

-- The function `h - h³ / 3` has the same critical points as the height, but both its critical
-- Hessians vanish, so it is not a Morse function and Reeb's theorem does not apply to it.
example (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    criticalPoints (𝓡 2) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) = {v, -v} ∧
      criticalHessian (𝓡 2) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) v = 0 ∧
      criticalHessian (𝓡 2) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) (-v) = 0 ∧
      ¬IsMorse (𝓡 2) ((fun t : ℝ ↦ t - t ^ 3 / 3) ∘ sphereHeight v) :=
  ⟨criticalPoints_cubic_comp_sphereHeight v, criticalHessian_cubic_comp_sphereHeight_self v,
    criticalHessian_cubic_comp_sphereHeight_neg v,
    not_isMorse_cubic_comp_sphereHeight two_ne_zero v⟩

-- The sphere theorem for smooth functions with exactly two critical points, of any degeneracy,
-- applies to `h - h³ / 3`.
example (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1))) 1) :=
  nonempty_homeomorph_sphere_of_two_criticalPoints
    ((contDiff_id.sub ((contDiff_id.pow 3).div_const 3)).comp_contMDiff (contMDiff_sphereHeight v))
    (totalCriticalCount_cubic_comp_sphereHeight v)

/-! ### Two minima, a saddle and a maximum on `S²` -/

section Saddle

variable {u v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}

-- For orthogonal unit vectors `u`, `v`, the function `-(hᵤ² + hᵥ)` has two critical points of
-- index `0`, one of index `1` and one of index `2`.
example (huv : ⟪(u : EuclideanSpace ℝ (Fin 3)), v⟫ = 0) :
    criticalCount (𝓡 2) (-(sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v)) 0 = 2 ∧
      criticalCount (𝓡 2) (-(sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v)) 1 = 1 ∧
      criticalCount (𝓡 2) (-(sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v)) 2 = 1 := by
  simp only [criticalCount_neg_sphereHeight_sq_add_smul_sphereHeight huv le_rfl one_ne_zero
    (by norm_num)]
  norm_num

-- Its negative `hᵤ² + hᵥ` has the reversed counts: one critical point of index `0`, one of index
-- `1` and two of index `2`.
example (huv : ⟪(u : EuclideanSpace ℝ (Fin 3)), v⟫ = 0) :
    criticalCount (𝓡 2) (sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v) 0 = 1 ∧
      criticalCount (𝓡 2) (sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v) 1 = 1 ∧
      criticalCount (𝓡 2) (sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v) 2 = 2 := by
  simp only [criticalCount_sphereHeight_sq_add_smul_sphereHeight huv le_rfl one_ne_zero
    (by norm_num)]
  norm_num

-- Its signed count `c₀ - c₁ + c₂ = 2 - 1 + 1` is the Euler characteristic of `S²`.
example (huv : ⟪(u : EuclideanSpace ℝ (Fin 3)), v⟫ = 0) :
    ∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i *
        (criticalCount (𝓡 2) (-(sphereHeight u ^ 2 + (1 : ℝ) • sphereHeight v)) i).toNat =
      eulerChar (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  rw [eulerChar_sphere (n := 2) (by simp)]
  simp only [criticalCount_neg_sphereHeight_sq_add_smul_sphereHeight huv le_rfl one_ne_zero
    (by norm_num)]
  norm_num [Finset.sum_range_succ]

end Saddle

/-! ### The moment function on `ℂℙ¹` -/

section ProjectiveLine

-- With the standard weights `(0, 1)`, the moment function on `ℂℙ¹` sends `[z₀ : z₁]` to
-- `‖z₁‖² / (‖z₀‖² + ‖z₁‖²)`, whose denominator is positive at every nonzero vector.
example (z : Fin 2 → ℂ) (hz : z ≠ 0) :
    projectiveMomentFunction ℂ (fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) (mk ℂ z hz) =
        ‖z 1‖ ^ 2 / (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2) ∧
      0 < ‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 := by
  refine ⟨by simp [Fin.sum_univ_two], ?_⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
  have := norm_pos_iff.2 hi
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at this <;> positivity

-- Its critical values are `0` and `1`.
example :
    projectiveMomentFunction ℂ (fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) ''
        criticalPoints 𝓘(ℝ, Fin 1 → ℂ) (projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) =
      {0, 1} := by
  rw [image_criticalPoints_projectiveMomentFunction]
  ext
  simp [Fin.exists_fin_two, eq_comm]

-- Its critical points are `[1 : 0]`, of index `0`, and `[0 : 1]`, of index `2`.
example :
    criticalPoints 𝓘(ℝ, Fin 1 → ℂ) (projectiveMomentFunction ℂ fun i : Fin 2 ↦ ((i : ℕ) : ℝ)) =
        {mk ℂ (Pi.single 0 1 : Fin 2 → ℂ) (by simp),
          mk ℂ (Pi.single 1 1 : Fin 2 → ℂ) (by simp)} ∧
      manifoldMorseIndex 𝓘(ℝ, Fin 1 → ℂ) (projectiveMomentFunction ℂ fun i ↦ ((i : ℕ) : ℝ))
        (mk ℂ (Pi.single 0 1 : Fin 2 → ℂ) (by simp)) = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, Fin 1 → ℂ) (projectiveMomentFunction ℂ fun i ↦ ((i : ℕ) : ℝ))
        (mk ℂ (Pi.single 1 1 : Fin 2 → ℂ) (by simp)) = 2 := by
  refine ⟨?_, manifoldMorseIndex_projectiveMomentFunction_natCast_complex 0,
    manifoldMorseIndex_projectiveMomentFunction_natCast_complex 1⟩
  rw [criticalPoints_projectiveMomentFunction (w := fun i : Fin 2 ↦ ((i : ℕ) : ℝ))
    fun _ _ h ↦ Fin.val_injective (Nat.cast_injective h)]
  ext
  simp [Fin.exists_fin_two, eq_comm]

end ProjectiveLine

end TauCeti
