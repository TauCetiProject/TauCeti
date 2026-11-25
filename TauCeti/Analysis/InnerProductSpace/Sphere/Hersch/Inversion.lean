/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Basic
import TauCeti.Analysis.Real.Sqrt

/-!
# Hersch transformations as translated inversions

On the unit sphere, Hersch's map agrees with a spherical inversion followed by a translation
wherever `1 + ⟪a, x⟫ ≠ 0`. The inversion's squared radius-to-distance ratio is
`√(1 - ‖a‖²) / (1 + ⟪a, x⟫)`. For `‖a‖ < 1` this is the positive length factor used to
track round metric distortion when balancing sphere-valued test functions.

The ambient formula uses `TauCeti.herschMap_def`.

## References

* J. Hersch, *Quatre propriétés isopérimétriques de membranes sphériques homogènes*,
  C. R. Acad. Sci. Paris Sér. A-B 270 (1970), A1645–A1648.
-/

public noncomputable section

open EuclideanGeometry Metric
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared radius-to-distance ratio of the inversion representing Hersch's map equals
its length factor. This identity holds for every parameter, including the boundary. -/
theorem inversion_factor_eq_hersch_length_factor {a x : E} (hx : ‖x‖ = 1) :
    let s := √(1 - ‖a‖ ^ 2)
    let b := (1 + s)⁻¹ • a
    (√(1 - ‖b‖ ^ 2) / dist x (-b)) ^ 2 = s / (1 + ⟪a, x⟫_ℝ) := by
  dsimp only
  by_cases ha : ‖a‖ < 1
  swap
  · have hs : √(1 - ‖a‖ ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith [le_of_not_gt ha])
    simp [hs]
  set s := √(1 - ‖a‖ ^ 2)
  set b := (1 + s)⁻¹ • a with hb
  have hs₀ : 0 < s := Real.sqrt_pos.2 (by nlinarith [norm_nonneg a])
  have hs₁ : 0 < 1 + s := by positivity
  have hd : 0 < 1 + ⟪a, x⟫_ℝ := one_add_inner_pos ha hx.le
  have hb₂ : ‖b‖ ^ 2 = (1 - s) / (1 + s) := by
    simpa [b, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs₁.le),
      div_eq_inv_mul] using
      Real.sq_div_one_add_sqrt_one_sub_sq (by simpa using ha.le : |‖a‖| ≤ 1)
  have hr : 1 - ‖b‖ ^ 2 = 2 * s / (1 + s) := by
    rw [hb₂]
    field_simp [hs₁.ne']
    ring
  have hd₂ : ‖x + b‖ ^ 2 = 2 * (1 + ⟪a, x⟫_ℝ) / (1 + s) := by
    rw [norm_add_sq_real, hx, hb₂, hb, real_inner_smul_right, real_inner_comm x a]
    field_simp
    ring
  have hr₀ : 0 ≤ 1 - ‖b‖ ^ 2 := by rw [hr]; positivity
  rw [div_pow, Real.sq_sqrt hr₀, dist_eq_norm, sub_neg_eq_add, hr, hd₂]
  field_simp

/-- On the unit sphere, Hersch's map is a spherical inversion followed by a translation
whenever its denominator is nonzero. This includes unit parameters away from the antipode. -/
theorem herschMap_eq_add_inversion {a x : E} (hd : 1 + ⟪a, x⟫_ℝ ≠ 0) (hx : ‖x‖ = 1) :
    let b := (1 + √(1 - ‖a‖ ^ 2))⁻¹ • a
    herschMap a x = 2 • b + inversion (-b) (√(1 - ‖b‖ ^ 2)) x := by
  dsimp only
  set s := √(1 - ‖a‖ ^ 2) with hs
  set b := (1 + s)⁻¹ • a with hb
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hscale : (√(1 - ‖b‖ ^ 2) / dist x (-b)) ^ 2 = s / (1 + ⟪a, x⟫_ℝ) :=
    inversion_factor_eq_hersch_length_factor hx
  have hcoeff : (1 + ⟪a, x⟫_ℝ)⁻¹ * (⟪a, x⟫_ℝ / (1 + s) + 1) =
      (1 + s)⁻¹ + (s / (1 + ⟪a, x⟫_ℝ)) * (1 + s)⁻¹ := by
    field_simp [hd]
    ring
  simp only [inversion, vsub_eq_sub, vadd_eq_add, sub_neg_eq_add, herschMap_def, ← hs, two_nsmul]
  rw [hscale, hb]
  simp only [smul_add, smul_smul, hcoeff, div_eq_inv_mul s]
  module

end TauCeti
