/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Hersch's maps in stereographic coordinates

Adapted from Giada Franz's local formalization of Hersch's balancing lemma.

Write `a = ρ u` with `u` a unit vector and `0 ≤ ρ < 1`. Hersch's map `T_a`
(`TauCeti.herschMap`) fixes the two points `±u` of the unit sphere, and under the stereographic
projection from `-u` (Mathlib's `stereographic`) it is the dilation of the hyperplane `uᗮ` by the
factor `√((1 - ρ) / (1 + ρ))`. In particular `T_a` is a conformal diffeomorphism of the sphere.

## Main results

* `TauCeti.herschMap_smul_self`, `TauCeti.herschMap_smul_neg_self`: `T_(ρu)` fixes `u` and `-u`.
* `TauCeti.stereographic_herschHomeomorph`: the stereographic conjugate of `T_(ρu)` is the
  dilation by `√((1 - ρ) / (1 + ρ))`.

## References

* J. Hersch, *Quatre propriétés isopérimétriques de membranes sphériques homogènes*,
  C. R. Acad. Sci. Paris Sér. A-B 270 (1970), A1645–A1648.
-/

public section

open Metric RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E} {ρ : ℝ}

/-- `T_(ρu)` fixes `u`. -/
theorem herschMap_smul_self (hu : ‖u‖ = 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    herschMap (ρ • u) u = u := by
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - ρ ^ 2)
  have hs0 : 0 ≤ √(1 - ρ ^ 2) := Real.sqrt_nonneg _
  simp only [herschMap_def, norm_smul_of_nonneg hρ0, hu, mul_one, real_inner_smul_left,
    real_inner_self_eq_norm_sq, smul_smul, ← add_smul]
  set s := √(1 - ρ ^ 2)
  convert one_smul ℝ u using 2
  field_simp
  linear_combination hs

/-- `T_(ρu)` fixes `-u`, for `ρ < 1`. -/
theorem herschMap_smul_neg_self (hu : ‖u‖ = 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    herschMap (ρ • u) (-u) = -u := by
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - ρ ^ 2)
  have hs0 : 0 ≤ √(1 - ρ ^ 2) := Real.sqrt_nonneg _
  have hρ' : 1 + -ρ ≠ 0 := by linarith
  simp only [herschMap_def, norm_smul_of_nonneg hρ0, hu, mul_one, inner_neg_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, smul_smul, smul_neg, ← neg_smul, ← add_smul]
  set s := √(1 - ρ ^ 2)
  convert neg_one_smul ℝ u using 2
  field_simp
  linear_combination -hs

/-- **Hersch's maps in stereographic coordinates.** Under the stereographic projection from `-u`,
the map `T_(ρu)` of the unit sphere becomes the dilation by `√((1 - ρ) / (1 + ρ))`. -/
theorem stereographic_herschHomeomorph (hu : ‖u‖ = 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (x : sphere (0 : E) 1) :
    stereographic (v := -u) (by rwa [norm_neg])
        (herschHomeomorph (a := ρ • u) (by simpa [norm_smul_of_nonneg hρ0, hu] using hρ1)
          x) =
      √((1 - ρ) / (1 + ρ)) • stereographic (v := -u) (by rwa [norm_neg]) x := by
  have hu' : ‖-u‖ = 1 := by rwa [norm_neg]
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - ρ ^ 2)
  have hspos : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  set w := ⟪u, (x : E)⟫ with hw
  have hD : 0 < 1 + ρ * w := by
    have := one_add_inner_pos (a := ρ • u) (x := x)
      (by simpa [norm_smul_of_nonneg hρ0, hu] using hρ1) hx
    rwa [real_inner_smul_left] at this
  have h1ρ : 0 < 1 + ρ := by linarith
  have hlam : √((1 - ρ) / (1 + ρ)) = √(1 - ρ ^ 2) / (1 + ρ) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (div_nonneg (by linarith) h1ρ.le) (by positivity)]
    field_simp
    linear_combination -hs
  apply Subtype.ext
  simp only [stereographic_apply, Submodule.coe_smul, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu', coe_herschHomeomorph, herschMap_def,
    norm_smul_of_nonneg hρ0, hu, mul_one, real_inner_smul_left, ← hw, hlam]
  simp only [inner_neg_left, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu,
    ← hw, neg_neg, sub_neg_eq_add, smul_neg, neg_smul]
  set s := √(1 - ρ ^ 2)
  have hs1 : 1 + s ≠ 0 := by positivity
  have hden : 1 - (1 + ρ * w)⁻¹ * (s * -w + (ρ * w / (1 + s) + 1) * (ρ * -1 ^ 2)) =
      (1 + ρ) * (1 + w) / (1 + ρ * w) := by
    field_simp
    linear_combination w * hs
  rw [hden]
  by_cases hw1 : 1 + w = 0
  · simp [hw1]
  · match_scalars <;> field_simp
    ring

end TauCeti
