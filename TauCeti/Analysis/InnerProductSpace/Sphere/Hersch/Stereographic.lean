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

Write `a = ρ u` with `u` a unit vector and `-1 < ρ < 1`. Hersch's map `T_a`
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

/-- **Hersch's maps in stereographic coordinates.** Under the stereographic projection from `-u`,
the map `T_(ρu)` of the unit sphere becomes the dilation by `√((1 - ρ) / (1 + ρ))`. -/
theorem stereographic_herschHomeomorph (hu : ‖u‖ = 1) (hρ0 : -1 < ρ) (hρ1 : ρ < 1)
    (x : sphere (0 : E) 1) :
    stereographic (v := -u) (by rwa [norm_neg])
        (herschHomeomorph (a := ρ • u) (by simpa [norm_smul, hu, abs_lt] using And.intro hρ0 hρ1)
          x) =
      √((1 - ρ) / (1 + ρ)) • stereographic (v := -u) (by rwa [norm_neg]) x := by
  have hu' : ‖-u‖ = 1 := by rwa [norm_neg]
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - ρ ^ 2)
  have hspos : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hx : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.1 x.property
  set w := ⟪u, (x : E)⟫ with hw
  have hD : 0 < 1 + ρ * w := by
    have := one_add_inner_pos (a := ρ • u) (x := x)
      (by simpa [norm_smul, hu, abs_lt] using And.intro hρ0 hρ1) hx.le
    rwa [real_inner_smul_left] at this
  have h1ρ : 0 < 1 + ρ := by linarith
  have hlam : √((1 - ρ) / (1 + ρ)) = √(1 - ρ ^ 2) / (1 + ρ) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (div_nonneg (by linarith) h1ρ.le) (by positivity)]
    field_simp
    linear_combination -hs
  have hs1 : 1 + √(1 - ρ ^ 2) ≠ 0 := by positivity
  have hden : 1 - ⟪-u, herschMap (ρ • u) (x : E)⟫ =
      (1 + ρ) * (1 + w) / (1 + ρ * w) := by
    simp only [herschMap_def, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs, inner_neg_left,
      real_inner_smul_left, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, ← hw]
    field_simp
    linear_combination w * hs
  apply Subtype.ext
  simp only [stereographic_apply, Submodule.coe_smul, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu', coe_herschHomeomorph]
  rw [hden]
  simp only [herschMap_def, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
    real_inner_smul_left, ← hw, hlam,
    inner_neg_left, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    neg_neg, sub_neg_eq_add, smul_neg, neg_smul]
  by_cases hw1 : 1 + w = 0
  · simp [hw1]
  · match_scalars <;> field_simp
    ring

end TauCeti
