/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Balls are Lipschitz domains

An open Euclidean ball in `WithLp 2 (ℝ × E)` is a Lipschitz domain with every positive Lipschitz
constant. At a boundary point `x` of `ball c r`, the rigid coordinates translate `x` to the
origin and then apply the reflection that sends the inward unit normal `r⁻¹ • (c - x)` to the
first basis vector `(1, 0)`. In these coordinates the ball is the ball of radius `r` about
`(r, 0)`, which inside the cylinder `normalCylinder r r` is the region above the lower hemisphere
`y ↦ r - √(r² - ‖y‖²)`. That graph vanishes with its derivative at the origin, so
`TauCeti.isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero` applies.

The planar case `E = ℝ` is the disc, whose Sobolev consequences are recorded in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.Disc`.

## Main declarations

* `TauCeti.isLipschitzDomainWith_ball`: a ball of positive radius is a Lipschitz domain with
  every positive constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In the model `WithLp 2 (ℝ × E)`, inside the cylinder `normalCylinder r r`, the ball of radius
`r` about `(r, 0)` is the region above the lower hemisphere `y ↦ r - √(r² - ‖y‖²)`. -/
private theorem norm_sub_smul_lt_iff {r : ℝ} {z : WithLp 2 (ℝ × E)}
    (hz : z ∈ normalCylinder r r) :
    ‖z - r • WithLp.toLp 2 ((1 : ℝ), (0 : E))‖ < r ↔ r - √(r ^ 2 - ‖z.snd‖ ^ 2) < z.fst := by
  rw [mem_normalCylinder] at hz
  obtain ⟨-, hzr, hzy⟩ := hz
  have hr : 0 < r := (norm_nonneg _).trans_lt hzy
  have hnorm : ‖z - r • WithLp.toLp 2 ((1 : ℝ), (0 : E))‖ ^ 2 =
      (r - z.fst) ^ 2 + ‖z.snd‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.sub_fst, WithLp.sub_snd, WithLp.smul_fst, WithLp.smul_snd,
      WithLp.toLp_fst, WithLp.toLp_snd, smul_eq_mul, mul_one, smul_zero, sub_zero,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [← sq_lt_sq₀ (norm_nonneg _) hr.le, hnorm, sub_lt_comm,
    Real.lt_sqrt (sub_pos.2 hzr).le]
  constructor <;> intro h <;> linarith

/-- The lower hemisphere `y ↦ r - √(r² - ‖y‖²)` has derivative zero at the origin. -/
private theorem hasFDerivAt_hemisphere {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (fun y : E ↦ r - √(r ^ 2 - ‖y‖ ^ 2)) (0 : E →L[ℝ] ℝ) 0 := by
  have h := ((hasStrictFDerivAt_id (𝕜 := ℝ) (0 : E)).hasFDerivAt.norm_sq.const_sub
    (r ^ 2)).sqrt (by simp [hr.ne'])
  simpa using h.const_sub r

/-- **Balls are Lipschitz domains.** An open ball of positive radius in `WithLp 2 (ℝ × E)` is a
Lipschitz domain with every positive Lipschitz constant: its boundary is a `C¹` sphere. -/
theorem isLipschitzDomainWith_ball (c : WithLp 2 (ℝ × E)) {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hL : 0 < L) : (ball c r).IsLipschitzDomainWith L := by
  refine isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero isOpen_ball hL fun x hx ↦ ?_
  have hxc : ‖c - x‖ = r := by
    rw [← dist_eq_norm, dist_comm]
    exact frontier_ball_subset_sphere hx
  -- The first basis vector `u` and the inward unit normal `v` at `x`.
  set u : WithLp 2 (ℝ × E) := WithLp.toLp 2 ((1 : ℝ), (0 : E)) with hu_def
  set v : WithLp 2 (ℝ × E) := r⁻¹ • (c - x) with hv_def
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = ‖u‖ := by
    rw [hu, hv_def, norm_smul, hxc, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ hr.ne']
  set R := (ℝ ∙ (v - u))ᗮ.reflection
  have hRu : R u = v := by
    rw [← Submodule.reflection_sub hv, Submodule.reflection_reflection]
  let e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) :=
    (AffineIsometryEquiv.vaddConst ℝ x).symm.trans R.toAffineIsometryEquiv
  have he : ∀ z, e.symm z - c = R (z - r • u) := by
    intro z
    have hsymm : e.symm z = R z + x := by
      rw [e.symm_apply_eq]
      simp [e, AffineIsometryEquiv.coe_trans, R, Submodule.reflection_reflection]
    rw [hsymm, map_sub, map_smul, hRu, hv_def, smul_inv_smul₀ hr.ne']
    abel
  refine ⟨e, fun y ↦ r - √(r ^ 2 - ‖y‖ ^ 2), r, r, by simp [e], hr, hr, by simp [hr.le],
    contDiffAt_const.sub ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt
      (by simp [hr.ne'])), (hasFDerivAt_hemisphere hr).fderiv, fun z hz ↦ ?_⟩
  rw [mem_ball, dist_eq_norm, he, LinearIsometryEquiv.norm_map]
  exact norm_sub_smul_lt_iff hz

end TauCeti
