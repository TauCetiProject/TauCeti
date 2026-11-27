/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Graph
import TauCeti.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
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
`y ↦ r - √(r² - ‖y‖²)`. Modified outside the cylinder by a bump function, this graph is smooth on
all of `E` (`TauCeti.exists_affineIsometryEquiv_contDiff_ball_iff`), as the boundary charts of the
`W^{2,p}` theory of the Dirichlet problem require. It vanishes with its derivative at the origin,
so `TauCeti.isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero` applies.

The planar case `E = ℝ` is the disc, whose Sobolev consequences are recorded in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.Disc`.

## Main declarations

* `TauCeti.exists_affineIsometryEquiv_contDiff_ball_iff`: the smooth boundary charts of a ball.
* `TauCeti.isLipschitzDomainWith_ball`: a ball of positive radius is a Lipschitz domain with
  every positive constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open scoped NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The boundary charts of a ball.** Let `x` be a frontier point of the ball `B(c, r)`, `r > 0`,
in `ℝ × E`. There is a rigid motion `e` with `e x = 0` and a smooth function `φ` on `E` with
`φ 0 = 0` and `Dφ(0) = 0` such that, in the normal cylinder of radii `r / 2`, the image of the ball
under `e` is the region `φ z' < z₁` above the graph of `φ`. -/
theorem exists_affineIsometryEquiv_contDiff_ball_iff (c : WithLp 2 (ℝ × E)) {r : ℝ} (hr : 0 < r)
    {x : WithLp 2 (ℝ × E)} (hx : x ∈ frontier (ball c r)) :
    ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
      e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ ∞ φ ∧ fderiv ℝ φ 0 = 0 ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ ball c r ↔ φ z.snd < z.fst) := by
  have hxc : ‖c - x‖ = r := by
    rw [← dist_eq_norm, dist_comm]
    exact frontier_ball_subset_sphere hx
  -- The first basis vector `u` and the inward unit normal `v` at `x`.
  set u : WithLp 2 (ℝ × E) := WithLp.toLp 2 ((1 : ℝ), (0 : E))
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
  -- The lower hemisphere `y ↦ r - √(r² - ‖y‖²)`, cut off by a bump function `ψ` equal to `1` on
  -- the closed ball of radius `r / 2` and supported in the ball of radius `r`.
  let ψ : ContDiffBump (0 : E) := ⟨r / 2, r, by positivity, by linarith⟩
  have hpos : ∀ y : E, r ^ 2 - ψ y * ‖y‖ ^ 2 ≠ 0 := fun y => by
    by_cases hy : ‖y‖ < r
    · nlinarith [ψ.le_one (x := y), ψ.nonneg (x := y), norm_nonneg y]
    · rw [ψ.zero_of_le_dist (by simpa using not_lt.1 hy)]
      simpa using hr.ne'
  have hloc : (fun y => r - √(r ^ 2 - ψ y * ‖y‖ ^ 2)) =ᶠ[nhds 0]
      fun y => r - √(r ^ 2 - ‖y‖ ^ 2) := by
    filter_upwards [closedBall_mem_nhds (0 : E) (by positivity : (0 : ℝ) < r / 2)] with y hy
    rw [ψ.one_of_mem_closedBall hy, one_mul]
  refine ⟨e, fun y => r - √(r ^ 2 - ψ y * ‖y‖ ^ 2), r / 2, r / 2, by simp [e], by positivity,
    by positivity, by simp [hr.le], contDiff_const.sub ((contDiff_const.sub
      (ψ.contDiff.mul (contDiff_norm_sq ℝ))).sqrt hpos), ?_, fun z hz => ?_⟩
  · rw [hloc.fderiv_eq]
    simpa using ((hasFDerivAt_sqrt_sub_norm_sq (x := (0 : E)) (a := r ^ 2)
      (by simp [hr.ne'])).const_sub r).fderiv
  -- Translated by `r • u`, the ball becomes `ball 0 r`, cut out by `TauCeti.ballGraph`.
  have hball := symm_mem_ball_iff_ballGraph_lt (e := AffineIsometryEquiv.vaddConst ℝ (r • u))
    (ρ := r) (a := r / 2) (b := r / 2) hr.le (by simp [u]; linarith) (by simp [u]; linarith) hz
  rw [mem_normalCylinder] at hz
  rw [mem_ball, dist_eq_norm, he, LinearIsometryEquiv.norm_map]
  dsimp only
  rw [ψ.one_of_mem_closedBall (by simpa using hz.2.2.le), one_mul]
  simpa [u, ballGraph_def, min_eq_left (hz.2.2.trans (half_lt_self hr)).le] using hball

/-- **Balls are Lipschitz domains.** An open ball of positive radius in `WithLp 2 (ℝ × E)` is a
Lipschitz domain with every positive Lipschitz constant: its boundary is a `C¹` sphere. -/
theorem isLipschitzDomainWith_ball (c : WithLp 2 (ℝ × E)) {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hL : 0 < L) : (ball c r).IsLipschitzDomainWith L := by
  refine isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero isOpen_ball hL fun x hx ↦ ?_
  obtain ⟨e, φ, h₀, r₀, hex, hh₀, hr₀, hφ0, hφ, hdφ, hgraph⟩ :=
    exists_affineIsometryEquiv_contDiff_ball_iff c hr hx
  exact ⟨e, φ, h₀, r₀, hex, hh₀, hr₀, hφ0, (hφ.of_le (by simp)).contDiffAt, hdφ, hgraph⟩

end TauCeti
