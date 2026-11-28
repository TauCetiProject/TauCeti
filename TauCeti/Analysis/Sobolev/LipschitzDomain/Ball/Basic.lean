/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Graph
import TauCeti.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.BumpFunction.Basic

/-!
# Balls are Lipschitz domains

An open Euclidean ball in `WithLp 2 (ℝ × E)` is a Lipschitz domain with every positive Lipschitz
constant. At a boundary point `x` of `ball c r`, the rigid coordinates translate `x` to the
origin and then apply the reflection that sends the inward unit normal `r⁻¹ • (c - x)` to the
first basis vector `(1, 0)`. In these coordinates the ball is the ball of radius `r` about
`(r, 0)`, which inside the cylinder `normalCylinder r r` is the region above the lower hemisphere
`y ↦ r - √(r² - ‖y‖²)`. That graph vanishes with its derivative at the origin, so
`TauCeti.isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero` applies.

The same coordinates give smooth boundary charts: near the origin the hemisphere agrees with a
function of class `Cᵏ` on all of `E` for every `k`, obtained by composing it with a smooth map that
is the identity near `0` and takes values in `ball 0 (r / 2)`, so that the square root stays away
from `0`. These are the global `C²` graph charts that the
`W^{2,p}` Dirichlet theory on domains with `C²` boundary takes as its boundary hypothesis.

The planar case `E = ℝ` is the disc, whose Sobolev consequences are recorded in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.Disc`.

## Main declarations

* `TauCeti.isLipschitzDomainWith_ball`: a ball of positive radius is a Lipschitz domain with
  every positive constant.
* `TauCeti.exists_contDiff_graph_of_mem_frontier_ball`: at every frontier point a ball is the region
  above the graph of a `Cᵏ` function in rigid coordinates.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Rigid coordinates at a boundary point `x` of `ball c r`: they send `x` to the origin, and inside
the cylinder `normalCylinder r r` they show the ball as the region above the lower hemisphere
`y ↦ r - √(r² - ‖y‖²)`. -/
private theorem exists_affineIsometryEquiv_symm_mem_ball_iff (c : WithLp 2 (ℝ × E)) {r : ℝ}
    (hr : 0 < r) {x : WithLp 2 (ℝ × E)} (hx : x ∈ frontier (ball c r)) :
    ∃ e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E), e x = 0 ∧
      ∀ z ∈ normalCylinder r r, (e.symm z ∈ ball c r ↔ r - √(r ^ 2 - ‖z.snd‖ ^ 2) < z.fst) := by
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
  refine ⟨e, by simp [e], fun z hz ↦ ?_⟩
  -- Translated by `r • u`, the ball becomes `ball 0 r`, cut out by `TauCeti.ballGraph`.
  have hball := symm_mem_ball_iff_ballGraph_lt (e := AffineIsometryEquiv.vaddConst ℝ (r • u))
    (ρ := r) hr.le (by simp [u]) (by simp [u]) hz
  rw [mem_normalCylinder] at hz
  rw [mem_ball, dist_eq_norm, he, LinearIsometryEquiv.norm_map]
  simpa [u, ballGraph_def, min_eq_left hz.2.2.le] using hball

/-- **Balls are Lipschitz domains.** An open ball of positive radius in `WithLp 2 (ℝ × E)` is a
Lipschitz domain with every positive Lipschitz constant: its boundary is a `C¹` sphere. -/
theorem isLipschitzDomainWith_ball (c : WithLp 2 (ℝ × E)) {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hL : 0 < L) : (ball c r).IsLipschitzDomainWith L := by
  refine isLipschitzDomainWith_of_contDiffAt_fderiv_eq_zero isOpen_ball hL fun x hx ↦ ?_
  obtain ⟨e, hex, he⟩ := exists_affineIsometryEquiv_symm_mem_ball_iff c hr hx
  refine ⟨e, fun y ↦ r - √(r ^ 2 - ‖y‖ ^ 2), r, r, hex, hr, hr, by simp [hr.le],
    contDiffAt_const.sub ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt
      (by simp [hr.ne'])), ?_, he⟩
  simpa using ((hasFDerivAt_sqrt_sub_norm_sq (x := (0 : E)) (a := r ^ 2)
    (by simp [hr.ne'])).const_sub r).fderiv

/-- **Balls have smooth boundary charts.** At every frontier point `x` of a ball of positive
radius in `WithLp 2 (ℝ × E)` there are rigid coordinates `e` with `e x = 0` and a graph function
`φ` of class `Cᵏ` on all of `E`, for any `k`, with `φ 0 = 0`, such that inside a cylinder about
the origin the ball is the region above the graph of `φ`. This is the boundary regularity
hypothesis of the `W^{2,p}` Dirichlet theory on domains with `C²` boundary. -/
theorem exists_contDiff_graph_of_mem_frontier_ball (c : WithLp 2 (ℝ × E)) {r : ℝ} (hr : 0 < r)
    {k : ℕ∞} {x : WithLp 2 (ℝ × E)} (hx : x ∈ frontier (ball c r)) :
    ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
      e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ k φ ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ ball c r ↔ φ z.snd < z.fst) := by
  obtain ⟨e, hex, he⟩ := exists_affineIsometryEquiv_symm_mem_ball_iff c hr hx
  -- The hemisphere `r - √(r² - ‖ρ y‖²)` for a smooth `ρ` equal to the identity near `0` with values
  -- in `ball 0 (r / 2)`, so that the square root stays away from `0`.
  obtain ⟨ρ, hρ, hρ0, hρr⟩ := exists_contDiff_eventuallyEq_id_forall_mem_ball (E := E) (half_pos hr)
  obtain ⟨ε, hε, hερ⟩ := Metric.eventually_nhds_iff_ball.1 hρ0
  have hpos : ∀ y : E, r ^ 2 - ‖ρ y‖ ^ 2 ≠ 0 := fun y ↦ by
    have := mem_ball_zero_iff.1 (hρr y)
    nlinarith [norm_nonneg (ρ y)]
  refine ⟨e, fun y ↦ r - √(r ^ 2 - ‖ρ y‖ ^ 2), r, min ε r, hex, hr, lt_min hε hr, ?_, ?_,
    fun z hz ↦ ?_⟩
  · simp [hερ 0 (mem_ball_self hε), Real.sqrt_sq hr.le]
  · exact contDiff_const.sub ((contDiff_const.sub ((contDiff_norm_sq ℝ).comp
      (hρ.of_le (by exact_mod_cast le_top)))).sqrt hpos)
  · rw [mem_normalCylinder, lt_min_iff] at hz
    have hz' : z ∈ normalCylinder r r := mem_normalCylinder.2 ⟨hz.1, hz.2.1, hz.2.2.2⟩
    simp only [he z hz', hερ z.snd (mem_ball_zero_iff.2 hz.2.2.1), id]

end TauCeti
