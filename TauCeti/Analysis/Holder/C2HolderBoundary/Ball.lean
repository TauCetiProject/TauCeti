/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Holder.C2HolderBoundary.Basic
import TauCeti.Analysis.Holder.CompLinear
import TauCeti.Analysis.Holder.Translation
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.SphereChart

/-!
# Balls have `C^{2,α}` boundary

An open ball `B(c, R)` in a finite-dimensional real inner product space has `C^{2,α}` boundary
for every `α ≤ 1` (`TauCeti.hasC2HolderBoundary_ball`). So balls satisfy the boundary hypothesis
`Set.HasC2HolderBoundary` of the global Schauder estimate and of the method-of-continuity
reduction of the Dirichlet problem to the Laplacian in
`TauCeti/Analysis/PDE/Regularity/Hessian/Schauder/`.

## The graph patch

Let `z` be a point of the sphere `∂B(c, R)` and let `ν = (c - z) / R` be the inner unit normal
there. Write `P y = y - ⟪ν, y⟫ ν` for the orthogonal projection onto the hyperplane `ν^⊥`. Since
`‖x - c‖² = ⟪ν, x - c⟫² + ‖P (x - c)‖²` and `⟪ν, x - c⟫ < 0` near `z`, near `z` the ball is the
region above the lower hemisphere

`{x | ⟪c, ν⟫ - √(R² - ‖P (x - c)‖²) < ⟪x, ν⟫}`.

On `‖v‖ ≤ 1/4` the cut-off sphere graph `TauCeti.unitSphereGraph` is `1 - √(1 - ‖v‖²)`, so
this hemisphere is `γ x = ⟪z, ν⟫ + R g(R⁻¹ P (x - c))` with `g = TauCeti.unitSphereGraph`, in the
ball `B(z, R/4)`. The function `g` is smooth with compact support, so it is a bounded `C^{2,α}`
function for `α ≤ 1` (`TauCeti.CkHolderSpace.exists_coe_eq_of_contDiff`), and so is
`x ↦ R g(R⁻¹ P (x - c))`, a multiple of its precomposition with a linear map and a translation
(`TauCeti.CkHolderSpace.compLinearL`, `TauCeti.CkHolderSpace.translateLIE`). The function `γ` is
invariant along `ν` because `P ν = 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (domains with `C^{2,α}` boundary).
-/

public section

open Metric Function
open scoped InnerProductSpace NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Near a point `z` of the sphere `∂B(c, R)`, with inner unit normal `ν`, the ball `B(c, R)` is the
region above the graph of `x ↦ ⟪z, ν⟫ + R g(R⁻¹ P (x - c))`, where `g` is the cut-off sphere graph
and `P` is the orthogonal projection onto `ν^⊥`. -/
private theorem norm_sub_lt_iff_of_norm_sub_lt {c z ν x : E} {R : ℝ}
    (hR : 0 < R) (hν : ‖ν‖ = 1) (hzc : z - c = (-R) • ν) (hx : ‖x - z‖ < R / 4) :
    ‖x - c‖ < R ↔ ⟪z, ν⟫_ℝ +
      R * unitSphereGraph ((R⁻¹ • (ℝ ∙ ν)ᗮ.starProjection) (x - c)) < ⟪x, ν⟫_ℝ := by
  -- `‖x - c‖² = ⟪ν, x - c⟫² + ‖P (x - c)‖²`, where `P` is the projection onto `ν^⊥`.
  have hPsq : ‖x - c‖ ^ 2 = ⟪ν, x - c⟫_ℝ ^ 2 + ‖(ℝ ∙ ν)ᗮ.starProjection (x - c)‖ ^ 2 := by
    rw [Submodule.norm_sq_eq_add_norm_sq_starProjection (x - c) (ℝ ∙ ν),
      Submodule.starProjection_unit_singleton ℝ hν]
    simp only [norm_smul, hν, mul_one, Real.norm_eq_abs, sq_abs]
  set P := (ℝ ∙ ν)ᗮ.starProjection
  have hxc : x - c = (x - z) + (-R) • ν := by rw [← hzc]; abel
  have hPx : ‖P (x - c)‖ ≤ R / 4 := by
    have hPν : P ν = 0 := Submodule.starProjection_orthogonalComplement_singleton_eq_zero ν
    simpa [hxc, hPν] using (Submodule.norm_starProjection_apply_le _ (x - z)).trans hx.le
  -- In the coordinates `r = R`, `s = ⟪x, ν⟫ - ⟪z, ν⟫`, `v = P (x - c)` of `sq_add_sq_lt_iff`,
  -- `r - s = -⟪ν, x - c⟫`.
  have hxz : ⟪ν, x - z⟫_ℝ = ⟪x, ν⟫_ℝ - ⟪z, ν⟫_ℝ := by simp [inner_sub_right, real_inner_comm]
  have ht : ⟪ν, x - c⟫_ℝ = ⟪ν, x - z⟫_ℝ - R := by
    simp [hxc, inner_add_right, inner_smul_right, hν, sub_eq_add_neg]
  have hνxz : ⟪ν, x - z⟫_ℝ ≤ ‖x - z‖ := by simpa [hν] using real_inner_le_norm ν (x - z)
  have key := (sq_add_sq_lt_iff hR (s := ⟪x, ν⟫_ℝ - ⟪z, ν⟫_ℝ) (by linarith) hPx).1
  rw [show R - (⟪x, ν⟫_ℝ - ⟪z, ν⟫_ℝ) = -⟪ν, x - c⟫_ℝ by linarith, neg_sq,
    lt_sub_iff_add_lt'] at key
  rw [smul_apply, ← pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero, hPsq, key]

/-- **Balls have `C^{2,α}` boundary.** In a finite-dimensional real inner product space, every open
ball has `C^{2,α}` boundary for `α ≤ 1`: near each point `z` of its sphere it is the region above
the graph of a smooth function over the tangent hyperplane, the lower hemisphere seen from the
inner normal at `z`. -/
theorem hasC2HolderBoundary_ball [FiniteDimensional ℝ E] (c : E) (R : ℝ) {α : ℝ≥0}
    (hα : α ≤ 1) : (ball c R).HasC2HolderBoundary α := by
  refine Set.hasC2HolderBoundary_iff.2 fun z hz => ?_
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.2 hR] at hz
  rw [frontier_ball c hR.ne', mem_sphere, dist_eq_norm] at hz
  -- The inner unit normal `ν` at `z` and the orthogonal projection `P` onto `ν^⊥`.
  set ν : E := R⁻¹ • (c - z) with hν_def
  have hν : ‖ν‖ = 1 := by
    simp [hν_def, norm_smul, abs_of_pos hR, ← norm_neg (c - z), hz, hR.ne']
  have hzc : z - c = (-R) • ν := by
    simp [hν_def, smul_smul, hR.ne']
  set P := (ℝ ∙ ν)ᗮ.starProjection
  -- The cut-off sphere graph is a bounded `C^{2,α}` function, being smooth with compact support.
  obtain ⟨g, hg⟩ := CkHolderSpace.exists_coe_eq_of_contDiff (F := ℝ) hα 2
    (contDiff_unitSphereGraph (K := E) (k := 3)) fun i hi =>
      Continuous.bounded_above_of_compact_support
        ((contDiff_unitSphereGraph (K := E) (k := 3)).continuous_iteratedFDeriv
          (by exact_mod_cast hi))
        (hasCompactSupport_unitSphereGraph.iteratedFDeriv i)
  -- So is `H x = R g(R⁻¹ P (x - c))`, and the graph function is `γ = ⟪z, ν⟫ + H`.
  set H : CkHolderSpace 2 α E ℝ :=
    R • CkHolderSpace.translateLIE 2 α ℝ (-c) (CkHolderSpace.compLinearL (R⁻¹ • P) g)
  have hH (x : E) : H x = R * unitSphereGraph ((R⁻¹ • P) (x - c)) := by
    simp [H, hg, sub_eq_add_neg]
  have hγ : fderiv ℝ (fun x => ⟪z, ν⟫_ℝ + H x) = fderiv ℝ H :=
    funext fun x => fderiv_const_add _
  refine ⟨ν, fun x => ⟪z, ν⟫_ℝ + H x, ‖H.iteratedFDeriv 1‖₊ + ‖H.iteratedFDeriv 2‖₊ +
      nnHolderNorm α (iteratedFDeriv ℝ 2 H), R / 4, hν, contDiff_const.add H.contDiff,
    fun x t => ?_, fun x => ?_, fun x => ?_, ?_, by positivity, ?_⟩
  · beta_reduce
    rw [hH, hH, add_sub_right_comm]
    have hPν : P ν = 0 := Submodule.starProjection_orthogonalComplement_singleton_eq_zero ν
    simp only [map_add, map_smul, smul_apply, hPν, smul_zero, add_zero]
  · rw [hγ]
    refine (H.norm_fderiv_le_iteratedFDeriv_one x).trans ?_
    simp only [NNReal.coe_add, coe_nnNorm]
    linarith [norm_nonneg (H.iteratedFDeriv 2), (nnHolderNorm α (iteratedFDeriv ℝ 2 H)).coe_nonneg]
  · rw [hγ]
    refine (H.norm_fderiv_fderiv_le_iteratedFDeriv_two x).trans ?_
    simp only [NNReal.coe_add, coe_nnNorm]
    linarith [norm_nonneg (H.iteratedFDeriv 1), (nnHolderNorm α (iteratedFDeriv ℝ 2 H)).coe_nonneg]
  · rw [hγ]
    exact holderOnWith_univ.1 ((holderOnWith_univ.2 H.holderWith_fderiv_fderiv).mono_const
      le_add_self)
  -- Inside `B(z, R/4)`, the ball is the region above the graph.
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_ball, dist_eq_norm, and_congr_left_iff]
  intro hx
  rw [hH]
  exact norm_sub_lt_iff_of_norm_sub_lt hR hν hzc hx

end TauCeti
