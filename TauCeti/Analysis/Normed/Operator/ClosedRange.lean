/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Topology.Algebra.Module.Complement
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The a priori estimate of a closed-range operator

A continuous linear map `T : E →L[𝕜] F` between Banach spaces with closed range fails to be
bounded below only in the direction of its kernel. When that kernel is complemented, this file
makes the failure quantitative, in the classical form

`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`,

where `P` is a continuous projection of `E` onto `ker T`. When `ker T` is finite-dimensional, as
for a Fredholm operator, `P x` lies in a finite-dimensional space, and over a proper normed field,
such as `ℝ` or `ℂ`, the finite-rank projection `P` is a compact operator.

## Main declarations

* `ContinuousLinearMap.exists_norm_le_mul_norm_of_mem`: a closed-range operator is bounded below
  on any topological complement of its kernel.
* `ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_projectionL`: the a priori estimate
  against the projection onto the kernel determined by a chosen complement.
* `ContinuousLinearMap.exists_projection_norm_le`: the same estimate with the
  complement discharged, so that the only data left is a continuous projection with range the
  kernel.
* `ContinuousLinearMap.tendsto_subseq_of_cauchySeq_comp`: when the kernel is moreover
  finite-dimensional, a bounded sequence whose image is Cauchy has a convergent subsequence.
* `ContinuousLinearMap.eq_zero_of_norm_le_mul_norm_apply`: an operator `Q` on whose range `T` is
  bounded below by more than `‖R‖`, with `T ∘ Q = R ∘ Q`, vanishes.

`TauCeti.Analysis.Fredholm.Proper` uses the estimate below to prove
that a map with Fredholm derivative is proper near a point (Smale, *An infinite dimensional version
of Sard's theorem*, Amer. J. Math. 87 (1965)); local properness is in turn what makes the critical
values of such a map locally closed, and hence what upgrades Sard--Smale from a density statement
to a residuality statement.
-/

public section

namespace ContinuousLinearMap

open Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {X₁ : Submodule 𝕜 E}

/-- If `T` is bounded below by `C⁻¹` on the range of `Q`, that is `‖Q y‖ ≤ C * ‖T (Q y)‖` for
all `y`, and `T ∘ Q = R ∘ Q` for an operator `R` with `C * ‖R‖ < 1`, then `Q = 0`. -/
theorem eq_zero_of_norm_le_mul_norm_apply {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] {T R : E →L[𝕜] F} {Q : G →L[𝕜] E} {C : ℝ}
    (hle : ∀ y, ‖Q y‖ ≤ C * ‖T (Q y)‖) (hTQ : T ∘L Q = R ∘L Q) (hC : 0 ≤ C)
    (hCR : C * ‖R‖ < 1) : Q = 0 := by
  ext y
  have hTQy : T (Q y) = R (Q y) := congr($hTQ y)
  have : ‖Q y‖ ≤ C * ‖R‖ * ‖Q y‖ :=
    calc ‖Q y‖ ≤ C * ‖R (Q y)‖ := hTQy ▸ hle y
      _ ≤ C * (‖R‖ * ‖Q y‖) := by gcongr; exact R.le_opNorm _
      _ = _ := by ring
  have : ‖Q y‖ = 0 := by nlinarith [norm_nonneg (Q y)]
  simpa using this

variable [CompleteSpace E] [CompleteSpace F]

/-- **A closed-range operator is bounded below off its kernel.** On any topological complement
`X₁` of `ker T` there is a constant `C > 0` with `‖x‖ ≤ C * ‖T x‖` for every `x ∈ X₁`. -/
theorem exists_norm_le_mul_norm_of_mem (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x ∈ X₁, ‖x‖ ≤ C * ‖T x‖ := by
  have : CompleteSpace X₁ := h.isClosed'.completeSpace_coe
  have hinj : Function.Injective (T ∘L X₁.subtypeL) :=
    LinearMap.injective_domRestrict_iff.mpr h.isCompl.disjoint.symm
  -- The restriction of `T` to `X₁` has the same range as `T`, which is closed.
  have hrange : Set.range (T ∘L X₁.subtypeL) = Set.range T := by
    rw [coe_comp, Set.range_comp, coe_subtypeL, coe_subtype, Subtype.range_coe]
    simpa only [map_coe, LinearMap.coe_range, coe_coe] using
      congr(($(map_eq_range_iff.mpr h.isCompl.codisjoint.symm) : Set F))
  -- The open mapping theorem, applied to the restriction of `T` to `X₁`.
  obtain ⟨K, hK⟩ :=
    (T ∘L X₁.subtypeL).antilipschitz_of_injective_of_isClosed_range hinj (hrange ▸ hclosed)
  refine ⟨K + 1, by positivity, fun x hx ↦ ?_⟩
  have hx' := hK.le_mul_norm (map_zero _) ⟨x, hx⟩
  simp only [comp_apply, coe_subtypeL, coe_subtype, ← norm_coe] at hx'
  exact hx'.trans (by gcongr; linarith)

/-- **The a priori estimate of a closed-range operator**, stated against the projection onto the
kernel along a chosen topological complement: there is a `C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖` for all `x`, where `P` is that projection. -/
theorem exists_norm_le_mul_norm_add_norm_projectionL
    (T : E →L[𝕜] F) (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_of_mem hclosed h
  refine ⟨C, hC, fun x ↦ ?_⟩
  calc ‖x‖ = ‖X₁.projectionL T.ker h.symm x + T.ker.projectionL X₁ h x‖ := by
        rw [add_comm, projectionL_add_projectionL_eq_self]
    _ ≤ ‖X₁.projectionL T.ker h.symm x‖ + ‖T.ker.projectionL X₁ h x‖ := norm_add_le _ _
    _ ≤ C * ‖T x‖ + ‖T.ker.projectionL X₁ h x‖ := by
        grw [hbound _ (projectionL_apply_mem h.symm x), T.apply_projectionL_ker h.symm x]

/-- **The a priori estimate of a closed-range operator with complemented kernel**, with the
complement discharged: there is a continuous projection `P` of `E` onto `ker T` and a constant
`C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`.

When `ker T` is finite-dimensional, `P x` lies in the finite-dimensional space `ker T`, and over
a proper normed field the finite-rank projection `P` is compact. This says that a Fredholm
operator is bounded below "up to a compact error". -/
theorem exists_projection_norm_le (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (hcompl : T.ker.ClosedComplemented) :
    ∃ (P : E →L[𝕜] E) (C : ℝ), 0 < C ∧ IsIdempotentElem P ∧ P.range = T.ker ∧
      ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖P x‖ := by
  obtain ⟨X₁, h⟩ := hcompl.exists_isTopCompl
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_add_norm_projectionL hclosed h
  exact ⟨(T.ker).projectionL X₁ h, C, hC, isIdempotentElem_projectionL h,
    range_projectionL h, hbound⟩

open Filter Topology in
/-- **A closed-range operator with finite-dimensional complemented kernel is proper on bounded
sets.** If `x` is a bounded sequence and `T ∘ x` is Cauchy, then `x` has a convergent
subsequence. In particular a Fredholm operator admits no bounded sequence `x` with `T (x n) → 0`
whose terms stay a fixed distance apart. -/
theorem tendsto_subseq_of_cauchySeq_comp [ProperSpace 𝕜] (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (hfinite : FiniteDimensional 𝕜 T.ker)
    (hcompl : T.ker.ClosedComplemented) {x : ℕ → E} (hx : Bornology.IsBounded (Set.range x))
    (hTx : CauchySeq (T ∘ x)) :
    ∃ a : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨X₁, h⟩ := hcompl.exists_isTopCompl
  obtain ⟨C, hC, hest⟩ := T.exists_norm_le_mul_norm_add_norm_projectionL hclosed h
  have : ProperSpace T.ker := FiniteDimensional.proper 𝕜 T.ker
  -- The kernel components of `x n` lie in the finite-dimensional kernel, so a subsequence
  -- converges.
  set Q := T.ker.projectionOntoL X₁ h
  obtain ⟨b, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Q.lipschitzWith.isBounded_image hx)
    fun n ↦ Set.mem_image_of_mem Q (Set.mem_range_self n)
  have hTxφ : CauchySeq (T ∘ x ∘ φ) := hTx.comp_tendsto hφ.tendsto_atTop
  -- The a priori estimate makes `x` Cauchy along the subsequence where `T x` and `Q x` are.
  suffices hcauchy : CauchySeq (x ∘ φ) from
    (cauchySeq_tendsto_of_complete hcauchy).imp fun a ha ↦ ⟨φ, hφ, ha⟩
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ :=
    Metric.cauchySeq_iff'.1 (hTxφ.prodMk hlim.cauchySeq) (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := max_lt_iff.1 ((Prod.dist_eq ..).symm.trans_lt (hN n hn))
  simp only [Function.comp_apply, dist_eq_norm, ← map_sub] at h₁ h₂ ⊢
  calc ‖x (φ n) - x (φ N)‖ ≤ C * ‖T (x (φ n) - x (φ N))‖ + ‖Q (x (φ n) - x (φ N))‖ := by
        simpa only [projectionL_apply, norm_coe] using hest _
    _ < C * (ε / (C + 1)) + 1 * (ε / (C + 1)) := by
      gcongr
      simpa using h₂
    _ = ε := by field_simp

end ContinuousLinearMap
