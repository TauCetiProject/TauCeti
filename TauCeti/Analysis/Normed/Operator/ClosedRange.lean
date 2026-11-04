/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Complement
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

variable [CompleteSpace E] [CompleteSpace F]

/-- **A closed-range operator is bounded below off its kernel.** On any topological complement
`X₁` of `ker T` there is a constant `C > 0` with `‖x‖ ≤ C * ‖T x‖` for every `x ∈ X₁`. -/
theorem exists_norm_le_mul_norm_of_mem (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x ∈ X₁, ‖x‖ ≤ C * ‖T x‖ := by
  have : CompleteSpace X₁ := h.isClosed'.completeSpace_coe
  have hinj : Function.Injective (T ∘L X₁.subtypeL) :=
    LinearMap.injective_domRestrict_iff.mpr h.isCompl.disjoint.symm
  have hrange : (T ∘L X₁.subtypeL).range = T.range := by
    simpa only [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using
      (map_eq_range_iff.mpr h.isCompl.codisjoint.symm : X₁.map T.toLinearMap = T.range)
  have hclosed_restrict : IsClosed (Set.range (T ∘L X₁.subtypeL)) := by
    have hc : IsClosed ((T ∘L X₁.subtypeL).range : Set F) := hrange.symm ▸ hclosed
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hc
  -- The open mapping theorem, applied to the restriction of `T` to `X₁`.
  obtain ⟨K, hK⟩ :=
    (T ∘L X₁.subtypeL).antilipschitz_of_injective_of_isClosed_range hinj hclosed_restrict
  refine ⟨K + 1, by positivity, fun x hx => ?_⟩
  have hx' := hK.le_mul_dist (⟨x, hx⟩ : X₁) 0
  simp only [ContinuousLinearMap.comp_apply, coe_subtypeL, coe_subtype, map_zero,
    dist_eq_norm, sub_zero] at hx'
  calc ‖x‖ ≤ (K : ℝ) * ‖T x‖ := hx'
    _ ≤ ((K : ℝ) + 1) * ‖T x‖ := by gcongr; exact le_add_of_nonneg_right zero_le_one

/-- **The a priori estimate of a closed-range operator**, stated against the projection onto the
kernel along a chosen topological complement: there is a `C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖` for all `x`, where `P` is that projection. -/
theorem exists_norm_le_mul_norm_add_norm_projectionL
    (T : E →L[𝕜] F) (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_of_mem hclosed h
  refine ⟨C, hC, fun x => ?_⟩
  have hsum : (T.ker).projectionL X₁ h x + X₁.projectionL (T.ker) h.symm x = x :=
    projectionL_add_projectionL_eq_self h x
  have hq := hbound (X₁.projectionL (T.ker) h.symm x)
    (X₁.projectionOntoL (T.ker) h.symm x).2
  have hTx : T (X₁.projectionL (T.ker) h.symm x) = T x := by
    have hker : T ((T.ker).projectionL X₁ h x) = 0 :=
      LinearMap.mem_ker.mp (projectionL_apply_mem h x)
    rw [projectionL_eq_self_sub_projectionL h, map_sub, hker, sub_zero]
  rw [hTx] at hq
  calc ‖x‖ = ‖(T.ker).projectionL X₁ h x + X₁.projectionL (T.ker) h.symm x‖ := by rw [hsum]
    _ ≤ ‖(T.ker).projectionL X₁ h x‖ + ‖X₁.projectionL (T.ker) h.symm x‖ := norm_add_le _ _
    _ ≤ ‖(T.ker).projectionL X₁ h x‖ + C * ‖T x‖ := by gcongr
    _ = C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := add_comm _ _

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
  obtain ⟨P, C, hC, -, hPrange, hest⟩ := T.exists_projection_norm_le hclosed hcompl
  have : ProperSpace T.ker := FiniteDimensional.proper 𝕜 T.ker
  -- The components `P (x n)` lie in the finite-dimensional kernel, so a subsequence converges.
  have hmem (n : ℕ) : P (x n) ∈ T.ker := hPrange ▸ ⟨x n, rfl⟩
  obtain ⟨R, hR⟩ := hx.exists_norm_le
  have hbdd : Bornology.IsBounded (Set.range fun n ↦ (⟨P (x n), hmem n⟩ : T.ker)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖P‖ * R, Set.forall_mem_range.2 fun n ↦
      (P.le_opNorm (x n)).trans (by gcongr; exact hR _ (Set.mem_range_self n))⟩
  obtain ⟨b, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd (fun n ↦ Set.mem_range_self n)
  have hPx : CauchySeq (P ∘ x ∘ φ) :=
    ((continuous_subtype_val.tendsto b).comp hlim).cauchySeq
  have hTxφ : CauchySeq (T ∘ x ∘ φ) := hTx.comp_tendsto hφ.tendsto_atTop
  -- The a priori estimate makes `x` Cauchy along the subsequence where `T x` and `P x` are.
  suffices h : CauchySeq (x ∘ φ) from
    (cauchySeq_tendsto_of_complete h).imp fun a ha ↦ ⟨φ, hφ, ha⟩
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 (hTxφ.prodMk hPx) (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := max_lt_iff.1 ((Prod.dist_eq ..).symm.trans_lt (hN n hn))
  simp only [Function.comp_apply, dist_eq_norm, ← map_sub] at h₁ h₂ ⊢
  calc ‖x (φ n) - x (φ N)‖ ≤ C * ‖T (x (φ n) - x (φ N))‖ + ‖P (x (φ n) - x (φ N))‖ := hest _
    _ < C * (ε / (C + 1)) + 1 * (ε / (C + 1)) := by
      gcongr
      simpa using h₂
    _ = ε := by field_simp

end ContinuousLinearMap
