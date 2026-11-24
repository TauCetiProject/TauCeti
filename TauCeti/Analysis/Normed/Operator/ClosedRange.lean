/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Topology.Algebra.Module.Complement
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Closed-range operators and their a priori estimate

A continuous linear map `T : E →L[𝕜] F` between normed spaces has closed range as soon as every
bounded sequence whose `T`-images converge has a convergent subsequence. This sequential criterion
needs no completeness and no complement of the kernel. Applied only to sequences whose images tend
to zero, the same hypothesis bounds the quotient norm modulo `ker T` by a multiple of `‖T x‖`; the
closed-range criterion follows by choosing preimages of almost minimal norm.

Conversely, a closed-range operator `T` between Banach spaces fails to be bounded below only in
the direction of its kernel. When that kernel is complemented, this file makes the failure
quantitative, in the classical form

`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`,

where `P` is a continuous projection of `E` onto `ker T`. When `ker T` is finite-dimensional, as
for a Fredholm operator, `P x` lies in a finite-dimensional space, and over a proper normed field,
such as `ℝ` or `ℂ`, the finite-rank projection `P` is a compact operator.

## Main declarations

* `ContinuousLinearMap.exists_norm_quotientMk_ker_le_of_exists_subseq_tendsto`: the quotient
  estimate `‖[x]‖ ≤ C * ‖T x‖` modulo `ker T` from the sequential criterion.
* `ContinuousLinearMap.isClosed_range_of_exists_subseq_tendsto`: the sequential closed-range
  criterion, over any nontrivially normed field and without completeness.
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

open Filter Topology in
/-- **Quotient estimate from the sequential criterion.** If every bounded sequence whose `T`-images
tend to zero has a convergent subsequence, then the quotient norm of `x` modulo `ker T`, that is
the distance from `x` to `ker T`, is at most a constant multiple of `‖T x‖`. Neither space needs
to be complete. -/
theorem exists_norm_quotientMk_ker_le_of_exists_subseq_tendsto (T : E →L[𝕜] F)
    (hT : ∀ {R : ℝ} {v : ℕ → E}, (∀ n, ‖v n‖ ≤ R) → Tendsto (fun n ↦ T (v n)) atTop (𝓝 0) →
      ∃ (x : E) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun n ↦ v (ψ n)) atTop (𝓝 x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(Submodule.Quotient.mk x : E ⧸ T.ker)‖ ≤ C * ‖T x‖ := by
  by_contra! hcon
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Counterexamples, normalized to quotient norm in a fixed shell, with bounded representatives.
  have hshell : ∀ n : ℕ, ∃ x : E, ‖x‖ ≤ 2 ∧
      ‖a‖⁻¹ ≤ ‖(Submodule.Quotient.mk x : E ⧸ T.ker)‖ ∧ ‖T x‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨y, hy⟩ := hcon (n + 1) (by positivity)
    set q : E ⧸ T.ker := Submodule.Quotient.mk y
    obtain ⟨d, -, hdlt, hdge, -⟩ :=
      rescale_to_shell_semi_normed ha one_pos
        ((by positivity : (0 : ℝ) ≤ (n + 1) * ‖T y‖).trans_lt hy).ne'
    obtain ⟨x, hx, hxlt⟩ := Submodule.Quotient.norm_mk_lt (d • q) one_pos
    have hmem : x - d • y ∈ T.ker :=
      (Submodule.Quotient.eq _).1 (by rw [hx, Submodule.Quotient.mk_smul])
    have hTx : T x = d • T y := by
      rw [← map_smul, ← sub_eq_zero, ← map_sub]
      exact LinearMap.mem_ker.1 hmem
    refine ⟨x, by linarith, by simpa [hx] using hdge, ?_⟩
    rw [hTx, norm_smul, le_div_iff₀ (by positivity)]
    calc ‖d‖ * ‖T y‖ * (n + 1) = ‖d‖ * ((n + 1) * ‖T y‖) := by ring
      _ ≤ ‖d‖ * ‖q‖ := by gcongr
      _ = ‖d • q‖ := (norm_smul d q).symm
      _ ≤ 1 := hdlt.le
  choose v hvbound hvge hTv using hshell
  have hTv0 := squeeze_zero_norm hTv tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨x, ψ, hψ, hx⟩ := hT hvbound hTv0
  have hxker : x ∈ T.ker := LinearMap.mem_ker.mpr <|
    tendsto_nhds_unique ((T.continuous.tendsto x).comp hx) (hTv0.comp hψ.tendsto_atTop)
  -- The classes of the subsequence converge to the class of `x ∈ ker T`, which is zero.
  have hmk : Tendsto (fun n ↦ (Submodule.Quotient.mk (v (ψ n)) : E ⧸ T.ker)) atTop (𝓝 0) := by
    have hx0 : (Submodule.Quotient.mk x : E ⧸ T.ker) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hxker
    simpa only [Function.comp_def, Submodule.coe_mkQL, Submodule.mkQ_apply, hx0] using
      (T.ker.mkQL.continuous.tendsto x).comp hx
  have hge : ‖a‖⁻¹ ≤ 0 := by
    simpa using ge_of_tendsto' hmk.norm fun n ↦ hvge (ψ n)
  exact hge.not_gt (by positivity)

open Filter Topology in
/-- **Sequential closed-range criterion.** If every bounded sequence whose `T`-images converge
has a convergent subsequence, then `T` has closed range. Neither space needs to be complete. -/
theorem isClosed_range_of_exists_subseq_tendsto (T : E →L[𝕜] F)
    (hT : ∀ {R : ℝ} {v : ℕ → E} {y : F}, (∀ n, ‖v n‖ ≤ R) →
      Tendsto (fun n ↦ T (v n)) atTop (𝓝 y) →
      ∃ (x : E) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun n ↦ v (ψ n)) atTop (𝓝 x)) :
    IsClosed (T.range : Set F) := by
  -- The quotient estimate gives preimages whose norms are bounded by a multiple of the norms of
  -- their images, so the preimages of a convergent sequence are bounded.
  obtain ⟨C, hC0, hC⟩ := T.exists_norm_quotientMk_ker_le_of_exists_subseq_tendsto hT
  refine isSeqClosed_iff_isClosed.mp fun y z hy hyz ↦ ?_
  -- Replace arbitrary preimages by preimages of almost minimal norm.
  have hpre : ∀ n, ∃ w : E, T w = y n ∧ ‖w‖ ≤ C * ‖y n‖ + 1 := fun n ↦ by
    obtain ⟨x, hx⟩ := hy n
    have hx' : T x = y n := hx
    obtain ⟨w, hw, hwlt⟩ :=
      Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk x : E ⧸ T.ker) one_pos
    have hmem : w - x ∈ T.ker := (Submodule.Quotient.eq _).1 hw
    refine ⟨w, ?_, by linarith [hx' ▸ hC x]⟩
    rw [← hx', ← sub_eq_zero, ← map_sub]
    exact LinearMap.mem_ker.1 hmem
  choose w hTw hw using hpre
  obtain ⟨R, hR⟩ := hyz.norm.bddAbove_range
  have hwle (n : ℕ) : ‖w n‖ ≤ C * R + 1 :=
    (hw n).trans (by gcongr; exact hR ⟨n, rfl⟩)
  obtain ⟨x, ψ, hψ, hx⟩ := hT hwle (by simpa only [hTw] using hyz)
  exact ⟨x, tendsto_nhds_unique ((T.continuous.tendsto x).comp hx)
    (by simpa only [Function.comp_def, hTw] using hyz.comp hψ.tendsto_atTop)⟩

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
