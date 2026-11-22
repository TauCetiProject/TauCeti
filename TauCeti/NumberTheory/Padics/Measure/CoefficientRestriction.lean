/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restriction of measure coefficients along an embedding

If a ring homomorphism embeds one topological coefficient ring into another, a measure restricts
along it whenever the integral of every transported test lies in the coefficient image.
This criterion is `RingHom.exists_apply_comp_eq_of_mem_range`.

Over a nontrivially normed field `K`, for an embedding `j` onto its closed unit ball and compact
`X`, `AbstractMeasure.exists_apply_comp_eq_of_norm_le_one` restricts any `K`-valued measure of
operator norm at most `1`. The converse and uniqueness are recorded in
`AbstractMeasure.existsUnique_apply_comp_eq_iff_norm_le_one`. These statements require neither
completeness nor an ultrametric norm on `K`, nor separation or total disconnectedness of `X`.
-/

public section

open ContinuousMap

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X]

/-- Restrict a measure through a coefficient embedding when every transported test has its
integral in the coefficient image. -/
theorem _root_.RingHom.exists_apply_comp_eq_of_mem_range {O K : Type*}
    [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (j : O →+* K) (hje : Topology.IsEmbedding j)
    (ν : D(X, K))
    (hmem : ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) ∈ Set.range j) :
    ∃ μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f) := by
  let := j.toAlgebra
  have halg : algebraMap O K = j := j.algebraMap_toAlgebra
  have hlin : ⇑(Algebra.linearMap O K) = j := by
    funext a
    rw [Algebra.linearMap_apply, halg]
  have hlinj : Function.Injective (Algebra.linearMap O K) := by
    rw [hlin]
    exact hje.injective
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K (by rw [halg]; exact hje.continuous)
  have hlin_cont : Continuous (Algebra.linearMap O K) := by
    rw [hlin]
    exact hje.continuous
  let J : O →L[O] K := ⟨Algebra.linearMap O K, hlin_cont⟩
  have hJ : ⇑J = j := by
    rw [ContinuousLinearMap.coe_mk', hlin]
  let F : C(X, O) →L[O] K :=
    ((toCLMEquiv ν).restrictScalars O).comp (J.compLeftContinuous O X)
  have hF (f : C(X, O)) : F f = ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) := by
    have hcomp : J.compLeftContinuous O X f = (⟨j, hje.continuous⟩ : C(O, K)).comp f := by
      have hcomp' := (ContinuousLinearMap.compLeftContinuous_apply O X J f).trans
        (AddMonoidHom.compLeftContinuous_apply X J.toLinearMap.toAddMonoidHom J.continuous f)
      rw [hcomp']
      ext x
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, LinearMap.toAddMonoidHom_coe,
        ContinuousLinearMap.coe_coe, hJ]
    simp only [F, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      coe_toCLMEquiv, hcomp]
  have hmem' (f : C(X, O)) : F.toLinearMap f ∈ (Algebra.linearMap O K).range := by
    rw [LinearMap.mem_range]
    obtain ⟨a, ha⟩ := hmem f
    exact ⟨a, by rw [hlin, ContinuousLinearMap.coe_coe, hF]; exact ha⟩
  let L := F.toLinearMap.codRestrictOfInjective (Algebra.linearMap O K) hlinj hmem'
  have hLj (f : C(X, O)) : j (L f) = F f := by
    rw [← hlin]
    exact LinearMap.codRestrictOfInjective_comp_apply F.toLinearMap (Algebra.linearMap O K)
      hlinj hmem' f
  have hL : Continuous L := hje.continuous_iff.mpr <| by
    simpa only [Function.comp_def, hLj] using F.continuous
  exact ⟨toCLMEquiv.symm ⟨L, hL⟩, fun f ↦ by
    rw [coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', hLj, hF]⟩

section OperatorNorm

variable [CompactSpace X] {K O : Type*} [NontriviallyNormedField K] [CommRing O]
  [TopologicalSpace O] [IsTopologicalRing O] {j : O →+* K}

section CoefficientRestriction

variable (hj : ∀ a, ‖j a‖ ≤ 1)

include hj in
/-- If `j` is a topological embedding onto the closed unit ball of `K`, a `K`-valued measure `ν` of
norm at most `1` sends the test functions `j ∘ f` into the image of `j`, and the preimages form an
`O`-valued measure `μ` with `ν (j ∘ f) = j (μ f)`. -/
theorem exists_apply_comp_eq_of_norm_le_one (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) {ν : D(X, K)} (hν : ‖toCLMEquiv ν‖ ≤ 1) :
    ∃ μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f) := by
  let J : C(O, K) := ⟨j, hje.continuous⟩
  refine j.exists_apply_comp_eq_of_mem_range hje ν fun f ↦ hjr ?_
  rw [mem_closedBall_zero_iff, ← coe_toCLMEquiv]
  have hf : ‖J.comp f‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr fun x ↦ hj (f x)
  exact ((toCLMEquiv ν).le_of_opNorm_le_of_le hν hf).trans_eq (one_mul 1)

include hj in
/-- If `j` is a topological embedding onto the closed unit ball of `K`, a `K`-valued measure `ν`
has operator norm at most `1` exactly when there is a unique `O`-valued measure `μ` with
`ν (j ∘ f) = j (μ f)` for every `f ∈ C(X, O)`. -/
theorem existsUnique_apply_comp_eq_iff_norm_le_one (hje : Topology.IsEmbedding j)
    (hjr : Metric.closedBall 0 1 ⊆ Set.range j) (ν : D(X, K)) :
    (∃! μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f)) ↔
      ‖toCLMEquiv ν‖ ≤ 1 := by
  refine ⟨fun ⟨μ, hμ, _⟩ ↦ ?_, fun hν ↦ ?_⟩
  · -- a test function of norm at most `1` factors through `j`, so `ν` does not increase it
    have hunit (g : C(X, K)) (hg : ‖g‖ ≤ 1) : ‖ν g‖ ≤ 1 := by
      have hmem (x : X) : g x ∈ Set.range j := hjr <| by
        rw [mem_closedBall_zero_iff]
        exact (ContinuousMap.norm_coe_le_norm g x).trans hg
      choose h hh using hmem
      have hcont : Continuous h := hje.continuous_iff.mpr <| by
        have : j ∘ h = g := funext hh
        rw [this]; exact g.continuous
      have hg' : g = (⟨j, hje.continuous⟩ : C(O, K)).comp ⟨h, hcont⟩ := by ext x; exact (hh x).symm
      rw [hg', hμ]
      exact hj _
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g ↦ ?_
    rw [coe_toCLMEquiv, one_mul]
    -- rescale by a value of `g` of maximal norm
    rcases isEmpty_or_nonempty X with hX | hX
    · have : g = 0 := Subsingleton.elim _ _
      simp [this]
    obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (continuous_norm.comp g.continuous).continuousOn
    have hgt : ‖g t‖ = ‖g‖ := le_antisymm (ContinuousMap.norm_coe_le_norm g t)
      ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ ht (Set.mem_univ x))
    rcases eq_or_ne (g t) 0 with h0 | h0
    · have : g = 0 := by
        rw [← norm_eq_zero, ← hgt, h0, norm_zero]
      simp [this]
    have hnorm : ‖(g t)⁻¹ • g‖ ≤ 1 := by
      rw [norm_smul, norm_inv, hgt, ← hgt]
      exact (inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)).le
    have := hunit _ hnorm
    rw [map_smul, smul_eq_mul, norm_mul, norm_inv] at this
    rw [← hgt]
    rwa [inv_mul_le_iff₀ (norm_pos_iff.2 h0), mul_one] at this
  · obtain ⟨μ, hμ⟩ := exists_apply_comp_eq_of_norm_le_one hj hje hjr hν
    exact ⟨μ, hμ, fun μ' hμ' ↦ ext fun f ↦ hje.injective ((hμ' f).symm.trans (hμ f))⟩

end CoefficientRestriction

end OperatorNorm

end AbstractMeasure
