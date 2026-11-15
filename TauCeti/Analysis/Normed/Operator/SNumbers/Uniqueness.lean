/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
import TauCeti.Analysis.InnerProductSpace.Gram.Factor
import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Uniqueness of s-number sequences on inner product spaces

On Banach spaces the five classical s-number sequences (approximation, Gelfand, Kolmogorov,
Bernstein and Hilbert numbers) are pairwise distinct, with the approximation numbers at the top.
Between inner product spaces over `ℝ` or `ℂ`, every sequence satisfying Pietsch's five s-number
axioms collapses to the approximation numbers, and in finite dimension to the singular values.

* **Scalar factorization through `ℓ₂^{n+1}`.** For every bounded operator `T : H₁ →L[𝕜] H₂`
  between seminormed inner product spaces over `ℝ` or `ℂ` and every `0 ≤ c < aₙ(T)` there exist
  contractions `A : ℓ₂^{n+1} →L[𝕜] H₁` and `B : H₂ →L[𝕜] ℓ₂^{n+1}` with
  `B ∘L T ∘L A = c • id`. Passing to `T.completion` preserves `aₙ(T)`
  (`ContinuousLinearMap.singularValue_completion`), so converse min–max localization on
  `Completion H₁` (`TauCeti.HasMinMaxLowerBound.of_completeSpace`) supplies an `(n + 1)`-dimensional
  subspace on which `T.completion` is `s`-coercive with `c < s`. Perturbing an orthonormal
  parameterization of this subspace from `Completion H₁` into `H₁`
  (`ContinuousLinearMap.denseRange_comp`) and rescaling yields a contraction `A` such that
  `Completion.toComplL ∘L T ∘L A` is `c`-coercive, and factoring `c • id` through this map in
  `Completion H₂` (`ContinuousLinearMap.factorThru`) followed by `Completion.toComplL` gives `B`.
* **Uniqueness on inner product spaces.** Every s-number sequence `s` satisfies `s T n ≤ aₙ(T)` on
  all normed spaces. Conversely, applying the two-sided ideal axiom, homogeneity and Euclidean
  normalization to `B ∘L T ∘L A = c • id` yields `c ≤ s T n` for every `0 ≤ c < aₙ(T)`, hence
  `s T n = aₙ(T)` with no completeness hypothesis on either space.
* **Singular values and compactness.** Combining uniqueness with the Eckart–Young theorem
  identifies `s T n` with Mathlib's `LinearMap.singularValues` in finite dimension, and combining
  it with the approximation-number compactness criterion shows that on inner product spaces with a
  complete codomain, `T` is compact if and only if `s T n → 0`.

## Main declarations

* `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: for `0 ≤ c < aₙ(T)` between seminormed inner
  product spaces, `B ∘L T ∘L A = c • id` on `EuclideanSpace 𝕜 (Fin (n + 1))` with `‖A‖ ≤ 1` and
  `‖B‖ ≤ 1`.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`: every s-number sequence agrees with the
  approximation numbers on bounded operators between inner product spaces.
* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValues`: in finite dimension, every s-number
  sequence agrees with `LinearMap.singularValues`.
* `TauCeti.SNumbers.IsSNumberSequence.tendsto_nhds_zero_of_isCompactOperator`,
  `TauCeti.SNumbers.IsSNumberSequence.isCompactOperator_of_tendsto_nhds_zero`,
  `TauCeti.SNumbers.IsSNumberSequence.isCompactOperator_iff`: compactness criteria for s-number
  sequences on inner product spaces.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), Theorem 8.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Theorem 2.11.9.
* C. Eckart, G. Young, *The approximation of one matrix by another of lower rank*,
  Psychometrika 1 (1936), 211–218.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean`, `SNumbers/SingularValuesFinDim.lean`, `AddOns/Compact.lean`: an
  earlier Lean formalization of Hilbert-space uniqueness, finite-dimensional singular values and
  compactness for s-number sequences.
-/

public section

open Filter UniformSpace
open scoped InnerProductSpace NNReal Topology

namespace ContinuousLinearMap

section Factorization

/-- **Scalar factorization through Euclidean space.** For every bounded linear map
`T : H₁ →L[𝕜] H₂` between seminormed inner product spaces over `ℝ` or `ℂ` and every
`0 ≤ c < aₙ(T)` there exist contractions `A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁` and
`B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))` such that `B ∘L T ∘L A = c • id`. Neither `H₁` nor
`H₂` needs to be complete or separated. -/
theorem exists_comp_comp_eq_smul_id {𝕜 H₁ H₂ : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [SeminormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < T.singularValue n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁)
      (B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ B ∘L T ∘L A = (c : 𝕜) • ContinuousLinearMap.id 𝕜 _ := by
  rcases hc0.eq_or_lt with rfl | hc_pos
  · exact ⟨0, 0, by simp, by simp, by ext; simp⟩
  have hc' : c < T.completion.singularValue n := by rwa [T.singularValue_completion]
  obtain ⟨s, hcs, v, hv, hs⟩ :=
    TauCeti.hasMinMaxLowerBound_iff.mp TauCeti.HasMinMaxLowerBound.of_completeSpace
      T.completion n hc0 hc'
  set V : Submodule 𝕜 (Completion H₁) := Submodule.span 𝕜 (Set.range v)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hdim : Module.finrank 𝕜 V = n + 1 := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  let e : OrthonormalBasis (Fin (n + 1)) 𝕜 V := (stdOrthonormalBasis 𝕜 V).reindex (finCongr hdim)
  let Aᵢ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] Completion H₁ :=
    V.subtypeₗᵢ.comp e.repr.symm.toLinearIsometry
  let A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] Completion H₁ := Aᵢ.toContinuousLinearMap
  let ι₁ : H₁ →L[𝕜] Completion H₁ := Completion.toComplL
  let ι₂ : H₂ →L[𝕜] Completion H₂ := Completion.toComplL
  have hD : 0 < c + ‖T‖ + 1 := by positivity
  set δ : ℝ := (s - c) / (c + ‖T‖ + 1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hcs) hD
  obtain ⟨A₀, hA₀_dist⟩ := Metric.denseRange_iff.mp
    (ContinuousLinearMap.denseRange_comp (g := ι₁) Completion.denseRange_coe) A' δ hδ
  have hA₀_err : ‖A' - ι₁ ∘L A₀‖ ≤ δ := (dist_eq_norm A' (ι₁ ∘L A₀)).symm.trans_le hA₀_dist.le
  have hA₀_norm : ‖A₀‖ ≤ 1 + δ := by
    rw [← norm_toComplL_comp (f := A₀)]
    calc ‖ι₁ ∘L A₀‖ ≤ ‖A'‖ + ‖A' - ι₁ ∘L A₀‖ := norm_le_insert _ _
      _ ≤ 1 + δ := add_le_add Aᵢ.norm_toContinuousLinearMap_le hA₀_err
  set α : ℝ := 1 + δ with hα_def
  have hα : 0 < α := by positivity
  let A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] H₁ := (α : 𝕜)⁻¹ • A₀
  have hA_norm : ‖A‖ ≤ 1 := by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hα]
    exact (inv_mul_le_iff₀ hα).mpr (by linarith)
  let F : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] Completion H₂ := ι₂ ∘L T ∘L A
  let C_id : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
    (c : 𝕜) • ContinuousLinearMap.id 𝕜 _
  have hbound (u : EuclideanSpace 𝕜 (Fin (n + 1))) : ‖C_id u‖ ≤ 1 * ‖F u‖ := by
    have hAu : s * ‖u‖ ≤ ‖T.completion (A' u)‖ := by
      simpa only [A', LinearIsometry.coe_toContinuousLinearMap, Aᵢ.norm_map u] using
        hs (A' u) (e.repr.symm u).2
    have hdiff : T.completion (A' u) - T.completion (ι₁ (A₀ u)) =
        T.completion ((A' - ι₁ ∘L A₀) u) := by simp [map_sub]
    have herr : ‖T.completion (A' u) - T.completion (ι₁ (A₀ u))‖ ≤ ‖T‖ * (δ * ‖u‖) := by
      rw [hdiff, ← T.norm_completion]
      refine (T.completion.le_opNorm _).trans ?_
      gcongr
      exact ((A' - ι₁ ∘L A₀).le_opNorm u).trans (by gcongr)
    have htri : s * ‖u‖ - ‖T‖ * (δ * ‖u‖) ≤ ‖T.completion (ι₁ (A₀ u))‖ := by
      have h := norm_le_insert (T.completion (ι₁ (A₀ u))) (T.completion (A' u))
      rw [norm_sub_rev] at h; linarith
    have hFu : ‖F u‖ = α⁻¹ * ‖T.completion (ι₁ (A₀ u))‖ := by
      simp [F, A, ι₁, ι₂, norm_smul, abs_of_pos hα]
    have hCid : ‖C_id u‖ = c * ‖u‖ := by
      simp [C_id, norm_smul, abs_of_pos hc_pos]
    rw [one_mul, hCid, hFu, ← div_eq_inv_mul, le_div_iff₀' hα, ← mul_assoc]
    have hδ_le : (c + ‖T‖) * δ ≤ s - c := by
      calc (c + ‖T‖) * δ ≤ (c + ‖T‖ + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
        _ = s - c := mul_div_cancel₀ _ hD.ne'
    rw [hα_def]; nlinarith [norm_nonneg u]
  let B : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := (C_id.factorThru F) ∘L ι₂
  refine ⟨A, B, hA_norm, ?_, ?_⟩
  · exact (opNorm_comp_le _ _).trans <|
      (mul_le_mul (norm_factorThru_le zero_le_one hbound)
        (Completion.toComplₗᵢ : H₂ →ₗᵢ[𝕜] Completion H₂).norm_toContinuousLinearMap_le
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · change (C_id.factorThru F) ∘L F = C_id
    exact factorThru_comp ⟨1, hbound⟩

end Factorization

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers.IsSNumberSequence

variable {𝕜 : Type u} [RCLike 𝕜] {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
include hs

/-- **Uniqueness of s-number sequences on inner product spaces.** Between inner product spaces over
`ℝ` or `ℂ`, every s-number sequence coincides with the approximation numbers at every index,
without completeness assumptions on either space. -/
theorem eq_singularValue {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    s T n = T.singularValue n := by
  refine (hs.le_singularValue T n).antisymm ?_
  rw [← NNReal.coe_le_coe]
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  rcases le_or_gt c 0 with hc0 | hc_pos
  · exact hc0.trans (NNReal.coe_nonneg _)
  obtain ⟨A, B, hA, hB, hfac⟩ := T.exists_comp_comp_eq_smul_id n hc_pos.le hc
  have hA' : ‖A‖₊ ≤ 1 := by exact_mod_cast hA
  have hB' : ‖B‖₊ ≤ 1 := by exact_mod_cast hB
  have hle : s (B ∘L T ∘L A) n ≤ s T n :=
    (hs.comp_le B T A n).trans <| by
      calc ‖B‖₊ * s T n * ‖A‖₊ ≤ 1 * s T n * 1 := by gcongr
        _ = s T n := by simp
  rw [hfac, hs.smul, hs.normalize, mul_one, ← NNReal.coe_le_coe, coe_nnNorm, RCLike.norm_ofReal,
    abs_of_pos hc_pos] at hle
  exact hle

/-- **Finite-dimensional singular values.** Between finite-dimensional inner product spaces over
`ℝ` or `ℂ`, every s-number sequence equals Mathlib's `LinearMap.singularValues` at every index. -/
theorem eq_singularValues {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    (s T n : ℝ) = (T : H₁ →ₗ[𝕜] H₂).singularValues n := by
  rw [hs.eq_singularValue, T.singularValue_eq_linearMap_singularValues]

/-- Every s-number sequence of a compact operator from a normed space into an inner product space
tends to zero. Neither space needs to be complete, and the domain needs no inner product. -/
theorem tendsto_nhds_zero_of_isCompactOperator {X H₂ : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    {T : X →L[𝕜] H₂} (hT : IsCompactOperator T) :
    Tendsto (s T) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT.tendsto_singularValue
    (fun _ ↦ zero_le) (hs.le_singularValue T)

/-- Between inner product spaces with a complete codomain, if some s-number sequence of `T` tends
to zero then `T` is a compact operator. -/
theorem isCompactOperator_of_tendsto_nhds_zero {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    {T : H₁ →L[𝕜] H₂} (h : Tendsto (s T) atTop (𝓝 0)) :
    IsCompactOperator T :=
  ContinuousLinearMap.isCompactOperator_of_tendsto_singularValue
    (h.congr (hs.eq_singularValue T))

/-- **Compactness characterization by s-numbers on Hilbert spaces.** Between inner product spaces
over `ℝ` or `ℂ` with a complete codomain, a bounded operator is compact if and only if its terms
under an s-number sequence tend to zero. -/
theorem isCompactOperator_iff {H₁ H₂ : Type u}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    (T : H₁ →L[𝕜] H₂) :
    IsCompactOperator T ↔ Tendsto (s T) atTop (𝓝 0) :=
  ⟨hs.tendsto_nhds_zero_of_isCompactOperator, hs.isCompactOperator_of_tendsto_nhds_zero⟩

end TauCeti.SNumbers.IsSNumberSequence
