/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Factorization

/-!
# Uniqueness of s-number sequences on inner product spaces

On Banach spaces the five classical s-number sequences (approximation, Gelfand, Kolmogorov,
Bernstein and Hilbert numbers) are pairwise distinct, with the approximation numbers at the top.
Between inner product spaces over `ℝ` or `ℂ`, every sequence satisfying Pietsch's five s-number
axioms collapses to the approximation numbers, and in finite dimension to the singular values.

* **Uniqueness on inner product spaces.** Every s-number sequence `s` satisfies `s T n ≤ aₙ(T)` on
  all normed spaces. Conversely, for every `0 ≤ c < aₙ(T)` the scalar factorization theorem
  (`ContinuousLinearMap.exists_comp_comp_eq_smul_id` in
  `TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Factorization`) yields contractions
  `A : ℓ₂^{n+1} →L[𝕜] H₁` and `B : H₂ →L[𝕜] ℓ₂^{n+1}` with `B ∘L T ∘L A = c • id`. Applying the
  two-sided ideal axiom, homogeneity and Euclidean normalization gives `c ≤ s T n` for every
  `0 ≤ c < aₙ(T)`, hence `s T n = aₙ(T)` with no completeness hypothesis on either space.
* **Singular values and compactness.** Combining uniqueness with the Eckart–Young theorem
  identifies `s T n` with Mathlib's `LinearMap.singularValues` in finite dimension, and combining
  it with the approximation-number compactness criterion shows that on inner product spaces with a
  complete codomain, `T` is compact if and only if `s T n → 0`.

## Main declarations

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

open Filter
open scoped Topology

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
  have hle := hs.comp_comp_le_of_norm_le_one B T A n hB hA
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
