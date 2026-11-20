/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.Normed.Operator.SNumbers.Hilbert
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Factorization

/-!
# Uniqueness of s-numbers on Hilbert spaces

On Hilbert spaces all s-number sequences coincide with the approximation numbers. The key input
is the **scalar factorization** `ContinuousLinearMap.exists_comp_comp_eq_smul_id`: if `H₁` is a
complete inner product space, `T : H₁ →L[𝕜] H₂` and `0 ≤ c < aₙ(T)`, then there are contractions
`A : ℓ₂^{n+1} → H₁` and `B : H₂ → ℓ₂^{n+1}` with `B ∘ T ∘ A = c • id`.

For an s-number sequence `s`, the ideal inequality and the Euclidean normalization turn the
factorization into `c ≤ s T n`, while every s-number sequence lies below the approximation numbers.
Hence `s T n = aₙ(T)` whenever the source of `T` is a complete inner product space and its target
an inner product space. In particular the Hilbert numbers lie below every s-number sequence,
which completes the sandwich `hₙ ≤ sₙ ≤ aₙ`, and on finite-dimensional inner product spaces every
s-number sequence is the sequence of singular values.

## Main declarations

* `TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`: every s-number sequence equals the
  approximation numbers on operators from a complete inner product space to an inner product
  space.
* `TauCeti.SNumbers.IsSNumberSequence.hilbertNumber_le`: the Hilbert numbers are the smallest
  s-numbers, `hₙ(T) ≤ s T n`.
* `TauCeti.SNumbers.IsSNumberSequence.eq_linearMap_singularValues`: on finite-dimensional inner
  product spaces every s-number sequence is the sequence of singular values.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §5,
  Theorem 5.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §§2.2, 2.11.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Uniqueness.lean` and `SNumbers/SingularValuesFinDim.lean`: an earlier Lean
  formalization of the uniqueness theorem.
-/

public section

open scoped NNReal

namespace TauCeti.SNumbers

universe u

variable {𝕜 : Type u} [RCLike 𝕜] {s : SNumberFamily 𝕜}

namespace IsSNumberSequence

variable (hs : IsSNumberSequence s)
include hs

/-- **Uniqueness of s-numbers on Hilbert spaces.** Every s-number sequence equals the
approximation numbers on operators from a complete inner product space to an inner product
space. -/
theorem eq_singularValue {X Y : Type u}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] (T : X →L[𝕜] Y) (n : ℕ) :
    s T n = T.singularValue n := by
  refine (hs.le_singularValue T n).antisymm (le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_)
  -- Every `c < aₙ(T)` is at most `s T n`, by the scalar factorization.
  obtain ⟨A, B, hA, hB, hBA⟩ := T.exists_comp_comp_eq_smul_id c.2 (by exact_mod_cast hc)
  calc c = s (B ∘L T ∘L A) n := by
        rw [hBA, hs.smul, hs.normalize, mul_one]
        ext
        simp
    _ ≤ s T n := hs.comp_comp_le_of_norm_le_one hB hA T n

/-- **Hilbert numbers are the smallest s-numbers.** Every s-number sequence dominates the
Hilbert numbers. Together with `TauCeti.SNumbers.IsSNumberSequence.le_singularValue` this is the
sandwich `hₙ(T) ≤ s T n ≤ aₙ(T)`. -/
theorem hilbertNumber_le {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : T.hilbertNumber n ≤ s T n := by
  refine ContinuousLinearMap.hilbertNumber_le_iff.mpr fun A B hA hB ↦ ?_
  -- Each compression acts between copies of `ℓ₂`, where `s` is the approximation numbers.
  rw [← hs.eq_singularValue]
  exact hs.comp_comp_le_of_norm_le_one hB hA T n

/-- **Singular values in finite dimension.** On finite-dimensional inner product spaces, every
s-number sequence is the sequence of singular values `LinearMap.singularValues`. -/
theorem eq_linearMap_singularValues {X Y : Type u}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : (s T n : ℝ) = (T : X →ₗ[𝕜] Y).singularValues n := by
  have := FiniteDimensional.completeSpace 𝕜 X
  rw [hs.eq_singularValue, T.singularValue_eq_linearMap_singularValues]

end IsSNumberSequence

end TauCeti.SNumbers
