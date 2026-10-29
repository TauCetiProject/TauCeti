/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Factor
public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence

/-!
# Approximation numbers under pointwise norm domination and of the modulus

Let `T : E →L[𝕜] F` and `A : E →L[𝕜] G` be bounded operators with a common source, where `G` is
a Hilbert space and `F` is a Banach space. If `‖T x‖ ≤ C * ‖A x‖` for every `x`, then `T` factors
as `T = V A` through a bounded operator `V` of norm at most `C` (the elementary direction of
Douglas's factorization lemma, `ContinuousLinearMap.factorThru`). The ideal inequality for
approximation numbers then gives `aₙ(T) ≤ C aₙ(A)` for every `n`.

Consequently two operators with the same pointwise norms, `‖T x‖ = ‖A x‖` for every `x`, into
Hilbert spaces have the same approximation numbers. Since `‖|T| x‖ = ‖T x‖`, a bounded operator
between Hilbert spaces and
its modulus `|T| = √(T† T)` have the same approximation numbers, `aₙ(|T|) = aₙ(T)`, and hence the
same Ky Fan gauges. This reduces approximation-number questions about an arbitrary operator to
questions about a positive one.

## Main declarations

* `ContinuousLinearMap.singularValue_le_mul_of_forall_norm_apply_le`: if `‖T x‖ ≤ C * ‖A x‖` for
  every `x`, then `aₙ(T) ≤ C aₙ(A)`.
* `ContinuousLinearMap.singularValue_eq_of_forall_norm_apply_eq`: if `‖T x‖ = ‖A x‖` for every
  `x`, then `aₙ(T) = aₙ(A)`.
* `ContinuousLinearMap.singularValue_modulus`: `aₙ(|T|) = aₙ(T)`.
* `ContinuousLinearMap.kyFanGauge_modulus`: `Kₖ(|T|) = Kₖ(T)`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* R. G. Douglas, *On majorization, factorization, and range inclusion of operators on Hilbert
  space*, Proc. Amer. Math. Soc. 17 (1966), 413–415.
-/

public section

open scoped InnerProduct NNReal

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]

section Domination

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Domination bound.** If `‖T x‖ ≤ C * ‖A x‖` for every `x`, where `A` maps into a Hilbert
space and `T` into a Banach space, then `aₙ(T) ≤ C aₙ(A)` for every `n`. -/
theorem singularValue_le_mul_of_forall_norm_apply_le {T : E →L[𝕜] F} {A : E →L[𝕜] G} {C : ℝ≥0}
    (h : ∀ x, ‖T x‖ ≤ C * ‖A x‖) (n : ℕ) :
    T.singularValue n ≤ C * A.singularValue n := by
  have hV : ‖T.factorThru A‖₊ ≤ C := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact norm_factorThru_le C.coe_nonneg h
  calc T.singularValue n = (T.factorThru A ∘L A).singularValue n := by
        rw [factorThru_comp ⟨C, h⟩]
    _ ≤ ‖T.factorThru A‖₊ * A.singularValue n := singularValue_comp_le_left _ _ n
    _ ≤ C * A.singularValue n := by gcongr

end Domination

section Isometric

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Two operators into Hilbert spaces with the same pointwise norms, `‖T x‖ = ‖A x‖` for every
`x`, have the same approximation numbers. -/
theorem singularValue_eq_of_forall_norm_apply_eq {T : E →L[𝕜] F} {A : E →L[𝕜] G}
    (h : ∀ x, ‖T x‖ = ‖A x‖) (n : ℕ) : T.singularValue n = A.singularValue n := by
  apply le_antisymm
  · simpa using singularValue_le_mul_of_forall_norm_apply_le (C := 1) (by simp [h]) n
  · simpa using singularValue_le_mul_of_forall_norm_apply_le (C := 1) (by simp [h]) n

/-- Two operators into Hilbert spaces with the same pointwise norms have the same
approximation-number sequence. -/
theorem sameSingularValues_of_forall_norm_apply_eq {T : E →L[𝕜] F} {A : E →L[𝕜] G}
    (h : ∀ x, ‖T x‖ = ‖A x‖) : SameSingularValues T A :=
  (sameSingularValues_iff T A).2 (singularValue_eq_of_forall_norm_apply_eq h)

end Isometric

section Modulus

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Modulus invariance.** A bounded operator between Hilbert spaces and its modulus have the
same approximation numbers: `aₙ(|T|) = aₙ(T)`. -/
@[simp]
theorem singularValue_modulus (T : E →L[𝕜] F) (n : ℕ) :
    T.modulus.singularValue n = T.singularValue n :=
  singularValue_eq_of_forall_norm_apply_eq T.norm_modulus_apply n

/-- A bounded operator between Hilbert spaces and its modulus have the same approximation-number
sequence. -/
theorem sameSingularValues_modulus (T : E →L[𝕜] F) : SameSingularValues T.modulus T :=
  sameSingularValues_of_forall_norm_apply_eq T.norm_modulus_apply

/-- **Ky Fan modulus invariance.** `Kₖ(|T|) = Kₖ(T)`. -/
@[simp]
theorem kyFanGauge_modulus (T : E →L[𝕜] F) (k : ℕ) : T.modulus.kyFanGauge k = T.kyFanGauge k :=
  (sameSingularValues_modulus T).kyFanGauge_eq k

end Modulus

end ContinuousLinearMap
