/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compression
public import TauCeti.Analysis.Normed.Operator.StableSequence

/-!
# Condition numbers and stable sequences on Hilbert spaces

On a Hilbert space, the operator adjoint coincides with `star`, so `TauCeti.conditionNumber` and
`TauCeti.IsStableSequence` are invariant under `ContinuousLinearMap.adjoint` as well as under
compression along linear isometric equivalences.

## Main results

* `TauCeti.conditionNumber_adjoint`: taking the Hilbert adjoint preserves the condition number.
* `TauCeti.isStableSequence_adjoint_iff`: a sequence of Hilbert-space operators is stable if and
  only if the sequence of its adjoints is.
* `TauCeti.conditionNumber_compression_linearIsometryEquiv` and
  `TauCeti.isStableSequence_compression_linearIsometryEquiv_iff`: compression along linear
  isometric equivalences preserves condition numbers and stability.

## References

* A. Böttcher, *C\*-Algebras in Numerical Analysis*, Irish Math. Soc. Bull. 45 (2000), 57–101,
  Section 1.
-/

public section

namespace TauCeti

section Single

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Taking the Hilbert adjoint preserves the operator condition number. -/
@[simp]
theorem conditionNumber_adjoint (A : E →L[𝕜] E) :
    conditionNumber (ContinuousLinearMap.adjoint A) = conditionNumber A := by
  rw [← ContinuousLinearMap.star_eq_adjoint, conditionNumber_star]

/-- Compressing an operator along a linear isometric equivalence preserves its condition number. -/
@[simp]
theorem conditionNumber_compression_linearIsometryEquiv (e : F ≃ₗᵢ[𝕜] E) (A : E →L[𝕜] E) :
    conditionNumber (A.compression (e : F →L[𝕜] E)) = conditionNumber A := by
  rw [ContinuousLinearMap.compression_def, LinearIsometryEquiv.adjoint_eq_symm]
  exact conditionNumber_linearIsometryEquiv_comp e e.symm A

end Single

section Sequence

variable {𝕜 : Type*} [RCLike 𝕜] {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace 𝕜 (E n)] [∀ n, CompleteSpace (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace 𝕜 (F n)] [∀ n, CompleteSpace (F n)]

/-- A sequence of Hilbert-space operators is stable if and only if the sequence of its adjoints
is. -/
@[simp]
theorem isStableSequence_adjoint_iff {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence (fun n ↦ ContinuousLinearMap.adjoint (A n)) ↔ IsStableSequence A := by
  simpa only [← ContinuousLinearMap.star_eq_adjoint] using isStableSequence_star_iff (a := A)

/-- Compressing a sequence of operators along linear isometric equivalences preserves stability. -/
@[simp]
theorem isStableSequence_compression_linearIsometryEquiv_iff (e : ∀ n, F n ≃ₗᵢ[𝕜] E n)
    {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence (fun n ↦ (A n).compression (e n : F n →L[𝕜] E n)) ↔ IsStableSequence A := by
  simp only [ContinuousLinearMap.compression_def, LinearIsometryEquiv.adjoint_eq_symm]
  exact isStableSequence_linearIsometryEquiv_comp_iff e (fun n ↦ (e n).symm)

end Sequence

end TauCeti
