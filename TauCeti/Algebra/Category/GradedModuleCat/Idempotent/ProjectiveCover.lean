/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.GradedDimension
public import TauCeti.Algebra.Module.ProjectiveCover.Multiplicity
import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
import TauCeti.RingTheory.Idempotents.Hom

/-!
# Idempotent coordinates of simple heads over a general field

If the idempotent projective `Ae` covers a simple graded module `S` concentrated in degree zero,
then the idempotent graded dimension of `S` is the constant `dim_k End_A(S)`. Thus the diagonal
in the graded projective/simple pairing need not be one over a nonsplitting field.

The calculation combines evaluation at `e` with the projective-cover Hom dimension formula
`TauCeti.IsProjectiveCover.finrank_linearMap_eq_finrank_end`.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Section 7.4, for the
  division-endomorphism correction to the projective/simple pairing.
-/

public section

namespace TauCeti.GradedModuleCat

open LaurentPolynomial

universe uk uA v

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {e : A}

/-- If `Ae` covers the degree-zero simple `S`, its idempotent graded dimension is the constant
dimension of the division algebra `End_A(S)`. The cover concerns the actual underlying modules;
no scalar action of this division algebra on other Hom spaces is asserted. -/
theorem smulGradedDimension_eq_C_finrank_end_of_isProjectiveCover
    (S : GradedModuleCat.{v} 𝒜) [Module.Finite k S] [IsSimpleModule A S]
    (he : IsIdempotentElem e)
    (hconc : ∀ p, p ≠ 0 → S.grading.piece p = ⊥)
    {f : (Ideal.span {e} : Ideal A) →ₗ[A] S} (hf : IsProjectiveCover f) :
    S.smulGradedDimension e = C (Module.finrank k (Module.End A S) : ℤ) := by
  rw [S.smulGradedDimension_eq_C_of_concentrated e hconc, piece_eq_top_of_concentrated hconc,
    ← (he.spanSingletonHomEquivSMulTop (k := k)).finrank_eq,
    hf.finrank_linearMap_eq_finrank_end (LinearEquiv.refl A S)]

end TauCeti.GradedModuleCat
