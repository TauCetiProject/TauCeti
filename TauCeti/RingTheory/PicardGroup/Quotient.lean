/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Reduction of invertible modules over semilocal quotients

If `M` is an invertible module over a commutative ring `R` and `R / J` is semilocal,
then `M / JM` is isomorphic to `R / J`. The isomorphism need not be canonical: it amounts
to choosing a basis for the invertible module after reduction. In particular, invertible
ideals have the same quotient dimensions as the base ring after semilocal reduction.

The base-change argument generalizes the corresponding step of the point-to-class
surjectivity proof, adapted from Chris Birkbeck's AINTLIB (`github.com/CBirkbeck/AINTLIB`,
`HasseWeil/Pic0/ToClassSurjective.lean`, revision `dev/hasse-weil @ 513e83879e2f`, Apache-2.0).
-/

public section

open scoped TensorProduct

namespace Module.Invertible

variable {R : Type*} [CommRing R]

/-- An invertible module reduced modulo an ideal with semilocal quotient is isomorphic to
the quotient ring. No choice of a trivialization is specified. -/
theorem nonempty_quotientEquiv (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (J : Ideal R) [Finite (MaximalSpectrum (R ⧸ J))] :
    Nonempty ((M ⧸ J • (⊤ : Submodule R M)) ≃ₗ[R] R ⧸ J) := by
  let A := R ⧸ J
  let e : A ⊗[R] M ≃ₗ[A] A :=
    (free_iff_linearEquiv.mp (inferInstance : Module.Free A (A ⊗[R] M))).some
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M J).symm.trans (e.restrictScalars R)⟩

end Module.Invertible
