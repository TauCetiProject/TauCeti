/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Inverse conversion between additive and multiplicative monoid algebras

The inverses of Mathlib's algebra and bialgebra equivalences induced by `Multiplicative`
send a monomial at `m` to the monomial at `m.toAdd`, with the same coefficient.
-/

public section

namespace AddMonoidAlgebra

variable {R A M : Type*} [CommSemiring R] [Semiring A] [AddMonoid M]

/-- The inverse algebra equivalence induced by `Multiplicative` preserves monomials. -/
@[simp]
theorem toMultiplicativeAlgEquiv_symm_single [Algebra R A] (m : Multiplicative M) (a : A) :
    (toMultiplicativeAlgEquiv R A M).symm (MonoidAlgebra.single m a) = single m.toAdd a := by
  rw [AlgEquiv.symm_apply_eq, toMultiplicativeAlgEquiv_single, ofAdd_toAdd]

/-- The inverse bialgebra equivalence induced by `Multiplicative` preserves monomials. -/
@[simp]
theorem toMultiplicativeBialgEquiv_symm_single [Bialgebra R A] (m : Multiplicative M) (a : A) :
    (toMultiplicativeBialgEquiv R A M).symm (MonoidAlgebra.single m a) = single m.toAdd a := by
  -- The bialgebra equivalence is built with `BialgEquiv.ofAlgEquiv`, retaining the inverse
  -- function of `toMultiplicativeAlgEquiv`.
  exact toMultiplicativeAlgEquiv_symm_single (R := R) m a

end AddMonoidAlgebra
