/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Equivalences of monoid algebras

The inverses of Mathlib's algebra and bialgebra equivalences induced by `Multiplicative`
send a monomial at `m` to the monomial at `m.toAdd`, with the same coefficient.

Relabelling a monoid algebra along an equivalence `e : M ≃* N` and then mapping along a
homomorphism `f : N →* O` is mapping along the composite `f ∘ e`.
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

namespace MonoidAlgebra

variable {R M N O : Type*} [CommSemiring R] [Monoid M] [Monoid N] [Monoid O]

/-- Relabelling along `e` and then mapping along `f` is mapping along the composite `f ∘ e`. -/
@[simp]
theorem mapDomainBialgHom_domCongr (f : N →* O) (e : M ≃* N) (x : MonoidAlgebra R M) :
    mapDomainBialgHom R f (domCongr R R e x) = mapDomainBialgHom R (f.comp e.toMonoidHom) x := by
  have h : (mapDomainBialgHom R f).toAlgHom.comp (domCongr R R e).toAlgHom =
      (mapDomainBialgHom R (f.comp e.toMonoidHom)).toAlgHom := by
    apply algHom_ext (R := R) (A := R) (M := M)
    · intro m
      simp [domCongr_single]
    · ext
  exact AlgHom.congr_fun h x

end MonoidAlgebra
