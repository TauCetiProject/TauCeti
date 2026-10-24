/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Jacobson.Semiperfect
public import TauCeti.RingTheory.Morita.Corner
public import TauCeti.RingTheory.Semisimple.BasicAlgebra
import TauCeti.RingTheory.Idempotents.Corner.Jacobson
import TauCeti.RingTheory.Idempotents.Full
import TauCeti.RingTheory.Semisimple.FullIdempotent

/-!
# Morita reduction to a basic ring

Every semiperfect ring `A` -- in particular every finite-dimensional algebra over a field -- is
Morita equivalent to a **basic** ring (`TauCeti.IsBasic`), one whose quotient by the Jacobson
radical is a finite product of division rings. The basic ring is a corner `eAe` of `A`:

* by Artin–Wedderburn, `A ⧸ J(A) ≅ ∏ᵢ Matₙᵢ(Dᵢ)` has a full idempotent `ē`, the matrix unit `E₁₁`
  of every block, whose corner is `∏ᵢ Dᵢ`
  (`IsSemisimpleRing.exists_isIdempotentElem_full_corner_ringEquiv_pi_divisionRing`);
* since `A` is semiperfect, `ē` lifts to a full idempotent `e` of `A`
  (`TauCeti.IsSemiperfectRing.exists_isIdempotentElem_full_eq`);
* the radical quotient of the corner is the corner of the radical quotient,
  `eAe ⧸ J(eAe) ≃ ē (A ⧸ J(A)) ē ≅ ∏ᵢ Dᵢ` (`IsIdempotentElem.cornerQuotientJacobsonEquiv`), so
  `eAe` is basic;
* and a full idempotent makes `A` Morita equivalent to its corner
  (`IsIdempotentElem.isMoritaEquivalent_corner`).

In module-theoretic terms `Ae` is the direct sum of one indecomposable projective `A`-module for
each simple module, and `eAe` is its endomorphism ring (up to taking the opposite ring): the
classical basic algebra `A^b` of `A`. This is the normalisation step before presenting a
finite-dimensional algebra over an algebraically closed field by a quiver with relations.

## Main results

* `TauCeti.IsSemiperfectRing.exists_isIdempotentElem_full_isBasic_corner`: a semiperfect ring has
  a full idempotent whose corner ring is basic.
* `TauCeti.IsSemiperfectRing.exists_isBasic_isMoritaEquivalent`: a semiperfect algebra is Morita
  equivalent to a basic algebra.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, CUP (2006), Section I.6.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., GTM 13, Springer
  (1992), §27 (basic rings).
-/

public section

namespace TauCeti.IsSemiperfectRing

universe u

/-- **A semiperfect ring has a full idempotent with a basic corner.** The idempotent lifts the
matrix unit `E₁₁` of every Wedderburn block of `A ⧸ J(A)`; its corner `eAe` has radical quotient
the product of the division rings of the blocks. -/
theorem exists_isIdempotentElem_full_isBasic_corner (A : Type u) [Ring A] [IsSemiperfectRing A] :
    ∃ (e : A) (he : IsIdempotentElem e), TwoSidedIdeal.span {e} = ⊤ ∧ IsBasic he.Corner := by
  obtain ⟨ē, hē, hfull, n, D, hD, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_isIdempotentElem_full_corner_ringEquiv_pi_divisionRing
      (A ⧸ Ring.jacobson A)
  obtain ⟨e, he, rfl, hefull⟩ := exists_isIdempotentElem_full_eq ē hē hfull
  exact ⟨e, he, hefull, (isBasic_iff_pi_divisionRing _).mpr
    ⟨n, D, hD, ⟨he.cornerQuotientJacobsonEquiv.trans φ⟩⟩⟩

/-- **Morita reduction to a basic algebra.** A semiperfect algebra, for instance a
finite-dimensional algebra over a field (`TauCeti.isSemiperfectRing_of_finiteDimensional`), is
Morita equivalent to a basic algebra: the corner ring of
`TauCeti.IsSemiperfectRing.exists_isIdempotentElem_full_isBasic_corner`. -/
theorem exists_isBasic_isMoritaEquivalent (R : Type*) [CommSemiring R] (A : Type u) [Ring A]
    [Algebra R A] [IsSemiperfectRing A] :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra R B), IsBasic B ∧ IsMoritaEquivalent R A B := by
  obtain ⟨e, he, hfull, hB⟩ := exists_isIdempotentElem_full_isBasic_corner A
  exact ⟨he.Corner, inferInstance, inferInstance, hB, he.isMoritaEquivalent_corner R hfull⟩

end TauCeti.IsSemiperfectRing
