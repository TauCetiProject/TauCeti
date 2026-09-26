/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# The symmetric algebra of a finite module over a Noetherian ring is Noetherian

The symmetric algebra of a *free* module with basis indexed by `κ` is the polynomial ring
`MvPolynomial κ R` (Mathlib's `SymmetricAlgebra.equivMvPolynomial`), so the Hilbert basis theorem
makes it Noetherian as soon as `κ` is finite. Freeness is not needed: a module finite over `R` is a
quotient of `Rⁿ`, and the symmetric algebra of a quotient is a quotient of the symmetric algebra
(`SymmetricAlgebra.map_surjective`), so `SymmetricAlgebra R M` is a quotient of a polynomial ring
in finitely many variables.

The hypotheses are therefore the same two that make `MonoidAlgebra`-style constructions Noetherian:
`R` Noetherian and `M` module-finite, with no freeness and no field. The symmetric algebra is the
commutative model of an enveloping algebra, and this instance is consumed in that role by
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/Noetherian.lean`: the symmetric algebra of a Lie
algebra surjects onto the associated graded of its PBW filtration, which is thereby Noetherian
under the same two hypotheses.

## Main results

* `TauCeti.SymmetricAlgebra.instIsNoetherianRing`: **the symmetric algebra of a module finite over
  a Noetherian commutative ring is Noetherian.**

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Springer GTM 150
  (1995), §1.4 (the Hilbert basis theorem).
-/

public section

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M]

/-- **The symmetric algebra of a module finite over a Noetherian commutative ring is Noetherian.**
Neither freeness of `M` nor a field is needed. -/
instance instIsNoetherianRing [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherianRing (_root_.SymmetricAlgebra R M) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  have hpoly : IsNoetherianRing (_root_.SymmetricAlgebra R (Fin n → R)) :=
    isNoetherianRing_of_ringEquiv (MvPolynomial (Fin n) R)
      (_root_.SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n))).symm.toRingEquiv
  exact isNoetherianRing_of_surjective (_root_.SymmetricAlgebra R (Fin n → R))
    (_root_.SymmetricAlgebra R M) (_root_.SymmetricAlgebra.map R g).toRingHom
    (SymmetricAlgebra.map_surjective R g hg) (H := hpoly)

end TauCeti.SymmetricAlgebra
