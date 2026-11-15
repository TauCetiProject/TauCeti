/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.FiniteType

/-!
# The symmetric algebra of a finite module over a Noetherian ring is Noetherian

The symmetric algebra of a finite module over a Noetherian commutative ring is Noetherian,
including when the module is not free.

The hypotheses are therefore the same two that make `MonoidAlgebra`-style constructions Noetherian:
`R` Noetherian and `M` module-finite, with no freeness and no field. The symmetric algebra is the
commutative model of an enveloping algebra, and this instance is consumed in that role by
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/Noetherian/Basic.lean`: the symmetric algebra of a Lie
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
    IsNoetherianRing (_root_.SymmetricAlgebra R M) :=
  Algebra.FiniteType.isNoetherianRing R (_root_.SymmetricAlgebra R M)

end TauCeti.SymmetricAlgebra
