/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Chain conditions for the monoid algebra of a finite monoid

The monoid algebra `R[M]` of a **finite** monoid is a module-finite algebra over its coefficients,
being free on the finitely many basis elements `single m 1`. Both chain conditions therefore pass
from the coefficients to `R[M]`, and this file registers each of them as an instance. Mathlib
proves the two transfers as the theorems `IsArtinianRing.of_finite` and
`IsNoetherianRing.of_finite`, which instance search cannot use on its own.

Artinian coefficients are what puts the Jordan-Hölder theory of an Artinian ring —
`TauCeti.simpleClassBasis` and the simple-class basis of an exact `K₀` — at the disposal of a
monoid algebra; Noetherian coefficients already suffice to make `FGModuleCat R[M]` abelian.

## Main statements

* `TauCeti.isNoetherianRing_monoidAlgebra`: the monoid algebra of a finite monoid over a
  Noetherian commutative ring is Noetherian.
* `TauCeti.isArtinianRing_monoidAlgebra`: the monoid algebra of a finite monoid over an Artinian
  commutative ring is Artinian.
-/

public section

namespace TauCeti

variable (R M : Type*) [CommRing R] [Monoid M] [Finite M]

/-- **The monoid algebra of a finite monoid is Noetherian** over Noetherian coefficients, being a
module-finite algebra over them. This is already enough to make `FGModuleCat R[M]` abelian. -/
instance isNoetherianRing_monoidAlgebra [IsNoetherianRing R] :
    IsNoetherianRing (MonoidAlgebra R M) :=
  IsNoetherianRing.of_finite R (MonoidAlgebra R M)

/-- **The monoid algebra of a finite monoid is Artinian** over Artinian coefficients, being a
module-finite algebra over them. This is the hypothesis of `TauCeti.simpleClassBasis`. -/
instance isArtinianRing_monoidAlgebra [IsArtinianRing R] :
    IsArtinianRing (MonoidAlgebra R M) :=
  IsArtinianRing.of_finite R (MonoidAlgebra R M)

end TauCeti
