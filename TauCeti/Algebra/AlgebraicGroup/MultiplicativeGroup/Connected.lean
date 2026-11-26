/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Geometric connectedness and finite type of the multiplicative group

The coordinate Hopf algebra `R[T;T⁻¹]` of `𝔾ₘ` is isomorphic to the group Hopf algebra
`R[Multiplicative ℤ]` via `AddMonoidAlgebra.toMultiplicativeBialgEquiv`. Consequently it is of
finite type over every commutative ring `R`, and over every field `k` it is geometrically connected.

## Main declarations

* `TauCeti.MultiplicativeGroup.instAlgebraFiniteTypeLaurentPolynomial`: `LaurentPolynomial R` is
  a finite-type `R`-algebra.
* `TauCeti.MultiplicativeGroup.geometricallyConnectedCommHopfAlgProperty_laurentPolynomial`:
  `k[T;T⁻¹]` is geometrically connected over every field `k`.
-/

public section

open CategoryTheory
open scoped LaurentPolynomial

namespace TauCeti.MultiplicativeGroup

universe u

/-- The Laurent polynomial coordinate Hopf algebra `R[T;T⁻¹]` of `𝔾ₘ` is of finite type over
any commutative ring `R`. -/
noncomputable instance instAlgebraFiniteTypeLaurentPolynomial (R : Type u) [CommRing R] :
    Algebra.FiniteType R (LaurentPolynomial R) :=
  (MonoidAlgebra.finiteType_of_fg (R := R) (M := Multiplicative ℤ)).equiv
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm.toAlgEquiv

/-- **The multiplicative group `𝔾ₘ = Spec k[T;T⁻¹]` is geometrically connected over every field.**
-/
theorem geometricallyConnectedCommHopfAlgProperty_laurentPolynomial (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (LaurentPolynomial k)) :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (_root_.CommHopfAlgCat.isoMk (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm)
    (DiagonalizableGroup.geometricallyConnected_coordinateRing k
      (FGCommGrpCat.of.{0} (Multiplicative ℤ)))

end TauCeti.MultiplicativeGroup
