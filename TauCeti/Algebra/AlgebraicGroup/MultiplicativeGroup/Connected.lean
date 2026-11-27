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
# Geometric connectedness of the multiplicative group

The coordinate Hopf algebra `k[T;T⁻¹]` of `𝔾ₘ` is isomorphic to the group Hopf algebra
`k[Multiplicative ℤ]` via `AddMonoidAlgebra.toMultiplicativeBialgEquiv`, and hence is
geometrically connected over every field `k`.

## Main declarations

* `TauCeti.MultiplicativeGroup.geometricallyConnectedCommHopfAlgProperty_laurentPolynomial`:
  `k[T;T⁻¹]` is geometrically connected over every field `k`.
-/

public section

open CategoryTheory
open scoped LaurentPolynomial

namespace TauCeti.MultiplicativeGroup

universe u

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
