/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
import Mathlib.Algebra.Group.Ext

/-!
# Stabilizers and finite-comodule carriers

The carrier of `FGComoduleCat.of M` reconstructs its additive group from scalar multiplication.
Its stabilizer Hopf ideals agree with those computed using the original additive group on `M`.

## Main declarations

* `TauCeti.FGComoduleCat.stabilizerHopfIdeal_of`: forgetting the finite-comodule wrapper does
  not change subspace stabilizer ideals.
-/

public section

namespace TauCeti.FGComoduleCat

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The stabilizer ideal is unchanged when the finite-comodule carrier reconstructs the
additive group from the module structure instead of using the original additive group. -/
theorem stabilizerHopfIdeal_of (W : Submodule k M) :
    @Submodule.stabilizerHopfIdeal k H (of (R := k) (C := H) M) _ _ _
        (instAddCommGroupCarrier _) _ _ W = W.stabilizerHopfIdeal H := by
  congr 1
  exact AddCommGroup.ext rfl

end TauCeti.FGComoduleCat
