/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Additive units of finitely supported functions

If an additive monoid `M` has trivial additive units (`Subsingleton (AddUnits M)`), then so does
the finitely supported function space `ι →₀ M`.
-/

public section

namespace TauCeti

instance instSubsingletonAddUnitsFinsupp {ι M : Type*} [AddMonoid M]
    [Subsingleton (AddUnits M)] : Subsingleton (AddUnits (ι →₀ M)) :=
  (AddUnits.map_injective (f := Finsupp.coeFnAddHom) DFunLike.coe_injective).subsingleton

end TauCeti
