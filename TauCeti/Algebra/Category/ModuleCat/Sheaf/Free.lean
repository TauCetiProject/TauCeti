/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Free sheaves on one or no generators

This file records the canonical identification between the free sheaf of modules on one
generator and the tensor unit, and that the free sheaf on no generators is a zero object. It is
stated over an arbitrary site and without tying the universe of the coefficient modules to either
universe of the site.

## Main declarations

* `TauCeti.SheafOfModules.freePUnitIsoUnit` identifies the free sheaf on `PUnit` with the sheaf
  of rings itself, regarded as a sheaf of modules;
* `TauCeti.SheafOfModules.isZero_free`: the free sheaf on an empty type is a zero object.

The first comparison is used both by tensor-unit computations and when restricting a rank-one
local trivialization. No formalization is vendored; it is Mathlib's canonical isomorphism from a
coproduct indexed by a unique type to its unique summand.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf on one generator is canonically isomorphic to the tensor unit. -/
def freePUnitIsoUnit (S : Sheaf J RingCat.{u}) :
    _root_.SheafOfModules.free.{u, v₁, u₁} (R := S) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit.{v₁, u₁, u} S :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

/-- The free sheaf of modules on an empty type is a zero object: it is the coproduct of the empty
family. -/
theorem isZero_free {S : Sheaf J RingCat.{u}} (I : Type u) [IsEmpty I] :
    IsZero (_root_.SheafOfModules.free (R := S) I) :=
  (isColimitEquivIsInitialOfIsEmpty _ _ (colimit.isColimit _)).isZero

end SheafOfModules

end


end TauCeti
