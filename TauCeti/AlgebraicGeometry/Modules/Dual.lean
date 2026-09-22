/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Dual
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Duality for sheaves of modules on a scheme

The self-duality of a finite free sheaf of modules specializes to the symmetric monoidal category
`X.Modules` on a scheme. This is the local model for duality of finite locally free sheaves.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exactPairingFree`: a finite free `𝒪_X`-module is
  self-dual.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

local instance : MonoidalCategory
    (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X

/-- The free `𝒪_X`-module on a finite type is self-dual. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.exactPairingFree
    (I : Type u) [Finite I] :
    ExactPairing
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) :=
  @TauCeti.SheafOfModules.exactPairingFree _ _ _ _ _ _ X.sheaf I _

end


end AlgebraicGeometry

end TauCeti
