/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-!
# Pullback and restriction of modules on schemes

For a scheme morphism `f : X ⟶ Y` and an open `V ⊆ Y`, restricting the pullback `f^* M` to
`f⁻¹ V` agrees with pulling back the restriction `M|_V` along `f ∣_ V`. This compatibility lets
local properties of modules, expressed on open covers, be transported along scheme morphisms.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.restrictPullbackObjIso` identifies these two restricted
  pullbacks.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback commutes with restriction to opens: for an open `V ⊆ Y`, the restriction of
`f^* M` to the preimage `f⁻¹ V` is the pullback of `M|_V` along `f ∣_ V : f⁻¹ V ⟶ V`. -/
def restrictPullbackObjIso (V : Y.Opens) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ V).ι ≅ (pullback (f ∣_ V)).obj (M.restrict V.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫ (pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    ((pullbackComp (f ∣_ V) V.ι).app M).symm ≪≫
    (pullback (f ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).app M).symm

end

end AlgebraicGeometry.Scheme.Modules
