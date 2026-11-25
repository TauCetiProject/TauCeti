/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of pullback of sheaves of modules

Pullback of sheaves of modules along a morphism of ringed spaces is additive, since it is a
left adjoint and therefore preserves binary coproducts. The instance
`SheafOfModules.additive_pullback` requires no flatness hypothesis.
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- Pullback of sheaves of modules along a morphism of ringed spaces is additive. -/
instance _root_.SheafOfModules.additive_pullback :
    (_root_.SheafOfModules.pullback φ).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (_root_.SheafOfModules.pullback φ)
  Functor.additive_of_preservesBinaryBiproducts _

end SheafOfModules

end

end TauCeti
