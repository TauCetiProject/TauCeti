/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Flat
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Exactness of flat pullback

Pullback of sheaves of modules along a flat morphism of schemes `f : X ⟶ Y` is exact: it preserves
monomorphisms, homology and finite limits. This holds for all sheaves of modules, not only
quasi-coherent ones, so `f^*` carries an injective resolution of a sheaf of modules to a resolution
of its pullback. No finiteness or Noetherian hypothesis is needed.

As a morphism of ringed spaces, `f` has the stalk maps `Scheme.Hom.stalkMap`
(`AlgebraicGeometry.Scheme.Hom.ringStalkMap_toRingCatSheafHom`), and these are flat
(`AlgebraicGeometry.Flat.iff_flat_stalkMap`). So the results for flat morphisms of ringed spaces
of `TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Flat` apply.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.preservesMonomorphisms_pullback_of_flat`,
  `AlgebraicGeometry.Scheme.Modules.preservesHomology_pullback_of_flat` and
  `AlgebraicGeometry.Scheme.Modules.preservesFiniteLimits_pullback_of_flat`: the instances saying
  that pullback along a flat morphism of schemes is exact.

## References

* The Stacks Project, *Sheaves of Modules*, the section on flat morphisms of ringed spaces.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The stalk maps of a morphism of schemes, viewed as a morphism of ringed spaces through
`Scheme.Hom.toRingCatSheafHom`, are its stalk maps `Scheme.Hom.stalkMap`. -/
@[simp]
lemma Scheme.Hom.ringStalkMap_toRingCatSheafHom (x : X) :
    TauCeti.SheafOfModules.ringStalkMap f.toRingCatSheafHom x = f.stalkMap x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hx ↦ ?_
  ext r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, TauCeti.SheafOfModules.ringStalkMap_germ]
  exact (f.germ_stalkMap_apply U x hx r).symm

namespace Scheme.Modules

variable [Flat f]

/-- The stalk maps of a flat morphism of schemes, as a morphism of ringed spaces, are flat. -/
private lemma flat_ringStalkMap (x : X) :
    (TauCeti.SheafOfModules.ringStalkMap f.toRingCatSheafHom x).hom.Flat := by
  simpa using Flat.stalkMap f x

/-- Pullback along a flat morphism of schemes preserves monomorphisms of sheaves of modules. -/
instance preservesMonomorphisms_pullback_of_flat : (pullback f).PreservesMonomorphisms :=
  TauCeti.SheafOfModules.preservesMonomorphisms_pullback_of_flat _ (flat_ringStalkMap f)

/-- Pullback along a flat morphism of schemes preserves homology: it is an exact functor on
sheaves of modules. -/
instance preservesHomology_pullback_of_flat : (pullback f).PreservesHomology :=
  TauCeti.SheafOfModules.preservesHomology_pullback_of_flat _ (flat_ringStalkMap f)

/-- Pullback along a flat morphism of schemes preserves finite limits of sheaves of modules. -/
instance preservesFiniteLimits_pullback_of_flat : PreservesFiniteLimits (pullback f) :=
  TauCeti.SheafOfModules.preservesFiniteLimits_pullback_of_flat _ (flat_ringStalkMap f)

end Scheme.Modules

end AlgebraicGeometry
