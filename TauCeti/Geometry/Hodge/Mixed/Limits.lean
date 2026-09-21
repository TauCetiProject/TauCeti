/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.Geometry.Hodge.Mixed.Kernels

/-!
# Isomorphisms of mixed Hodge structures

A morphism in the category of mixed Hodge structures is an isomorphism exactly when its
underlying rational map is bijective. This is Deligne's strictness: the inverse of a bijective
morphism preserves both filtrations (`TauCeti.Hodge.MixedHodgeStructure.Hom.invOfBijective`), so
the rational realization reflects isomorphisms.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructureCat.isIso_iff_bijective`: isomorphisms are detected
  rationally.
* the instance `ReflectsIsomorphisms TauCeti.Hodge.MixedHodgeStructureCat.rational`: the rational
  realization reflects isomorphisms.

## References

Deligne, *Théorie de Hodge II*, 2.3.5; Peters--Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/
public section

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

variable {X Y : MixedHodgeStructureCat.{u}}

/-- **A bijective morphism of mixed Hodge structures is an isomorphism.** Its inverse is a
morphism of mixed Hodge structures by strictness. -/
theorem isIso_of_bijective (f : X ⟶ Y) (hf : Function.Bijective f.toRatLinearMap) : IsIso f :=
  ⟨⟨f.invOfBijective hf, MixedHodgeStructure.Hom.invOfBijective_comp f hf,
    MixedHodgeStructure.Hom.comp_invOfBijective f hf⟩⟩

/-- A morphism of mixed Hodge structures is an isomorphism exactly when its rational map is
bijective. -/
theorem isIso_iff_bijective (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f.toRatLinearMap :=
  ⟨fun _ ↦ ConcreteCategory.bijective_of_isIso (rational.map f), isIso_of_bijective f⟩

/-- The rational realization reflects isomorphisms: a morphism of mixed Hodge structures whose
rational map is invertible is itself invertible. -/
instance : rational.ReflectsIsomorphisms where
  reflects f _ := isIso_of_bijective f (ConcreteCategory.bijective_of_isIso (rational.map f))

end TauCeti.Hodge.MixedHodgeStructureCat
