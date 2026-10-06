/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Basic

/-!
# The category of right A-infinity modules

`AInfinityRightModuleCat AA` bundles right `A∞` modules over a fixed algebra `AA`.
Its morphisms are the existing bar-comodule morphisms `AInfinityRightModuleHom`, and
composition is composition of bar maps. This is the category before taking homotopy classes
or inverting quasi-isomorphisms. Its differential graded enrichment is constructed in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.DGCategory`.

The constructor `of` is an abbreviation so that its carrier is the supplied module type.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- A bundled right `A∞` module over `AA`. -/
structure AInfinityRightModuleCat (AA : AInfinityAlgebra R A) where
  /-- The underlying module carrier. -/
  carrier : Type uM
  [addCommGroup : AddCommGroup carrier]
  [moduleBase : Module R carrier]
  /-- The right `A∞` module structure on the carrier. -/
  str : AInfinityRightModule AA carrier

namespace AInfinityRightModuleCat

attribute [instance] addCommGroup moduleBase

variable {AA : AInfinityAlgebra R A}

instance : CoeSort (AInfinityRightModuleCat.{uR, uA, uM} AA) (Type uM) := ⟨carrier⟩

/-- Bundle a right `A∞` module with its existing module structures. -/
abbrev of {M : Type uM} [AddCommGroup M] [Module R M] (MM : AInfinityRightModule AA M) :
    AInfinityRightModuleCat AA where
  carrier := M
  str := MM

noncomputable instance : Category (AInfinityRightModuleCat.{uR, uA, uM} AA) where
  Hom M N := AInfinityRightModuleHom M.str N.str
  id M := AInfinityRightModuleHom.id M.str
  comp f g := g.comp f
  id_comp f := AInfinityRightModuleHom.comp_id f
  comp_id f := AInfinityRightModuleHom.id_comp f
  assoc f g k := (AInfinityRightModuleHom.comp_assoc k g f).symm

variable {M N P : AInfinityRightModuleCat.{uR, uA, uM} AA}

/-- Morphisms of bundled modules are determined by their bar maps. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.barMap = g.barMap) : f = g :=
  AInfinityRightModuleHom.barMap_injective h

/-- The bar map of the categorical identity is the identity map. -/
@[simp]
theorem barMap_id (M : AInfinityRightModuleCat.{uR, uA, uM} AA) :
    (𝟙 M : M ⟶ M).barMap = LinearMap.id :=
  AInfinityRightModuleHom.barMap_id M.str

/-- Categorical composition is composition of the underlying bar maps. -/
@[simp]
theorem barMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).barMap = g.barMap ∘ₗ f.barMap :=
  AInfinityRightModuleHom.barMap_comp g f

end AInfinityRightModuleCat

end TauCeti
