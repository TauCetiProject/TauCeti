/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import TauCeti.Algebra.Category.LieModuleCat.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Finite Lie modules form an essentially small category

For a commutative ring `R : Type u` and a Lie algebra `L : Type v` over `R`, the category
`TauCeti.FGLieModuleCat R L` of Lie modules finite over `R` is essentially small in the universe
`max u v`, whatever the universe of the carriers.

A Lie module is a module over the universal enveloping algebra `U(L)`
(`TauCeti.UniversalEnvelopingAlgebra.asModule`), and its morphisms of Lie modules are exactly its
`U(L)`-linear maps (`TauCeti.UniversalEnvelopingAlgebra.lieModuleHomEquiv`). A module finite over
`R` is finitely generated over `U(L)`, so this gives a fully faithful functor into Mathlib's
`FGModuleCat U(L)`, which Mathlib proves essentially small in the universe of `U(L)`.

Essential smallness is the hypothesis of the split Grothendieck group `TauCeti.SplitK0`, whose
elements, over a field, are the virtual finite-dimensional representations of `L`.

## Main results

* `TauCeti.FGLieModuleCat.essentiallySmall`: finite Lie modules form an essentially small
  category.

## References

* Tau Ceti's `TauCeti.Algebra.Category.FiniteHopfModuleCat.EssentiallySmall`
  (`TauCeti.FiniteHopfModuleCat.essentiallySmall`), for the proof plan of lifting a fully faithful
  functor to `FGModuleCat`.
* Mathlib's `Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall`, for the essential smallness
  of `FGModuleCat`.
-/

public section

open CategoryTheory

universe w u v

namespace TauCeti.FGLieModuleCat

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance] UniversalEnvelopingAlgebra.asModule
  UniversalEnvelopingAlgebra.isScalarTower_asModule

/-- A finite Lie module, regarded as a module over the universal enveloping algebra. -/
private noncomputable def toEnvelopingModule :
    FGLieModuleCat.{w} R L ⥤ ModuleCat.{w} (_root_.UniversalEnvelopingAlgebra R L) where
  obj M := ModuleCat.of _ M.obj
  map f := ModuleCat.ofHom <| UniversalEnvelopingAlgebra.lieModuleHomEquiv
    (UniversalEnvelopingAlgebra.asModule_ι_smul R L _)
    (UniversalEnvelopingAlgebra.asModule_ι_smul R L _) f.hom.hom

/-- Regarding finite Lie modules as modules over the universal enveloping algebra is fully
faithful. -/
private noncomputable def fullyFaithfulToEnvelopingModule :
    (toEnvelopingModule.{w} (R := R) (L := L)).FullyFaithful where
  preimage g := ObjectProperty.homMk <| LieModuleCat.ofHom <|
    (UniversalEnvelopingAlgebra.lieModuleHomEquiv
      (UniversalEnvelopingAlgebra.asModule_ι_smul R L _)
      (UniversalEnvelopingAlgebra.asModule_ι_smul R L _)).symm g.hom
  map_preimage _ := by ext; simp [toEnvelopingModule]
  preimage_map _ := by ext; simp [toEnvelopingModule]

/-- **Finite Lie modules form an essentially small category**, in the universe `max u v` of the
ring `R : Type u` and the Lie algebra `L : Type v`. -/
instance essentiallySmall : EssentiallySmall.{max u v} (FGLieModuleCat.{w} R L) :=
  have := fullyFaithfulToEnvelopingModule.{w} (R := R) (L := L).full
  have := fullyFaithfulToEnvelopingModule.{w} (R := R) (L := L).faithful
  essentiallySmall_of_fully_faithful <| (ModuleCat.isFG _).lift toEnvelopingModule fun M ↦
    have : Module.Finite (_root_.UniversalEnvelopingAlgebra R L) M.obj :=
      .of_restrictScalars_finite R _ _
    (ModuleCat.isFG_iff _).2 this

end TauCeti.FGLieModuleCat
