/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import TauCeti.Algebra.Group.CrossedModule.Basic

/-!
# The category of crossed modules

`TauCeti.CrossedModuleCat` bundles crossed modules of groups `∂ : T → H`, with the morphisms of
crossed modules `TauCeti.CrossedModule.Hom` as morphisms. The kernel and the cokernel of the
boundary are functors to commutative groups and to groups, built from the induced homomorphisms
`TauCeti.CrossedModule.Hom.kerMap` and `TauCeti.CrossedModule.Hom.cokerMap`.

## Main definitions and results

* `TauCeti.CrossedModuleCat`: the bundled category, with object constructor `of`.
* `TauCeti.CrossedModuleCat.Hom.hom` and `TauCeti.CrossedModuleCat.ofHom`: conversions between
  categorical morphisms and morphisms of crossed modules.
* `TauCeti.CrossedModuleCat.hom_id`, `TauCeti.CrossedModuleCat.hom_comp`: identities and
  composites of the underlying morphisms of crossed modules.
* `TauCeti.CrossedModuleCat.ofHom_id`, `TauCeti.CrossedModuleCat.ofHom_comp`: identities and
  composites of morphisms of crossed modules give categorical identities and composites.
* `TauCeti.CrossedModuleCat.ker`: the kernel of the boundary, as a functor to `CommGrpCat`.
* `TauCeti.CrossedModuleCat.coker`: the cokernel of the boundary, as a functor to `GrpCat`.

## References

* M. Kisin, *Mod p points on Shimura varieties of abelian type*, J. Amer. Math. Soc. 30 (2017),
  §3.2.1.
* J.-P. Labesse, *Cohomologie, stabilisation et changement de base*, Astérisque 257 (1999), §1.1.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

/-- Crossed modules of groups `∂ : T → H` with `T` and `H` in universe `u`. -/
structure CrossedModuleCat : Type (u + 1) where
  /-- The source of the boundary. -/
  T : Type u
  /-- The target of the boundary. -/
  H : Type u
  /-- The group structure on the source of the boundary. -/
  [groupT : Group T]
  /-- The group structure on the target of the boundary. -/
  [groupH : Group H]
  /-- The crossed module structure. -/
  toCrossedModule : CrossedModule T H

attribute [instance] CrossedModuleCat.groupT CrossedModuleCat.groupH

namespace CrossedModuleCat

/-- Bundle a crossed module. -/
abbrev of {T H : Type u} [Group T] [Group H] (M : CrossedModule T H) : CrossedModuleCat :=
  ⟨T, H, M⟩

/-- A morphism of bundled crossed modules. -/
structure Hom (M N : CrossedModuleCat.{u}) where
  /-- The underlying morphism of crossed modules. -/
  hom : M.toCrossedModule.Hom N.toCrossedModule

instance : Category CrossedModuleCat.{u} where
  Hom M N := Hom M N
  id M := ⟨CrossedModule.Hom.id M.toCrossedModule⟩
  comp f g := ⟨g.hom.comp f.hom⟩

variable {M N P : CrossedModuleCat.{u}}

/-- Regard a morphism of crossed modules as a categorical morphism. -/
abbrev ofHom (f : M.toCrossedModule.Hom N.toCrossedModule) : M ⟶ N :=
  ⟨f⟩

/-- The underlying morphism of the identity is the identity morphism of crossed modules. -/
@[simp]
theorem hom_id : (𝟙 M : M ⟶ M).hom = CrossedModule.Hom.id M.toCrossedModule :=
  rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem hom_comp (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

/-- Constructing a categorical morphism preserves its underlying morphism of crossed modules. -/
@[simp]
theorem hom_ofHom (f : M.toCrossedModule.Hom N.toCrossedModule) : (ofHom f).hom = f :=
  rfl

/-- A categorical morphism is recovered from its underlying morphism of crossed modules. -/
@[simp]
theorem ofHom_hom (f : M ⟶ N) : ofHom f.hom = f :=
  rfl

/-- The identity morphism of crossed modules gives the categorical identity. -/
@[simp]
theorem ofHom_id : ofHom (CrossedModule.Hom.id M.toCrossedModule) = 𝟙 M :=
  rfl

/-- Composites of morphisms of crossed modules give categorical composites. -/
@[simp]
theorem ofHom_comp (f : M.toCrossedModule.Hom N.toCrossedModule)
    (g : N.toCrossedModule.Hom P.toCrossedModule) : ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/-- Categorical morphisms are equal if their underlying morphisms of crossed modules agree. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

open scoped IsMulCommutative in
/-- The kernel of the boundary, as a functor from crossed modules to commutative groups. -/
@[expose, simps]
def ker : CrossedModuleCat.{u} ⥤ CommGrpCat.{u} where
  obj M := CommGrpCat.of M.toCrossedModule.boundary.ker
  map f := CommGrpCat.ofHom f.hom.kerMap

/-- The cokernel of the boundary, as a functor from crossed modules to groups. -/
@[expose, simps]
def coker : CrossedModuleCat.{u} ⥤ GrpCat.{u} where
  obj M := GrpCat.of (M.H ⧸ M.toCrossedModule.boundary.range)
  map f := GrpCat.ofHom f.hom.cokerMap
  map_id M := by
    ext
    simp
  map_comp f g := by
    ext
    simp [CrossedModule.Hom.cokerMap_comp]

end CrossedModuleCat

end TauCeti
