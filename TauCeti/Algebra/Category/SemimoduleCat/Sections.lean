/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Matching sections of semimodule diagrams

The matching families of a diagram of semimodules form a submodule of the product of its
objects. This supplies linear operations on matching families without an additive-inverse
hypothesis. The construction follows Mathlib's `ModuleCat.sectionsSubmodule`, using the
same `CategoryTheory.Functor.sections` carrier for semirings and semimodules.
Natural transformations induce linear maps on these matching families, respecting
identity and composition. Restriction along an index functor is linear as well.
Their underlying maps are Mathlib section maps.

Adapted from `yuma-mizuno-lean/Mei`, commit
`61509bfe75ce943898bc99cfa509fb40bb78c614`, under the Apache 2.0 license.
The section-precomposition construction is adapted from the same source at commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`.
-/

public section

open CategoryTheory

namespace SemimoduleCat

variable {R : Type*} [Semiring R] {J : Type*} [Category* J]

/-- The submodule of families compatible with every arrow of a semimodule diagram. -/
def sectionsSubmodule (F : J ⥤ SemimoduleCat R) : Submodule R (∀ j, F.obj j) where
  carrier := (F ⋙ forget (SemimoduleCat R)).sections
  zero_mem' := by intro j j' f; exact map_zero (F.map f).hom
  add_mem' := by
    intro x y hx hy j j' f
    exact (map_add (F.map f).hom _ _).trans (congrArg₂ (· + ·) (hx f) (hy f))
  smul_mem' := by
    intro r x hx j j' f
    exact (map_smul (F.map f).hom r _).trans (congrArg (r • ·) (hx f))

/-- Membership means compatibility along all arrows. -/
@[simp]
theorem mem_sectionsSubmodule {F : J ⥤ SemimoduleCat R} {s : ∀ j, F.obj j} :
    s ∈ sectionsSubmodule F ↔ ∀ {j j'} (f : j ⟶ j'), F.map f (s j) = s j' := Iff.rfl

/-- Restrict matching sections along a functor of index categories, using Mathlib's
section precomposition on the underlying type-valued diagrams. -/
def sectionsPrecomp {K : Type*} [Category* K] (p : K ⥤ J) (F : J ⥤ SemimoduleCat R) :
    sectionsSubmodule F →ₗ[R] sectionsSubmodule (p ⋙ F) where
  toFun := p.sectionsPrecomp (P := F ⋙ forget (SemimoduleCat R))
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

/-- Restriction along an initial index functor is bijective on matching sections. -/
theorem bijective_sectionsPrecomp {K : Type*} [Category* K]
    (p : K ⥤ J) (F : J ⥤ SemimoduleCat R) [p.Initial] :
    Function.Bijective (sectionsPrecomp p F) :=
  p.bijective_sectionsPrecomp (F ⋙ forget (SemimoduleCat R))

/-- Restricting a matching section reads its component at the image index. -/
@[simp]
theorem sectionsPrecomp_apply {K : Type*} [Category* K] (p : K ⥤ J)
    (F : J ⥤ SemimoduleCat R) (s : sectionsSubmodule F) (k : K) :
    (sectionsPrecomp p F s).val k = s.val (p.obj k) := (rfl)

/-- Restricting along the identity leaves every matching section unchanged. -/
@[simp]
theorem sectionsPrecomp_id (F : J ⥤ SemimoduleCat R) :
    sectionsPrecomp (𝟭 J) F = LinearMap.id := by
  ext s j
  rfl

/-- Successive restrictions agree with restriction along the composite index functor. -/
@[simp]
theorem sectionsPrecomp_comp {K L : Type*} [Category* K] [Category* L]
    (p : K ⥤ J) (q : L ⥤ K) (F : J ⥤ SemimoduleCat R) :
    sectionsPrecomp (q ⋙ p) F = (sectionsPrecomp q (p ⋙ F)).comp (sectionsPrecomp p F) := by
  ext s j
  rfl

section Maps

variable {F G H : J ⥤ SemimoduleCat R}

/-- Apply a natural transformation of semimodule diagrams to every section component. -/
def sectionsMap (α : F ⟶ G) : sectionsSubmodule F →ₗ[R] sectionsSubmodule G where
  toFun := (Functor.sectionsFunctor J).map (Functor.whiskerRight α (forget _))
  map_add' x y := by ext j; exact map_add (α.app j).hom _ _
  map_smul' r x := by ext j; exact map_smul (α.app j).hom r _

/-- Section transport evaluates by the corresponding coefficient map. -/
@[simp]
theorem sectionsMap_apply (α : F ⟶ G) (x : sectionsSubmodule F) (j : J) :
    (sectionsMap α x).val j = (α.app j).hom (x.val j) := (rfl)

/-- Identity coefficient maps fix matching sections. -/
@[simp]
theorem sectionsMap_id : sectionsMap (𝟙 F) = LinearMap.id := by
  ext x j
  rfl

/-- Successive coefficient changes compose on matching sections. -/
@[simp]
theorem sectionsMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    sectionsMap (α ≫ β) = (sectionsMap β).comp (sectionsMap α) := by
  ext x j
  rfl

/-- Restriction along an index functor commutes with changing coefficients. -/
theorem sectionsPrecomp_naturality {K : Type*} [Category* K]
    (p : K ⥤ J) (α : F ⟶ G) :
    (sectionsMap (Functor.whiskerLeft p α)).comp (sectionsPrecomp p F) =
      (sectionsPrecomp p G).comp (sectionsMap α) := by
  ext s k
  rfl

/-- The pointwise form of coefficient naturality for section restriction. -/
theorem sectionsPrecomp_naturality_apply {K : Type*} [Category* K]
    (p : K ⥤ J) (α : F ⟶ G) (s : sectionsSubmodule F) :
    sectionsMap (Functor.whiskerLeft p α) (sectionsPrecomp p F s) =
      sectionsPrecomp p G (sectionsMap α s) :=
  LinearMap.congr_fun (sectionsPrecomp_naturality p α) s

/-- An index transformation transports restricted sections to the new restriction. -/
@[simp]
theorem sectionsMap_whiskerRight_comp_sectionsPrecomp {K : Type*} [Category* K]
    {p q : K ⥤ J} (β : p ⟶ q) (F : J ⥤ SemimoduleCat R) :
    (sectionsMap (Functor.whiskerRight β F)).comp (sectionsPrecomp p F) =
      sectionsPrecomp q F := by
  ext s k
  exact (mem_sectionsSubmodule.mp s.property) (β.app k)

/-- Pointwise transport along an index transformation agrees with restriction. -/
@[simp]
theorem sectionsMap_whiskerRight_sectionsPrecomp {K : Type*} [Category* K]
    {p q : K ⥤ J} (β : p ⟶ q) (F : J ⥤ SemimoduleCat R)
    (s : sectionsSubmodule F) :
    sectionsMap (Functor.whiskerRight β F) (sectionsPrecomp p F s) =
      sectionsPrecomp q F s :=
  LinearMap.congr_fun (sectionsMap_whiskerRight_comp_sectionsPrecomp β F) s

end Maps

end SemimoduleCat
