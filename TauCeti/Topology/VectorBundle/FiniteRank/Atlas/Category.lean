/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Basic

/-!
# Category structure on variable-rank bundle atlases

`TauCeti.FiniteRankAtlas 𝕜 X` inherits its category structure, total-space realization functor,
fibre evaluation functors, isomorphism constructor, and isomorphism invariance of rank from the
shared `TauCeti.VariableRankBundle` interface in `TauCeti.Topology.VectorBundle.FiniteRank.Glued`.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Small variable-rank coordinate atlases form a category of continuous fibrewise-linear maps. -/
instance : Category (FiniteRankAtlas 𝕜 X) := VariableRankBundle.category

/-- Morphisms of variable-rank bundle atlases, delegated to `VariableRankBundle.Hom`. -/
abbrev Hom (A D : FiniteRankAtlas 𝕜 X) := VariableRankBundle.Hom A D

variable {A D C : FiniteRankAtlas 𝕜 X}

/-- Bundle morphisms are determined by their maps on every fibre. -/
@[ext] theorem hom_ext {f g : A ⟶ D}
    (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  VariableRankBundle.hom_ext h

theorem fiberMap_id (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (𝟙 A : A ⟶ A).fiberMap x = LinearMap.id := (rfl)

theorem fiberMap_comp (f : A ⟶ D) (g : D ⟶ C) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

theorem totalSpaceMap_id (A : FiniteRankAtlas 𝕜 X) :
    (𝟙 A : A ⟶ A).totalSpaceMap = ContinuousMap.id _ :=
  VariableRankBundle.totalSpaceMap_id A

theorem totalSpaceMap_comp (f : A ⟶ D) (g : D ⟶ C) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap :=
  VariableRankBundle.totalSpaceMap_comp f g

/-- Passing to the continuous maps of total spaces is faithful. -/
theorem totalSpaceMap_injective :
    Function.Injective (VariableRankBundle.Hom.totalSpaceMap (V := A) (W := D)) :=
  VariableRankBundle.totalSpaceMap_injective

/-- Realize bundle atlases and their morphisms as topological spaces and continuous maps. -/
abbrev totalSpaceFunctor : FiniteRankAtlas 𝕜 X ⥤ TopCat.{max u v} :=
  VariableRankBundle.totalSpaceFunctor (FiniteRankAtlas 𝕜 X)

theorem totalSpaceFunctor_obj (A : FiniteRankAtlas 𝕜 X) :
    totalSpaceFunctor.obj A = TopCat.of (Bundle.TotalSpace Unit A.Fiber) := (rfl)

theorem totalSpaceFunctor_map_apply (f : A ⟶ D) (p : Bundle.TotalSpace Unit A.Fiber) :
    totalSpaceFunctor.map f p = f.totalSpaceMap p := (rfl)

/-- Evaluate an atlas and its morphisms on the fibre at a base point. -/
abbrev fiberFunctor (x : X) : FiniteRankAtlas 𝕜 X ⥤ ModuleCat.{v} 𝕜 :=
  VariableRankBundle.fiberFunctor (FiniteRankAtlas 𝕜 X) x

theorem fiberFunctor_obj (x : X) (A : FiniteRankAtlas 𝕜 X) :
    (fiberFunctor x).obj A = ModuleCat.of 𝕜 (A.Fiber x) := (rfl)

theorem fiberFunctor_map_apply (x : X) (f : A ⟶ D) (v : A.Fiber x) :
    (fiberFunctor x).map f v = f.fiberMap x v := (rfl)

/-- Construct a bundle isomorphism from linear equivalences on the fibres, with
continuity of both induced total-space maps. -/
abbrev isoMk (e : ∀ x, A.Fiber x ≃ₗ[𝕜] D.Fiber x)
    (h : Continuous (fun p : Bundle.TotalSpace Unit A.Fiber =>
      (⟨p.proj, e p.proj p.snd⟩ : Bundle.TotalSpace Unit D.Fiber)))
    (h' : Continuous (fun p : Bundle.TotalSpace Unit D.Fiber =>
      (⟨p.proj, (e p.proj).symm p.snd⟩ : Bundle.TotalSpace Unit A.Fiber))) : A ≅ D :=
  VariableRankBundle.isoMk e h h'

theorem fiberMap_isoMk_hom (e : ∀ x, A.Fiber x ≃ₗ[𝕜] D.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap :=
  VariableRankBundle.fiberMap_isoMk_hom e h h' x

theorem fiberMap_isoMk_inv (e : ∀ x, A.Fiber x ≃ₗ[𝕜] D.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap :=
  VariableRankBundle.fiberMap_isoMk_inv e h h' x

end TauCeti.FiniteRankAtlas

namespace CategoryTheory.Iso

open TauCeti

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {A D : FiniteRankAtlas 𝕜 X}

/-- Isomorphic atlases have the same locally constant rank, even on noncompact
or disconnected bases. -/
theorem finiteRankAtlas_rank_eq (e : A ≅ D) : A.rank = D.rank :=
  e.variableRankBundle_rank_eq

end CategoryTheory.Iso
