/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Morphisms of variable-rank bundle atlases

The objects `FiniteRankAtlas 𝕜 X` form a category whose morphisms are fibrewise linear
maps continuous on the reconstructed total spaces. The ranks of the source and target
may differ and need not be bounded. Neither compactness nor separation assumptions on
the base are needed.

`totalSpaceFunctor` faithfully realizes these morphisms as continuous maps, while
`fiberFunctor` evaluates them as linear maps. `isoMk` constructs bundle isomorphisms
from fibrewise linear equivalences with continuous forward and inverse total-space
maps. Conversely, applying these functors to an isomorphism gives a native
`ModuleCat` linear equivalence and a `TopCat` homeomorphism. In particular such an
isomorphism preserves rank.

The topology used here is the glued native vector-bundle-core topology from
`FiniteRankAtlas.totalSpaceHomeomorph`, not the product topology on the coordinates.
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- A morphism of variable-rank bundle atlases is a linear map on each fibre whose
induced map on the reconstructed total spaces is continuous. -/
@[ext]
structure Hom (A D : FiniteRankAtlas 𝕜 X) where
  /-- The linear map on each actual reconstructed fibre. -/
  fiberMap (x : X) : A.Fiber x →ₗ[𝕜] D.Fiber x
  /-- Continuity is measured in the glued bundle topologies. -/
  continuous_totalSpaceMap : Continuous (fun p : TotalSpace Unit A.Fiber =>
    (⟨p.proj, fiberMap p.proj p.2⟩ : TotalSpace Unit D.Fiber))

namespace Hom

variable {A D C : FiniteRankAtlas 𝕜 X}

/-- The continuous total-space map of a bundle morphism. -/
def totalSpaceMap (f : Hom A D) : C(TotalSpace Unit A.Fiber, TotalSpace Unit D.Fiber) :=
  ⟨_, f.continuous_totalSpaceMap⟩

@[simp] theorem totalSpaceMap_mk (f : Hom A D) (x : X) (v : A.Fiber x) :
    f.totalSpaceMap ⟨x, v⟩ = ⟨x, f.fiberMap x v⟩ := (rfl)

@[simp] theorem proj_totalSpaceMap (f : Hom A D) (p : TotalSpace Unit A.Fiber) :
    (f.totalSpaceMap p).proj = p.proj := (rfl)

end Hom

/-- The category of small variable-rank atlases with genuine continuous linear
bundle maps. For real or complex scalars both objects and morphisms lie in `Type u`. -/
instance : Category (FiniteRankAtlas 𝕜 X) where
  Hom := Hom
  id A :=
    { fiberMap _ := LinearMap.id
      continuous_totalSpaceMap := continuous_id }
  comp f g :=
    { fiberMap x := (g.fiberMap x).comp (f.fiberMap x)
      continuous_totalSpaceMap := g.continuous_totalSpaceMap.comp f.continuous_totalSpaceMap }
  id_comp f := by ext x v; rfl
  comp_id f := by ext x v; rfl
  assoc f g h := by ext x v; rfl

variable {A D C : FiniteRankAtlas 𝕜 X}

/-- Bundle morphisms are determined by their maps on every fibre. -/
@[ext] theorem hom_ext {f g : A ⟶ D}
    (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  Hom.ext (funext h)

@[simp] theorem fiberMap_id (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (𝟙 A : A ⟶ A).fiberMap x = LinearMap.id := (rfl)

@[simp] theorem fiberMap_comp (f : A ⟶ D) (g : D ⟶ C) (x : X) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) := (rfl)

@[simp] theorem totalSpaceMap_id (A : FiniteRankAtlas 𝕜 X) :
    (𝟙 A : A ⟶ A).totalSpaceMap = ContinuousMap.id _ := (rfl)

@[simp] theorem totalSpaceMap_comp (f : A ⟶ D) (g : D ⟶ C) :
    (f ≫ g).totalSpaceMap = g.totalSpaceMap.comp f.totalSpaceMap := (rfl)

/-- Passing to the continuous maps of total spaces is faithful. -/
theorem totalSpaceMap_injective : Function.Injective (Hom.totalSpaceMap (A := A) (D := D)) := by
  intro f g h
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  have hp := congrArg (fun k => k ⟨x, v⟩) h
  exact (TotalSpace.mk_inj.mp hp)

/-- Realize bundle atlases and their morphisms as topological spaces and continuous maps. -/
-- Expose the object assignment so morphism types reduce to the reconstructed total spaces.
@[expose] def totalSpaceFunctor : FiniteRankAtlas 𝕜 X ⥤ TopCat.{max u v} where
  obj A := TopCat.of (TotalSpace Unit A.Fiber)
  map f := TopCat.ofHom f.totalSpaceMap

@[simp] theorem totalSpaceFunctor_obj (A : FiniteRankAtlas 𝕜 X) :
    totalSpaceFunctor.obj A = TopCat.of (TotalSpace Unit A.Fiber) := (rfl)

@[simp] theorem totalSpaceFunctor_map_apply (f : A ⟶ D) (p : TotalSpace Unit A.Fiber) :
    totalSpaceFunctor.map f p = f.totalSpaceMap p := (rfl)

instance : (totalSpaceFunctor (𝕜 := 𝕜) (X := X)).Faithful where
  map_injective h := totalSpaceMap_injective (congrArg TopCat.Hom.hom h)

/-- Evaluate an atlas and its morphisms on the fibre at a base point. -/
-- Expose the object assignment so evaluated morphisms act on the original coordinate fibres.
@[expose] def fiberFunctor (x : X) : FiniteRankAtlas 𝕜 X ⥤ ModuleCat.{v} 𝕜 where
  obj A := ModuleCat.of 𝕜 (A.Fiber x)
  map f := ModuleCat.ofHom (f.fiberMap x)

@[simp] theorem fiberFunctor_obj (x : X) (A : FiniteRankAtlas 𝕜 X) :
    (fiberFunctor x).obj A = ModuleCat.of 𝕜 (A.Fiber x) := (rfl)

@[simp] theorem fiberFunctor_map_apply (x : X) (f : A ⟶ D) (v : A.Fiber x) :
    (fiberFunctor x).map f v = f.fiberMap x v := (rfl)

end TauCeti.FiniteRankAtlas

namespace CategoryTheory.Iso

open TauCeti

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {A D : FiniteRankAtlas 𝕜 X}

/-- Isomorphic atlases have the same locally constant rank, even on noncompact
or disconnected bases. -/
theorem finiteRankAtlas_rank_eq (e : A ≅ D) : A.rank = D.rank := by
  ext x
  calc
    A.rank x = Module.finrank 𝕜 ((FiniteRankAtlas.fiberFunctor x).obj A) :=
      (Module.finrank_fin_fun 𝕜).symm
    _ = Module.finrank 𝕜 ((FiniteRankAtlas.fiberFunctor x).obj D) :=
      ((FiniteRankAtlas.fiberFunctor x).mapIso e).toLinearEquiv.finrank_eq
    _ = D.rank x := Module.finrank_fin_fun 𝕜

end CategoryTheory.Iso

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] {A D : FiniteRankAtlas 𝕜 X}

/-- Construct a bundle isomorphism from linear equivalences on the fibres, with
continuity of both induced total-space maps. -/
def isoMk (e : ∀ x, A.Fiber x ≃ₗ[𝕜] D.Fiber x)
    (h : Continuous (fun p : TotalSpace Unit A.Fiber =>
      (⟨p.proj, e p.proj p.2⟩ : TotalSpace Unit D.Fiber)))
    (h' : Continuous (fun p : TotalSpace Unit D.Fiber =>
      (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace Unit A.Fiber))) : A ≅ D where
  hom := ⟨fun x => (e x).toLinearMap, h⟩
  inv := ⟨fun x => (e x).symm.toLinearMap, h'⟩
  hom_inv_id := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    exact (e x).symm_apply_apply
  inv_hom_id := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    exact (e x).apply_symm_apply

@[simp] theorem fiberMap_isoMk_hom (e : ∀ x, A.Fiber x ≃ₗ[𝕜] D.Fiber x) (h h') (x : X) :
    (isoMk e h h').hom.fiberMap x = (e x).toLinearMap := (rfl)

@[simp] theorem fiberMap_isoMk_inv (e : ∀ x, A.Fiber x ≃ₗ[𝕜] D.Fiber x) (h h') (x : X) :
    (isoMk e h h').inv.fiberMap x = (e x).symm.toLinearMap := (rfl)

end TauCeti.FiniteRankAtlas
