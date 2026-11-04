/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# The topological nerve of a category and its fat classifying space

Let `C` be a category whose total set of arrows `Quiver.Total C` carries a topology, as for a
topological groupoid. Its *topological nerve* `TauCeti.topologicalNerve C` is the simplicial
space whose `n`-simplices are the strings `F : ComposableArrows C n` of `n` composable arrows,
with the coarsest topology making each arrow `F.obj i ⟶ F.obj j` (`i ≤ j`) of the string,
viewed as a total arrow `F.totalArrow i j hij`, depend continuously on `F`. The face and
degeneracy maps are those of Mathlib's `CategoryTheory.nerve C`, which is the underlying
simplicial set (`TauCeti.topologicalNerve_map_apply`).

Recording every arrow `i ⟶ j` rather than only the consecutive ones makes all simplicial
operators continuous with no hypothesis on `C`: an operator only reindexes the arrows of the
string. Identity arrows are among them, so the objects of the string are recorded too. When
source, target, units and composition are continuous, every arrow of a string is a continuous
function of its consecutive arrows, so this is the subspace topology of composable strings in the
product of arrow spaces. The general recursive identification is
`CategoryTheory.ComposableArrows.precompHomeomorph` in
`TauCeti.Topology.CategoryTheory.ComposableArrows`. For action groupoids the explicit coordinates
are given by `TauCeti.ActionGroupoid.nerveHomeomorph`.

The *fat classifying space* `TauCeti.fatClassifyingSpace C` is the fat realization
(`TauCeti.fatRealization`) of the underlying semi-simplicial space, obtained by forgetting
degeneracies along `SemiSimplexCategory.toSimplexCategory`.

A functor `φ : C ⥤ D` whose action on total arrows (`Prefunctor.mapTotal`) is continuous induces
a map of topological nerves `CategoryTheory.Functor.topologicalNerveMap` and of fat classifying
spaces `CategoryTheory.Functor.fatClassifyingSpaceMap`. If it is an embedding on total arrows, it
induces levelwise embeddings
(`CategoryTheory.ComposableArrows.isEmbedding_mapComposableArrows_obj`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Topology

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D] {n : ℕ}

/-- The arrow of a string of composable arrows from its `i`-th to its `j`-th object, as a total
arrow of `C`. For `i = j` this is the identity arrow of the `i`-th object. -/
def totalArrow (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) : Quiver.Total C :=
  ⟨F.obj i, F.obj j, F.map (homOfLE hij)⟩

@[simp]
theorem totalArrow_left (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).left = F.obj i := (rfl)

@[simp]
theorem totalArrow_right (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).right = F.obj j := (rfl)

theorem totalArrow_def (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    F.totalArrow i j hij = ⟨F.obj i, F.obj j, F.map (homOfLE hij)⟩ := (rfl)

/-- The first arrow of a string obtained by prepending an arrow is that arrow, including
when its target is identified with the first vertex by an equality. -/
@[simp]
theorem totalArrow_precomp_zero_one {n : ℕ} (a : Quiver.Total C)
    (F : ComposableArrows C n) (h : a.right = F.left) :
    (F.precomp (a.hom ≫ eqToHom h)).totalArrow 0 1 (Fin.zero_le _) = a := by
  rcases a with ⟨x, z, f⟩
  dsimp only at h
  subst z
  rw [totalArrow_def]
  simp only [precomp, Precomp.obj_zero, Precomp.obj_one, Precomp.map_zero_one,
    eqToHom_refl, Category.comp_id]

/-- An arrow from the new first vertex to a later vertex is the prepended arrow followed by
an arrow of the original string. -/
@[simp]
theorem totalArrow_precomp_zero_succ_succ (F : ComposableArrows C n) {X : C}
    (f : X ⟶ F.left) (j : ℕ) (hj : j + 2 < n + 1 + 1) :
    (F.precomp f).totalArrow 0 ⟨j + 2, hj⟩ (Nat.zero_le _) =
      ⟨X, F.obj' (j + 1) (by omega), f ≫ F.map' 0 (j + 1) (by omega) (by omega)⟩ := by
  -- At these indices precomp inserts f before the original arrow from vertex 0 to j + 1.
  rfl

/-- Arrows between shifted vertices of a prepended string are the arrows of the original
string. -/
@[simp]
theorem totalArrow_precomp_succ_succ (F : ComposableArrows C n) {X : C}
    (f : X ⟶ F.left) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.precomp f).totalArrow i.succ j.succ (Fin.succ_le_succ_iff.mpr hij) =
      F.totalArrow i j hij := by
  -- Both endpoints lie in the shifted tail, where precomp retains the original map.
  rfl

/-- Reindexing a string of composable arrows along a functor `Φ` of the indexing posets reindexes
its arrows. -/
@[simp]
theorem totalArrow_whiskerLeft {m : ℕ} (F : ComposableArrows C m)
    (Φ : Fin (n + 1) ⥤ Fin (m + 1)) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.whiskerLeft Φ).totalArrow i j hij = F.totalArrow (Φ.obj i) (Φ.obj j) (Φ.monotone hij) := by
  -- Morphisms in the poset `Fin (m + 1)` are unique, so `Φ` sends `homOfLE hij` to `homOfLE _`.
  have h : Φ.map (homOfLE hij) = homOfLE (Φ.monotone hij) := Subsingleton.elim _ _
  simp only [totalArrow, whiskerLeft, Functor.comp_obj, Functor.comp_map, h]

/-- An arrow of the image of a string under a functor is the image of the arrow of the string. -/
@[simp]
theorem totalArrow_mapComposableArrows_obj (φ : C ⥤ D) (F : ComposableArrows C n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((φ.mapComposableArrows n).obj F).totalArrow i j hij =
      φ.toPrefunctor.mapTotal (F.totalArrow i j hij) :=
  (φ.toPrefunctor.mapTotal_mk _).symm

/-- A string of composable arrows is determined by its arrows. -/
theorem ext_of_totalArrow {F G : ComposableArrows C n}
    (h : ∀ i j (hij : i ≤ j), F.totalArrow i j hij = G.totalArrow i j hij) : F = G := by
  refine Functor.hext (fun i ↦ congrArg Quiver.Total.left (h i i le_rfl)) fun i j g ↦ ?_
  -- Morphisms in the poset `Fin (n + 1)` are unique, so `g` is the morphism `homOfLE g.le` that
  -- `totalArrow` uses, and the hypothesis `h i j g.le` applies to it.
  rw [show g = homOfLE g.le from Subsingleton.elim _ _]
  have := h i j g.le
  simp only [totalArrow, Quiver.Total.mk.injEq] at this
  exact this.2.2

variable [TopologicalSpace (Quiver.Total C)]

/-- The topology on strings of `n` composable arrows: the coarsest topology making each arrow of
the string, `F.totalArrow i j hij`, depend continuously on the string `F`. -/
instance instTopologicalSpace : TopologicalSpace (ComposableArrows C n) :=
  ⨅ (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : i ≤ j),
    .induced (fun F : ComposableArrows C n ↦ F.totalArrow i j hij) inferInstance

/-- A map into strings of composable arrows is continuous exactly when each arrow of the string
depends continuously on the argument. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → ComposableArrows C n} :
    Continuous f ↔ ∀ i j (hij : i ≤ j), Continuous fun y ↦ (f y).totalArrow i j hij := by
  simp only [continuous_iInf_rng, continuous_induced_rng, Function.comp_def]

@[fun_prop]
theorem continuous_totalArrow (i j : Fin (n + 1)) (hij : i ≤ j) :
    Continuous fun F : ComposableArrows C n ↦ F.totalArrow i j hij :=
  continuous_iff.1 continuous_id i j hij

/-- Reindexing strings of composable arrows along a functor of the indexing posets is
continuous. -/
@[fun_prop]
theorem continuous_whiskerLeft {m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    Continuous fun F : ComposableArrows C m ↦ F.whiskerLeft Φ :=
  continuous_iff.2 fun i j hij ↦ by
    simpa only [totalArrow_whiskerLeft] using continuous_totalArrow _ _ _

variable [TopologicalSpace (Quiver.Total D)]

/-- A functor that is continuous on total arrows is continuous on strings of composable arrows. -/
theorem continuous_mapComposableArrows_obj {φ : C ⥤ D} (hφ : Continuous φ.toPrefunctor.mapTotal) :
    Continuous (φ.mapComposableArrows n).obj :=
  continuous_iff.2 fun i j hij ↦ by
    simp only [totalArrow_mapComposableArrows_obj]
    exact hφ.comp (continuous_totalArrow i j hij)

/-- A functor that is an embedding on total arrows is an embedding on strings of composable
arrows. -/
theorem isEmbedding_mapComposableArrows_obj {φ : C ⥤ D} (hφ : IsEmbedding φ.toPrefunctor.mapTotal) :
    IsEmbedding (φ.mapComposableArrows n).obj := by
  refine ⟨⟨?_⟩, fun F G h ↦ ext_of_totalArrow fun i j hij ↦ hφ.injective ?_⟩
  · simp only [instTopologicalSpace, induced_iInf, induced_compose]
    refine iInf_congr fun i ↦ iInf_congr fun j ↦ iInf_congr fun hij ↦ ?_
    rw [hφ.eq_induced, induced_compose]
    simp only [Function.comp_def, totalArrow_mapComposableArrows_obj]
  · simpa only [totalArrow_mapComposableArrows_obj] using
      congrArg (fun F ↦ totalArrow F i j hij) h

end CategoryTheory.ComposableArrows

namespace TauCeti

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- The topological nerve of a category whose total arrows carry a topology: the simplicial space
of strings of composable arrows, topologized by `ComposableArrows.instTopologicalSpace`, with the
simplicial operators of `CategoryTheory.nerve C`. -/
@[expose] def topologicalNerve : SimplexCategoryᵒᵖ ⥤ TopCat.{max u v} where
  obj Δ := TopCat.of (ComposableArrows C Δ.unop.len)
  map f := TopCat.ofHom ⟨fun F ↦ F.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor,
    ComposableArrows.continuous_whiskerLeft _⟩

variable {C}

@[simp]
theorem topologicalNerve_obj (Δ : SimplexCategoryᵒᵖ) :
    (topologicalNerve C).obj Δ = TopCat.of (ComposableArrows C Δ.unop.len) := (rfl)

/-- The simplicial operators of the topological nerve are those of the nerve. -/
@[simp]
theorem topologicalNerve_map_apply {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (F : ComposableArrows C Δ.unop.len) :
    (topologicalNerve C).map f F = (nerve C).map f F := (rfl)

/-- The underlying simplicial set of the topological nerve is the nerve. -/
theorem topologicalNerve_comp_forget : topologicalNerve C ⋙ forget TopCat = nerve C := (rfl)

variable (C)

/-- The fat classifying space of a category whose total arrows carry a topology: the fat
realization of its topological nerve, with degeneracies forgotten. -/
@[expose] def fatClassifyingSpace : TopCat.{max u v} :=
  fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C)

end TauCeti

namespace CategoryTheory.Functor

open TauCeti

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)]
  {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The map of topological nerves induced by a functor that is continuous on total arrows. -/
def topologicalNerveMap (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal) :
    topologicalNerve C ⟶ topologicalNerve D where
  app Δ := TopCat.ofHom ⟨(nerveMap φ).app Δ,
    ComposableArrows.continuous_mapComposableArrows_obj hφ⟩
  naturality _ _ f := by
    ext F
    rfl

/-- The map of topological nerves induced by a functor applies the functor to each string. -/
@[simp]
theorem topologicalNerveMap_app_apply (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal)
    (Δ : SimplexCategoryᵒᵖ) (F : ComposableArrows C Δ.unop.len) :
    (topologicalNerveMap φ hφ).app Δ F = (φ.mapComposableArrows _).obj F := (rfl)

/-- The underlying function of a component of the map of topological nerves induced by a functor
applies the functor to strings. -/
theorem coe_topologicalNerveMap_app (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal)
    (Δ : SimplexCategoryᵒᵖ) :
    ⇑((topologicalNerveMap φ hφ).app Δ) = (φ.mapComposableArrows Δ.unop.len).obj := (rfl)

/-- The map of topological nerves induced by the identity functor is the identity. -/
@[simp]
theorem topologicalNerveMap_id (h : Continuous (𝟭 C).toPrefunctor.mapTotal) :
    topologicalNerveMap (𝟭 C) h = 𝟙 (topologicalNerve C) := by
  ext Δ F
  rfl

/-- The map of topological nerves induced by a composite of functors is the composite of the
induced maps. -/
theorem topologicalNerveMap_comp {E : Type u} [Category.{v} E] [TopologicalSpace (Quiver.Total E)]
    (φ : C ⥤ D) (ψ : D ⥤ E) (hφ : Continuous φ.toPrefunctor.mapTotal)
    (hψ : Continuous ψ.toPrefunctor.mapTotal) (hφψ : Continuous (φ ⋙ ψ).toPrefunctor.mapTotal) :
    topologicalNerveMap (φ ⋙ ψ) hφψ = topologicalNerveMap φ hφ ≫ topologicalNerveMap ψ hψ := by
  ext Δ F
  rfl

/-- The map of fat classifying spaces induced by a functor that is continuous on total arrows: the
fat realization of the induced map of topological nerves
(`CategoryTheory.Functor.fatClassifyingSpaceMap_eq`). -/
def fatClassifyingSpaceMap (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal) :
    fatClassifyingSpace C ⟶ fatClassifyingSpace D :=
  fatRealization.map
    (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op (topologicalNerveMap φ hφ))

/-- The map of fat classifying spaces induced by a functor is the fat realization of the induced
map of topological nerves, restricted to the semi-simplicial part. -/
theorem fatClassifyingSpaceMap_eq (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap φ hφ = fatRealization.map
      (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op (topologicalNerveMap φ hφ)) :=
  (rfl)

/-- The map of fat classifying spaces induced by a functor applies the functor to the string of
each simplex and keeps its barycentric coordinates. -/
theorem fatClassifyingSpaceMap_ι (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal)
    (n : SemiSimplexCategory) (F : ComposableArrows C n.len)
    (t : SemiSimplexCategory.toTop.{max u v}.obj n) :
    fatClassifyingSpaceMap φ hφ (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n ((φ.mapComposableArrows n.len).obj F, t) :=
  fatRealization.map_ι
    (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op (topologicalNerveMap φ hφ)) n F t

/-- The map of fat classifying spaces induced by the identity functor is the identity. -/
@[simp]
theorem fatClassifyingSpaceMap_id (h : Continuous (𝟭 C).toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap (𝟭 C) h = 𝟙 (fatClassifyingSpace C) := by
  rw [fatClassifyingSpaceMap_eq, topologicalNerveMap_id, Functor.whiskerLeft_id',
    fatRealization.map_id]
  rfl

/-- The map of fat classifying spaces induced by a composite of functors is the composite of the
induced maps. -/
theorem fatClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (φ : C ⥤ D) (ψ : D ⥤ E)
    (hφ : Continuous φ.toPrefunctor.mapTotal) (hψ : Continuous ψ.toPrefunctor.mapTotal)
    (hφψ : Continuous (φ ⋙ ψ).toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap (φ ⋙ ψ) hφψ =
      fatClassifyingSpaceMap φ hφ ≫ fatClassifyingSpaceMap ψ hψ := by
  rw [fatClassifyingSpaceMap_eq, fatClassifyingSpaceMap_eq, fatClassifyingSpaceMap_eq,
    topologicalNerveMap_comp φ ψ hφ hψ, Functor.whiskerLeft_comp, fatRealization.map_comp]
  rfl

end CategoryTheory.Functor
