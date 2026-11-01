/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# The topological nerve of a category with a topology on its arrows

Let `C` be a category whose total space of arrows `Quiver.Total C` carries a topology, such as
the arrows of a topological or Lie groupoid. The `n`-simplices of Mathlib's nerve `nerve C` are
the strings `F : ComposableArrows C n` of `n` composable arrows. This file topologizes them by
recording, for all `i ≤ j`, the composite `F.map (i ⟶ j)` as a total arrow
(`CategoryTheory.ComposableArrows.totalArrow`): the topology on `ComposableArrows C n` is induced
by the map to the product of copies of `Quiver.Total C` indexed by the pairs `i ≤ j`. The
identity arrows `F.map (𝟙 i)` record the objects, so no separate topology on objects is needed.

Recording every composite, rather than only the consecutive arrows, makes each simplicial
operator of the nerve continuous with no hypothesis on composition: precomposing with a functor
`Fin (m + 1) ⥤ Fin (n + 1)` only selects and repeats composites. For a topological groupoid,
whose units and composition are continuous, each composite is a continuous function of the `n`
consecutive arrows (of the single object when `n = 0`), so this topology agrees with the usual
subspace topology on composable tuples.

The result is the simplicial space `TauCeti.topologicalNerve C`, whose underlying simplicial set
is `nerve C`. A functor whose action on total arrows (`Prefunctor.mapTotal`) is continuous induces
a map of topological nerves, and an embedding on total arrows induces levelwise embeddings
(`CategoryTheory.ComposableArrows.isEmbedding_mapComposableArrows_obj`). The fat realization of
the topological nerve, forgetting its degeneracies, is the fat classifying space
`TauCeti.fatClassifyingSpace C`; for a topological groupoid it is the fat model of the classifying
space.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112,
  §2.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Opposite Topology

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D] {m n : ℕ}

/-- The composite `F.map (i ⟶ j)` of a string of composable arrows, as a total arrow of `C`. -/
@[expose] def totalArrow (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    Quiver.Total C :=
  ⟨F.obj i, F.obj j, F.map (homOfLE hij)⟩

/-- The source of a composite is its first index's object. -/
@[simp]
theorem totalArrow_left (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).left = F.obj i := (rfl)

/-- The target of a composite is its last index's object. -/
@[simp]
theorem totalArrow_right (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).right = F.obj j := (rfl)

/-- The arrow underlying a composite is the image of the order relation between its indices. -/
@[simp]
theorem totalArrow_hom (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).hom = F.map (homOfLE hij) := (rfl)

/-- A composite of a precomposed string is the composite of the original string between the
image indices. -/
theorem totalArrow_whiskerLeft (F : ComposableArrows C n) (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (i j : Fin (m + 1)) (hij : i ≤ j) :
    (F.whiskerLeft Φ).totalArrow i j hij =
      F.totalArrow (Φ.obj i) (Φ.obj j) (Φ.map (homOfLE hij)).le :=
  (rfl)

/-- A composite of the image of a string under a functor is the image of its composite. -/
@[simp]
theorem totalArrow_mapComposableArrows_obj (φ : C ⥤ D) (F : ComposableArrows C n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((φ.mapComposableArrows n).obj F).totalArrow i j hij =
      φ.toPrefunctor.mapTotal (F.totalArrow i j hij) :=
  (rfl)

/-- Strings of composable arrows are determined by their composites. -/
theorem totalArrow_injective :
    Function.Injective fun (F : ComposableArrows C n) (p : {p : Fin (n + 1) × Fin (n + 1) //
      p.1 ≤ p.2}) => F.totalArrow p.1.1 p.1.2 p.2 := by
  intro F G h
  have hp (i j : Fin (n + 1)) (hij : i ≤ j) : F.totalArrow i j hij = G.totalArrow i j hij :=
    congrFun h ⟨(i, j), hij⟩
  refine Functor.hext (fun i => congrArg Quiver.Total.left (hp i i le_rfl)) fun i j g => ?_
  rw [show g = homOfLE g.le from Subsingleton.elim _ _]
  have := hp i j g.le
  simp only [totalArrow, Quiver.Total.mk.injEq] at this
  exact this.2.2

variable [TopologicalSpace (Quiver.Total C)]

/-- The topology on strings of composable arrows induced by recording all their composites as
total arrows. -/
instance instTopologicalSpace : TopologicalSpace (ComposableArrows C n) :=
  .induced (fun F (p : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}) =>
    F.totalArrow p.1.1 p.1.2 p.2) inferInstance

/-- The topology on strings of composable arrows is induced by their composites. -/
theorem isEmbedding_totalArrow :
    IsEmbedding fun (F : ComposableArrows C n) (p : {p : Fin (n + 1) × Fin (n + 1) //
      p.1 ≤ p.2}) => F.totalArrow p.1.1 p.1.2 p.2 :=
  ⟨⟨rfl⟩, totalArrow_injective⟩

/-- Each composite of a string of composable arrows depends continuously on the string. -/
@[fun_prop]
theorem continuous_totalArrow (i j : Fin (n + 1)) (hij : i ≤ j) :
    Continuous fun F : ComposableArrows C n => F.totalArrow i j hij :=
  (continuous_apply (⟨(i, j), hij⟩ : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2})).comp
    isEmbedding_totalArrow.continuous

/-- A map into strings of composable arrows is continuous exactly when each of its composites
is. -/
theorem continuous_iff {Y : Type*} [TopologicalSpace Y] {f : Y → ComposableArrows C n} :
    Continuous f ↔ ∀ i j (hij : i ≤ j), Continuous fun y => (f y).totalArrow i j hij := by
  rw [isEmbedding_totalArrow.isInducing.continuous_iff, continuous_pi_iff]
  exact ⟨fun h i j hij => h ⟨(i, j), hij⟩, fun h p => h p.1.1 p.1.2 p.2⟩

/-- Precomposing strings of composable arrows with a functor `Fin (m + 1) ⥤ Fin (n + 1)`, such as
a simplicial operator of the nerve, is continuous. -/
@[fun_prop]
theorem continuous_whiskerLeft (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    Continuous fun F : ComposableArrows C n => F.whiskerLeft Φ :=
  continuous_iff.2 fun i j hij => by
    simpa only [totalArrow_whiskerLeft] using continuous_totalArrow _ _ _

variable [TopologicalSpace (Quiver.Total D)]

/-- A functor that is continuous on total arrows is continuous on strings of composable arrows. -/
theorem continuous_mapComposableArrows_obj {φ : C ⥤ D} (hφ : Continuous φ.toPrefunctor.mapTotal) :
    Continuous (φ.mapComposableArrows n).obj :=
  continuous_iff.2 fun i j hij => hφ.comp (continuous_totalArrow i j hij)

/-- A functor that is an embedding on total arrows is an embedding on strings of composable
arrows. -/
theorem isEmbedding_mapComposableArrows_obj {φ : C ⥤ D} (hφ : IsEmbedding φ.toPrefunctor.mapTotal) :
    IsEmbedding (φ.mapComposableArrows n).obj := by
  refine IsEmbedding.of_comp (continuous_mapComposableArrows_obj hφ.continuous)
    isEmbedding_totalArrow.continuous ?_
  have : ((fun (F : ComposableArrows D n) (p : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}) =>
      F.totalArrow p.1.1 p.1.2 p.2) ∘ (φ.mapComposableArrows n).obj) =
      (fun F p => φ.toPrefunctor.mapTotal (F p)) ∘ (fun (F : ComposableArrows C n)
        (p : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2}) => F.totalArrow p.1.1 p.1.2 p.2) :=
    (rfl)
  rw [this]
  exact (IsEmbedding.piMap fun _ => hφ).comp isEmbedding_totalArrow

end CategoryTheory.ComposableArrows

namespace TauCeti

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- The topological nerve of a category with a topology on its total arrows: the simplicial
space whose `n`-simplices are the strings of `n` composable arrows, topologized by their
composites, with the simplicial operators of `nerve C`. -/
@[expose] def topologicalNerve : SimplexCategoryᵒᵖ ⥤ TopCat.{max u v} where
  obj Δ := TopCat.of (ComposableArrows C Δ.unop.len)
  map f := TopCat.ofHom ⟨(nerve C).map f, ComposableArrows.continuous_whiskerLeft _⟩

/-- The `n`-simplices of the topological nerve are the strings of `n` composable arrows. -/
theorem topologicalNerve_obj (Δ : SimplexCategoryᵒᵖ) :
    (topologicalNerve C).obj Δ = TopCat.of (ComposableArrows C Δ.unop.len) := (rfl)

/-- The simplicial operators of the topological nerve are those of the nerve. -/
@[simp]
theorem topologicalNerve_map_apply {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (F : ComposableArrows C Δ.unop.len) : (topologicalNerve C).map f F = (nerve C).map f F :=
  (rfl)

/-- Forgetting the topology of the topological nerve gives the nerve. -/
theorem topologicalNerve_comp_forget : topologicalNerve C ⋙ forget TopCat = nerve C := (rfl)

variable {C} {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

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

variable (C)

/-- The fat classifying space of a category with a topology on its total arrows: the fat
realization of its topological nerve, which forgets the degeneracies. For a topological groupoid
this is the fat model `‖N C‖` of its classifying space. It is an abbreviation so that the API of
`TauCeti.fatRealization` applies directly. -/
abbrev fatClassifyingSpace : TopCat.{max u v} :=
  fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C)

variable {C}

/-- The map of fat classifying spaces induced by a functor that is continuous on total arrows: the
fat realization of the induced map of topological nerves. -/
abbrev fatClassifyingSpaceMap (φ : C ⥤ D) (hφ : Continuous φ.toPrefunctor.mapTotal) :
    fatClassifyingSpace C ⟶ fatClassifyingSpace D :=
  fatRealization.map
    (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op (topologicalNerveMap φ hφ))

end TauCeti
