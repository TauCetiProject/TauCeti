/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Combinatorics.Quiver.Subquiver
public import TauCeti.AlgebraicTopology.FatRealization

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
product of arrow spaces. For action groupoids this identification is
`TauCeti.ActionGroupoid.nerveHomeomorph`.

The *fat classifying space* `TauCeti.fatClassifyingSpace C` is the fat realization
(`TauCeti.fatRealization`) of the underlying semi-simplicial space, obtained by forgetting
degeneracies along `SemiSimplexCategory.toSimplexCategory`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Topology

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {n : ℕ}

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

/-- Reindexing a string of composable arrows along a functor `Φ` of the indexing posets reindexes
its arrows. -/
@[simp]
theorem totalArrow_whiskerLeft {m : ℕ} (F : ComposableArrows C m)
    (Φ : Fin (n + 1) ⥤ Fin (m + 1)) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.whiskerLeft Φ).totalArrow i j hij = F.totalArrow (Φ.obj i) (Φ.obj j) (Φ.monotone hij) := by
  -- Morphisms in the poset `Fin (m + 1)` are unique, so `Φ` sends `homOfLE hij` to `homOfLE _`.
  have h : Φ.map (homOfLE hij) = homOfLE (Φ.monotone hij) := Subsingleton.elim _ _
  simp only [totalArrow, whiskerLeft, Functor.comp_obj, Functor.comp_map, h]

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
