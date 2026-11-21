/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.FatRealization.Skeleton

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

When the total arrows form a regular, `T1`, second-countable space, so do the strings of
composable arrows (the `T1Space`, `RegularSpace` and `SecondCountableTopology` instances on
`ComposableArrows C n`). The levels of the topological nerve are then regular, `T1` and Lindelöf,
so the fat classifying space is paracompact and `T4`
(`TauCeti.fatClassifyingSpace.paracompactSpace`, `TauCeti.fatClassifyingSpace.t4Space`), by
paracompactness of fat realizations (`TauCeti.fatRealization.paracompactSpace`).

A functor `Φ : C ⥤ D` whose action on total arrows (`Prefunctor.mapTotal`) is continuous induces
maps `TauCeti.topologicalNerveMap Φ` of topological nerves and `TauCeti.fatClassifyingSpaceMap Φ`
of fat classifying spaces, by applying `Φ` to strings of composable arrows. A family of functors
`Φ s`, `s ∈ [0, 1]`, depending continuously on `s` and the total arrow induces a homotopy
`TauCeti.fatClassifyingSpaceHomotopy` from the map induced by `Φ 0` to that induced by `Φ 1`.
If `Φ` is an embedding on total arrows, it induces levelwise embeddings
(`CategoryTheory.ComposableArrows.isEmbedding_mapComposableArrows_obj`). Recording all arrows
`i ⟶ j` (`i ≤ j`) embeds `ComposableArrows C n` into a finite product of copies of `Quiver.Total C`
(`CategoryTheory.ComposableArrows.isEmbedding_totalArrowTuple`), so both `ComposableArrows C n` and
`(topologicalNerve C).obj Δ` inherit separation, regularity, countability and metrizability from
`Quiver.Total C`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Topology

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {n : ℕ}

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

/-- Strings of composable arrows form a `T1` space when the total arrows do. -/
instance [T1Space (Quiver.Total C)] : T1Space (ComposableArrows C n) where
  t1 F := by
    have : ({F} : Set (ComposableArrows C n)) =
        ⋂ (i) (j) (hij : i ≤ j), (fun G ↦ G.totalArrow i j hij) ⁻¹' {F.totalArrow i j hij} := by
      ext G
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage]
      exact ⟨by rintro rfl _ _ _; rfl, fun h ↦ ext_of_totalArrow h⟩
    rw [this]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun hij ↦
      isClosed_singleton.preimage (continuous_totalArrow i j hij)

/-- Strings of composable arrows form a regular space when the total arrows do. -/
instance [RegularSpace (Quiver.Total C)] : RegularSpace (ComposableArrows C n) :=
  regularSpace_iInf fun _ ↦ regularSpace_iInf fun _ ↦ regularSpace_iInf fun _ ↦
    regularSpace_induced _

/-- Strings of composable arrows form a second-countable space when the total arrows do. -/
instance [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (ComposableArrows C n) :=
  TopologicalSpace.secondCountableTopology_iInf fun _ ↦
    TopologicalSpace.secondCountableTopology_iInf fun _ ↦
      TopologicalSpace.secondCountableTopology_iInf fun _ ↦
        TopologicalSpace.secondCountableTopology_induced _ _ _

/-- Reindexing strings of composable arrows along a functor of the indexing posets is
continuous. -/
@[fun_prop]
theorem continuous_whiskerLeft {m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    Continuous fun F : ComposableArrows C m ↦ F.whiskerLeft Φ :=
  continuous_iff.2 fun i j hij ↦ by
    simpa only [totalArrow_whiskerLeft] using continuous_totalArrow _ _ _

variable {D : Type*} [Category D] [TopologicalSpace (Quiver.Total D)]

/-- Applying a functor that is continuous on total arrows to strings of composable arrows is
continuous. -/
theorem continuous_mapComposableArrows_obj {Φ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) : Continuous (Φ.mapComposableArrows n).obj :=
  continuous_iff.2 fun i j hij ↦ by
    simpa only [totalArrow_mapComposableArrows_obj, Function.comp_def] using
      hΦ.comp (continuous_totalArrow i j hij)

/-- Applying a family of functors to strings of composable arrows is jointly continuous in the
parameter and the string when it is so on total arrows. -/
theorem continuous_uncurry_mapComposableArrows_obj {T : Type*} [TopologicalSpace T]
    {Φ : T → C ⥤ D}
    (hΦ : Continuous fun p : T × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    Continuous fun p : T × ComposableArrows C n ↦ ((Φ p.1).mapComposableArrows n).obj p.2 :=
  continuous_iff.2 fun i j hij ↦ by
    simpa only [totalArrow_mapComposableArrows_obj, Function.comp_def] using
      hΦ.comp (continuous_fst.prodMk ((continuous_totalArrow i j hij).comp continuous_snd))

/-- A functor that is an embedding on total arrows is an embedding on strings of composable
arrows. -/
theorem isEmbedding_mapComposableArrows_obj {Φ : C ⥤ D} (hΦ : IsEmbedding Φ.toPrefunctor.mapTotal) :
    IsEmbedding (Φ.mapComposableArrows n).obj := by
  refine ⟨⟨?_⟩, fun F G h ↦ ext_of_totalArrow fun i j hij ↦ hΦ.injective ?_⟩
  · simp only [instTopologicalSpace, induced_iInf, induced_compose]
    refine iInf_congr fun i ↦ iInf_congr fun j ↦ iInf_congr fun hij ↦ ?_
    rw [hΦ.eq_induced, induced_compose]
    simp only [Function.comp_def, totalArrow_mapComposableArrows_obj]
  · simpa only [totalArrow_mapComposableArrows_obj] using
      congrArg (fun F ↦ totalArrow F i j hij) h

/-- Recording all total arrows `F.totalArrow i j hij` (`i ≤ j`) embeds strings of `n` composable
arrows into a finite product of copies of `Quiver.Total C`. No continuity of source, target,
units or composition is needed. -/
theorem isEmbedding_totalArrowTuple :
    IsEmbedding fun (F : ComposableArrows C n)
      (p : (i : Fin (n + 1)) × (j : Fin (n + 1)) × PLift (i ≤ j)) ↦
        F.totalArrow p.1 p.2.1 p.2.2.down :=
  ⟨⟨by
    simp only [instTopologicalSpace, induced_to_pi, iInf_sigma]
    exact iInf_congr fun _ ↦ iInf_congr fun _ ↦ (iInf_plift_down _).symm⟩,
    fun _ _ h ↦ ext_of_totalArrow fun i j hij ↦ congrFun h ⟨i, j, ⟨hij⟩⟩⟩

instance instT0Space [T0Space (Quiver.Total C)] : T0Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t0Space
instance instT1Space [T1Space (Quiver.Total C)] : T1Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t1Space
instance instT2Space [T2Space (Quiver.Total C)] : T2Space (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.t2Space
instance instRegularSpace [RegularSpace (Quiver.Total C)] : RegularSpace (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.isInducing.regularSpace
instance instFirstCountableTopology [FirstCountableTopology (Quiver.Total C)] :
    FirstCountableTopology (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.firstCountableTopology
instance instSecondCountableTopology [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.secondCountableTopology
instance instMetrizableSpace [TopologicalSpace.MetrizableSpace (Quiver.Total C)] :
    TopologicalSpace.MetrizableSpace (ComposableArrows C n) :=
  isEmbedding_totalArrowTuple.metrizableSpace

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

section TopologicalNerveInstances

variable (C) (Δ : SimplexCategoryᵒᵖ)

instance [T0Space (Quiver.Total C)] : T0Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T0Space (ComposableArrows C Δ.unop.len))
instance [T1Space (Quiver.Total C)] : T1Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T1Space (ComposableArrows C Δ.unop.len))
instance [T2Space (Quiver.Total C)] : T2Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T2Space (ComposableArrows C Δ.unop.len))
instance [RegularSpace (Quiver.Total C)] : RegularSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (RegularSpace (ComposableArrows C Δ.unop.len))
instance [CompactSpace (ComposableArrows C Δ.unop.len)] :
    CompactSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (CompactSpace (ComposableArrows C Δ.unop.len))
instance [FirstCountableTopology (Quiver.Total C)] :
    FirstCountableTopology ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (FirstCountableTopology (ComposableArrows C Δ.unop.len))
instance [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (SecondCountableTopology (ComposableArrows C Δ.unop.len))
instance [TopologicalSpace.MetrizableSpace (Quiver.Total C)] :
    TopologicalSpace.MetrizableSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace (ComposableArrows C Δ.unop.len))

end TopologicalNerveInstances

variable (C)

/-- The fat classifying space of a category whose total arrows carry a topology: the fat
realization of its topological nerve, with degeneracies forgotten. -/
@[expose] def fatClassifyingSpace : TopCat.{max u v} :=
  fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C)

variable {C}

section Paracompact

variable [RegularSpace (Quiver.Total C)] [T1Space (Quiver.Total C)]
  [SecondCountableTopology (Quiver.Total C)]

-- The levels of the topological nerve are spaces of strings of composable arrows.
private instance (n : SemiSimplexCategoryᵒᵖ) :
    RegularSpace ((SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C).obj n) :=
  inferInstanceAs (RegularSpace (ComposableArrows C _))

private instance (n : SemiSimplexCategoryᵒᵖ) :
    T1Space ((SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C).obj n) :=
  inferInstanceAs (T1Space (ComposableArrows C _))

private instance (n : SemiSimplexCategoryᵒᵖ) :
    LindelofSpace ((SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve C).obj n) :=
  inferInstanceAs (LindelofSpace (ComposableArrows C _))

/-- **Paracompactness of fat classifying spaces.** The fat classifying space of a category whose
total arrows form a regular, `T1`, second-countable space, such as a groupoid whose arrows form a
second-countable Hausdorff manifold, is paracompact. -/
instance fatClassifyingSpace.paracompactSpace : ParacompactSpace (fatClassifyingSpace C) :=
  fatRealization.paracompactSpace

/-- The fat classifying space of a category whose total arrows form a regular, `T1`,
second-countable space is normal and `T1`, in particular Hausdorff. -/
instance fatClassifyingSpace.t4Space : T4Space (fatClassifyingSpace C) :=
  fatRealization.t4Space

end Paracompact

/-- Two maps out of the fat classifying space agree once they agree on every simplex. -/
@[ext]
theorem fatClassifyingSpace.hom_ext {Z : TopCat.{max u v}} {g h : fatClassifyingSpace C ⟶ Z}
    (H : ∀ (n : SemiSimplexCategory)
      (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj n).len)
      (t : SemiSimplexCategory.toTop.obj n),
        g (fatRealization.ι _ n (F, t)) = h (fatRealization.ι _ n (F, t))) : g = h :=
  fatRealization.hom_ext _ H

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

open SemiSimplexCategory (toSimplexCategory)

/-- The map of topological nerves induced by a functor that is continuous on total arrows: it
applies the functor to strings of composable arrows. -/
def topologicalNerveMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    topologicalNerve C ⟶ topologicalNerve D where
  app Δ := TopCat.ofHom ⟨(Φ.mapComposableArrows _).obj,
    ComposableArrows.continuous_mapComposableArrows_obj hΦ⟩

@[simp]
theorem topologicalNerveMap_app_apply (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (Δ : SimplexCategoryᵒᵖ) (F : ComposableArrows C Δ.unop.len) :
    (topologicalNerveMap Φ hΦ).app Δ F = (Φ.mapComposableArrows _).obj F :=
  (rfl)

/-- The underlying function of a component of the map of topological nerves induced by a functor
applies the functor to strings. -/
theorem coe_topologicalNerveMap_app (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (Δ : SimplexCategoryᵒᵖ) :
    ⇑((topologicalNerveMap Φ hΦ).app Δ) = (Φ.mapComposableArrows Δ.unop.len).obj :=
  (rfl)

variable (C) in
@[simp]
theorem topologicalNerveMap_id :
    topologicalNerveMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (topologicalNerve C) :=
  (rfl)

theorem topologicalNerveMap_comp {E : Type u} [Category.{v} E] [TopologicalSpace (Quiver.Total E)]
    (Φ : C ⥤ D) (Ψ : D ⥤ E) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    topologicalNerveMap (Φ ⋙ Ψ) (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸
        hΨ.comp hΦ) =
      topologicalNerveMap Φ hΦ ≫ topologicalNerveMap Ψ hΨ :=
  (rfl)

/-- The map of fat classifying spaces induced by a functor that is continuous on total arrows: the
fat realization of the induced map of topological nerves. -/
def fatClassifyingSpaceMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatClassifyingSpace C ⟶ fatClassifyingSpace D :=
  fatRealization.map (Functor.whiskerLeft toSimplexCategory.op (topologicalNerveMap Φ hΦ))

/-- The map of fat classifying spaces induced by a functor is the fat realization of the induced
map of topological nerves, restricted to the semi-simplicial part. -/
theorem fatClassifyingSpaceMap_eq (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap Φ hΦ =
      fatRealization.map (Functor.whiskerLeft toSimplexCategory.op (topologicalNerveMap Φ hΦ)) :=
  (rfl)

/-- The map of fat classifying spaces induced by a functor applies the functor to the string of
composable arrows of each simplex. This is not a `simp` lemma: `simp` rewrites the dependent type
of the string `F` on its left-hand side. -/
theorem fatClassifyingSpaceMap_ι (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (n : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    fatClassifyingSpaceMap Φ hΦ (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n ((Φ.mapComposableArrows _).obj F, t) :=
  fatRealization.map_ι (Functor.whiskerLeft toSimplexCategory.op (topologicalNerveMap Φ hΦ)) n F
    t

/-- Two functors that agree on strings of composable arrows induce the same map of fat classifying
spaces. -/
theorem fatClassifyingSpaceMap_eq_of_mapComposableArrows_obj {Φ Ψ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal)
    (h : ∀ n F, (Φ.mapComposableArrows n).obj F = (Ψ.mapComposableArrows n).obj F) :
    fatClassifyingSpaceMap Φ hΦ = fatClassifyingSpaceMap Ψ hΨ :=
  fatClassifyingSpace.hom_ext fun n F t ↦ (fatClassifyingSpaceMap_ι Φ hΦ n F t).trans <|
    (congrArg (fun F ↦ fatRealization.ι _ n (F, t)) (h _ F)).trans
      (fatClassifyingSpaceMap_ι Ψ hΨ n F t).symm

variable (C) in
@[simp]
theorem fatClassifyingSpaceMap_id :
    fatClassifyingSpaceMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (fatClassifyingSpace C) :=
  fatRealization.map_id

theorem fatClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap (Φ ⋙ Ψ) (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸
        hΨ.comp hΦ) =
      fatClassifyingSpaceMap Φ hΦ ≫ fatClassifyingSpaceMap Ψ hΨ :=
  fatRealization.map_comp (Functor.whiskerLeft toSimplexCategory.op (topologicalNerveMap Φ hΦ))
    (Functor.whiskerLeft toSimplexCategory.op (topologicalNerveMap Ψ hΨ))

/-- A family of functors `Φ s`, `s ∈ [0, 1]`, depending continuously on `s` and the total arrow,
induces the homotopy `(s, [F, t]) ↦ [Φ s ∘ F, t]` from the map of fat classifying spaces induced by
`Φ 0` to that induced by `Φ 1`. -/
def fatClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (fatClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (fatClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  fatRealization.homotopy
    (fun s ↦ Functor.whiskerLeft toSimplexCategory.op
      (topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))))
    fun _ ↦ ComposableArrows.continuous_uncurry_mapComposableArrows_obj hΦ

theorem fatClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    fatClassifyingSpaceHomotopy Φ hΦ (s, fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n (((Φ s).mapComposableArrows _).obj F, t) :=
  fatRealization.homotopy_apply_ι
    (fun s ↦ Functor.whiskerLeft toSimplexCategory.op
      (topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))) _ s n F t

end TauCeti
