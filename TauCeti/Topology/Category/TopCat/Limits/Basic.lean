/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Coherent
public import TauCeti.Topology.Coherent

/-!
# Basic facts about colimits in `TopCat`

The initial object of `TopCat` is empty, through Mathlib's isomorphism `TopCat.initialIsoPEmpty`.
As an instance, this makes the separation properties of the empty space, such as being Hausdorff,
available for it by instance search. It is the base of every CW complex in Mathlib's categorical
sense, `TopCat.CWComplex X`, which is a relative CW complex over the map out of `⊥_ TopCat`.

A directed colimit in `TopCat` along injective transition maps has injective colimit maps
(`TauCeti.TopCat.injective_ι_of_isColimit`), since the forgetful functor to types preserves it.

The ranges of the maps to the vertex of a cocone over a preorder increase
(`TauCeti.TopCat.monotone_range_ι`). The colimit maps of any colimit in `TopCat` jointly cover it
(`TauCeti.TopCat.iUnion_range_ι_of_isColimit`), and its topology is coherent with their ranges
(`TauCeti.TopCat.isCoherentWith_range_ι_of_isColimit`): a set is closed as soon as it meets each
range in a relatively closed set. These are the hypotheses under which the colimit of a sequence is
treated as the increasing union of its stages.

Conversely, an increasing family of subsets `A j` of a space `Y`, indexed by a directed order,
forms a diagram in `TopCat` along the inclusions (`TauCeti.TopCat.subspaceDiagram`), with `Y` as
a cocone over it (`TauCeti.TopCat.subspaceCocone`). If the `A j` cover `Y` and `Y` carries the
topology coherent with them, then `Y` is the colimit of this diagram
(`TauCeti.TopCat.isColimitOfIsCoherentWith`): maps out of the `A j` agreeing along the inclusions
glue by `ContinuousMap.liftCoherent`.
-/

public section

open CategoryTheory Limits

universe w u

namespace TopCat

/-- The initial topological space is empty. -/
instance initial_isEmpty : IsEmpty (⊥_ TopCat.{u}) :=
  Function.isEmpty initialIsoPEmpty.hom

end TopCat

namespace TauCeti.TopCat

/-- If all transition maps of a directed diagram in `TopCat` are injective, then so are the maps
from the objects of the diagram to its colimit. -/
theorem injective_ι_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J]
    {F : J ⥤ TopCat.{u}} (hF : ∀ ⦃i j : J⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    {c : Cocone F} (hc : IsColimit c) (i : J) : Function.Injective (c.ι.app i) := fun x y h ↦ by
  have : Nonempty J := ⟨i⟩
  obtain ⟨k, g, hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget TopCat) hc) x y).1 h
  exact hF (leOfHom g) hk

/-- The ranges of the maps of a diagram in `TopCat` indexed by a preorder to the vertex of a cocone
increase along the order. -/
theorem monotone_range_ι {J : Type w} [Preorder J] {F : J ⥤ TopCat.{u}} (c : Cocone F) :
    Monotone fun j ↦ (Set.range (c.ι.app j) : Set c.pt) := fun i j hij ↦ by
  rintro _ ⟨w, rfl⟩
  exact ⟨F.map (homOfLE hij) w, by rw [← ConcreteCategory.comp_apply, c.w]⟩

/-- The maps to a colimit in `TopCat` are jointly surjective. -/
theorem iUnion_range_ι_of_isColimit {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    {c : Cocone F} (hc : IsColimit c) : ⋃ j, (Set.range (c.ι.app j) : Set c.pt) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 <|
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) x

/-- A colimit in `TopCat` carries the topology coherent with the ranges of the maps to it: a set
whose intersection with every range is relatively closed is closed. -/
theorem isCoherentWith_range_ι_of_isColimit {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    {c : Cocone F} (hc : IsColimit c) :
    Topology.IsCoherentWith (Set.range fun j ↦ (Set.range (c.ι.app j) : Set c.pt)) := by
  refine .of_isClosed fun t ht ↦ (TopCat.isClosed_iff_of_isColimit _ hc t).2 fun j ↦ ?_
  -- The preimage of `t` in `F.obj j` is its preimage in the range, pulled back along `c.ι.app j`.
  exact (ht _ ⟨j, rfl⟩).preimage
    ((c.ι.app j).hom.continuous.subtype_mk fun x ↦ Set.mem_range_self x)

section Subspace

variable {J : Type w} [Preorder J] {Y : Type u} [TopologicalSpace Y] {A : J → Set Y}
  (hA : Monotone A)

/-- The diagram in `TopCat` of an increasing family of subsets of a space and their inclusions. -/
@[expose, simps map]
def subspaceDiagram : J ⥤ TopCat.{u} where
  obj j := TopCat.of (A j)
  map u := TopCat.ofHom ⟨Set.inclusion (hA (leOfHom u)), continuous_inclusion _⟩

/-- A space is a cocone over the diagram of an increasing family of its subsets, by the
inclusions. -/
@[expose, simps ι_app]
def subspaceCocone : Cocone (subspaceDiagram hA) where
  pt := TopCat.of Y
  ι := { app j := TopCat.ofHom (ContinuousMap.subtypeVal _) }

/-- **A coherent increasing union is a colimit.** If an increasing family of subsets `A j` of `Y`,
indexed by a directed order, covers `Y`, and `Y` carries the topology coherent with the `A j`, then
`Y` is the colimit in `TopCat` of the `A j` along the inclusions. -/
noncomputable def isColimitOfIsCoherentWith [IsDirectedOrder J] (hAY : ⋃ j, A j = Set.univ)
    (hAc : Topology.IsCoherentWith (Set.range A)) : IsColimit (subspaceCocone hA) :=
  -- Maps out of the `A j` forming a cocone agree on overlaps, as both factor through a larger
  -- `A k`, so they glue to a continuous map on `Y`.
  have hφ (s : Cocone (subspaceDiagram hA)) (i j : J) (y : Y) (hi : y ∈ A i) (hj : y ∈ A j) :
      s.ι.app i ⟨y, hi⟩ = s.ι.app j ⟨y, hj⟩ := by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact (ConcreteCategory.congr_hom (s.w (homOfLE hik)) ⟨y, hi⟩).symm.trans
      (ConcreteCategory.congr_hom (s.w (homOfLE hjk)) ⟨y, hj⟩)
  let desc (s : Cocone (subspaceDiagram hA)) : C(Y, s.pt) :=
    ContinuousMap.liftCoherent A (fun j ↦ (s.ι.app j).hom) (hφ s) hAc hAY
  have hdesc (s : Cocone (subspaceDiagram hA)) (j : J) (y : A j) : desc s y = s.ι.app j y :=
    ContinuousMap.liftCoherent_coe y
  { desc s := TopCat.ofHom (desc s)
    fac s j := by
      ext y
      exact hdesc s j y
    uniq s m hm := by
      ext y
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hAY ▸ Set.mem_univ y)
      exact (ConcreteCategory.congr_hom (hm j) ⟨y, hj⟩).trans (hdesc s j ⟨y, hj⟩).symm }

end Subspace

end TauCeti.TopCat
