/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Coherent
public import TauCeti.Topology.Coherent

/-!
# Basic facts about limits and colimits in `TopCat`

The `j`-th coordinate of the image of a point under the map `IsLimit.map c hd η` between limit
cones in `TopCat` is the image under `η j` of its `j`-th coordinate (`TopCat.isLimitMap_π_apply`).

The initial object of `TopCat` is empty, through Mathlib's isomorphism `TopCat.initialIsoPEmpty`.
As an instance, this makes the separation properties of the empty space, such as being Hausdorff,
available for it by instance search. It is the base of every CW complex in Mathlib's categorical
sense, `TopCat.CWComplex X`, which is a relative CW complex over the map out of `⊥_ TopCat`.

A filtered colimit in `TopCat` along injective transition maps has injective colimit maps
(`TauCeti.TopCat.injective_ι_of_isColimit`), since the forgetful functor to types preserves it.
In a colimit of `T1` spaces in `TopCat`, any set whose preimage in every stage is finite is closed
(`CategoryTheory.Limits.IsColimit.isClosed_of_forall_finite_preimage`); in particular, any colimit
of `T1` spaces with injective colimit maps is `T1` (`CategoryTheory.Limits.IsColimit.t1Space`), so
such a filtered colimit is.

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

Read through Mathlib's identification `TopCat.sigmaIsoSigma` of coproducts in `TopCat` with
disjoint unions, the map of coproducts `Limits.Sigma.map φ` of a family of maps is the map
`Sigma.map id φ` of disjoint unions (`TauCeti.TopCat.coe_sigmaMap`). Hence a coproduct of
embeddings is an embedding (`TauCeti.TopCat.isEmbedding_sigmaMap`). Likewise a map out of a
coproduct is the map `ContinuousMap.sigma` glued from its restrictions to the summands
(`TauCeti.TopCat.hom_eq_sigma_comp_sigmaIsoSigma_hom`).
-/

public section

open CategoryTheory Limits

universe w u

namespace TopCat

/-- The initial topological space is empty. -/
instance initial_isEmpty : IsEmpty (⊥_ TopCat.{u}) :=
  Function.isEmpty initialIsoPEmpty.hom

/-- The `j`-th coordinate of the image of a point `x` under the map `hd.map c η` between limit
cones in `TopCat` is the image under `η j` of the `j`-th coordinate of `x`. -/
@[simp]
theorem isLimitMap_π_apply {K : Type*} [Category K] {F G : K ⥤ TopCat} (c : Cone F) {d : Cone G}
    (hd : IsLimit d) (η : F ⟶ G) (j : K) (x : c.pt) :
    -- The source of `d.π.app j` is given as `d.pt`, as `elementwise` does, so that the left-hand
    -- side is in simp normal form; `simp` still rewrites the usual `d.π.app j (hd.map c η x)`.
    ConcreteCategory.hom (X := d.pt) (d.π.app j) (hd.map c η x) = η.app j (c.π.app j x) :=
  ConcreteCategory.congr_hom (IsLimit.map_π c hd η j) x

end TopCat

namespace CategoryTheory.Limits.IsColimit

/-- In the colimit of a diagram of `T1` spaces in `TopCat`, a set meeting every stage in
finitely many points is closed. -/
theorem isClosed_of_forall_finite_preimage {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    {c : Cocone F} (hc : IsColimit c) [∀ j, T1Space (F.obj j)] {S : Set c.pt}
    (hS : ∀ j, (c.ι.app j ⁻¹' S).Finite) : IsClosed S :=
  (TopCat.isClosed_iff_of_isColimit _ hc S).2 fun j ↦ (hS j).isClosed

/-- A colimit of `T1` spaces in `TopCat` whose colimit maps are injective is `T1`. -/
theorem t1Space {J : Type w} [Category J] {F : J ⥤ TopCat.{u}} {c : Cocone F}
    (hc : IsColimit c) (hι : ∀ j, Function.Injective (c.ι.app j)) [∀ j, T1Space (F.obj j)] :
    T1Space c.pt :=
  ⟨fun _ ↦ hc.isClosed_of_forall_finite_preimage fun j ↦
    (Set.subsingleton_singleton.preimage (hι j)).finite⟩

end CategoryTheory.Limits.IsColimit

namespace TauCeti.TopCat

/-- If all transition maps of a filtered diagram in `TopCat` are injective, then so are the maps
from the objects of the diagram to its colimit. -/
theorem injective_ι_of_isColimit {J : Type w} [Category J] [IsFilteredOrEmpty J]
    {F : J ⥤ TopCat.{u}} (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Injective (F.map f))
    {c : Cocone F} (hc : IsColimit c) (i : J) : Function.Injective (c.ι.app i) := fun x y h ↦ by
  obtain ⟨k, f, hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget TopCat) hc) x y).1 h
  exact hF f hk

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

/-- The range of a bonding map of the diagram of an increasing family of subsets is the smaller
subset, seen inside the larger one. -/
theorem range_subspaceDiagram_map {i j : J} (u : i ⟶ j) :
    Set.range ((subspaceDiagram hA).map u) = ((↑) ⁻¹' A i : Set (A j)) := by
  -- By definition, the bonding map is `Set.inclusion`.
  exact Set.range_inclusion (hA (leOfHom u))

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

section Sigma

variable {ι : Type u} {A X : ι → TopCat.{u}} (φ : ∀ i, A i ⟶ X i)

/-- Read through the homeomorphisms `TopCat.sigmaIsoSigma` with disjoint unions, the map of
coproducts `Limits.Sigma.map φ` is the map `Sigma.map id φ` of disjoint unions. -/
theorem coe_sigmaMap :
    ⇑(Limits.Sigma.map φ) = TopCat.homeoOfIso (TopCat.sigmaIsoSigma X).symm ∘
      Sigma.map id (fun i ↦ φ i) ∘ TopCat.homeoOfIso (TopCat.sigmaIsoSigma A) := by
  have : Limits.Sigma.map φ = (TopCat.sigmaIsoSigma A).hom ≫ TopCat.ofHom
      ⟨Sigma.map id fun i ↦ φ i, continuous_sigma_map.2 fun i ↦ (φ i).hom.continuous⟩ ≫
        (TopCat.sigmaIsoSigma X).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Limits.Sigma.ι_map_assoc, TopCat.sigmaIsoSigma_hom_ι, ← Category.assoc,
      TopCat.sigmaIsoSigma_hom_ι]
    -- Both sides send `x : A i` to `⟨i, φ i x⟩`.
    refine TopCat.ext fun x ↦ ?_
    simp [Sigma.map]
  ext x
  rw [this, Function.comp_apply, Function.comp_apply, TopCat.homeoOfIso_apply,
    TopCat.homeoOfIso_apply, Iso.symm_hom]
  simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, ContinuousMap.coe_mk]

/-- **A coproduct of embeddings in `TopCat` is an embedding.** -/
theorem isEmbedding_sigmaMap (hφ : ∀ i, Topology.IsEmbedding (φ i)) :
    Topology.IsEmbedding (Limits.Sigma.map φ) := by
  rw [coe_sigmaMap]
  exact (TopCat.homeoOfIso (TopCat.sigmaIsoSigma X).symm).isEmbedding.comp
    (((Topology.isEmbedding_sigmaMap Function.injective_id).2 hφ).comp
      (TopCat.homeoOfIso (TopCat.sigmaIsoSigma A)).isEmbedding)

/-- Read through the homeomorphism `TopCat.sigmaIsoSigma` with the disjoint union, a map `χ` out
of a coproduct in `TopCat` is the map `ContinuousMap.sigma` glued from its restrictions
`Limits.Sigma.ι X i ≫ χ` to the summands. -/
theorem hom_eq_sigma_comp_sigmaIsoSigma_hom {Y : TopCat.{u}} (χ : ∐ X ⟶ Y) :
    χ.hom = (ContinuousMap.sigma fun i ↦ (Limits.Sigma.ι X i ≫ χ).hom).comp
      (TopCat.sigmaIsoSigma X).hom.hom := by
  refine congrArg TopCat.Hom.hom (Limits.Sigma.hom_ext χ ((TopCat.sigmaIsoSigma X).hom ≫
    TopCat.ofHom (ContinuousMap.sigma fun i ↦ (Limits.Sigma.ι X i ≫ χ).hom)) fun i ↦ ?_)
  rw [TopCat.sigmaIsoSigma_hom_ι_assoc]
  exact TopCat.ext fun _ ↦ by simp

end Sigma

end TauCeti.TopCat
