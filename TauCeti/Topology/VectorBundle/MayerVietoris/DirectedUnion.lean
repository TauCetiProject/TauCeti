/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Thom-pair vanishing over arbitrary bases

For a finite-dimensional real vector bundle `E → B` of rank `r`, the relative singular
homology of its total space modulo the nonzero vectors vanishes in degrees below `r`,
with coefficients in an abelian category with exact filtered colimits.
No compactness, separation or paracompactness of the base and no orientation of the bundle
is needed.

Finite unions of trivializing open sets already have this vanishing by
`TauCeti.isZero_singularHomology_thomPairOver_biUnion`. Their Thom pairs form a filtered
diagram. Every compact subset of the total space, or of its nonzero subspace, projects
into finitely many trivializing sets. Thus `TopPair.isColimitMapCoconeSingularHomology`
identifies the homology of the whole Thom pair with a filtered colimit of zero objects.
The diagram, cocone and homology colimit presentation are available in every degree.
Universal coefficients then gives the same vanishing for relative cohomology with projective
chain coefficients.

This is the below-rank vanishing used in constructing Thom classes from local fibre
generators. It does not identify the degree-r group or construct a Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §10, Lemma 10.3 and
  the proof of Theorem 10.4 (finite trivializing unions and directed unions of chains).
* A. Hatcher, *Algebraic Topology*, §4.D, proof of Theorem 4D.10.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

section DirectedUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The filtered diagram of Thom pairs over finite unions of the chosen trivializing sets,
indexed by finite sets of base points. -/
def thomPairFiniteTrivializingUnionDiagram : Finset B ⥤ TopPair.{w} where
  obj s := thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := thomPairOverMap F E (biUnion_subset_biUnion_left f.le)
  map_id _ := thomPairOverMap_self F E
  map_comp _ _ := (thomPairOverMap_comp_thomPairOverMap F E _ _).symm

@[simp]
theorem thomPairFiniteTrivializingUnionDiagram_obj (s : Finset B) :
    (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s =
      thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet) := (rfl)

@[simp]
theorem thomPairFiniteTrivializingUnionDiagram_map {s t : Finset B} (f : s ⟶ t) :
    (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).map f =
      eqToHom (thomPairFiniteTrivializingUnionDiagram_obj s) ≫
        thomPairOverMap F E (biUnion_subset_biUnion_left f.le) ≫
        eqToHom (thomPairFiniteTrivializingUnionDiagram_obj t).symm :=
  (conj_eqToHom_iff_heq _ _ (thomPairFiniteTrivializingUnionDiagram_obj s)
    (thomPairFiniteTrivializingUnionDiagram_obj t)).2 HEq.rfl

/-- The inclusions from finite trivializing unions into the whole Thom pair. -/
def thomPairFiniteTrivializingUnionCocone :
    Cocone (thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)) where
  pt := thomPair F E
  ι :=
    { app _ := thomPairOverMap F E (subset_univ _) ≫ (thomPairOverUnivIso F E).hom
      naturality _ _ _ := thomPairOverMap_comp_thomPairOverMap_assoc F E _ _ _ }

@[simp]
theorem thomPairFiniteTrivializingUnionCocone_pt :
    (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt = thomPair F E := (rfl)

@[simp]
theorem thomPairFiniteTrivializingUnionCocone_ι_app (s : Finset B) :
    (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s =
      eqToHom (thomPairFiniteTrivializingUnionDiagram_obj s) ≫
        thomPairOverMap F E (subset_univ _) ≫ (thomPairOverUnivIso F E).hom ≫
        eqToHom thomPairFiniteTrivializingUnionCocone_pt.symm :=
  (conj_eqToHom_iff_heq _
    (thomPairOverMap F E (subset_univ _) ≫ (thomPairOverUnivIso F E).hom)
    (thomPairFiniteTrivializingUnionDiagram_obj s)
    (thomPairFiniteTrivializingUnionCocone_pt (F := F) (E := E))).2 HEq.rfl

/-- On ambient spaces, each finite-union cocone leg forgets the restriction to the union.
Heterogeneous equality keeps the diagram and cocone bodies unexposed. -/
theorem thomPairFiniteTrivializingUnionCocone_ι_app_fst (s : Finset B) :
    HEq (⇑(TopPair.Hom.fst
      ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s)))
      (Subtype.val : (π F E ⁻¹' ⋃ b ∈ s, (trivializationAt F E b).baseSet) →
        TotalSpace F E) := by
  unfold thomPairFiniteTrivializingUnionCocone thomPairFiniteTrivializingUnionDiagram
  apply heq_of_eq
  funext p
  -- Hom.fst preserves composition definitionally; erw also passes through the
  -- ConcreteCategory coercion from a TopCat morphism to its underlying function.
  erw [CategoryTheory.comp_apply, thomPairOverUnivIso_hom_fst_apply,
    thomPairOverMap_fst_apply]

/-- In every degree, the homology of the Thom pair is the filtered colimit of its homology
over finite trivializing unions, for coefficients with exact filtered colimits. -/
def isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] (R : C) (n : ℕ) :
    IsColimit ((TopPair.singularHomologyFunctor R n).mapCocone
      (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))) := by
  classical
  -- The characteristic HEq lemma identifies the abstract source and target of each leg
  -- with the restriction subtype and total space, without exposing the diagram's body.
  have hfst (s : Finset B) :
      (⇑(TopPair.Hom.fst
        ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s)) :
          (π F E ⁻¹' ⋃ b ∈ s, (trivializationAt F E b).baseSet) → TotalSpace F E) =
        Subtype.val := eq_of_heq (thomPairFiniteTrivializingUnionCocone_ι_app_fst s)
  -- Check compact absorption for both spaces of the pair, not just the total space.
  refine TopPair.isColimitMapCoconeSingularHomology R n
    (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))
    (fun s ↦ by
      rw [hfst s]
      exact Topology.IsEmbedding.subtypeVal)
    (fun (K : Set (TotalSpace F E)) hcomp ↦ by
      -- Identify the abstract apex's topology with the total-space topology.
      have hcomp : IsCompact K := hcomp
      obtain ⟨s, hs⟩ := IsCompact.exists_finset_subset_preimage_biUnion_baseSet
        (F := F) (E := E) (K := K) hcomp
      exact ⟨s, fun p hp ↦ ⟨⟨p, hs hp⟩,
        congrFun (hfst s) _⟩⟩)
    (fun K hcomp ↦ by
      obtain ⟨s, hs⟩ := IsCompact.exists_finset_subset_preimage_biUnion_baseSet
        (F := F) (E := E) (hcomp.image continuous_subtype_val)
      exact ⟨s, fun p hp ↦ ⟨⟨p.1, hs (mem_image_of_mem _ hp), p.2⟩, by
        apply Subtype.ext
        have h := TopPair.Hom.w_apply
          ((thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).ι.app s)
          ⟨p.1, hs (mem_image_of_mem _ hp), p.2⟩
        rw [hfst s] at h
        exact h⟩⟩)

end DirectedUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The homology of the Thom pair of a real vector bundle vanishes below the rank,
with coefficients in an abelian category with exact filtered colimits. The base is arbitrary. -/
theorem isZero_singularHomology_thomPair
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
    (R : C) {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPair F E).singularHomology R n) := by
  rw [← TopPair.singularHomologyFunctor_obj (thomPair F E) R n]
  exact (isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion
    (F := F) (E := E) R n).isZero_pt (Functor.isZero _ fun s ↦ by
      simpa only [Functor.comp_obj, thomPairFiniteTrivializingUnionDiagram_obj,
        TopPair.singularHomologyFunctor_obj] using
        isZero_singularHomology_thomPairOver_biUnion R s
          (fun b _ ↦ (trivializationAt F E b).open_baseSet)
          (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hn)

/-- The relative cohomology of a real vector bundle modulo its nonzero vectors vanishes
below the rank, over an arbitrary base and with projective chain coefficients. -/
theorem isZero_singularCohomology_thomPair
    {k : Type*} [CommRing k] (R M : ModuleCat.{w} k) [Module.Projective k R]
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPair F E).singularCohomology R k M n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M n fun _ hj ↦
    isZero_singularHomology_thomPair R (hj.trans_lt hn)

end TauCeti
