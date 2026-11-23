/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import TauCeti.AlgebraicTopology.EilenbergSteenrod
public import TauCeti.Topology.Category.BasedTopologicalSpace

/-!
# Split pair sequences and reduced homology for homology pretheories

Let `HP` be a homology pretheory with the long exact sequence of pairs. For a pair `(X, A)` the
sequence `Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A)` (`TopPair.HomologyPretheory.pairShortComplex`) is exact. When
every `Hⱼ(A) ⟶ Hⱼ(X)` is a monomorphism the boundary maps of the pair vanish, and the sequence is
short exact. A retraction `r : X ⟶ A` of the inclusion splits it, so that
`Hᵢ(X) ≅ Hᵢ(A) ⊞ Hᵢ(X, A)`, with first component induced by `r`.

The two main instances are the following.

* For a based space `X`, the reduced groups are the relative groups `H~ᵢ(X) = Hᵢ(X, *)` of the pair
  `(X, *)` (`TopPair.HomologyPretheory.reducedH`). The map `X ⟶ *` retracts the basepoint, which
  gives the split augmentation `Hᵢ(X) ≅ Hᵢ(*) ⊞ H~ᵢ(X)`
  (`TopPair.HomologyPretheory.augmentationIso`), natural in based maps.
* If the ambient space of a pair is the coproduct `A ⊔ B` of the subspace with a space `B`, and the
  pretheory takes this coproduct to a coproduct, then the composite `Hᵢ(B) ⟶ Hᵢ(A ⊔ B) ⟶
  Hᵢ(A ⊔ B, A)` is an isomorphism (`TopPair.HomologyPretheory.isIso_map_inr_comp_hFstToHₚ`). For
  the point `A = *` this is the identification `Hᵢ(B) ≅ H~ᵢ(B₊)` of unreduced homology with the
  reduced homology of `B` with a disjoint basepoint (`TopPair.HomologyPretheory.addBasepointIso`).

The coefficient category is only assumed preadditive and balanced. Every abelian category, and the
opposite of every abelian category, is such a category. A pretheory valued in `Dᵒᵖ` has groups
`Eⁿ(X)` contravariant in `X`, and read in `D` these results are the corresponding statements in
cohomology; for instance `Eⁿ(X) ≅ Eⁿ(*) ⊞ E~ⁿ(X)`
(`TopPair.HomologyPretheory.cohomologyAugmentationIso`).

## Main declarations

* `TopPair.HomologyPretheory.pairShortComplex`: the sequence `Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A)`.
* `TopPair.HomologyPretheory.δ_app_eq_zero_of_mono`, `epi_hFstToHₚ_of_mono` and
  `pairShortComplex_shortExact`: monomorphic maps `Hⱼ(A) ⟶ Hⱼ(X)` give short exact sequences.
* `TopPair.HomologyPretheory.pairSplittingOfRetraction` and `isoBiprodOfRetraction`: the splitting
  `Hᵢ(X) ≅ Hᵢ(A) ⊞ Hᵢ(X, A)` given by a retraction of the pair.
* `TopPair.HomologyPretheory.reducedH` and `augmentationIso`: reduced homology of based spaces and
  the split augmentation `Hᵢ(X) ≅ Hᵢ(*) ⊞ H~ᵢ(X)`.
* `TopPair.HomologyPretheory.isIso_map_inr_comp_hFstToHₚ` and `addBasepointIso`: the relative
  homology of a coproduct relative to a summand, and `Hᵢ(B) ≅ H~ᵢ(B₊)`.
* `TopPair.HomologyPretheory.cohomologyAugmentationIso`: the split augmentation in cohomology.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, Section 8.
* A. Hatcher, *Algebraic Topology*, Section 2.3, the reduced groups of a homology theory.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TopPair.HomologyPretheory

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  (HP : HomologyPretheory.{u} C c)

/-! ### The short exact sequence of a pair -/

section PairSequence

variable [HP.HasPairSequence]

/-- The sequence `Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A)` of a pair `(X, A)`, induced by the inclusion
`A ⟶ X` and the map to relative homology. It is exact (`pairShortComplex_exact`). -/
abbrev pairShortComplex (i : ι) (X : TopPair.{u}) : ShortComplex C :=
  ShortComplex.mk ((HP.H i).map X.map) (HP.hFstToHₚ i X) ((HP.exact_fst X i).toIsComplex.zero 0)

/-- The sequence `Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A)` of a pair is exact. -/
lemma pairShortComplex_exact (i : ι) (X : TopPair.{u}) : (HP.pairShortComplex i X).Exact :=
  (HP.exact_fst X i).exact 0

/-- If `Hⱼ(A) ⟶ Hⱼ(X)` is a monomorphism, the boundary `Hᵢ(X, A) ⟶ Hⱼ(A)` of the pair vanishes. -/
lemma δ_app_eq_zero_of_mono (i j : ι) (X : TopPair.{u}) [Mono ((HP.H j).map X.map)] :
    (HP.δ i j).app X = 0 := by
  by_cases hij : c.Rel i j
  · exact (cancel_mono ((HP.H j).map X.map)).mp
      (((HP.exact_snd X i j hij).toIsComplex.zero 0).trans zero_comp.symm)
  · rw [HP.shape_δ i j hij, NatTrans.app_zero]

/-- If the maps `Hⱼ(A) ⟶ Hⱼ(X)` into the degrees `j` following `i` are monomorphisms, then
`Hᵢ(X) ⟶ Hᵢ(X, A)` is an epimorphism. -/
lemma epi_hFstToHₚ_of_mono (i : ι) (X : TopPair.{u})
    (hX : ∀ j, c.Rel i j → Mono ((HP.H j).map X.map)) : Epi (HP.hFstToHₚ i X) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    have := hX j hij
    exact ((HP.exact_pair X i j hij).exact 0).epi_f (HP.δ_app_eq_zero_of_mono i j X)
  · push Not at hi
    exact HP.epi_hFstToHₚ_of_not_rel i hi X

/-- If `Hᵢ(A) ⟶ Hᵢ(X)` and the maps `Hⱼ(A) ⟶ Hⱼ(X)` into the following degrees are
monomorphisms, then `0 ⟶ Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A) ⟶ 0` is short exact. -/
lemma pairShortComplex_shortExact (i : ι) (X : TopPair.{u}) [Mono ((HP.H i).map X.map)]
    (hX : ∀ j, c.Rel i j → Mono ((HP.H j).map X.map)) : (HP.pairShortComplex i X).ShortExact :=
  have := HP.epi_hFstToHₚ_of_mono i X hX
  { exact := HP.pairShortComplex_exact i X
    mono_f := inferInstanceAs (Mono ((HP.H i).map X.map))
    epi_g := inferInstanceAs (Epi (HP.hFstToHₚ i X)) }

/-! ### Pairs with a retraction -/

section Retraction

variable {X : TopPair.{u}} (r : X.fst ⟶ X.snd) (hr : X.map ≫ r = 𝟙 X.snd)
include hr

/-- For a pair `(X, A)` with a retraction `r : X ⟶ A` of the inclusion, the boundary maps
`Hᵢ(X, A) ⟶ Hⱼ(A)` vanish. -/
lemma δ_app_eq_zero_of_retraction (i j : ι) : (HP.δ i j).app X = 0 :=
  have : IsSplitMono X.map := .mk' ⟨r, hr⟩
  HP.δ_app_eq_zero_of_mono i j X

/-- For a pair `(X, A)` with a retraction `r : X ⟶ A` of the inclusion, the map
`Hᵢ(X) ⟶ Hᵢ(X, A)` is an epimorphism. -/
lemma epi_hFstToHₚ_of_retraction (i : ι) : Epi (HP.hFstToHₚ i X) :=
  have : IsSplitMono X.map := .mk' ⟨r, hr⟩
  HP.epi_hFstToHₚ_of_mono i X fun _ _ ↦ inferInstance

variable [Balanced C]

/-- The splitting of the short exact sequence `Hᵢ(A) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A)` of a pair given by a
retraction `r : X ⟶ A` of the inclusion. Its retraction `Hᵢ(X) ⟶ Hᵢ(A)` is induced by `r`. -/
def pairSplittingOfRetraction (i : ι) : (HP.pairShortComplex i X).Splitting :=
  .ofExactOfRetraction _ (HP.pairShortComplex_exact i X) ((HP.H i).map r)
    (by rw [← (HP.H i).map_comp, hr, (HP.H i).map_id]) (HP.epi_hFstToHₚ_of_retraction r hr i)

/-- The retraction `Hᵢ(X) ⟶ Hᵢ(A)` of the splitting given by `r` is induced by `r`. -/
@[simp]
lemma pairSplittingOfRetraction_r (i : ι) :
    (HP.pairSplittingOfRetraction r hr i).r = (HP.H i).map r :=
  (rfl)

/-- The decomposition `Hᵢ(X) ≅ Hᵢ(A) ⊞ Hᵢ(X, A)` of the homology of a pair `(X, A)` with a
retraction `r : X ⟶ A` of the inclusion. The first component is induced by `r` and the second is
the map to relative homology. -/
def isoBiprodOfRetraction (i : ι) [HasBinaryBiproduct ((HP.H i).obj X.snd) ((HP.Hₚ i).obj X)] :
    (HP.H i).obj X.fst ≅ (HP.H i).obj X.snd ⊞ (HP.Hₚ i).obj X :=
  (HP.pairSplittingOfRetraction r hr i).isoBinaryBiproduct

@[reassoc (attr := simp)]
lemma isoBiprodOfRetraction_hom_fst (i : ι)
    [HasBinaryBiproduct ((HP.H i).obj X.snd) ((HP.Hₚ i).obj X)] :
    (HP.isoBiprodOfRetraction r hr i).hom ≫ biprod.fst = (HP.H i).map r :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma isoBiprodOfRetraction_hom_snd (i : ι)
    [HasBinaryBiproduct ((HP.H i).obj X.snd) ((HP.Hₚ i).obj X)] :
    (HP.isoBiprodOfRetraction r hr i).hom ≫ biprod.snd = HP.hFstToHₚ i X :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
lemma inl_isoBiprodOfRetraction_inv (i : ι)
    [HasBinaryBiproduct ((HP.H i).obj X.snd) ((HP.Hₚ i).obj X)] :
    biprod.inl ≫ (HP.isoBiprodOfRetraction r hr i).inv = (HP.H i).map X.map :=
  biprod.inl_desc _ _

end Retraction

/-! ### The relative homology of a coproduct relative to a summand -/

/-- Let `(X, A)` be a pair whose ambient space is the coproduct of `A` and a space `B`, with
inclusions `A ⟶ X` and `inr : B ⟶ X`. If the pretheory takes this coproduct to a coproduct, then
`Hᵢ(B) ⟶ Hᵢ(X) ⟶ Hᵢ(X, A)` is an isomorphism. -/
theorem isIso_map_inr_comp_hFstToHₚ [Balanced C] (i : ι) {X : TopPair.{u}} {B : TopCat.{u}}
    (inr : B ⟶ X.fst) (hc : IsColimit (BinaryCofan.mk X.map inr))
    [∀ j, PreservesColimit (pair X.snd B) (HP.H j)] :
    IsIso ((HP.H i).map inr ≫ HP.hFstToHₚ i X) := by
  -- In every degree the images of the two inclusions form a coproduct in `C`, hence a bilimit
  -- bicone `b j`: the image of `A ⟶ X` has the retraction `(b j).fst`, and `Hⱼ(X)` is the
  -- biproduct of `Hⱼ(A)` and `Hⱼ(B)`.
  let hcj (j : ι) := mapIsColimitOfPreservesOfIsColimit (HP.H j) _ _ hc
  let b (j : ι) := BinaryBicone.ofColimitCocone (hcj j)
  have hmono (j : ι) : Mono ((HP.H j).map X.map) :=
    have : IsSplitMono ((HP.H j).map X.map) := .mk' ⟨(b j).fst, (b j).inl_fst⟩
    inferInstance
  -- The cone point of `b i` is `Hᵢ(X)` only up to unfolding `BinaryCofan.mk`, so the projections
  -- and the identities they satisfy are restated with `Hᵢ(X)` as their source.
  let fst : (HP.H i).obj X.fst ⟶ (HP.H i).obj X.snd := (b i).fst
  let snd : (HP.H i).obj X.fst ⟶ (HP.H i).obj B := (b i).snd
  have hinl : (HP.H i).map X.map ≫ snd = 0 := (b i).inl_snd
  have hinr : (HP.H i).map inr ≫ snd = 𝟙 _ := (b i).inr_snd
  have htotal : fst ≫ (HP.H i).map X.map + snd ≫ (HP.H i).map inr = 𝟙 _ :=
    IsBilimit.binary_total (binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (hcj i))
  -- The short exact sequence of the pair identifies `Hᵢ(X, A)` with the cokernel of
  -- `Hᵢ(A) ⟶ Hᵢ(X)`, through which the projection `snd` to `Hᵢ(B)` factors.
  have hS := HP.pairShortComplex_exact i X
  have := HP.epi_hFstToHₚ_of_mono i X fun j _ ↦ hmono j
  refine ⟨hS.desc snd hinl, ?_, ?_⟩
  · rw [Category.assoc, hS.g_desc, hinr]
  · rw [← cancel_epi (HP.hFstToHₚ i X), hS.g_desc_assoc, ← Category.assoc,
      eq_sub_of_add_eq' htotal]
    simp [(HP.pairShortComplex i X).zero]

end PairSequence

/-! ### Reduced homology of based spaces -/

open TauCeti

/-- The reduced homology `H~ᵢ(X) = Hᵢ(X, *)` of a based space `X`: the relative homology of the
pair `(X, *)`, as a functor of based maps. Its value `(HP.reducedH i).obj X` simplifies to
`(HP.Hₚ i).obj (BasedTopologicalSpace.toTopPair.obj X)`, the form used in the statements below. -/
abbrev reducedH (i : ι) : BasedTopologicalSpace.{u} ⥤ C :=
  BasedTopologicalSpace.toTopPair ⋙ HP.Hₚ i

section Augmentation

variable [HP.HasPairSequence] [Balanced C] [HasBinaryBiproducts C]

/-- The map from a based space `X` to the point, which retracts the inclusion of the basepoint. -/
private abbrev toPoint (X : BasedTopologicalSpace.{u}) :
    TopCat.of X.carrier ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

/-- The split augmentation `Hᵢ(X) ≅ Hᵢ(*) ⊞ H~ᵢ(X)` of a based space `X`. Its first component is
induced by the map `X ⟶ *`, and its second is the map to the relative homology of `(X, *)`. -/
def augmentationIso (i : ι) (X : BasedTopologicalSpace.{u}) :
    (HP.H i).obj (TopCat.of X.carrier) ≅
      (HP.H i).obj (TopCat.of PUnit.{u + 1}) ⊞
        (HP.Hₚ i).obj (BasedTopologicalSpace.toTopPair.obj X) :=
  HP.isoBiprodOfRetraction (X := BasedTopologicalSpace.toTopPair.obj X) (toPoint X)
    (TopCat.isTerminalPUnit.hom_ext _ _) i

@[reassoc (attr := simp)]
lemma augmentationIso_hom_fst (i : ι) (X : BasedTopologicalSpace.{u}) :
    (HP.augmentationIso i X).hom ≫ biprod.fst =
      (HP.H i).map (TopCat.ofHom (ContinuousMap.const _ PUnit.unit)) :=
  HP.isoBiprodOfRetraction_hom_fst _ _ i

@[reassoc (attr := simp)]
lemma augmentationIso_hom_snd (i : ι) (X : BasedTopologicalSpace.{u}) :
    (HP.augmentationIso i X).hom ≫ biprod.snd =
      HP.hFstToHₚ i (BasedTopologicalSpace.toTopPair.obj X) :=
  HP.isoBiprodOfRetraction_hom_snd _ _ i

@[reassoc (attr := simp)]
lemma inl_augmentationIso_inv (i : ι) (X : BasedTopologicalSpace.{u}) :
    biprod.inl ≫ (HP.augmentationIso i X).inv =
      (HP.H i).map (TopCat.ofHom (ContinuousMap.const _ X.basepoint)) :=
  HP.inl_isoBiprodOfRetraction_inv (X := BasedTopologicalSpace.toTopPair.obj X) (toPoint X)
    (TopCat.isTerminalPUnit.hom_ext _ _) i

/-- The split augmentation is natural in based maps. -/
@[reassoc]
lemma augmentationIso_hom_naturality (i : ι) {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    (HP.H i).map (TopCat.ofHom f.toContinuousMap) ≫ (HP.augmentationIso i Y).hom =
      (HP.augmentationIso i X).hom ≫
        biprod.map (𝟙 _) ((HP.Hₚ i).map (BasedTopologicalSpace.toTopPair.map f)) := by
  ext
  · simp [← Functor.map_comp, ← TopCat.ofHom_comp]
  · simpa using (HP.hFstToHₚ_naturality (BasedTopologicalSpace.toTopPair.map f) i).symm

end Augmentation

/-! ### Adding a disjoint basepoint -/

section AddBasepoint

variable [HP.HasPairSequence] [Balanced C]
  [∀ j, PreservesColimitsOfShape (Discrete WalkingPair) (HP.H j)]

/-- The isomorphism `Hᵢ(X) ≅ H~ᵢ(X₊)` between the homology of a space and the reduced homology of
the space with a disjoint basepoint added. It is induced by the inclusion `X ⟶ X₊` followed by the
map to the relative homology of `(X₊, *)`. -/
def addBasepointIso (i : ι) (X : TopCat.{u}) :
    (HP.H i).obj X ≅ (HP.Hₚ i).obj
      (BasedTopologicalSpace.toTopPair.obj (BasedTopologicalSpace.addBasepoint.obj X)) :=
  haveI := HP.isIso_map_inr_comp_hFstToHₚ i _
    (BasedTopologicalSpace.addBasepointIsColimit X)
  asIso ((HP.H i).map (BasedTopologicalSpace.addBasepointInr X) ≫ HP.hFstToHₚ i
    (BasedTopologicalSpace.toTopPair.obj (BasedTopologicalSpace.addBasepoint.obj X)))

@[simp]
lemma addBasepointIso_hom (i : ι) (X : TopCat.{u}) :
    (HP.addBasepointIso i X).hom = (HP.H i).map (BasedTopologicalSpace.addBasepointInr X) ≫
      HP.hFstToHₚ i
        (BasedTopologicalSpace.toTopPair.obj (BasedTopologicalSpace.addBasepoint.obj X)) :=
  (rfl)

/-- The isomorphism `Hᵢ(X) ≅ H~ᵢ(X₊)` is natural in `X`. -/
@[reassoc]
lemma addBasepointIso_hom_naturality (i : ι) {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (HP.H i).map f ≫ (HP.addBasepointIso i Y).hom =
      (HP.addBasepointIso i X).hom ≫
        (HP.Hₚ i).map
          (BasedTopologicalSpace.toTopPair.map (BasedTopologicalSpace.addBasepoint.map f)) := by
  rw [addBasepointIso_hom, addBasepointIso_hom, Category.assoc, hFstToHₚ_naturality]
  simp only [← Functor.map_comp_assoc, BasedTopologicalSpace.toTopPair_map_right]
  rw [BasedTopologicalSpace.addBasepointInr_comp_addBasepoint_map]

end AddBasepoint

/-! ### Cohomology -/

section Cohomology

variable {D : Type*} [Category* D] [Preadditive D] [Balanced D] [HasBinaryBiproducts D]
  (E : HomologyPretheory.{u} Dᵒᵖ c) [E.HasPairSequence]

/-- For a pretheory `E` valued in `Dᵒᵖ`, whose groups `Eⁱ(X)` are contravariant in `X`, the split
augmentation `Eⁱ(X) ≅ Eⁱ(*) ⊞ E~ⁱ(X)` of a based space, read in `D`. The summand `Eⁱ(*)` is
included by the map `X ⟶ *` and `E~ⁱ(X) = Eⁱ(X, *)` by the map from relative to absolute
groups. -/
def cohomologyAugmentationIso (i : ι) (X : BasedTopologicalSpace.{u}) :
    Opposite.unop ((E.H i).obj (TopCat.of X.carrier)) ≅
      Opposite.unop ((E.H i).obj (TopCat.of PUnit.{u + 1})) ⊞
        Opposite.unop ((E.Hₚ i).obj (BasedTopologicalSpace.toTopPair.obj X)) :=
  (E.augmentationIso i X).unop.symm ≪≫ (biprod.opIso _ _).unop

/-- The inverse of the split augmentation in cohomology, read off from the homological one. -/
lemma cohomologyAugmentationIso_inv (i : ι) (X : BasedTopologicalSpace.{u}) :
    (E.cohomologyAugmentationIso i X).inv =
      (biprod.opIso _ _).inv.unop ≫ (E.augmentationIso i X).hom.unop :=
  (rfl)

@[reassoc (attr := simp)]
lemma inl_cohomologyAugmentationIso_inv (i : ι) (X : BasedTopologicalSpace.{u}) :
    biprod.inl ≫ (E.cohomologyAugmentationIso i X).inv =
      ((E.H i).map (TopCat.ofHom (ContinuousMap.const X.carrier PUnit.unit))).unop := by
  apply Quiver.Hom.op_inj
  simp only [cohomologyAugmentationIso_inv, op_comp, Quiver.Hom.op_unop, Category.assoc,
    biprod.opIso_inv_inl_op]
  exact E.augmentationIso_hom_fst i X

@[reassoc (attr := simp)]
lemma inr_cohomologyAugmentationIso_inv (i : ι) (X : BasedTopologicalSpace.{u}) :
    biprod.inr ≫ (E.cohomologyAugmentationIso i X).inv =
      (E.hFstToHₚ i (BasedTopologicalSpace.toTopPair.obj X)).unop := by
  apply Quiver.Hom.op_inj
  simp only [cohomologyAugmentationIso_inv, op_comp, Quiver.Hom.op_unop, Category.assoc,
    biprod.opIso_inv_inr_op]
  exact E.augmentationIso_hom_snd i X

/-- The split augmentation in cohomology, read off from the homological one. -/
lemma cohomologyAugmentationIso_hom (i : ι) (X : BasedTopologicalSpace.{u}) :
    (E.cohomologyAugmentationIso i X).hom =
      (E.augmentationIso i X).inv.unop ≫ (biprod.opIso _ _).hom.unop :=
  (rfl)

@[reassoc (attr := simp)]
lemma cohomologyAugmentationIso_hom_fst (i : ι) (X : BasedTopologicalSpace.{u}) :
    (E.cohomologyAugmentationIso i X).hom ≫ biprod.fst =
      ((E.H i).map (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} X.basepoint))).unop := by
  apply Quiver.Hom.op_inj
  simp only [cohomologyAugmentationIso_hom, op_comp, Quiver.Hom.op_unop,
    biprod.fst_op_opIso_hom_assoc]
  exact E.inl_augmentationIso_inv i X

/-- The split augmentation in cohomology is natural in based maps: a based map `f : X ⟶ Y`
acts on `Eⁱ(*) ⊞ E~ⁱ(Y)` by the identity on `Eⁱ(*)` and by `f` on the reduced groups. -/
@[reassoc]
lemma cohomologyAugmentationIso_inv_naturality (i : ι) {X Y : BasedTopologicalSpace.{u}}
    (f : X ⟶ Y) :
    biprod.map (𝟙 _) ((E.Hₚ i).map (BasedTopologicalSpace.toTopPair.map f)).unop ≫
        (E.cohomologyAugmentationIso i X).inv =
      (E.cohomologyAugmentationIso i Y).inv ≫
        ((E.H i).map (TopCat.ofHom f.toContinuousMap)).unop := by
  apply biprod.hom_ext'
  · simp [← unop_comp, ← Functor.map_comp, ← TopCat.ofHom_comp]
  · simpa [← unop_comp] using
      congrArg Quiver.Hom.unop (E.hFstToHₚ_naturality (BasedTopologicalSpace.toTopPair.map f) i)

end Cohomology

end TopPair.HomologyPretheory
