/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Chains
public import TauCeti.Topology.CWComplex.Classical.Map

/-!
# Cellular maps act on cellular chains

A continuous map between the carriers of relative CW complexes is cellular when it carries each
stage of the skeletal filtration into the stage of the same degree. It then induces maps of
consecutive skeletal pairs. Naturality of the connecting morphism of a pair shows that these maps
commute with the cellular differential, giving a chain map. Restrictions to skeleta relative
to the base and the map of the whole base pairs commute with the skeletal inclusions. These
are the maps used in the natural cellular–singular comparison. This construction keeps the
maps of pairs visible, so the resulting chain map is induced by the original continuous map.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- The restrictions to three consecutive skeleta form a map of skeletal triples. -/
private def skeletonTripleMap (n : ℕ) : skeletonTriple C n ⟶ skeletonTriple C' n :=
  ⟨ComposableArrows.homMk₂ (skeletonMap C C' hf n)
    (skeletonMap C C' hf (n + 1)) (skeletonMap C C' hf (n + 2))
    (skeletonMap_comp_inclusion C C' hf n.le_succ).symm
    (skeletonMap_comp_inclusion C C' hf (n + 1).le_succ).symm⟩

/-- The restrictions to two consecutive skeleta form a map of skeletal pairs. -/
def skeletonPairMap (n : ℕ) : skeletonPair C n ⟶ skeletonPair C' n :=
  TopTriple.innerPair.map (skeletonTripleMap C C' hf n)

@[simp]
lemma skeletonPairMap_fst (n : ℕ) :
    TopPair.Hom.fst (skeletonPairMap C C' hf n) = skeletonMap C C' hf (n + 1) := by
  exact TopTriple.innerPair_map_fst (skeletonTripleMap C C' hf n)

@[simp]
lemma skeletonPairMap_snd (n : ℕ) :
    TopPair.Hom.snd (skeletonPairMap C C' hf n) = skeletonMap C C' hf n := by
  exact TopTriple.innerPair_map_snd (skeletonTripleMap C C' hf n)

/-- A cellular map restricts to each skeleton relative to the base. -/
def skeletonBasePairMap (n : ℕ) : skeletonBasePair C n ⟶ skeletonBasePair C' n :=
  TopPair.ofHom (skeletonMap C C' hf (n + 1)) (skeletonMap C C' hf 0)
    (skeletonMap_comp_inclusion C C' hf (Nat.zero_le (n + 1)))

@[simp]
lemma skeletonBasePairMap_fst (n : ℕ) :
    TopPair.Hom.fst (skeletonBasePairMap C C' hf n) = skeletonMap C C' hf (n + 1) := (rfl)

@[simp]
lemma skeletonBasePairMap_snd (n : ℕ) :
    TopPair.Hom.snd (skeletonBasePairMap C C' hf n) = skeletonMap C C' hf 0 := (rfl)

/-- A cellular map induces a map of the whole complexes relative to their bases. -/
def complexBasePairMap : complexBasePair C ⟶ complexBasePair C' :=
  TopPair.ofHom f (skeletonMap C C' hf 0) (skeletonMap_comp_inclusion_complex C C' hf 0)

@[simp]
lemma complexBasePairMap_fst : TopPair.Hom.fst (complexBasePairMap C C' hf) = f := (rfl)

@[simp]
lemma complexBasePairMap_snd :
    TopPair.Hom.snd (complexBasePairMap C C' hf) = skeletonMap C C' hf 0 := (rfl)

/-- Restriction relative to the base commutes with inclusions between skeleta. -/
@[reassoc]
lemma skeletonBasePairMap_comp_inclusion {n m : ℕ} (h : n ≤ m) :
    skeletonBasePairMap C C' hf n ≫ skeletonBasePairInclusion C' h =
      skeletonBasePairInclusion C h ≫ skeletonBasePairMap C C' hf m := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, skeletonBasePairMap_snd]
    ext x
    -- The pair subspace objects and their skeletal presentations agree at default transparency.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      skeletonBasePairInclusion_snd_apply, skeletonBasePairInclusion_snd_apply]
    rfl
  · simp only [MorphismProperty.Comma.comp_right, skeletonBasePairMap_fst]
    have hC : (skeletonBasePairInclusion C h).right =
        TopCat.ofHom (ContinuousMap.inclusion
          (skeletonLT_mono (C := C) (mod_cast Nat.add_le_add_right h 1))) := by
      ext x
      exact Subtype.ext (coe_skeletonBasePairInclusion_fst_apply C h x)
    have hC' : (skeletonBasePairInclusion C' h).right =
        TopCat.ofHom (ContinuousMap.inclusion
          (skeletonLT_mono (C := C') (mod_cast Nat.add_le_add_right h 1))) := by
      ext x
      exact Subtype.ext (coe_skeletonBasePairInclusion_fst_apply C' h x)
    -- Use the ambient skeletal presentations when rewriting the pair components.
    erw [hC, hC']
    exact skeletonMap_comp_inclusion C C' hf (Nat.add_le_add_right h 1)

/-- Restriction relative to the base commutes with the map to a consecutive skeletal pair. -/
@[reassoc]
lemma skeletonBasePairMap_comp_toSkeletonPair (n : ℕ) :
    skeletonBasePairMap C C' hf n ≫ skeletonBasePairToSkeletonPair C' n =
      skeletonBasePairToSkeletonPair C n ≫ skeletonPairMap C C' hf n := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, skeletonBasePairMap_snd, skeletonPairMap_snd,
      skeletonBasePairToSkeletonPair_snd]
    exact skeletonMap_comp_inclusion C C' hf (Nat.zero_le n)
  · simp only [MorphismProperty.Comma.comp_right, skeletonBasePairMap_fst, skeletonPairMap_fst,
      skeletonBasePairToSkeletonPair_fst]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Restriction relative to the base commutes with inclusion into the whole complex. -/
@[reassoc]
lemma skeletonBasePairMap_comp_toComplex (n : ℕ) :
    skeletonBasePairMap C C' hf n ≫ skeletonBasePairToComplex C' n =
      skeletonBasePairToComplex C n ≫ complexBasePairMap C C' hf := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, skeletonBasePairMap_snd, complexBasePairMap_snd,
      skeletonBasePairToComplex_snd]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp only [MorphismProperty.Comma.comp_right, skeletonBasePairMap_fst, complexBasePairMap_fst,
      skeletonBasePairToComplex_fst]
    exact skeletonMap_comp_inclusion_complex C C' hf (n + 1)

/-- Restriction of the identity map to a skeletal pair is the identity pair map. -/
@[simp]
lemma skeletonPairMap_id (n : ℕ) :
    skeletonPairMap C C (isCellular_id C) n = 𝟙 (skeletonPair C n) := by
  ext : 1 <;> simp [skeletonPairMap_fst, skeletonPairMap_snd]

/-- The identity cellular map restricts to the identity on each base pair. -/
@[simp]
lemma skeletonBasePairMap_id (n : ℕ) :
    skeletonBasePairMap C C (isCellular_id C) n = 𝟙 (skeletonBasePair C n) := by
  ext : 1 <;> simp <;> rfl

/-- The identity cellular map induces the identity on the whole base pair. -/
@[simp]
lemma complexBasePairMap_id :
    complexBasePairMap C C (isCellular_id C) = 𝟙 (complexBasePair C) := by
  ext : 1 <;> simp <;> rfl

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] {F : Set Z}
  (C'' : Set Z) [RelCWComplex C'' F]
  {g : TopCat.of C' ⟶ TopCat.of C''} (hg : IsCellular C' C'' g)

/-- Maps of skeletal pairs respect composition of cellular maps. -/
@[reassoc]
lemma skeletonPairMap_comp (n : ℕ) :
    skeletonPairMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonPairMap C C' hf n ≫ skeletonPairMap C' C'' hg n := by
  ext : 1
  · exact skeletonMap_comp C C' hf C'' hg n
  · exact skeletonMap_comp C C' hf C'' hg (n + 1)

/-- Restrictions to base pairs respect composition of cellular maps. -/
@[reassoc]
lemma skeletonBasePairMap_comp (n : ℕ) :
    skeletonBasePairMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonBasePairMap C C' hf n ≫ skeletonBasePairMap C' C'' hg n := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · exact skeletonMap_comp C C' hf C'' hg 0
  · exact skeletonMap_comp C C' hf C'' hg (n + 1)

/-- Maps of whole base pairs respect composition of cellular maps. -/
@[reassoc]
lemma complexBasePairMap_comp :
    complexBasePairMap C C'' (IsCellular.comp C C' hf hg) =
      complexBasePairMap C C' hf ≫ complexBasePairMap C' C'' hg := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · exact skeletonMap_comp C C' hf C'' hg 0
  · rfl

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- A cellular map induces a morphism on each cellular chain group. -/
def cellularChainGroupMap (n : ℕ) :
    cellularChainGroup C R n ⟶ cellularChainGroup C' R n :=
  TopPair.singularHomologyMap (skeletonPairMap C C' hf n) R n

/-- The map on a cellular chain group is relative singular homology of the skeletal pair map.
This formula allows importing modules to rewrite without exposing the definition's body. -/
lemma cellularChainGroupMap_def (n : ℕ) :
    cellularChainGroupMap C C' hf R n =
      TopPair.singularHomologyMap (skeletonPairMap C C' hf n) R n := (rfl)

/-- The identity cellular map acts as the identity on each cellular chain group. -/
@[simp]
lemma cellularChainGroupMap_id (n : ℕ) :
    cellularChainGroupMap C C (isCellular_id C) R n = 𝟙 (cellularChainGroup C R n) := by
  simp [cellularChainGroupMap, skeletonPairMap_id,
    TopPair.singularHomologyMap]

/-- The maps on cellular chain groups respect composition of cellular maps. -/
@[reassoc]
lemma cellularChainGroupMap_comp (n : ℕ) :
    cellularChainGroupMap C C'' (IsCellular.comp C C' hf hg) R n =
      cellularChainGroupMap C C' hf R n ≫ cellularChainGroupMap C' C'' hg R n := by
  rw [cellularChainGroupMap,
    skeletonPairMap_comp C C' hf C'' hg n]
  rw [TopPair.singularHomologyMap, Functor.map_comp, SSetPair.homologyMap_comp]
  rfl

/-- The cellular chain-group maps commute with the cellular differential. -/
@[reassoc]
lemma cellularChainGroupMap_comp_cellularDifferential (n : ℕ) :
    cellularChainGroupMap C C' hf R (n + 1) ≫ cellularDifferential C' R n =
      cellularDifferential C R n ≫ cellularChainGroupMap C C' hf R n := by
  rw [cellularDifferential_eq_singularHomologyδ,
    cellularDifferential_eq_singularHomologyδ]
  exact (TopTriple.singularHomologyδ_naturality
    (skeletonTripleMap C C' hf n) R (n + 1) n).symm

/-- A cellular map induces a chain map between the cellular chain complexes. -/
def cellularChainComplexMap : cellularChainComplex C R ⟶ cellularChainComplex C' R :=
  ChainComplex.ofHom (fun n ↦
    eqToHom (cellularChainComplex_X C R n) ≫ cellularChainGroupMap C C' hf R n ≫
      eqToHom (cellularChainComplex_X C' R n).symm)
    (by
      intro n
      simp only [cellularChainComplex_d, Category.assoc]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      simpa only [Category.assoc] using congrArg
        (fun a ↦ eqToHom (cellularChainComplex_X C R (n + 1)) ≫ a ≫
          eqToHom (cellularChainComplex_X C' R n).symm)
        (cellularChainGroupMap_comp_cellularDifferential C C' hf R n))

@[simp]
lemma cellularChainComplexMap_f (n : ℕ) :
    (cellularChainComplexMap C C' hf R).f n =
      eqToHom (cellularChainComplex_X C R n) ≫ cellularChainGroupMap C C' hf R n ≫
        eqToHom (cellularChainComplex_X C' R n).symm := (rfl)

/-- The identity cellular map induces the identity chain map. -/
@[simp]
lemma cellularChainComplexMap_id :
    cellularChainComplexMap C C (isCellular_id C) R = 𝟙 (cellularChainComplex C R) := by
  ext n
  simp only [cellularChainComplexMap_f, cellularChainGroupMap_id]
  simp

/-- Composition of cellular maps induces composition of cellular chain maps. -/
@[reassoc]
lemma cellularChainComplexMap_comp :
    cellularChainComplexMap C C'' (IsCellular.comp C C' hf hg) R =
      cellularChainComplexMap C C' hf R ≫ cellularChainComplexMap C' C'' hg R := by
  ext n
  simp only [cellularChainComplexMap_f, HomologicalComplex.comp_f]
  rw [cellularChainGroupMap_comp C C' hf C'' hg R n]
  simp [Category.assoc]

end TauCeti
