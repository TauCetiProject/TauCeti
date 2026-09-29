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
commute with the cellular differential, giving a chain map. This construction keeps the maps of
pairs visible, so the resulting chain map is induced by the original continuous map.

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
    (skeletonMap_comp_inclusion C C' hf n).symm
    (skeletonMap_comp_inclusion C C' hf (n + 1)).symm⟩

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

/-- Restriction of the identity map to a skeletal pair is the identity pair map. -/
@[simp]
lemma skeletonPairMap_id (n : ℕ) :
    skeletonPairMap C C (isCellular_id C) n = 𝟙 (skeletonPair C n) := by
  ext : 1 <;> simp [skeletonPairMap_fst, skeletonPairMap_snd]

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

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- A cellular map induces a morphism on each cellular chain group. -/
def cellularChainGroupMap (n : ℕ) :
    cellularChainGroup C R n ⟶ cellularChainGroup C' R n :=
  TopPair.singularHomologyMap (skeletonPairMap C C' hf n) R n

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
