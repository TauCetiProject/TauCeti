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

A continuous map between relative CW complexes is cellular when it carries each stage of the
skeletal filtration into the stage of the same degree. It then induces maps of consecutive
skeletal pairs. Naturality of the connecting morphism of a pair shows that these maps commute
with the cellular differential, giving a chain map. This construction keeps the maps of pairs
visible, so the resulting chain map is induced by the original continuous map.

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

variable {f : TopCat.of X ⟶ TopCat.of Y} (hf : IsCellular C C' f)

/-- The restriction of a cellular map to the `n`-th stage of the skeletal filtration. -/
def skeletonMap (n : ℕ) : skeletonObj C n ⟶ skeletonObj C' n :=
  TopCat.ofHom ⟨(hf n).restrict, f.hom.continuous.restrict (hf n)⟩

@[simp]
lemma skeletonMap_apply (n : ℕ) (x : skeletonObj C n) :
    (skeletonMap C C' hf n x).1 = f x.1 := (rfl)

/-- The restrictions to two consecutive skeleta form a map of skeletal pairs. -/
def skeletonPairMap (n : ℕ) : skeletonPair C n ⟶ skeletonPair C' n :=
  TopPair.ofHom (skeletonMap C C' hf (n + 1)) (skeletonMap C C' hf n) (by ext x; rfl)

@[simp]
lemma skeletonPairMap_fst (n : ℕ) :
    TopPair.Hom.fst (skeletonPairMap C C' hf n) = skeletonMap C C' hf (n + 1) := (rfl)

@[simp]
lemma skeletonPairMap_snd (n : ℕ) :
    TopPair.Hom.snd (skeletonPairMap C C' hf n) = skeletonMap C C' hf n := (rfl)

/-- Restriction of the identity map to a skeleton is the identity. -/
@[simp]
lemma skeletonMap_id (n : ℕ) :
    skeletonMap C C (isCellular_id C) n = 𝟙 (skeletonObj C n) := by
  ext x
  rfl

/-- Restriction of the identity map to a skeletal pair is the identity pair map. -/
@[simp]
lemma skeletonPairMap_id (n : ℕ) :
    skeletonPairMap C C (isCellular_id C) n = 𝟙 (skeletonPair C n) := by
  ext : 2 <;> rfl

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] {F : Set Z}
  (C'' : Set Z) [RelCWComplex C'' F]
  {g : TopCat.of Y ⟶ TopCat.of Z} (hg : IsCellular C' C'' g)

/-- Restriction to a skeleton respects composition of cellular maps. -/
@[reassoc]
lemma skeletonMap_comp (n : ℕ) :
    skeletonMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonMap C C' hf n ≫ skeletonMap C' C'' hg n := by
  ext x
  rfl

/-- Maps of skeletal pairs respect composition of cellular maps. -/
@[reassoc]
lemma skeletonPairMap_comp (n : ℕ) :
    skeletonPairMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonPairMap C C' hf n ≫ skeletonPairMap C' C'' hg n := by
  ext : 2 <;> rfl

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- A cellular map induces a morphism on each cellular chain group. -/
def cellularChainGroupMap (n : ℕ) :
    cellularChainGroup C R n ⟶ cellularChainGroup C' R n :=
  TopPair.singularHomologyMap (skeletonPairMap C C' hf n) R n

/-- The identity cellular map acts as the identity on each cellular chain group. -/
@[simp]
lemma cellularChainGroupMap_id (n : ℕ) :
    cellularChainGroupMap C C (isCellular_id C) R n = 𝟙 (cellularChainGroup C R n) := by
  simp [cellularChainGroupMap, skeletonPairMap_id, TopPair.singularHomologyMap]

/-- The maps on cellular chain groups respect composition of cellular maps. -/
@[reassoc]
lemma cellularChainGroupMap_comp (n : ℕ) :
    cellularChainGroupMap C C'' (IsCellular.comp C C' hf hg) R n =
      cellularChainGroupMap C C' hf R n ≫ cellularChainGroupMap C' C'' hg R n := by
  rw [cellularChainGroupMap, skeletonPairMap_comp C C' hf C'' hg n]
  rw [TopPair.singularHomologyMap, Functor.map_comp, SSetPair.homologyMap_comp]
  rfl

/-- The cellular chain-group maps commute with the cellular differential. -/
@[reassoc]
lemma cellularChainGroupMap_comp_cellularDifferential (n : ℕ) :
    cellularChainGroupMap C C' hf R (n + 1) ≫ cellularDifferential C' R n =
      cellularDifferential C R n ≫ cellularChainGroupMap C C' hf R n := by
  rw [cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ,
    cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ]
  have hδ := TopPair.singularHomologyδ_naturality R
    (skeletonPairMap C C' hf (n + 1)) (n + 1) n
  have hπ := SSetPair.homologyπ_naturality
    (TopPair.toSSetPair.map (skeletonPairMap C C' hf n)) R n
  -- Both restrictions of a cellular map to the middle skeleton are the same map.
  have hπ' : SSet.homologyMap (TopCat.toSSet.map (skeletonMap C C' hf (n + 1))) R n ≫
      skeletonPairπ C' R n =
        skeletonPairπ C R n ≫ cellularChainGroupMap C C' hf R n := by
    simpa only [skeletonPairπ, cellularChainGroupMap, TopPair.singularHomologyMap,
      TopPair.singularHomologyπ, TopPair.toSSetPair_map_right,
      TopPair.toSSetPair_obj_right, skeletonPairMap_fst, skeletonPair_fst] using hπ
  have hδ' : cellularChainGroupMap C C' hf R (n + 1) ≫ skeletonPairδ C' R n =
      skeletonPairδ C R n ≫
        SSet.homologyMap (TopCat.toSSet.map (skeletonMap C C' hf (n + 1))) R n := by
    -- The pair's subspace and the corresponding skeleton are equal, but their homology objects
    -- are displayed through different wrappers in the two naturality statements.
    convert hδ.symm using 1
    simp only [cellularChainGroup, skeletonHomology, cellularChainGroupMap, skeletonPairδ,
      skeletonPairMap_snd, skeletonPair_snd]
    exact Iff.rfl
  calc
    _ = skeletonPairδ C R n ≫
          SSet.homologyMap (TopCat.toSSet.map (skeletonMap C C' hf (n + 1))) R n ≫
            skeletonPairπ C' R n := by
              simpa only [Category.assoc] using congrArg (· ≫ skeletonPairπ C' R n) hδ'
    _ = _ := by
      simpa only [Category.assoc] using congrArg (skeletonPairδ C R n ≫ ·) hπ'

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
  simp [cellularChainComplexMap_f, cellularChainGroupMap_id]

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
