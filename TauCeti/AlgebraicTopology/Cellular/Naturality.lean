/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.Map

/-!
# Naturality of the cellular–singular homology comparison

The cellular–singular comparison intertwines the homology map of a cellular chain map with the
relative singular homology map of the original continuous map. Thus it compares the functorial
homology theories, including their maps, rather than only their objects in each degree.

The underlying identification of cellular cycles with the homology of a skeleton relative
to the base is natural without a dimension bound. Both squares use the restrictions of the
original map to pairs, and require neither finite cell sets nor chosen singular representatives.
Coefficients are any object of an abelian category with coproducts exact for the cell sets
of both complexes.

The source is A. Hatcher, *Algebraic Topology*, Section 2.2, Theorem 2.35 and the discussion
of cellular maps following it. The comparison maps and their formulas on cycles are those
of `TauCeti.cellularCyclesIso` and `TauCeti.cellularSingularHomologyIso`.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex HomologicalComplex

universe w v u

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
  [∀ m, HasExactColimitsOfShape (Discrete (cell C' m)) A]

/-- The identification of cellular cycles with the homology of the skeleton relative to
the base is natural under cellular maps, without a dimension bound. -/
@[reassoc]
lemma cellularCyclesIso_hom_naturality (n : ℕ) :
    cyclesMap (cellularChainComplexMap C C' hf R) n ≫ (cellularCyclesIso C' R n).hom =
      (cellularCyclesIso C R n).hom ≫
        (skeletonBasePair C n).singularHomologyMap (skeletonBasePairMap C C' hf n) R n := by
  apply (cancel_epi (cellularCyclesIso C R n).inv).1
  apply (cancel_mono ((cellularCyclesIso C' R n).inv ≫
    (cellularChainComplex C' R).iCycles n)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [cyclesMap_i, cellularCyclesIso_inv_comp_iCycles_assoc,
    cellularCyclesIso_inv_comp_iCycles, cellularChainComplexMap_f]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [cellularChainGroupMap_def, ← TopPair.singularHomologyMap_comp_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, skeletonBasePairMap_comp_toSkeletonPair]

/-- The inverse identification from relative skeletal homology to cellular cycles is natural
under cellular maps, without a dimension bound. -/
@[reassoc]
lemma cellularCyclesIso_inv_naturality (n : ℕ) :
    (skeletonBasePair C n).singularHomologyMap (skeletonBasePairMap C C' hf n) R n ≫
        (cellularCyclesIso C' R n).inv =
      (cellularCyclesIso C R n).inv ≫ cyclesMap (cellularChainComplexMap C C' hf R) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (cellularCyclesIso_hom_naturality C C' hf R n).symm

variable (n : ℕ)
  [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
    (skeletonBasePairToComplex C (n + 1)) R n)]
  [IsIso ((skeletonBasePair C' (n + 1)).singularHomologyMap
    (skeletonBasePairToComplex C' (n + 1)) R n)]

/-- The cellular–singular comparison is natural under cellular maps of relative CW complexes.
The singular map is induced by the original map of the whole pairs. -/
@[reassoc]
lemma cellularSingularHomologyIso_hom_naturality :
    homologyMap (cellularChainComplexMap C C' hf R) n ≫
        (cellularSingularHomologyIso C' R n).hom =
      (cellularSingularHomologyIso C R n).hom ≫
        (complexBasePair C).singularHomologyMap (complexBasePairMap C C' hf) R n := by
  apply (cancel_epi ((cellularChainComplex C R).homologyπ n)).1
  simp only [homologyπ_naturality_assoc,
    homologyπ_comp_cellularSingularHomologyIso_hom,
    homologyπ_comp_cellularSingularHomologyIso_hom_assoc,
    cellularCyclesIso_hom_naturality_assoc]
  rw [← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
    skeletonBasePairMap_comp_toComplex]

/-- The inverse cellular–singular comparison is natural under cellular maps of relative CW
complexes. -/
@[reassoc]
lemma cellularSingularHomologyIso_inv_naturality :
    (complexBasePair C).singularHomologyMap (complexBasePairMap C C' hf) R n ≫
        (cellularSingularHomologyIso C' R n).inv =
      (cellularSingularHomologyIso C R n).inv ≫
        homologyMap (cellularChainComplexMap C C' hf R) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (cellularSingularHomologyIso_hom_naturality C C' hf R n).symm

end TauCeti
