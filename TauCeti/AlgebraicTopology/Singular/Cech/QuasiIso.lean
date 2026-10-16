/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotalComplex
public import TauCeti.AlgebraicTopology.Singular.Cech.SmallChains
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-!
# The Čech--singular total complex computes singular homology

Let `U` be a family of open subsets of `X`. The augmentation of the Čech--singular bicomplex of
`U` onto the singular chains of `X` induces a chain map `openCoverSingularTotalAugmentation` from
the total complex to the singular chains of `X`. On the summand of Čech degree zero it is the map
of singular chains induced by the projection `∐ᵢ Uᵢ ⟶ X`, and it vanishes on the summands of
positive Čech degree.

When `U` covers `X` and the coefficients lie in an abelian category, this chain map is a
quasi-isomorphism. The rows of the bicomplex resolve the singular chains which are small for `U`
(`TauCeti.TopCat.openCoverSmallSingularAugmentationRowHomotopyEquiv`), so the total complex is
quasi-isomorphic to the small chains (`HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`),
and the small-chain theorem `TauCeti.smallSingularChainHomotopyEquiv` identifies these with all
singular chains.

## Main definitions and results

* `TauCeti.TopCat.openCoverSingularTotalAugmentation`: the augmentation of the total
  Čech--singular complex onto the singular chains of `X`.
* `TauCeti.TopCat.quasiIso_openCoverSingularTotalAugmentation`: it is a quasi-isomorphism when `U`
  covers `X`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, §15, for the Čech--singular double complex of an open cover.
* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21, for the small-chain theorem.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TopologicalSpace Opposite
open scoped Simplicial

universe v u

namespace TauCeti.TopCat

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

section Preadditive

variable {C : Type v} [Category C] [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C]
  [HasCoproducts.{0} C] (R : C)

/-- The augmentation of the total Čech--singular complex of a family of open sets onto the
singular chains of the ambient space. -/
def openCoverSingularTotalAugmentation :
    openCoverSingularTotal U R ⟶ ((singularChainComplexFunctor.{u} C).obj R).obj X :=
  (openCoverSingularBicomplex U R).totalAugmentation
    ((openCoverSingularAugmentation U R).f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom)
    (HomologicalComplex₂.d_comp_f_zero_singleObjXSelf_hom _ (openCoverSingularAugmentation U R))

/-- On the summand of Čech degree zero, the augmentation of the total complex is the map of
singular chains induced by the projection of the disjoint union of the family onto the ambient
space. -/
@[simp, reassoc]
theorem ιTotal_openCoverSingularTotalAugmentation_f_zero (q : ℕ) :
    (openCoverSingularBicomplex U R).ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫
        (openCoverSingularTotalAugmentation U R).f q =
      (((singularChainComplexFunctor.{u} C).obj R).map
        ((openCoverArrow U).augmentedCechNerve.hom.app (op ⦋0⦌))).f q := by
  rw [openCoverSingularTotalAugmentation, HomologicalComplex₂.ιTotal_totalAugmentation_f_zero,
    HomologicalComplex.comp_f, openCoverSingularAugmentation_f_zero, ChainComplex.single₀ObjXSelf,
    Iso.refl_hom, HomologicalComplex.id_f]
  -- The identity is on degree `q` of the single complex's object, which is the singular chains
  -- only up to definitional unfolding of `HomologicalComplex.single`, so `rw` cannot close it.
  exact Category.comp_id _

/-- The augmentation of the total complex vanishes on the summands of positive Čech degree. -/
@[simp, reassoc]
theorem ιTotal_openCoverSingularTotalAugmentation_f_succ (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p + 1, q) = n) :
    (openCoverSingularBicomplex U R).ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫
        (openCoverSingularTotalAugmentation U R).f n = 0 :=
  HomologicalComplex₂.ιTotal_totalAugmentation_f_succ _ _ _ p q n h

omit [HasCoproducts.{0} C] in
/-- The column of the augmentation onto the small chains, followed by their inclusion, is the
column of the augmentation onto all singular chains. -/
private lemma openCoverSmallSingularAugmentation_f_zero_comp :
    ((openCoverSmallSingularAugmentation U R).f 0 ≫
        (HomologicalComplex.singleObjXSelf _ 0 _).hom) ≫
      SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R =
    (openCoverSingularAugmentation U R).f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom := by
  simp only [← openCoverSmallSingularAugmentation_comp_single₀_map, HomologicalComplex.comp_f,
    openCoverSmallSingularAugmentation_f_zero, ChainComplex.single₀_map_f_zero,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom]
  -- Both identities are on the singular chains, small for `U` on the left and all of them on the
  -- right; they are not identified syntactically with the targets of the adjacent maps.
  exact (congrArg (· ≫ _) (Category.comp_id _)).trans (Category.comp_id _).symm

end Preadditive

section Abelian

variable {C : Type v} [Category C] [Abelian C] [HasCoproducts.{u} C] [HasCoproducts.{0} C] (R : C)

/-- **The total Čech--singular complex of an open cover computes singular homology.** For an
open cover `U` of `X` and coefficients in an abelian category, the augmentation of the total
Čech--singular complex onto the singular chains of `X` is a quasi-isomorphism. -/
theorem quasiIso_openCoverSingularTotalAugmentation (hU : ⋃ i, (U i : Set X) = Set.univ) :
    QuasiIso (openCoverSingularTotalAugmentation U R) := by
  -- The small chains include into all singular chains by a chain homotopy equivalence.
  have : QuasiIso (SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι
      R) := by
    rw [← smallSingularChainHomotopyEquiv_hom R (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hU]
    infer_instance
  -- The rows of the bicomplex resolve the chains which are small for `U`.
  exact HomologicalComplex₂.quasiIso_totalAugmentation_of_rows_of_quasiIso
    (openCoverSmallSingularAugmentation U R) (fun q ↦ by
      rw [← openCoverSmallSingularAugmentationRowHomotopyEquiv_hom]
      infer_instance)
    (SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R) _
    (openCoverSmallSingularAugmentation_f_zero_comp U R)

end Abelian

end TauCeti.TopCat
