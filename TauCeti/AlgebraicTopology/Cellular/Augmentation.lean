/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Naturality
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The augmentation of the cellular chain complex

For a CW complex `C`, the augmentation `TauCeti.cellularAugmentation C R` of the cellular chain
complex is the map from the degree-zero cellular chain group `H₀(X⁰, ∅)` to the coefficient object
`R` that sends a cellular `0`-chain to its homology class in `H₀(C)`, through the
cellular–singular comparison, followed by the singular augmentation `H₀(C) ⟶ R` of Mathlib.
Equivalently, on `H₀(X⁰)` it is the map induced by the inclusion `X⁰ ⊆ C` followed by the
singular augmentation (`TauCeti.singularHomologyπ_comp_cellularAugmentation`), and with
coefficients in a ring it sends every `0`-cell of the cellular basis to `1`
(`TauCeti.cellularAugmentation_cellularChainBasis`).
It kills the boundaries of `1`-cells (`TauCeti.cellularDifferential_comp_cellularAugmentation`),
so it is a chain map `TauCeti.cellularChainComplexAugmentation C R` from the cellular chain
complex to `R` placed in degree `0`, and it is natural under cellular maps
(`TauCeti.cellularChainGroupMap_comp_cellularAugmentation`).

The augmentation identifies the zeroth cellular homology with the zeroth singular homology
followed by the singular augmentation
(`TauCeti.homologyMap_cellularChainComplexAugmentation_zero`). So when `C` is path connected and
its singular homology vanishes in positive degrees, the augmented cellular chain complex is exact:
the augmentation is a quasi-isomorphism
(`TauCeti.quasiIso_cellularChainComplexAugmentation`). Applied to the CW structure lifted along
a quotient covering map with acyclic total space, this makes its cellular chains a projective
resolution of the trivial representation (`TauCeti.cellularResolution`).

Coefficients are an object of an abelian category with coproducts exact for the cell sets, as for
modules. The comparison of cellular with singular homology must hold in the degrees used, through
its hypothesis on the inclusion of the `(n + 1)`-skeleton; it does for every finite-dimensional
complex and, when sequential colimits are exact, for every complex.

## Main definitions

* `TauCeti.cellularAugmentation`: the augmentation `H₀(X⁰, ∅) ⟶ R` of the cellular chains.
* `TauCeti.cellularChainComplexAugmentation`: the augmentation as a chain map to `R` placed in
  degree `0`.

## Main results

* `TauCeti.singularHomologyπ_comp_cellularAugmentation` and
  `TauCeti.cellularAugmentation_cellularChainBasis`: the augmentation on the zero-skeleton and on
  the cellular basis.
* `TauCeti.cellularChainGroupMap_comp_cellularAugmentation`: the augmentation is natural under
  cellular maps.
* `TauCeti.quasiIso_cellularChainComplexAugmentation`: the augmentation of a path-connected CW
  complex with vanishing positive-degree singular homology is a quasi-isomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2.
-/
public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex HomologicalComplex AlgebraicTopology

universe w v u

namespace TauCeti

section Augmentation

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
  [IsIso ((skeletonBasePair C 1).singularHomologyMap (skeletonBasePairToComplex C 1) R 0)]

/-- Every degree-zero cellular chain is a cellular cycle. -/
private abbrev cellularCyclesZeroLift :
    cellularChainGroup C R 0 ⟶ (cellularChainComplex C R).cycles 0 :=
  (cellularChainComplex C R).liftCycles (eqToHom (cellularChainComplex_X C R 0).symm) 0 (by simp)
    (by simp)

/-- **The augmentation of the cellular chains** of a CW complex `C`: a degree-zero cellular chain,
which is a cellular cycle, goes to its cellular homology class, then to its class in `H₀(C)` by
the cellular–singular comparison, and then to `R` by the singular augmentation. -/
def cellularAugmentation : cellularChainGroup C R 0 ⟶ R :=
  cellularCyclesZeroLift C R ≫ (cellularChainComplex C R).homologyπ 0 ≫
    (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫ (TopCat.of C).singularHomology₀ε R

/-- On cellular cycles in degree `0`, the augmentation is the cellular–singular comparison
followed by the singular augmentation. -/
lemma iCycles_comp_cellularAugmentation :
    (cellularChainComplex C R).iCycles 0 ≫ eqToHom (cellularChainComplex_X C R 0) ≫
        cellularAugmentation C R =
      (cellularChainComplex C R).homologyπ 0 ≫
        (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫
          (TopCat.of C).singularHomology₀ε R := by
  have h : (cellularChainComplex C R).iCycles 0 ≫ eqToHom (cellularChainComplex_X C R 0) ≫
      cellularCyclesZeroLift C R = 𝟙 _ := by
    rw [← cancel_mono ((cellularChainComplex C R).iCycles 0)]
    simp
  rw [cellularAugmentation, reassoc_of% h]

/-- The augmentation vanishes on the boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
lemma cellularDifferential_comp_cellularAugmentation :
    cellularDifferential C R 0 ≫ cellularAugmentation C R = 0 := by
  have h : cellularDifferential C R 0 ≫ cellularCyclesZeroLift C R ≫
      (cellularChainComplex C R).homologyπ 0 = 0 := by
    rw [comp_liftCycles_assoc]
    exact (cellularChainComplex C R).liftCycles_homologyπ_eq_zero_of_boundary _ 0 (by simp)
      (eqToHom (cellularChainComplex_X C R 1).symm) (by simp [cellularChainComplex_d])
  rw [cellularAugmentation, reassoc_of% h, zero_comp]

omit [IsIso ((skeletonBasePair C 1).singularHomologyMap (skeletonBasePairToComplex C 1) R 0)] in
private lemma cellularCyclesZeroLift_comp_cellularCyclesIso_hom :
    cellularCyclesZeroLift C R ≫ (cellularCyclesIso C R 0).hom = 𝟙 _ := by
  rw [← cancel_mono ((cellularCyclesIso C R 0).inv ≫ (cellularChainComplex C R).iCycles 0),
    Category.assoc, Iso.hom_inv_id_assoc]
  simp

/-- **The augmentation on the zero-skeleton**: on the singular homology `H₀(X⁰)` of the
zero-skeleton, the augmentation is the map induced by the inclusion `X⁰ ⊆ C` followed by the
singular augmentation of `C`. -/
lemma singularHomologyπ_comp_cellularAugmentation :
    (skeletonPair C 0).singularHomologyπ R 0 ≫ cellularAugmentation C R =
      ((singularHomologyFunctor A 0).obj R).map
          (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 1).subset_complex)) ≫
        (TopCat.of C).singularHomology₀ε R := by
  have h₁ : cellularCyclesZeroLift C R ≫ (cellularChainComplex C R).homologyπ 0 ≫
      (cellularSingularHomologyIso C R 0).hom =
        (skeletonBasePair C 0).singularHomologyMap (skeletonBasePairToComplex C 0) R 0 := by
    rw [homologyπ_comp_cellularSingularHomologyIso_hom,
      reassoc_of% cellularCyclesZeroLift_comp_cellularCyclesIso_hom]
  have h₂ := TopPair.singularHomologyπ_naturality (skeletonBasePairToComplex C 0) R 0
  rw [skeletonBasePairToComplex_fst] at h₂
  have key : (skeletonPair C 0).singularHomologyπ R 0 ≫ cellularCyclesZeroLift C R ≫
      (cellularChainComplex C R).homologyπ 0 ≫ (cellularSingularHomologyIsoOfCWComplex C R 0).hom =
        ((singularHomologyFunctor A 0).obj R).map
          (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 1).subset_complex)) := by
    apply (cancel_mono ((complexBasePair C).singularHomologyπ R 0)).1
    -- The absolute comparison lands in `singularHomologyFunctor`, while the quotient map starts
    -- from the homology of the singular simplicial set; the two presentations agree only up to
    -- unfolding, so `rw` cannot reassociate here and the composites are rearranged as terms.
    refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (cellularSingularHomologyIsoOfCWComplex_hom_comp_singularHomologyπ C R 0))))))).trans ?_
    exact (congrArg (_ ≫ ·) h₁).trans h₂.symm
  rw [cellularAugmentation]
  exact (reassoc_of% key) _

/-- The augmentation is the identity on the summand of each `0`-cell of the degree-zero cellular
chain group `∐ R`. -/
@[reassoc (attr := simp)]
lemma ι_cellularChainGroupIso_inv_comp_cellularAugmentation (i : cell C 0) :
    Sigma.ι (fun _ : cell C 0 ↦ R) i ≫ (cellularChainGroupIso C R 0).inv ≫
      cellularAugmentation C R = 𝟙 R := by
  have hL := singularHomologyπ_comp_cellularAugmentation C R
  rw [singularHomologyMap_singularHomology₀ε] at hL
  rw [ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    Iso.inv_comp_eq, Category.comp_id, singularHomologyDiskBoundaryPairIso_zero_hom]
  -- As above, the ordinary homology of the disk appears in two presentations that agree only up
  -- to unfolding, so the remaining steps are composed as terms rather than rewritten.
  refine (cancel_epi ((diskBoundaryPair.{w} 0).singularHomologyπ R 0)).1
    (Eq.trans ?_ (IsIso.hom_inv_id_assoc _ _).symm)
  have h := TopPair.singularHomologyπ_naturality (characteristicCellPairMap C i) R 0
  exact (Category.assoc _ _ _).symm.trans ((h =≫ _).symm.trans ((Category.assoc _ _ _).trans
    ((_ ≫= hL).trans (singularHomologyMap_singularHomology₀ε R
      (TopPair.Hom.fst (characteristicCellPairMap C i))))))

/-- **The augmented cellular chain complex**: the augmentation as a chain map from the cellular
chain complex to the coefficient object placed in degree `0`. -/
def cellularChainComplexAugmentation :
    cellularChainComplex C R ⟶ (ChainComplex.single₀ A).obj R :=
  ((cellularChainComplex C R).toSingle₀Equiv R).symm
    ⟨eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R, by
      simp [cellularChainComplex_d]⟩

/-- In degree `0` the augmentation chain map is `TauCeti.cellularAugmentation`. -/
@[simp]
lemma cellularChainComplexAugmentation_f_zero :
    (cellularChainComplexAugmentation C R).f 0 =
      eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- On zeroth homology the augmentation is the cellular–singular comparison followed by the
singular augmentation. -/
lemma homologyMap_cellularChainComplexAugmentation_zero :
    homologyMap (cellularChainComplexAugmentation C R) 0 ≫
        (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 R).hom =
      (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫ (TopCat.of C).singularHomology₀ε R := by
  rw [← cancel_epi ((cellularChainComplex C R).homologyπ 0), homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom, cyclesMap_i_assoc,
    cellularChainComplexAugmentation_f_zero, ← iCycles_comp_cellularAugmentation]
  simp

variable {Y : Type w} [TopologicalSpace Y] [T2Space Y] (C' : Set Y) [CWComplex C']
  [∀ m, HasExactColimitsOfShape (Discrete (cell C' m)) A]
  [IsIso ((skeletonBasePair C' 1).singularHomologyMap (skeletonBasePairToComplex C' 1) R 0)]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- **The augmentation is natural under cellular maps.** -/
@[reassoc (attr := simp)]
lemma cellularChainGroupMap_comp_cellularAugmentation :
    cellularChainGroupMap C C' hf R 0 ≫ cellularAugmentation C' R = cellularAugmentation C R := by
  have h : cellularChainGroupMap C C' hf R 0 ≫ cellularCyclesZeroLift C' R =
      cellularCyclesZeroLift C R ≫ cyclesMap (cellularChainComplexMap C C' hf R) 0 := by
    rw [← cancel_mono ((cellularChainComplex C' R).iCycles 0)]
    simp
  rw [cellularAugmentation, reassoc_of% h, ← homologyπ_naturality_assoc,
    cellularSingularHomologyIsoOfCWComplex_hom_naturality_assoc,
    singularHomologyMap_singularHomology₀ε, cellularAugmentation]

end Augmentation

section Basis

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  (R : Type w) [Ring R]

/-- **The augmentation sends every `0`-cell to `1`**: with coefficients in a ring, it is the sum of
the coefficients of a cellular `0`-chain in the cellular basis. This is not a `simp` lemma:
`simp` unfolds `TauCeti.cellularChainBasis` by `TauCeti.cellularChainBasis_apply` first. -/
lemma cellularAugmentation_cellularChainBasis (i : cell C 0) :
    cellularAugmentation C (ModuleCat.of R R) (cellularChainBasis C R 0 i) = 1 := by
  rw [cellularChainBasis_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ι_cellularChainGroupIso_inv_comp_cellularAugmentation]
  rfl

end Basis

section QuasiIso

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
  [∀ n, IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
    (skeletonBasePairToComplex C (n + 1)) R n)]

/-- **The augmented cellular chain complex of an acyclic CW complex is exact**: if `C` is path
connected and its singular homology vanishes in positive degrees, the augmentation is a
quasi-isomorphism. -/
theorem quasiIso_cellularChainComplexAugmentation [PathConnectedSpace C]
    (hC : ∀ n, IsZero (((singularHomologyFunctor A (n + 1)).obj R).obj (TopCat.of C))) :
    QuasiIso (cellularChainComplexAugmentation C R) := by
  rw [quasiIso_iff]
  rintro (_ | n)
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have : IsIso (homologyMap (cellularChainComplexAugmentation C R) 0 ≫
        (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 R).hom) := by
      rw [homologyMap_cellularChainComplexAugmentation_zero]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 R).hom
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj R n),
      exactAt_iff_isZero_homology]
    exact (hC n).of_iso (cellularSingularHomologyIsoOfCWComplex C R (n + 1))

end QuasiIso

end TauCeti
