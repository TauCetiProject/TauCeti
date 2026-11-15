/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.AlgebraicTopology.Cellular.Coproduct
public import TauCeti.AlgebraicTopology.Cellular.Naturality
public import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# The augmented cellular chain complex of a contractible CW complex

The **augmentation** of the cellular chain complex of a CW complex `C` with coefficients in `R`
is the map `TauCeti.cellularAugmentation C R` from the cellular chains in degree `0` to `R`
obtained by passing to cellular homology in degree `0`, identifying it with the ordinary singular
homology `H₀(C; R)` by the cellular–singular comparison
`TauCeti.cellularSingularHomologyIsoOfCWComplex`, and applying Mathlib's augmentation
`TopCat.singularHomology₀ε` of singular homology in degree `0`. It vanishes on the boundaries of
`1`-cells, so it defines a chain map `TauCeti.cellularChainComplexAugmentation C R` from the
cellular chain complex to `R` placed in degree `0`, and it is natural under cellular maps
(`TauCeti.cellularChainGroupMap_comp_cellularAugmentation`).

If `C` is contractible, its singular homology is that of a point, so the cellular–singular
comparison shows that the cellular chain complex is exact in positive degrees
(`TauCeti.exactAt_cellularChainComplex_of_contractibleSpace`), and the augmentation is a
quasi-isomorphism (`TauCeti.quasiIso_cellularChainComplexAugmentation`): the augmented cellular
chain complex of a contractible CW complex is a resolution of the coefficients. Applied to the
universal cover of a `K(G, 1)` CW complex with the lifted CW structure, this is the exactness
behind the cellular projective resolution of the trivial representation of `G`.

The coefficients lie in an abelian category with coproducts in which coproducts are exact. The
cellular–singular comparison in degree `0` needs the inclusion of the `1`-skeleton to induce an
isomorphism on `H₀`, which is assumed as an instance hypothesis; it holds for every
finite-dimensional complex, and for every complex when sequential colimits are exact in the
coefficient category, as for modules over a ring.

## Main definitions

* `TauCeti.cellularAugmentation`: the augmentation of the cellular chains in degree `0`.
* `TauCeti.cellularChainComplexAugmentation`: the augmentation as a chain map to the coefficients
  placed in degree `0`.

## Main results

* `TauCeti.ι_cellularChainGroupIso_inv_comp_cellularAugmentation`: the augmentation takes the
  value `1` on the generator of each `0`-cell.
* `TauCeti.descOpcycles_cellularAugmentation`: on cellular homology in degree `0`, the
  augmentation induces the cellular–singular comparison followed by the augmentation of singular
  homology.
* `TauCeti.cellularChainGroupMap_comp_cellularAugmentation`: the augmentation is natural under
  cellular maps.
* `TauCeti.exactAt_cellularChainComplex_of_contractibleSpace`: the cellular chain complex of a
  contractible CW complex is exact in positive degrees.
* `TauCeti.quasiIso_cellularChainComplexAugmentation`: **the augmented cellular chain complex of
  a contractible CW complex is a resolution**.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, Theorem 2.35.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex HomologicalComplex

universe w v u

namespace TauCeti

section Augmentation

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
  [IsIso ((skeletonBasePair C 1).singularHomologyMap (skeletonBasePairToComplex C 1) R 0)]

/-- The **augmentation** of the cellular chains of a CW complex `C` in degree `0`: the projection
onto cellular homology in degree `0`, followed by the cellular–singular comparison with
`H₀(C; R)` and the augmentation `TopCat.singularHomology₀ε` of singular homology. -/
def cellularAugmentation : cellularChainGroup C R 0 ⟶ R :=
  eqToHom (cellularChainComplex_X C R 0).symm ≫ (cellularChainComplex C R).pOpcycles 0 ≫
    (cellularChainComplex C R).isoHomologyι₀.inv ≫
      (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫ (TopCat.of C).singularHomology₀ε R

/-- On the zeroth singular homology of the `0`-skeleton, mapped to the cellular chains by the
quotient for the empty subspace, the augmentation is the augmentation of singular homology. -/
@[reassoc]
lemma singularHomologyπ_comp_cellularAugmentation :
    (skeletonPair C 0).singularHomologyπ R 0 ≫ cellularAugmentation C R =
      (TopCat.of (skeletonObj C 1)).singularHomology₀ε R := by
  have h1 := cellularCyclesIso_inv_comp_iCycles C R 0
  rw [skeletonBasePairToSkeletonPair_zero, TopPair.singularHomologyMap_id, Category.id_comp] at h1
  -- The absolute and relative homology objects agree only up to unfolding, so the composites
  -- through the quotient map of `C` are reassociated by terms rather than by `rw` or `simp`.
  have key : (skeletonPair C 0).singularHomologyπ R 0 ≫ (cellularCyclesIso C R 0).inv ≫
      homologyπ _ 0 ≫ (cellularSingularHomologyIsoOfCWComplex C R 0).hom =
        SSet.homologyMap
          (TopCat.toSSet.map (TopPair.Hom.fst (skeletonBasePairToComplex C 0))) R 0 := by
    refine (cancel_mono ((complexBasePair C).singularHomologyπ R 0)).1 ?_
    refine ((Category.assoc _ _ _).trans (_ ≫= (Category.assoc _ _ _).trans (_ ≫=
      (Category.assoc _ _ _).trans (_ ≫=
        cellularSingularHomologyIsoOfCWComplex_hom_comp_singularHomologyπ C R 0)))).trans ?_
    exact (_ ≫= (_ ≫= homologyπ_comp_cellularSingularHomologyIso_hom C R 0)).trans
      ((_ ≫= Iso.inv_hom_id_assoc _ _).trans
        (TopPair.singularHomologyπ_naturality (skeletonBasePairToComplex C 0) (R := R) 0).symm)
  have h2 := key =≫ (TopCat.of C).singularHomology₀ε R
  simp only [Category.assoc] at h2
  rw [cellularAugmentation, ← h1]
  simp only [Category.assoc]
  rw [← HomologicalComplex.homology_π_ι_assoc, isoHomologyι_hom_inv_id_assoc, h2]
  exact singularHomologyMap_singularHomology₀ε R _

/-- **The augmentation takes the value `1` on each `0`-cell**: it sends the generator of a
`0`-cell, under the identification `TauCeti.cellularChainGroupIso` of the cellular chains with
copies of `R` indexed by the cells, to the identity of `R`. -/
@[reassoc (attr := simp)]
lemma ι_cellularChainGroupIso_inv_comp_cellularAugmentation (j : cell C 0) :
    Sigma.ι (fun _ ↦ R) j ≫ (cellularChainGroupIso C R 0).inv ≫ cellularAugmentation C R =
      𝟙 R := by
  let φ := TopPair.sigmaι (fun _ ↦ diskBoundaryPair.{w} 0) j ≫
    (sigmaDiskBoundaryPairIso (cell C 0) 0).hom ≫ characteristicPairMap C 0
  -- The generator is the image of the class of the point `D⁰` under the characteristic map.
  -- As in `singularHomologyπ_comp_cellularAugmentation`, the singular homology of `D⁰` appears
  -- both as `SSet.homology` and as `singularHomologyFunctor`, which agree only up to unfolding.
  -- The goals are then not type-correct at the transparency `rw` checks, so `rw` and `simp` cannot
  -- reassociate them and the composites are reassociated by terms.
  have hφ : (diskBoundaryPair.{w} 0).singularHomologyπ R 0 ≫
      TopPair.singularHomologyMap φ R 0 ≫ cellularAugmentation C R =
        (TopCat.disk.{w} 0).singularHomology₀ε R :=
    ((Category.assoc _ _ _).symm.trans
      ((TopPair.singularHomologyπ_naturality φ (R := R) 0).symm =≫ _)).trans
        ((Category.assoc _ _ _).trans ((_ ≫= singularHomologyπ_comp_cellularAugmentation C R).trans
          (singularHomologyMap_singularHomology₀ε R _)))
  exact (ι_cellularChainGroupIso_inv_assoc C R 0 j _).trans
    ((_ ≫= ((IsIso.eq_inv_comp _).2 hφ).trans
      (singularHomologyDiskBoundaryPairIso_zero_hom R).symm).trans (Iso.inv_hom_id _))

/-- The augmentation vanishes on the boundaries of `1`-cells. -/
@[reassoc (attr := simp)]
lemma cellularDifferential_comp_cellularAugmentation :
    cellularDifferential C R 0 ≫ cellularAugmentation C R = 0 := by
  have h := (cellularChainComplex C R).d_pOpcycles 1 0
  rw [cellularChainComplex_d] at h
  simp only [cellularAugmentation]
  simpa using h =≫ ((cellularChainComplex C R).isoHomologyι₀.inv ≫
      (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫ (TopCat.of C).singularHomology₀ε R)

/-- The **augmentation of the cellular chain complex**: the chain map to the coefficients placed
in degree `0` given in degree `0` by `TauCeti.cellularAugmentation`. -/
def cellularChainComplexAugmentation :
    cellularChainComplex C R ⟶ (ChainComplex.single₀ A).obj R :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R, by simp⟩

/-- In degree `0` the augmentation of the cellular chain complex is
`TauCeti.cellularAugmentation`. -/
@[simp]
lemma cellularChainComplexAugmentation_f_zero :
    (cellularChainComplexAugmentation C R).f 0 =
      eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The map that the augmentation induces on cellular homology in degree `0`, identified with the
opcycles, is the cellular–singular comparison followed by the augmentation of singular homology. -/
lemma descOpcycles_cellularAugmentation :
    (cellularChainComplex C R).descOpcycles
        (eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R) 1 (by simp)
        (by simp) =
      (cellularChainComplex C R).isoHomologyι₀.inv ≫
        (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫
          (TopCat.of C).singularHomology₀ε R := by
  rw [← cancel_epi ((cellularChainComplex C R).pOpcycles 0), p_descOpcycles]
  simp [cellularAugmentation]

omit [IsIso ((skeletonBasePair C 1).singularHomologyMap (skeletonBasePairToComplex C 1) R 0)] in
/-- **The cellular chain complex of a contractible CW complex is exact in positive degrees**:
its homology there is the positive-degree singular homology of a contractible space. The
hypothesis on the inclusion of the `(n + 2)`-skeleton holds for every finite-dimensional complex,
and for every complex when sequential colimits are exact in the coefficient category. -/
theorem exactAt_cellularChainComplex_of_contractibleSpace [ContractibleSpace C] (n : ℕ)
    [IsIso ((skeletonBasePair C (n + 2)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 2)) R (n + 1))] :
    (cellularChainComplex C R).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isZero_singularHomologyFunctor_of_contractibleSpace R (TopCat.of C)
    n.succ_ne_zero).of_iso (cellularSingularHomologyIsoOfCWComplex C R (n + 1))

/-- **The augmented cellular chain complex of a contractible CW complex is a resolution** of the
coefficients: the augmentation is a quasi-isomorphism. In degree `0` it induces the composite of
the cellular–singular comparison with the augmentation `H₀(C; R) ⟶ R`, an isomorphism because `C`
is path connected; in positive degrees both complexes are exact. The hypotheses on the inclusions
of the skeleta hold for every finite-dimensional complex, and for every complex when sequential
colimits are exact in the coefficient category. -/
theorem quasiIso_cellularChainComplexAugmentation [ContractibleSpace C]
    [∀ n : ℕ, IsIso ((skeletonBasePair C (n + 2)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 2)) R (n + 1))] :
    QuasiIso (cellularChainComplexAugmentation C R) where
  quasiIsoAt m := by
    cases m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ (by simp) rfl rfl]
      have hε : (cellularChainComplex C R).d 1 0 ≫
          eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R = 0 := by simp
      -- The map induced on cellular homology in degree `0` is an isomorphism.
      have : IsIso ((cellularChainComplex C R).descOpcycles _ 1 (by simp) hε) := by
        rw [descOpcycles_cellularAugmentation]
        infer_instance
      obtain ⟨hex, hepi⟩ := (ChainComplex.isIso_descOpcycles_iff _ _ _).1 this
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 hex, ?_⟩
      · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).symm (by simp) (by simp)
      · simp only [shortComplexFunctor'_map_τ₂, cellularChainComplexAugmentation_f_zero]
        exact hepi
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact exactAt_cellularChainComplex_of_contractibleSpace C R m

end Augmentation

section Naturality

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  (C : Set X) [CWComplex C] (C' : Set Y) [CWComplex C']
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
  [∀ m, HasExactColimitsOfShape (Discrete (cell C' m)) A]
  [IsIso ((skeletonBasePair C 1).singularHomologyMap (skeletonBasePairToComplex C 1) R 0)]
  [IsIso ((skeletonBasePair C' 1).singularHomologyMap (skeletonBasePairToComplex C' 1) R 0)]

/-- **The augmentation is natural under cellular maps.** -/
@[reassoc (attr := simp)]
lemma cellularChainGroupMap_comp_cellularAugmentation :
    cellularChainGroupMap C C' hf R 0 ≫ cellularAugmentation C' R = cellularAugmentation C R := by
  have h : eqToHom (cellularChainComplex_X C R 0).symm ≫ (cellularChainComplexMap C C' hf R).f 0 =
      cellularChainGroupMap C C' hf R 0 ≫ eqToHom (cellularChainComplex_X C' R 0).symm := by
    simp
  simp only [cellularAugmentation, ← reassoc_of% h]
  rw [← HomologicalComplex.p_opcyclesMap_assoc,
    ← ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    cellularSingularHomologyIsoOfCWComplex_hom_naturality_assoc,
    singularHomologyMap_singularHomology₀ε]

end Naturality

end TauCeti
