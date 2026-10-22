/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
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

The coefficients lie in an abelian category with coproducts in which coproducts and sequential
colimits are exact, as for modules over a ring; no finiteness of the set of cells is needed.

## Main definitions

* `TauCeti.cellularAugmentation`: the augmentation of the cellular chains in degree `0`.
* `TauCeti.cellularChainComplexAugmentation`: the augmentation as a chain map to the coefficients
  placed in degree `0`.

## Main results

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
  [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]

/-- The **augmentation** of the cellular chains of a CW complex `C` in degree `0`: the projection
onto cellular homology in degree `0`, followed by the cellular–singular comparison with
`H₀(C; R)` and the augmentation `TopCat.singularHomology₀ε` of singular homology. -/
def cellularAugmentation : cellularChainGroup C R 0 ⟶ R :=
  eqToHom (cellularChainComplex_X C R 0).symm ≫ (cellularChainComplex C R).pOpcycles 0 ≫
    (cellularChainComplex C R).isoHomologyι₀.inv ≫
      (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫ (TopCat.of C).singularHomology₀ε R

/-- The augmentation factors through cellular homology in degree `0`, the cellular–singular
comparison and the augmentation of singular homology. -/
lemma cellularAugmentation_def :
    cellularAugmentation C R =
      eqToHom (cellularChainComplex_X C R 0).symm ≫ (cellularChainComplex C R).pOpcycles 0 ≫
        (cellularChainComplex C R).isoHomologyι₀.inv ≫
          (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫
            (TopCat.of C).singularHomology₀ε R :=
  (rfl)

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

omit [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] in
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
is path connected; in positive degrees both complexes are exact. -/
theorem quasiIso_cellularChainComplexAugmentation [ContractibleSpace C] :
    QuasiIso (cellularChainComplexAugmentation C R) where
  quasiIsoAt m := by
    cases m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ (by simp) rfl rfl]
      have hε : (cellularChainComplex C R).d 1 0 ≫
          eqToHom (cellularChainComplex_X C R 0) ≫ cellularAugmentation C R = 0 := by simp
      -- The map induced on cellular homology in degree `0` is an isomorphism.
      have : IsIso ((cellularChainComplex C R).descOpcycles _ 1 (by simp) hε) := by
        rw [show (cellularChainComplex C R).descOpcycles _ 1 _ hε =
          (cellularChainComplex C R).isoHomologyι₀.inv ≫
            (cellularSingularHomologyIsoOfCWComplex C R 0).hom ≫
              (TopCat.of C).singularHomology₀ε R by
          rw [← cancel_epi ((cellularChainComplex C R).pOpcycles 0), p_descOpcycles]
          simp [cellularAugmentation]]
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
  [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]

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
