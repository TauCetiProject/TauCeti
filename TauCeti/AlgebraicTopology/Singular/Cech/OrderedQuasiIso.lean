/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.OrderedCech.Cover
public import TauCeti.Algebra.Homology.TotalComplex
public import TauCeti.AlgebraicTopology.Singular.Cech
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import TauCeti.AlgebraicTopology.Singular.Subspace

/-!
# The ordered Čech--singular total complex computes singular homology

Let `U : ι → Opens X` be a family of open sets indexed by a linearly ordered type, and let
`TauCeti.cechDoubleComplex U R` be its ordered Čech double complex of singular chains, whose column
`p` is the sum of the singular chains of the intersections `U_{i₀} ∩ ⋯ ∩ U_{iₚ}` over
`i₀ < ⋯ < iₚ`. Its augmentation `TauCeti.cechTotalAugmentation U R` from the total complex to the
singular chains of `X` is a quasi-isomorphism when the `U i` cover `X` and the coefficients lie in
an abelian category (`TauCeti.quasiIso_cechTotalAugmentation`). For finitely many open sets the
double complex has finitely many nonzero columns, so its filtration by columns is finite.

The augmentation of column `0` factors through the singular chains which are small for `U`
(`TauCeti.cechSmallAugmentation`). In each singular degree `q`, the `q`-th row of the double
complex is the ordered Čech complex of the cover of the small `q`-simplices by the sets of
`q`-simplices lying in each `U i`, so by `TauCeti.freeCechHomotopyEquiv` its augmentation onto
the small `q`-chains is a chain homotopy equivalence
(`TauCeti.cechSmallAugmentationRowHomotopyEquiv`). Exact augmented rows make the total complex
quasi-isomorphic to the small chains, by `HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`,
and the small-chain theorem `TauCeti.smallSingularChainHomotopyEquiv` identifies these with all
singular chains.

## Main definitions and results

* `TauCeti.cechSmallAugmentation U R`: the augmentation of the ordered Čech double complex onto the
  singular chains small for `U`, refining `TauCeti.cechAugmentation`
  (`TauCeti.cechSmallAugmentation_f_zero_comp_chainComplexMap_ι`).
* `TauCeti.cechSmallAugmentationRowHomotopyEquiv U R q`: in each singular degree `q`, the row of
  this augmentation is a chain homotopy equivalence.
* `TauCeti.quasiIso_cechTotalAugmentation`: the augmentation of the total complex onto the singular
  chains of `X` is a quasi-isomorphism for an open cover.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982: §8 for the exactness of the rows of the Čech complex, and §15 for the
  Čech--singular double complex of an open cover.
* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21, for the small-chain theorem.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicTopology
open scoped Finset Simplicial

universe w v u

namespace TauCeti

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X : TopCat.{w}} {ι : Type w} (U : ι → Opens X) (R : C)

/-- `TopCat.toSmallSingularSubcomplex` for an open subset `V` of a member of the family, with its
source stated through `Opens.toTopCat`, as in `TauCeti.cechSingularChains`. -/
private def smallLift {V : Opens X} {i : ι} (h : V ≤ U i) :
    TopCat.toSSet.obj ((Opens.toTopCat X).obj V) ⟶
      (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) :=
  TopCat.toSmallSingularSubcomplex (fun i ↦ (U i : Set X)) (S := (V : Set X)) (i := i) h

private lemma smallLift_ι {V : Opens X} {i : ι} (h : V ≤ U i) :
    smallLift U h ≫ (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι =
      TopCat.toSSet.map (Opens.inclusion' V) :=
  TopCat.toSmallSingularSubcomplex_ι (fun i ↦ (U i : Set X)) (S := (V : Set X)) (i := i) h

/-- `smallLift` does not depend on the chosen member of the family. -/
private lemma smallLift_congr {V : Opens X} {i j : ι} (hi : V ≤ U i) (hj : V ≤ U j) :
    smallLift U hi = smallLift U hj :=
  (cancel_mono (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι).1
    ((smallLift_ι U hi).trans (smallLift_ι U hj).symm)

private lemma smallLift_app_coe {V : Opens X} {i : ι} (h : V ≤ U i) {n : SimplexCategoryᵒᵖ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj V)).obj n) :
    ((smallLift U h).app n τ).1 = (TopCat.toSSet.map (Opens.inclusion' V)).app n τ :=
  TopCat.toSmallSingularSubcomplex_app_coe (fun i ↦ (U i : Set X)) (S := (V : Set X)) (i := i) h τ

private lemma smallLift_app_toSSetObjCodRestrict {V : Opens X} {i : ι} (hV : V ≤ U i) {q : ℕ}
    (σ : (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) _⦋q⦌)
    (h : Set.range (X.toSSetObjEquiv _ σ.1) ⊆ V) :
    (smallLift U hV).app _ (TopCat.toSSetObjCodRestrict σ.1 h) = σ :=
  Subtype.ext ((smallLift_app_coe U hV _).trans
    (TopCat.toSSet_map_inclusion'_toSSetObjCodRestrict σ.1 h))

/-- The chain map from the singular chains of `U_s` to the small chains, for a nonempty set `s`
of indices. Its type is stated in terms of `TauCeti.cechSingularChains`, so that it composes
syntactically with the summand inclusions of the double complex. -/
private def smallLiftChains {s : Finset ι} {i : ι} (hi : i ∈ s) :
    (cechSingularChains U R).obj (op s) ⟶
      (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R :=
  SSet.chainComplexMap (smallLift U (Finset.inf_le hi : s.inf U ≤ U i)) R

private lemma smallLiftChains_comp_ι {s : Finset ι} {i : ι} (hi : i ∈ s) :
    smallLiftChains U R hi ≫
        SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R =
      ((singularChainComplexFunctor C).obj R).map (Opens.inclusion' (s.inf U)) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg _ (smallLift_ι U _))

section

variable [LinearOrder ι]

/-- The augmentation of column `0` onto the small chains, on summands. -/
private def cechSmallAugmentationX :
    (cechDoubleComplex U R).X 0 ⟶
      (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R :=
  cechDoubleComplexDesc U R fun s ↦
    smallLiftChains U R (Finset.min'_mem s.1 (Finset.card_pos.1 (by rw [s.2]; omega)))

private lemma ι_cechSmallAugmentationX (s : {s : Finset ι // #s = 0 + 1}) {i : ι} (hi : i ∈ s.1) :
    cechDoubleComplexι U R s ≫ cechSmallAugmentationX U R = smallLiftChains U R hi :=
  (ι_cechDoubleComplexDesc U R _ s).trans (congrArg (SSet.chainComplexMap · R)
    (smallLift_congr U _ _))

private lemma cechSmallAugmentationX_comp_ι :
    cechSmallAugmentationX U R ≫
        SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R =
      cechAugmentation U R := by
  ext s : 1
  rw [cechSmallAugmentationX, ι_cechDoubleComplexDesc_assoc, smallLiftChains_comp_ι]
  -- The two sides are typed by the two defeq forms of the singular chains of `X`.
  exact (ι_cechAugmentation U R s).symm

variable [HasZeroObject C]

/-- The augmentation of the ordered Čech double complex of a family of open sets onto the singular
chains small for the family, placed in Čech degree zero: on the summand `C(U i; R)` it is the map
induced by the inclusion of the singular simplices of `U i` among the small ones. -/
def cechSmallAugmentation :
    cechDoubleComplex U R ⟶
      (ChainComplex.single₀ (ChainComplex C ℕ)).obj
        ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨cechSmallAugmentationX U R, by
      have : Mono (SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R) :=
        inferInstanceAs
          (Mono (SSet.chainComplexMap (SSetPair.of (X.smallSingularSubcomplex _).ι).hom R))
      rw [← cancel_mono (SSet.chainComplexMap (X.smallSingularSubcomplex _).ι R), zero_comp,
        Category.assoc, cechSmallAugmentationX_comp_ι]
      -- `cechAugmentation` lands in the singular chains of `X`, which are the simplicial chains of
      -- its singular simplicial set only after unfolding `singularChainComplexFunctor`.
      exact cechDoubleComplex_d_comp_cechAugmentation U R⟩

private lemma cechSmallAugmentation_f_zero :
    (cechSmallAugmentation U R).f 0 = cechSmallAugmentationX U R :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private lemma ι_cechSmallAugmentation_f_zero (s : {s : Finset ι // #s = 0 + 1}) {i : ι}
    (hi : i ∈ s.1) :
    cechDoubleComplexι U R s ≫ (cechSmallAugmentation U R).f 0 = smallLiftChains U R hi :=
  (congrArg (cechDoubleComplexι U R s ≫ ·) (cechSmallAugmentation_f_zero U R)).trans
    (ι_cechSmallAugmentationX U R s hi)

/-- The augmentation onto small chains, followed by the inclusion of the small chains, is the
augmentation onto all singular chains. -/
@[reassoc (attr := simp)]
lemma cechSmallAugmentation_f_zero_comp_chainComplexMap_ι :
    (cechSmallAugmentation U R).f 0 ≫
        SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R =
      cechAugmentation U R :=
  (congrArg (· ≫ _) (cechSmallAugmentation_f_zero U R)).trans (cechSmallAugmentationX_comp_ι U R)

end

/-! ### The rows of the double complex -/

/-- The summand inclusion of a singular `q`-simplex of `U_s` into `C_q(U_s; R)`, with its target
stated in terms of `TauCeti.cechSingularChains`. -/
private def simplexι {s : Finset ι} {q : ℕ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌) :
    R ⟶ ((cechSingularChains U R).obj (op s)).X q :=
  (TopCat.toSSet.obj _).ιChainComplex τ

private lemma simplexι_map {s t : Finset ι} (h : t ⊆ s) {q : ℕ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌) :
    simplexι U R τ ≫ ((cechSingularChains U R).map (homOfLE h).op).f q =
      simplexι U R ((TopCat.toSSet.map
        ((Opens.toTopCat X).map (homOfLE (Finset.inf_mono h)))).app _ τ) :=
  SSet.ι_chainComplexMap_f _ _ _ R τ

private lemma simplexι_hom_ext {s : Finset ι} {q : ℕ} {Y : C}
    {f g : ((cechSingularChains U R).obj (op s)).X q ⟶ Y}
    (h : ∀ τ, simplexι U R τ ≫ f = simplexι U R τ ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

/-- The morphism out of `C_q(U_s; R)` given on each singular simplex. -/
private def simplexDesc {s : Finset ι} {q : ℕ} {Y : C}
    (f : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌ → (R ⟶ Y)) :
    ((cechSingularChains U R).obj (op s)).X q ⟶ Y :=
  Sigma.desc f

private lemma simplexι_simplexDesc {s : Finset ι} {q : ℕ} {Y : C}
    (f : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌ → (R ⟶ Y)) (τ) :
    simplexι U R τ ≫ simplexDesc U R f = f τ :=
  Sigma.ι_comp_desc f τ

private lemma simplexι_smallLiftChains {s : Finset ι} {i : ι} (hi : i ∈ s) {q : ℕ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌) :
    simplexι U R τ ≫ (smallLiftChains U R hi).f q =
      (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).ιChainComplex
        ((smallLift U (Finset.inf_le hi : s.inf U ≤ U i)).app _ τ) :=
  SSet.ι_chainComplexMap_f _ _ _ R τ

/-- The cover of the small singular `q`-simplices by the sets of `q`-simplices lying in each
`U i`. -/
private def simplexCover (q : ℕ) :
    ι → Set ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) _⦋q⦌) :=
  fun i ↦ {σ | Set.range (X.toSSetObjEquiv _ σ.1) ⊆ U i}

private lemma iUnion_simplexCover (q : ℕ) : ⋃ i, simplexCover U q i = Set.univ :=
  Set.eq_univ_of_forall fun σ ↦ Set.mem_iUnion.2
    ((TopCat.mem_smallSingularSubcomplex_iff _ _ _).1 σ.2)

private lemma range_subset_finset_inf {q : ℕ} {s : Finset ι}
    {σ : (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) _⦋q⦌}
    (hσ : ∀ i ∈ s, σ ∈ simplexCover U q i) :
    Set.range (X.toSSetObjEquiv _ σ.1) ⊆ (s.inf U : Opens X) := by
  rw [Opens.coe_finset_inf]
  exact Finset.le_inf hσ

variable [LinearOrder ι]

/-- A singular simplex of `U_s`, for a nonempty set `s`, as a small simplex lying in `U i` for
every `i ∈ s`. -/
private def smallSimplex {s : Finset ι} (hs : s.Nonempty) {q : ℕ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌) :
    (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) _⦋q⦌ :=
  (smallLift U (Finset.inf_le (s.min'_mem hs) : s.inf U ≤ U _)).app _ τ

private lemma smallSimplex_mem {s : Finset ι} (hs : s.Nonempty) {q : ℕ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌) :
    ∀ i ∈ s, smallSimplex U hs τ ∈ simplexCover U q i := fun _ hi ↦ by
  simpa only [simplexCover, Set.mem_ofPred_eq, smallSimplex, smallLift_app_coe] using
    (TopCat.range_toSSetObjEquiv_toSSet_map_inclusion'_subset τ).trans
      (Finset.inf_le hi : s.inf U ≤ U _)

private lemma smallSimplex_toSSetObjCodRestrict {s : Finset ι} (hs : s.Nonempty) {q : ℕ}
    (σ : (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) _⦋q⦌)
    (h : Set.range (X.toSSetObjEquiv _ σ.1) ⊆ (s.inf U : Opens X)) :
    smallSimplex U hs (TopCat.toSSetObjCodRestrict σ.1 h) = σ :=
  smallLift_app_toSSetObjCodRestrict U _ σ h

private lemma toSSetObjCodRestrict_smallSimplex {s : Finset ι} (hs : s.Nonempty) {q : ℕ}
    (τ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj (s.inf U))) _⦋q⦌)
    (h : Set.range (X.toSSetObjEquiv _ (smallSimplex U hs τ).1) ⊆ (s.inf U : Opens X)) :
    TopCat.toSSetObjCodRestrict (smallSimplex U hs τ).1 h = τ :=
  TopCat.toSSetObjCodRestrict_eq h (smallLift_app_coe U _ τ).symm

/-- The comparison of the ordered Čech complex of `simplexCover U q` with the `q`-th row of the
ordered Čech double complex: the summand of `(s, σ)` goes to the singular simplex `σ` of `U_s`. -/
private def rowHom (q : ℕ) :
    (freeCechFunctor R (simplexCover U q)).orderedCechComplex ⟶
      ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).obj
        (cechDoubleComplex U R) where
  f p := Functor.orderedCechComplexDesc _ fun s ↦ freeCechDesc R fun σ hσ ↦
    simplexι U R (TopCat.toSSetObjCodRestrict σ.1 (range_subset_finset_inf U hσ)) ≫
      (cechDoubleComplexι U R s).f q
  comm' := by
    rintro _ p rfl
    ext s : 1
    refine freeCechFunctor_hom_ext R fun σ hσ ↦ ?_
    rw [Functor.ι_orderedCechComplexDesc_assoc, ι_freeCechDesc_assoc, Category.assoc,
      Functor.mapHomologicalComplex_obj_d, HomologicalComplex.eval_map,
      cechDoubleComplexι_f_comp_d_f, Preadditive.comp_sum, Functor.ι_orderedCechComplex_d_assoc,
      Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
      ι_freeCechFunctor_map_assoc, Functor.ι_orderedCechComplexDesc, ι_freeCechDesc,
      ← Category.assoc, simplexι_map, TopCat.toSSet_map_homOfLE_toSSetObjCodRestrict]

private lemma ι_rowHom_f {q p : ℕ} (s : {s : Finset ι // #s = p + 1}) {σ} (hσ) :
    freeCechι R σ hσ ≫ (freeCechFunctor R (simplexCover U q)).orderedCechComplexι s ≫
        (rowHom U R q).f p =
      simplexι U R (TopCat.toSSetObjCodRestrict σ.1 (range_subset_finset_inf U hσ)) ≫
        (cechDoubleComplexι U R s).f q := by
  rw [rowHom, Functor.ι_orderedCechComplexDesc, ι_freeCechDesc]

/-- The inverse of `rowHom` in degree `p` on the summand of `s`: a singular simplex of `U_s` goes to
the summand of the corresponding small simplex. -/
private def rowInvSummand (q p : ℕ) (s : {s : Finset ι // #s = p + 1}) :
    ((cechSingularChains U R).obj (op s.1)).X q ⟶
      (freeCechFunctor R (simplexCover U q)).orderedCechComplex.X p :=
  simplexDesc U R fun τ ↦
    freeCechι R (smallSimplex U (Finset.card_pos.1 (by rw [s.2]; omega)) τ)
        (smallSimplex_mem U _ τ) ≫
      (freeCechFunctor R (simplexCover U q)).orderedCechComplexι s

/-- The inverse of `rowHom` in degree `p`. -/
private def rowInvX (q p : ℕ) :
    ((cechDoubleComplex U R).X p).X q ⟶
      (freeCechFunctor R (simplexCover U q)).orderedCechComplex.X p :=
  Cofan.IsColimit.desc (isColimitCechDoubleComplexXCofan U R p q) (rowInvSummand U R q p)

private lemma ι_rowInvX {q p : ℕ} (s : {s : Finset ι // #s = p + 1}) (τ) :
    simplexι U R τ ≫ (cechDoubleComplexι U R s).f q ≫ rowInvX U R q p =
      freeCechι R (smallSimplex U (Finset.card_pos.1 (by rw [s.2]; omega)) τ)
          (smallSimplex_mem U _ τ) ≫
        (freeCechFunctor R (simplexCover U q)).orderedCechComplexι s := by
  have h := Cofan.IsColimit.fac (isColimitCechDoubleComplexXCofan U R p q)
    (rowInvSummand U R q p) s
  rw [cofan_mk_inj] at h
  rw [rowInvX]
  exact (congrArg (simplexι U R τ ≫ ·) h).trans (simplexι_simplexDesc U R _ τ)

private instance isIso_rowHom (q : ℕ) : IsIso (rowHom U R q) := by
  have (p : ℕ) : IsIso ((rowHom U R q).f p) := by
    refine ⟨rowInvX U R q p, ?_, ?_⟩
    · ext s : 1
      refine freeCechFunctor_hom_ext R fun σ hσ ↦ ?_
      rw [reassoc_of% ι_rowHom_f, ι_rowInvX]
      simp only [smallSimplex_toSSetObjCodRestrict, Category.comp_id]
    · refine cechDoubleComplex_X_X_hom_ext U R fun s ↦ simplexι_hom_ext U R fun τ ↦ ?_
      rw [reassoc_of% ι_rowInvX, ι_rowHom_f]
      simp only [toSSetObjCodRestrict_smallSimplex]
      exact (Category.comp_id (_ ≫ _)).symm.trans (Category.assoc _ _ _)
  exact HomologicalComplex.Hom.isIso_of_components _

variable [HasZeroObject C]

/-- The identification of the ordered Čech complex of `simplexCover U q`, augmented, with the
`q`-th row of the double complex augmented to small chains. -/
private def rowTargetIso (q : ℕ) :
    (ChainComplex.single₀ C).obj
        (∐ fun _ : (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet) _⦋q⦌ ↦ R) ≅
      ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).obj
        ((ChainComplex.single₀ (ChainComplex C ℕ)).obj
          ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R)) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (HomologicalComplex.eval C (ComplexShape.down ℕ) q) (ComplexShape.down ℕ) 0).app
      ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R)).symm

private lemma rowHom_comp_map_cechSmallAugmentation (q : ℕ) :
    rowHom U R q ≫ ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex
        _).map (cechSmallAugmentation U R) =
      freeCechAugmentation R (simplexCover U q) ≫ (rowTargetIso U R q).hom := by
  ext (_ | p) : 1
  · ext s : 1
    refine freeCechFunctor_hom_ext R fun σ hσ ↦ ?_
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; omega : 0 < #s.1)
    have h := freeCechι_freeCechAugmentation_f_zero_assoc R s σ hσ ((rowTargetIso U R q).hom.f 0)
    calc _ = (X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).ιChainComplex σ := by
          rw [HomologicalComplex.comp_f, reassoc_of% ι_rowHom_f,
            Functor.mapHomologicalComplex_map_f, HomologicalComplex.eval_map,
            ← HomologicalComplex.comp_f, ι_cechSmallAugmentation_f_zero U R s hi]
          exact (simplexι_smallLiftChains U R hi _).trans
            (congrArg _ (smallLift_app_toSSetObjCodRestrict U _ σ _))
      _ = _ := by
          rw [HomologicalComplex.comp_f, h]
          simp only [rowTargetIso, Iso.symm_hom]
          -- The identity is on the summand `∐ R` of the small `q`-chains, which is their degree `q`
          -- only up to unfolding `SSet.chainComplex`.
          exact (Category.comp_id _).symm
  · exact ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 _ (p + 1)
        (by simp))).eq_of_tgt _ _

/-- **The rows of the ordered Čech--singular double complex resolve the small singular chains.**
In each singular degree `q`, the augmentation of the `q`-th row of the double complex of `U`
onto the singular `q`-chains small for `U` is a chain homotopy equivalence. -/
def cechSmallAugmentationRowHomotopyEquiv (q : ℕ) :
    HomotopyEquiv
      (((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).obj
        (cechDoubleComplex U R))
      (((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).obj
        ((ChainComplex.single₀ (ChainComplex C ℕ)).obj
          ((X.smallSingularSubcomplex (fun i ↦ (U i : Set X)) : SSet).chainComplex R))) :=
  (HomotopyEquiv.ofIso (asIso (rowHom U R q)).symm).trans
    ((freeCechHomotopyEquiv R (iUnion_simplexCover U q)).trans
      (HomotopyEquiv.ofIso (rowTargetIso U R q)))

/-- The homotopy equivalence of a row is the row of the augmentation onto small chains. -/
@[simp]
lemma cechSmallAugmentationRowHomotopyEquiv_hom (q : ℕ) :
    (cechSmallAugmentationRowHomotopyEquiv U R q).hom =
      ((HomologicalComplex.eval C (ComplexShape.down ℕ) q).mapHomologicalComplex _).map
        (cechSmallAugmentation U R) := by
  rw [← cancel_epi (rowHom U R q), rowHom_comp_map_cechSmallAugmentation]
  simp only [cechSmallAugmentationRowHomotopyEquiv, HomotopyEquiv.trans_hom,
    freeCechHomotopyEquiv_hom]
  -- The forward maps of `HomotopyEquiv.ofIso` are those of the isomorphisms.
  exact IsIso.hom_inv_id_assoc (rowHom U R q) _

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  {X : TopCat.{w}} {ι : Type w} [LinearOrder ι] (U : ι → Opens X) (R : C)

/-- **The ordered Čech--singular total complex of an open cover computes singular homology.** For
an open cover `U` of `X`, indexed by a linearly ordered type, and coefficients in an abelian
category, the augmentation of the total complex of the ordered Čech double complex onto the
singular chains of `X` is a quasi-isomorphism. -/
theorem quasiIso_cechTotalAugmentation (hU : ⋃ i, (U i : Set X) = Set.univ) :
    QuasiIso (cechTotalAugmentation U R) := by
  -- The small chains include into all singular chains by a chain homotopy equivalence.
  have : QuasiIso (SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι
      R) := by
    rw [← smallSingularChainHomotopyEquiv_hom R (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hU]
    infer_instance
  -- The rows of the double complex resolve the chains which are small for `U`.
  rw [cechTotalAugmentation_def]
  refine HomologicalComplex₂.quasiIso_totalAugmentation_of_rows_of_quasiIso
    (cechSmallAugmentation U R) (fun q ↦ by
      rw [← cechSmallAugmentationRowHomotopyEquiv_hom]
      infer_instance)
    (SSet.chainComplexMap (X.smallSingularSubcomplex (fun i ↦ (U i : Set X))).ι R) _ ?_
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom]
  -- The two sides are typed by the two defeq forms of the singular chains of `X`.
  exact (congrArg (· ≫ _) (Category.comp_id _)).trans
    (cechSmallAugmentation_f_zero_comp_chainComplexMap_ι U R)

end Abelian

end TauCeti
