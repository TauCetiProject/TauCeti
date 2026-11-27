/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Restriction.Basic
public import TauCeti.Algebra.Homology.LinearHomComplex.ExactPairing
public import TauCeti.Algebra.Homology.LinearHomComplex.Regrade
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Regrade

/-!
# The evaluation of a chain complex of modules and its regrading

Let `K` be a chain complex of modules over a commutative ring `R`, indexed by `ℤ` with
differential of degree `-1`, and let `K∨` be its dual complex (`ChainComplex.linearDual`), with
the linear forms on `K_(-p)` in degree `p` and the differential `d f = (-1)^(p + 1) f ∘ d_K`. This
file constructs the **evaluation** `ChainComplex.linearDualEvaluation K : K∨ ⊗ K ⟶ R[0]` in the
monoidal category of chain complexes, which sends `f ⊗ x` to `f(x)`, with no sign
(`ChainComplex.singleObjXSelf_hom_linearDualEvaluation_f_apply`). With this sign convention for the
dual differential and the Koszul sign `(-1)^p` of the tensor differential on `ComplexShape.down ℤ`,
it is a morphism of complexes, as is the evaluation of cochain complexes
(`TauCeti.linearHomComplexEvaluation`). It is dinatural in `K`
(`ChainComplex.linearDualMap_whiskerRight_comp_linearDualEvaluation`).

**Evaluation and regrading.** For an integer `n`, the regrading `C^k = K_(n-k)` of `K`
(`ChainComplex.regradeEquivalence`) turns raw homological degrees into cochain degrees. Its dual
complex `C∨` is the regrading of `K∨` by `-n` (`ChainComplex.regradeLinearDualIso`), and the
tensor product of the regradings of `K∨` by `-n` and of `K` by `n` is the regrading of `K∨ ⊗ K` by
`-n + n` (`ChainComplex.regradeTensorIso`). Through these two comparisons, the regrading of the
evaluation of `K` is `(-1)^n` times the evaluation of `C`
(`ChainComplex.restrictionMap_linearDualEvaluation`). On a form `f` of cochain degree `k` and an
element `x` of `C^(-k) = K_(n+k)`, the comparison of duals contributes the sign `(-1)^(k n)` and
that of tensor products the sign `(-1)^(-n (n + k))`, and their product is `(-1)^n`. This is the
same global sign as for the chain-compatible bidual maps (`ChainComplex.restrictionMap_bidualHom`).

For the Floer complex `CF_*` of a symplectic manifold of dimension `2n`, regraded as
`C^k = CF_(n-k)`, this is the conversion of the pairing of generators with their duals between
the raw grading, in which the counts of moduli spaces are oriented, and the cochain grading, in
which the product has degree zero.

## Main definitions

* `ChainComplex.linearDualEvaluation`: the evaluation `K∨ ⊗ K ⟶ R[0]` of a chain complex.

## Main results

* `ChainComplex.singleObjXSelf_hom_linearDualEvaluation_f_apply`: the evaluation sends `f ⊗ x` to
  `f(x)`.
* `ChainComplex.linearDualMap_whiskerRight_comp_linearDualEvaluation`: dinaturality.
* `ChainComplex.restrictionMap_linearDualEvaluation`: the regrading of the evaluation of `K` by
  `n` is `(-1)^n` times the evaluation of its regrading.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on Hom complexes and
  their sign conventions.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape
open scoped TensorProduct

universe u

namespace ChainComplex

variable {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℤ)

section Evaluation

/-- The component of the evaluation on the summand `K∨_p ⊗ K_q` of `K∨ ⊗ K`, for `p + q = 0`:
`f ⊗ x ↦ f(x)`, reading `x ∈ K_q` in `K_(-p)`. -/
private def evaluationSummand (p q : ℤ) (h : p + q = 0) :
    (linearDual K).X p ⊗ K.X q ⟶ 𝟙_ (ModuleCat.{u} R) :=
  ModuleCat.ofHom (contractLeft R (K.X (-p)) ∘ₗ
    TensorProduct.map LinearMap.id (K.XIsoOfEq (show q = -p by omega)).hom.hom)

private theorem evaluationSummand_tmul (p q : ℤ) (h : p + q = 0) (f : (linearDual K).X p)
    (x : K.X q) :
    (evaluationSummand K p q h).hom (f ⊗ₜ x) = f ((K.XIsoOfEq (show q = -p by omega)).hom.hom x) :=
  (rfl)

/-- The component of the evaluation in degree `0`. -/
private def evaluationX :
    (HomologicalComplex.tensorObj (linearDual K) K).X 0 ⟶ 𝟙_ (ModuleCat.{u} R) :=
  mapBifunctorDesc fun p q h ↦ evaluationSummand K p q h

private theorem ιTensorObj_evaluationX (p q : ℤ) (h : p + q = 0) :
    ιTensorObj (linearDual K) K p q 0 h ≫ evaluationX K = evaluationSummand K p q h :=
  ι_mapBifunctorDesc _ _ _ _

/-- On a summand `K∨_p ⊗ K_q` of degree `1`, the two terms of the tensor differential evaluate to
`(-1)^(p + 1) f(d x)` and `(-1)^p f(d x)`, which cancel. -/
private theorem ιTensorObj_d_comp_evaluationX (p q : ℤ) (h : p + q = 1) :
    ιTensorObj (linearDual K) K p q 1 h ≫
      (HomologicalComplex.tensorObj (linearDual K) K).d 1 0 ≫ evaluationX K = 0 := by
  rw [← Category.assoc,
    ιTensorObj_d_of_rel (linearDual K) K h (show (down ℤ).Rel p (p - 1) by simp)
      (show (down ℤ).Rel q (q - 1) by simp) (show p - 1 + q = 0 by omega)]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, ιTensorObj_evaluationX,
    ε_down_ℤ]
  refine ModuleCat.MonoidalCategory.tensor_ext fun f x ↦ ?_
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_whiskerRight,
    ModuleCat.hom_whiskerLeft, CategoryTheory.zsmul_whiskerRight, ModuleCat.hom_zero,
    LinearMap.zero_apply]
  -- The terms of `K∨ ⊗ K` are the tensor products of the underlying modules of the terms, which
  -- `rTensor_tmul` and `lTensor_tmul` see only up to this unfolding.
  erw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  rw [map_zsmul, evaluationSummand_tmul, evaluationSummand_tmul, ModuleCat.hom_ofHom,
    LinearMap.dualMap_apply,
    ← LinearMap.comp_apply (K.d _ _).hom, ← ModuleCat.hom_comp, XIsoOfEq_hom_comp_d,
    ← LinearMap.comp_apply (XIsoOfEq K _).hom.hom, ← ModuleCat.hom_comp, d_comp_XIsoOfEq_hom,
    ← add_smul, Int.negOnePow_succ, Units.val_neg, neg_add_cancel, zero_smul]

private theorem d_comp_evaluationX :
    (HomologicalComplex.tensorObj (linearDual K) K).d 1 0 ≫ evaluationX K = 0 :=
  mapBifunctor.hom_ext fun p q h ↦ by
    rw [comp_zero]
    exact ιTensorObj_d_comp_evaluationX K p q h

/-- The **evaluation** `K∨ ⊗ K ⟶ R[0]` of a chain complex of `R`-modules and its dual complex.
It sends `f ⊗ x` to `f(x)`, with no sign
(`ChainComplex.singleObjXSelf_hom_linearDualEvaluation_f_apply`). -/
def linearDualEvaluation : linearDual K ⊗ K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℤ) :=
  mkHomToSingle (evaluationX K) fun i hi ↦ by
    obtain rfl : 0 + 1 = i := hi
    exact d_comp_evaluationX K

private theorem ιTensorObj_linearDualEvaluation_f (p q : ℤ) (h : p + q = 0) :
    ιTensorObj (linearDual K) K p q 0 h ≫ (linearDualEvaluation K).f 0 =
      evaluationSummand K p q h ≫ (singleObjXSelf (down ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv := by
  rw [linearDualEvaluation, mkHomToSingle_f, ← Category.assoc, ιTensorObj_evaluationX]

private theorem ιTensorObj_linearDualEvaluation_f_singleObjXIsoOfEq_hom (p q j : ℤ)
    (h : p + q = j) (hj : j = 0) :
    ιTensorObj (linearDual K) K p q j h ≫ (linearDualEvaluation K).f j ≫
        (singleObjXIsoOfEq (down ℤ) 0 (𝟙_ (ModuleCat.{u} R)) j hj).hom =
      evaluationSummand K p q (h.trans hj) := by
  have h₀ : ιTensorObj (linearDual K) K p q j h ≫ (linearDualEvaluation K).f j =
      evaluationSummand K p q (h.trans hj) ≫
        (singleObjXIsoOfEq (down ℤ) 0 (𝟙_ (ModuleCat.{u} R)) j hj).inv := by
    subst hj
    exact ιTensorObj_linearDualEvaluation_f K p q h
  rw [reassoc_of% h₀, Iso.inv_hom_id, Category.comp_id]

/-- **The value of the evaluation.** On the summand `K∨_p ⊗ K_q` of `K∨ ⊗ K` in degree `0`, the
evaluation sends `f ⊗ x` to `f(x)`, where `x ∈ K_q` is read in `K_(-p)` and the value in the
degree-`0` term `R` of the tensor unit. -/
@[simp]
theorem singleObjXSelf_hom_linearDualEvaluation_f_apply (p q : ℤ) (h : p + q = 0)
    (f : (linearDual K).X p) (x : K.X q) :
    (singleObjXSelf (down ℤ) 0 (𝟙_ (ModuleCat.{u} R))).hom.hom
        ((linearDualEvaluation K).f 0 ((ιTensorObj (linearDual K) K p q 0 h).hom (f ⊗ₜ x))) =
      f ((K.XIsoOfEq (show q = -p by omega)).hom.hom x) :=
  congrArg (fun g ↦ ModuleCat.Hom.hom g (f ⊗ₜ x))
    (ιTensorObj_linearDualEvaluation_f_singleObjXIsoOfEq_hom K p q 0 h rfl)

variable {K} in
/-- **Dinaturality of the evaluation.** For a morphism `φ : K ⟶ L` of chain complexes, evaluating
the transpose of a form `f ∈ L∨` on `x ∈ K` is evaluating `f` on `φ x`. -/
@[reassoc]
theorem linearDualMap_whiskerRight_comp_linearDualEvaluation
    {L : ChainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    linearDualMap φ ▷ K ≫ linearDualEvaluation K = linearDual L ◁ φ ≫ linearDualEvaluation L := by
  refine to_single_hom_ext (mapBifunctor.hom_ext fun p q h ↦ ?_)
  replace h : p + q = 0 := h
  -- `mapBifunctor.hom_ext` states the summand inclusions as `ιMapBifunctor`, of which
  -- `ιTensorObj` is the abbreviation for the tensor product of complexes.
  change ιTensorObj _ _ p q 0 h ≫ _ = ιTensorObj _ _ p q 0 h ≫ _
  rw [comp_f, comp_f, ι_whiskerRight_assoc, ι_whiskerLeft_assoc, ιTensorObj_linearDualEvaluation_f,
    ιTensorObj_linearDualEvaluation_f, ← Category.assoc, ← Category.assoc]
  congr 1
  refine ModuleCat.MonoidalCategory.tensor_ext fun f x ↦ ?_
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerLeft]
  -- As above, `rTensor_tmul` and `lTensor_tmul` see the terms of the tensor products only after
  -- unfolding them to tensor products of modules.
  erw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  rw [evaluationSummand_tmul, evaluationSummand_tmul, linearDualMap_f_apply,
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, XIsoOfEq_hom_naturality]

end Evaluation

section Regrade

variable (n : ℤ)

/-- The two signs of the regrading comparisons on a form of cochain degree `a` multiply to
`(-1)^n`. -/
private theorem negOnePow_mul_negOnePow_eq (a : ℤ) :
    ((-n * (n - -a)).negOnePow : ℤ) * ((a * n).negOnePow : ℤ) = (n.negOnePow : ℤ) := by
  rw [← Units.val_mul, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff, show -n * (n - -a) + a * n - n = -(n * (n + 1)) by ring]
  exact (Int.even_mul_succ_self n).neg

/-- The identification of the degree-`0` term of the unit complex with `R` is the identity on
elements. -/
private theorem singleObjXSelf_inv_apply (z : 𝟙_ (ModuleCat.{u} R)) :
    ConcreteCategory.hom (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv z = z := by
  simp only [singleObjXSelf, singleObjXIsoOfEq, eqToIso.inv]
  -- Both terms are `𝟙_ (ModuleCat R)`, up to unfolding `single`.
  erw [eqToHom_refl]
  rfl

/-- The comparison of the regrading of `K∨` with the dual of the regrading of `K`, on a form `g`
of cochain degree `a` and an element `y` of `C^(-a) = K_(n + a)`. -/
private theorem regradeLinearDualIso_hom_f_apply (a : ℤ)
    (g : (CochainComplex.linearDual R (K.restriction (embeddingUpIntDownIntSub n))).X a)
    (y : (K.restriction (embeddingUpIntDownIntSub n)).X (-a)) :
    (show Module.Dual R (K.X (-(-n - a))) from ((K.regradeLinearDualIso n).hom.f a).hom g)
        ((K.XIsoOfEq (show n - -a = -(-n - a) by omega)).hom.hom y) =
      (a * n).negOnePow • CochainComplex.linearDualXEquiv _ (neg_add_cancel a) g y := by
  have hg := restrictionXIso_hom_regradeLinearDualIso_hom_f_apply K n a g
    ((K.XIsoOfEq (show n - -a = -(-n - a) by omega)).hom.hom y)
  have hy : (K.restrictionXIso (embeddingUpIntDownIntSub n)
      (show n - -a = -(-n - a) by omega)).inv.hom
        ((K.XIsoOfEq (show n - -a = -(-n - a) by omega)).hom.hom y) = y := by
    simp only [restrictionXIso, XIsoOfEq, eqToIso.inv, eqToIso.hom]
    -- The two transports compose to the transport along `n - -a = n - -a`.
    erw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eqToHom_trans, eqToHom_refl]
    rfl
  have hα : ∀ z : ((linearDual K).restriction (embeddingUpIntDownIntSub (-n))).X a,
      ((linearDual K).restrictionXIso (embeddingUpIntDownIntSub (-n)) (i := a) (i' := -n - a)
        rfl).hom.hom z = z := by
    intro z
    simp only [restrictionXIso, eqToIso.hom]
    -- The term of degree `a` of the restriction is the term of degree `-n - a` of `K∨`.
    erw [eqToHom_refl]
    rfl
  rwa [hy, hα] at hg

/-- On the summand `C∨^a ⊗ C^(-a)` of the tensor product of the regradings, the comparison of
tensor products followed by the evaluation of `K` is the evaluation summand with the sign
`(-1)^(-n (n + a))`. -/
private theorem regradeTensorSummand_comp_linearDualEvaluation_f (a : ℤ) (h : a + -a = 0) :
    regradeTensorSummand (-n) n (linearDual K) K a (-a) 0 h ≫
        (linearDualEvaluation K).f ((embeddingUpIntDownIntSub (-n + n)).f 0) ≫
          (singleObjXIsoOfEq (down ℤ) 0 (𝟙_ (ModuleCat.{u} R))
            ((embeddingUpIntDownIntSub (-n + n)).f 0) (by simp)).hom =
      ((-n * (n - -a)).negOnePow : ℤ) • evaluationSummand K (-n - a) (n - -a) (by omega) := by
  rw [regradeTensorSummand_def]
  refine (Linear.units_smul_comp _ _ _).trans ?_
  rw [Units.smul_def]
  congr 1
  exact ιTensorObj_linearDualEvaluation_f_singleObjXIsoOfEq_hom K _ _ _ _ (by simp)

/-- The evaluation of the regrading of `K` is `(-1)^n` times the regrading of the evaluation of
`K`, read through the comparisons of duals and of tensor products. -/
private theorem regradeLinearDualIso_hom_whiskerRight_comp_regradeTensorHom_comp :
    (K.regradeLinearDualIso n).hom ▷ (K.restriction (embeddingUpIntDownIntSub n)) ≫
        regradeTensorHom (-n) n (linearDual K) K ≫
          restrictionMap (linearDualEvaluation K) (embeddingUpIntDownIntSub (-n + n)) ≫
            (restrictionSingleIso (embeddingUpIntDownIntSub (-n + n)) (𝟙_ (ModuleCat.{u} R)) 0 0
              (by simp)).hom =
      n.negOnePow •
        TauCeti.linearHomComplexEvaluation R (K.restriction (embeddingUpIntDownIntSub n)) := by
  refine to_single_hom_ext (mapBifunctor.hom_ext fun a b h ↦ ?_)
  replace h : a + b = 0 := h
  obtain rfl : b = -a := by omega
  -- `mapBifunctor.hom_ext` states the summand inclusions as `ιMapBifunctor`, of which
  -- `ιTensorObj` is the abbreviation for the tensor product of complexes.
  change ιTensorObj _ _ a (-a) 0 h ≫ _ = ιTensorObj _ _ a (-a) 0 h ≫ _
  rw [← cancel_mono (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).hom, comp_f, comp_f, comp_f,
    ι_whiskerRight_assoc, ι_regradeTensorHom_f_assoc, restrictionMap_f,
    restrictionSingleIso_hom_f, units_smul_f_apply]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [regradeTensorSummand_comp_linearDualEvaluation_f K n a h, Linear.units_smul_comp]
  refine ModuleCat.MonoidalCategory.tensor_ext fun g y ↦ ?_
  -- The terms of the regraded complexes are those of `K` and `K∨` up to unfolding
  -- `HomologicalComplex.restriction`, which the rewrites below see only through `erw`.
  erw [Preadditive.comp_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_whiskerRight, LinearMap.rTensor_tmul,
    evaluationSummand_tmul]
  erw [Preadditive.comp_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    TauCeti.linearHomComplexEvaluation_ιTensorObj_tmul]
  rw [regradeLinearDualIso_hom_f_apply, Units.smul_def (a * n).negOnePow, smul_smul,
    negOnePow_mul_negOnePow_eq]
  congr 1
  rw [singleObjXSelf_inv_apply, CochainComplex.linearDualXEquiv_apply,
    TauCeti.cochainToTensorUnitLinearEquiv_apply]

/-- **The evaluations of the two gradings differ by `(-1)^n`.** The regrading by `-n + n` of the
evaluation `K∨ ⊗ K ⟶ R[0]` of a chain complex `K` is `(-1)^n` times the evaluation of the
regrading `C^k = K_(n-k)` of `K`, read through the comparison `ChainComplex.regradeTensorIso` of
the tensor product of the regradings of `K∨` by `-n` and of `K` by `n` with the regrading of
`K∨ ⊗ K`, and the comparison `ChainComplex.regradeLinearDualIso` of the regrading of `K∨` by `-n`
with the dual of `C`. -/
theorem restrictionMap_linearDualEvaluation :
    restrictionMap (linearDualEvaluation K) (embeddingUpIntDownIntSub (-n + n)) =
      (regradeTensorIso (-n) n (linearDual K) K).inv ≫
        (K.regradeLinearDualIso n).inv ▷ (K.restriction (embeddingUpIntDownIntSub n)) ≫
          (n.negOnePow •
            TauCeti.linearHomComplexEvaluation R (K.restriction (embeddingUpIntDownIntSub n))) ≫
              (restrictionSingleIso (embeddingUpIntDownIntSub (-n + n)) (𝟙_ (ModuleCat.{u} R)) 0 0
                (by simp)).inv := by
  rw [← regradeLinearDualIso_hom_whiskerRight_comp_regradeTensorHom_comp, ← regradeTensorIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc]

end Regrade

end ChainComplex
