/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.CategoryTheory.CStar.Functor

/-!
# Complex Hilbert spaces as a C⋆-category

`TauCeti.HilbertCat ℂ`, whose objects are complex Hilbert spaces and whose Hom spaces are bounded
`ℂ`-linear maps `X →L[ℂ] Y` with the operator norm and Hilbert-space adjoint, forms the archetype
of a complex C⋆-category (`TauCeti.HilbertCat.instCStarCategory`).

The Hom-space Banach instances exported by `CStarCategory` coincide definitionally with
`HilbertCat`'s native continuous-linear-map instances, and each endomorphism C⋆-algebra `End X` is
canonically `⋆`-isomorphic to `X →L[ℂ] X` (`TauCeti.HilbertCat.endStarAlgEquiv`), identifying the
abstract C⋆-algebraic spectral order on `End X` with Mathlib's Loewner inner-product order
(`TauCeti.HilbertCat.end_le_iff`).

Restricting along `TauCeti.HilbertCat.isFiniteDimensional` equips the full subcategory
`TauCeti.FinHilbertCat ℂ` of finite-dimensional complex Hilbert spaces with its induced
`CStarCategory` structure and isometric inclusion functor.

Finally, concrete operators on `EuclideanSpace ℂ (Fin 2)` witness the sharpness of the C⋆-category
axioms and hypotheses:
* zero objects in `HilbertCat 𝕜` are precisely the subsingleton Hilbert spaces, witnessing both
  branches `‖𝟙 X‖ = 0` (`PUnit`) and `‖𝟙 X‖ = 1` (`ℂ`) of the identity-norm dichotomy;
* on `EuclideanSpace ℂ (Fin 2)`, the Frobenius (Hilbert–Schmidt) norm fails the C⋆-identity
  (`TauCeti.HilbertCat.exists_frobenius_comp_dagger_self_ne_sq`), illustrating uniqueness of the
  C⋆-category norm;
* an oblique rank-one idempotent on `EuclideanSpace ℂ (Fin 2)` has norm `√2 > 1` and non-adjoint
  retraction (`TauCeti.HilbertCat.exists_idempotent_norm_gt_one`), showing that `dagger p = p` is
  essential for idempotents to be contractive.
-/

public section

noncomputable section

open CategoryTheory InnerProductSpace
open scoped ComplexInnerProductSpace

universe v

namespace TauCeti

namespace HilbertCat

/-! ### `CStarCategory` instance on `HilbertCat ℂ` and spectral order on `End X` -/

/-- Complex Hilbert spaces and bounded `ℂ`-linear maps form a complex C⋆-category under the
operator norm and Hilbert-space adjoint. -/
instance instCStarCategory : CStarCategory (HilbertCat.{0, v} ℂ) where
  norm_comp_le := HilbertCat.norm_comp_le
  norm_comp_dagger_self := HilbertCat.norm_self_comp_dagger
  exists_comp_dagger_eq {X Y} f := by
    have hpos : (0 : X →L[ℂ] X) ≤ (ContinuousLinearMap.adjoint f).comp f := by
      simpa using
        (ContinuousLinearMap.norm_map_le_norm_map_iff_le (0 : X →L[ℂ] Y) f).mp (by simp)
    let h : X →L[ℂ] X := CFC.sqrt ((ContinuousLinearMap.adjoint f).comp f)
    have hh0 : 0 ≤ h := CFC.sqrt_nonneg _
    have hhsa : ContinuousLinearMap.adjoint h = h := hh0.isSelfAdjoint.star_eq
    have hhsq : h * h = (ContinuousLinearMap.adjoint f).comp f := CFC.sqrt_mul_sqrt_self _ hpos
    refine ⟨h, ?_⟩
    rw [comp_eq_comp, comp_eq_comp, dagger_eq_adjoint, dagger_eq_adjoint, hhsa]
    exact hhsq.symm

-- Compile-time check that `CStarCategory`'s Hom-space instances agree definitionally with
-- `HilbertCat`'s native continuous-linear-map instances, and that `FinHilbertCat ℂ` inherits
-- `CStarCategory` automatically as a full subcategory.
example (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.homNormedAddCommGroup X Y =
      inferInstanceAs (NormedAddCommGroup (X →L[ℂ] Y)) := rfl

example (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.homNormedSpace X Y =
      inferInstanceAs (NormedSpace ℂ (X →L[ℂ] Y)) := rfl

example : CStarCategory (FinHilbertCat.{0, v} ℂ) := inferInstance

/-- On `HilbertCat ℂ`, the C⋆-algebraic spectral order on `End X` coincides with Mathlib's Loewner
order on `X →L[ℂ] X`. -/
@[simp] theorem end_le_iff {X : HilbertCat.{0, v} ℂ} {a b : End X} :
    a ≤ b ↔ ConcreteCategory.hom a.asHom ≤ ConcreteCategory.hom b.asHom := by
  simpa only [endStarAlgEquiv_apply] using (map_le_map_iff (endStarAlgEquiv X)).symm

/-- Nonnegativity in `End X` for `X : HilbertCat ℂ` coincides with `ContinuousLinearMap.IsPositive`
on `X →L[ℂ] X`. -/
theorem end_nonneg_iff {X : HilbertCat.{0, v} ℂ} {a : End X} :
    0 ≤ a ↔ (ConcreteCategory.hom a.asHom).IsPositive := by
  rw [end_le_iff, End.zero_asHom, hom_zero, ContinuousLinearMap.nonneg_iff_isPositive]

/-! ### Identity-norm dichotomy on `HilbertCat ℂ` -/

/-- On a subsingleton complex Hilbert space (such as `PUnit`), the categorical identity arrow has
norm `0`. -/
@[simp] theorem norm_id_of_subsingleton (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [Subsingleton E] :
    ‖𝟙 (of ℂ E)‖ = 0 :=
  (isZero_of_subsingleton E).norm_id_eq_zero

/-- On a nontrivial complex Hilbert space (such as `ℂ`), the categorical identity arrow has
norm `1`. -/
@[simp] theorem norm_id_of_nontrivial (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E] :
    ‖𝟙 (of ℂ E)‖ = 1 :=
  (not_isZero_iff_norm_id_eq_one (of ℂ E)).mp (not_isZero_of_nontrivial E)

/-! ### Sharpness witnesses on `EuclideanSpace ℂ (Fin 2)` -/

private abbrev H₂ := EuclideanSpace ℂ (Fin 2)

private abbrev eBasis : OrthonormalBasis (Fin 2) ℂ H₂ := EuclideanSpace.basisFun (Fin 2) ℂ

private theorem eBasis_inner_self (i : Fin 2) : ⟪eBasis i, eBasis i⟫ = 1 := by
  simp [inner_self_eq_norm_sq_to_K]

private theorem eBasis_inner_zero_one : ⟪eBasis 0, eBasis 1⟫ = 0 :=
  eBasis.orthonormal.2 (by decide : (0 : Fin 2) ≠ 1)

private theorem eBasis_inner_one_zero : ⟪eBasis 1, eBasis 0⟫ = 0 :=
  eBasis.orthonormal.2 (by decide : (1 : Fin 2) ≠ 0)

private theorem norm_eBasis_zero_add_one : ‖eBasis 0 + eBasis 1‖ = √2 := by
  have hsq : ‖eBasis 0 + eBasis 1‖ ^ 2 = (√2) ^ 2 := by
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ eBasis_inner_zero_one,
      eBasis.norm_eq_one 0, eBasis.norm_eq_one 1, Real.sq_sqrt (by norm_num)]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mp hsq

private def obliqueIdem : H₂ →L[ℂ] H₂ := rankOne ℂ (eBasis 0) (eBasis 0 + eBasis 1)
private def obliqueIncl : ℂ →L[ℂ] H₂ := ContinuousLinearMap.toSpanSingleton ℂ (eBasis 0)
private def obliqueRet : H₂ →L[ℂ] ℂ := innerSL ℂ (eBasis 0 + eBasis 1)

private theorem dagger_obliqueIdem_ne : dagger (ofHom obliqueIdem) ≠ ofHom obliqueIdem := by
  intro h
  have happ : ‖ContinuousLinearMap.adjoint obliqueIdem (eBasis 1)‖ = ‖obliqueIdem (eBasis 1)‖ :=
    congrArg (fun T : H₂ →L[ℂ] H₂ => ‖T (eBasis 1)‖) h
  have he1 : obliqueIdem (eBasis 1) = eBasis 0 := by
    rw [obliqueIdem, rankOne_apply, inner_add_left, eBasis_inner_zero_one, eBasis_inner_self,
      zero_add, one_smul]
  have hadj : ContinuousLinearMap.adjoint obliqueIdem (eBasis 1) = 0 := by
    rw [obliqueIdem, adjoint_rankOne, rankOne_apply, eBasis_inner_zero_one, zero_smul]
  rw [hadj, he1, norm_zero, eBasis.norm_eq_one 0] at happ
  exact zero_ne_one happ

private theorem obliqueRet_ne_dagger_obliqueIncl :
    ofHom obliqueRet ≠ dagger (ofHom obliqueIncl) := by
  intro h
  have happ : obliqueRet (eBasis 1) = ContinuousLinearMap.adjoint obliqueIncl (eBasis 1) :=
    congrArg (fun T : H₂ →L[ℂ] ℂ => T (eBasis 1)) h
  have hr1 : obliqueRet (eBasis 1) = 1 := by
    rw [obliqueRet, innerSL_apply_apply, inner_add_left, eBasis_inner_zero_one, eBasis_inner_self,
      zero_add]
  have hadj : ContinuousLinearMap.adjoint obliqueIncl (eBasis 1) = 0 :=
    ext_inner_left ℂ fun w => by
      rw [ContinuousLinearMap.adjoint_inner_right, obliqueIncl,
        ContinuousLinearMap.toSpanSingleton_apply, inner_smul_left, eBasis_inner_zero_one,
        mul_zero, inner_zero_right]
  rw [hr1, hadj] at happ
  exact one_ne_zero happ

/-- Self-adjointness (`dagger p = p`) is essential for idempotents in a C⋆-category to be
contractions: on `EuclideanSpace ℂ (Fin 2)` there exists an oblique rank-one idempotent morphism
`e = r ≫ ι` factoring through `of ℂ ℂ` (`ι ≫ r = 𝟙 (of ℂ ℂ)`) such that `e ≫ e = e`,
`dagger e ≠ e`, `r ≠ dagger ι`, and `‖e‖ = √2 > 1`. -/
theorem exists_idempotent_norm_gt_one :
    ∃ (e : of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ of ℂ (EuclideanSpace ℂ (Fin 2)))
      (ι : of ℂ ℂ ⟶ of ℂ (EuclideanSpace ℂ (Fin 2)))
      (r : of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ of ℂ ℂ),
      e = r ≫ ι ∧ ι ≫ r = 𝟙 (of ℂ ℂ) ∧ e ≫ e = e ∧ dagger e ≠ e ∧ r ≠ dagger ι ∧
        ‖e‖ = √2 ∧ ‖r‖ = √2 ∧ 1 < ‖e‖ := by
  have hfac : ofHom obliqueIdem = ofHom obliqueRet ≫ ofHom obliqueIncl := by
    rw [← ofHom_comp]
    exact congrArg ofHom (rankOne_def' (eBasis 0) (eBasis 0 + eBasis 1))
  have hret : ofHom obliqueIncl ≫ ofHom obliqueRet = 𝟙 (of ℂ ℂ) := by
    rw [← ofHom_comp, ← ofHom_id]
    refine congrArg ofHom (ContinuousLinearMap.ext fun z => ?_)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, obliqueIncl, obliqueRet,
      ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, inner_smul_right,
      inner_add_left, eBasis_inner_self, eBasis_inner_one_zero, add_zero, mul_one]
  have hidem : ofHom obliqueIdem ≫ ofHom obliqueIdem = ofHom obliqueIdem := by
    rw [← ofHom_comp]
    congr 1
    rw [obliqueIdem, rankOne_comp_rankOne, inner_add_left, eBasis_inner_self,
      eBasis_inner_one_zero, add_zero, one_smul]
  have he_norm : ‖ofHom obliqueIdem‖ = √2 := by
    rw [norm_ofHom, obliqueIdem, norm_rankOne, eBasis.norm_eq_one 0, one_mul,
      norm_eBasis_zero_add_one]
  have hr_norm : ‖ofHom obliqueRet‖ = √2 := by
    rw [norm_ofHom, obliqueRet, innerSL_apply_norm, norm_eBasis_zero_add_one]
  refine ⟨ofHom obliqueIdem, ofHom obliqueIncl, ofHom obliqueRet, hfac, hret, hidem,
    dagger_obliqueIdem_ne, obliqueRet_ne_dagger_obliqueIncl, he_norm, hr_norm, ?_⟩
  rw [he_norm]
  exact Real.lt_sqrt_of_sq_lt (by norm_num)

private def diagTwoOne : H₂ →L[ℂ] H₂ :=
  (2 : ℂ) • rankOne ℂ (eBasis 0) (eBasis 0) + rankOne ℂ (eBasis 1) (eBasis 1)

private theorem diagTwoOne_zero : diagTwoOne (eBasis 0) = (2 : ℂ) • eBasis 0 := by
  simp only [diagTwoOne, _root_.add_apply, _root_.smul_apply, rankOne_apply,
    eBasis_inner_self, eBasis_inner_one_zero, one_smul, zero_smul, add_zero]

private theorem diagTwoOne_one : diagTwoOne (eBasis 1) = eBasis 1 := by
  simp only [diagTwoOne, _root_.add_apply, _root_.smul_apply, rankOne_apply,
    eBasis_inner_zero_one, eBasis_inner_self, one_smul, zero_smul, smul_zero, zero_add]

private theorem adjoint_diagTwoOne : ContinuousLinearMap.adjoint diagTwoOne = diagTwoOne := by
  simp only [diagTwoOne, map_add, map_smulₛₗ, adjoint_rankOne, starRingEnd_apply, star_ofNat]

private theorem norm_diagTwoOne : ‖diagTwoOne‖ = 2 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow,
      ← eBasis.sum_sq_norm_inner_right (diagTwoOne x), ← eBasis.sum_sq_norm_inner_right x,
      Fin.sum_univ_two, Fin.sum_univ_two]
    have hi0 : ⟪eBasis 0, diagTwoOne x⟫ = 2 * ⟪eBasis 0, x⟫ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_diagTwoOne, diagTwoOne_zero,
        inner_smul_left, starRingEnd_apply, star_ofNat]
    have hi1 : ⟪eBasis 1, diagTwoOne x⟫ = ⟪eBasis 1, x⟫ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_diagTwoOne, diagTwoOne_one]
    rw [hi0, hi1, norm_mul, Complex.norm_ofNat]
    nlinarith [sq_nonneg ‖⟪eBasis 1, x⟫‖]
  · have hle := diagTwoOne.le_opNorm (eBasis 0)
    rw [diagTwoOne_zero, norm_smul, Complex.norm_ofNat, eBasis.norm_eq_one 0,
      mul_one, mul_one] at hle
    exact hle

/-- The Hilbert–Schmidt (Frobenius) norm on finite-dimensional Hom spaces fails the C⋆-identity:
on `EuclideanSpace ℂ (Fin 2)` the diagonal operator `diag(2, 1)` satisfies `‖f‖ = 2` and
`‖f ≫ dagger f‖ = 4 = ‖f‖ ^ 2` in the operator norm, whereas its Frobenius norm satisfies
`‖f‖_F ^ 2 = 5` and `‖f ≫ dagger f‖_F = √17 ≠ 5`. -/
theorem exists_frobenius_comp_dagger_self_ne_sq :
    ∃ f : of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ of ℂ (EuclideanSpace ℂ (Fin 2)),
      ‖f‖ = 2 ∧ ‖f ≫ dagger f‖ = 4 ∧
        UnitarilyInvariantSeminorm.frobenius ℂ _ _ f.toLinearMap ^ 2 = 5 ∧
        UnitarilyInvariantSeminorm.frobenius ℂ _ _ (f ≫ dagger f).toLinearMap = √17 ∧
        UnitarilyInvariantSeminorm.frobenius ℂ _ _ (f ≫ dagger f).toLinearMap ≠
          UnitarilyInvariantSeminorm.frobenius ℂ _ _ f.toLinearMap ^ 2 := by
  have hf_norm : ‖ofHom diagTwoOne‖ = 2 := by rw [norm_ofHom, norm_diagTwoOne]
  have hff_norm : ‖ofHom diagTwoOne ≫ dagger (ofHom diagTwoOne)‖ = 4 := by
    rw [norm_comp_dagger_self, hf_norm]
    norm_num
  have hcomp : ofHom diagTwoOne ≫ dagger (ofHom diagTwoOne) =
      ofHom (diagTwoOne.comp diagTwoOne) := by
    rw [dagger_ofHom, adjoint_diagTwoOne, ← ofHom_comp]
  have hf_frob :
      UnitarilyInvariantSeminorm.frobenius ℂ _ _ (ofHom diagTwoOne).toLinearMap ^ 2 = 5 := by
    rw [UnitarilyInvariantSeminorm.sq_frobenius_apply eBasis, Fin.sum_univ_two]
    simp only [ofHom_eq, ContinuousLinearMap.coe_coe, diagTwoOne_zero, diagTwoOne_one, norm_smul,
      Complex.norm_ofNat, eBasis.norm_eq_one 0, eBasis.norm_eq_one 1]
    norm_num
  have hff_frob :
      UnitarilyInvariantSeminorm.frobenius ℂ _ _
        (ofHom diagTwoOne ≫ dagger (ofHom diagTwoOne)).toLinearMap = √17 := by
    rw [hcomp, UnitarilyInvariantSeminorm.frobenius_apply eBasis, Fin.sum_univ_two]
    congr 1
    simp only [ofHom_eq, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      diagTwoOne_zero, diagTwoOne_one, map_smul, norm_smul, Complex.norm_ofNat,
      eBasis.norm_eq_one 0, eBasis.norm_eq_one 1]
    norm_num
  refine ⟨ofHom diagTwoOne, hf_norm, hff_norm, hf_frob, hff_frob, ?_⟩
  rw [hff_frob, hf_frob]
  intro h
  have hsq := congrArg (· ^ 2) h
  rw [Real.sq_sqrt (by norm_num)] at hsq
  norm_num at hsq

end HilbertCat

end TauCeti
