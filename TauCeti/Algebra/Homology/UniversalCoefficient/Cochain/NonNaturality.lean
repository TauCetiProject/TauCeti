/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
import Mathlib.Algebra.Homology.Double
import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic

/-!
# Non-naturality of the cochain universal coefficient splitting

Although `CochainComplex.linearHomComplexSingleKroneckerSection` provides a splitting of the
cochain universal coefficient sequence that is natural in the coefficient object `Y`, no splitting
can be chosen naturally in the cochain complex `K`, even when restricted to strictly bounded finite
free `ℤ`-cochain complexes with dualizing target `ℤ`.

## Main results

* `TauCeti.not_exists_natural_section_linearHomComplexSingleKronecker`: the chain map from
  `0 ⟶ ℤ xrightarrow{×2} ℤ ⟶ 0` (in degrees `0` and `1`) to `ℤ[0]` rules out any simultaneous
  natural additive section of `CochainComplex.linearHomComplexSingleKronecker` in degree `0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Example 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex

namespace TauCeti

section NonNaturality

private abbrev mulTwoHom : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private lemma up_rel_zero_one : (ComplexShape.up ℤ).Rel (0 : ℤ) 1 := by simp

/-- The two-term bounded finite free `ℤ`-cochain complex `0 ⟶ ℤ xrightarrow{×2} ℤ ⟶ 0` in degrees
`0` and `1` witnessing that the universal coefficient splitting cannot be chosen naturally. -/
private abbrev mulTwoCochainComplex : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  HomologicalComplex.double mulTwoHom up_rel_zero_one

private instance (i : ℤ) : Module.Free ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0
    exact Module.Free.of_equiv (doubleXIso₀ mulTwoHom up_rel_zero_one).symm.toLinearEquiv
  · by_cases hi1 : i = 1
    · subst hi1
      exact Module.Free.of_equiv
        (doubleXIso₁ mulTwoHom up_rel_zero_one (by decide)).symm.toLinearEquiv
    · have : Subsingleton (mulTwoCochainComplex.X i) :=
        ModuleCat.isZero_iff_subsingleton.1 (isZero_double_X mulTwoHom up_rel_zero_one i hi0 hi1)
      infer_instance

private instance (i : ℤ) : Module.Finite ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0
    exact Module.Finite.equiv (doubleXIso₀ mulTwoHom up_rel_zero_one).symm.toLinearEquiv
  · by_cases hi1 : i = 1
    · subst hi1
      exact Module.Finite.equiv
        (doubleXIso₁ mulTwoHom up_rel_zero_one (by decide)).symm.toLinearEquiv
    · have : Subsingleton (mulTwoCochainComplex.X i) :=
        ModuleCat.isZero_iff_subsingleton.1 (isZero_double_X mulTwoHom up_rel_zero_one i hi0 hi1)
      infer_instance

private instance : mulTwoCochainComplex.IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦
    isZero_double_X mulTwoHom up_rel_zero_one i (by omega) (by omega)

private instance : mulTwoCochainComplex.IsStrictlyLE 1 :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦
    isZero_double_X mulTwoHom up_rel_zero_one i (by omega) (by omega)

private lemma isZero_homology_zero_mulTwoCochainComplex :
    IsZero (mulTwoCochainComplex.homology 0) := by
  have hmul2 : Mono mulTwoHom :=
    (ModuleCat.mono_iff_injective _).2 fun a b hab ↦ by
      have h : (2 : ℤ) * (a : ℤ) = (2 : ℤ) * (b : ℤ) := by
        simpa only [mulTwoHom, ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearMap.id_apply,
          smul_eq_mul] using hab
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h
  have hmono : Mono (mulTwoCochainComplex.d 0 1) := by
    rw [double_d mulTwoHom up_rel_zero_one (by decide)]
    exact mono_comp _ _
  have hex : mulTwoCochainComplex.ExactAt 0 :=
    (HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)).2
      (((mulTwoCochainComplex.sc' (-1) 0 1).exact_iff_mono
        (double_d_eq_zero₀ mulTwoHom up_rel_zero_one (-1) 0 (by decide))).2 hmono)
  exact hex.isZero_homology

private lemma not_exists_leftInverse_mulTwoCochainComplex_d :
    ¬ ∃ g : mulTwoCochainComplex.X 1 ⟶ ModuleCat.of ℤ ℤ,
      mulTwoCochainComplex.d 0 1 ≫ g = (doubleXIso₀ mulTwoHom up_rel_zero_one).hom := by
  rintro ⟨g, hg⟩
  rw [double_d mulTwoHom up_rel_zero_one (by decide), Category.assoc, Category.assoc] at hg
  let f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ :=
    (doubleXIso₁ mulTwoHom up_rel_zero_one (by decide)).inv ≫ g
  have hg' : mulTwoHom ≫ f = 𝟙 (ModuleCat.of ℤ ℤ) := by
    rw [← cancel_epi (doubleXIso₀ mulTwoHom up_rel_zero_one).hom, Category.comp_id]
    exact hg
  have h1 : (2 : ℤ) * f.hom (1 : ℤ) = (1 : ℤ) := by
    have h := ConcreteCategory.congr_hom hg' (1 : ℤ)
    rw [ModuleCat.comp_apply, ModuleCat.ofHom_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ModuleCat.id_apply] at h
    simpa only [← smul_eq_mul, ← map_zsmul] using h
  omega

private abbrev singleIntComplex : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)

private instance (i : ℤ) : Module.Free ℤ (singleIntComplex.X i) := by
  by_cases hi : i = 0
  · subst hi
    exact Module.Free.of_equiv (singleObjXSelf (ComplexShape.up ℤ) 0 _).symm.toLinearEquiv
  · have : Subsingleton (singleIntComplex.X i) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi)
    infer_instance

private instance (i : ℤ) : Module.Finite ℤ (singleIntComplex.X i) := by
  by_cases hi : i = 0
  · subst hi
    exact Module.Finite.equiv (singleObjXSelf (ComplexShape.up ℤ) 0 _).symm.toLinearEquiv
  · have : Subsingleton (singleIntComplex.X i) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi)
    infer_instance

private instance : singleIntComplex.IsStrictlyLE 1 :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦
    isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i (by omega)

/-- Any degree-0 cocycle of `linearHomComplex ℤ ℤ[0] ℤ[0]` whose Kronecker evaluation is the
canonical isomorphism `H⁰(ℤ[0]) ≅ ℤ` has underlying degree-0 morphism equal to
`singleObjXSelf.hom`. -/
private lemma toSingleLinearEquiv_singleIntComplex_of_kronecker
    (cyc : (linearHomComplex ℤ singleIntComplex singleIntComplex).cycles 0)
    (hcyc : linearHomComplexSingleKronecker ℤ singleIntComplex (ModuleCat.of ℤ ℤ) 0
        (((linearHomComplex ℤ singleIntComplex singleIntComplex).homologyπ 0).hom cyc) =
      (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom) :
    Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)
        (((linearHomComplex ℤ singleIntComplex singleIntComplex).iCycles 0).hom cyc) =
      (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom := by
  have hkr : singleIntComplex.homologyπ 0 ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom =
      singleIntComplex.iCycles 0 ≫
        Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)
          (((linearHomComplex ℤ singleIntComplex singleIntComplex).iCycles 0).hom cyc) := by
    rw [← hcyc]
    exact homologyπ_linearHomComplexSingleKronecker (k := ℤ) (K := singleIntComplex)
      (Y := ModuleCat.of ℤ ℤ) 0 cyc
  have hkr' := congrArg
    ((singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).inv ≫ ·) hkr
  rw [homologyπ_singleObjHomologySelfIso_hom, Iso.inv_hom_id,
    singleObjCyclesSelfIso_inv_iCycles_assoc] at hkr'
  simpa using congrArg
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom ≫ ·) hkr'.symm

/-- **No simultaneous natural splitting of the cochain universal coefficient sequence exists.**
Even among strictly bounded finite free `ℤ`-cochain complexes with dualizing target `ℤ`, there is
no family of additive sections `s K : (H⁰(K) ⟶ ℤ) →+ H⁰(Hom(K, ℤ[0]))` of
`linearHomComplexSingleKronecker` in degree `0` that commutes with chain maps. -/
theorem not_exists_natural_section_linearHomComplexSingleKronecker :
    ¬ ∃ s : ∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
        [∀ i, Module.Free ℤ (K.X i)] [∀ i, Module.Finite ℤ (K.X i)]
        [K.IsStrictlyGE 0] [K.IsStrictlyLE 1],
        (K.homology 0 ⟶ ModuleCat.of ℤ ℤ) →+
          (linearHomComplex ℤ K ((singleFunctor (ModuleCat.{0} ℤ) 0).obj
            (ModuleCat.of ℤ ℤ))).homology 0,
      (∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ i, Module.Free ℤ (K.X i)] [∀ i, Module.Finite ℤ (K.X i)]
          [K.IsStrictlyGE 0] [K.IsStrictlyLE 1] (g : K.homology 0 ⟶ ModuleCat.of ℤ ℤ),
        linearHomComplexSingleKronecker ℤ K (ModuleCat.of ℤ ℤ) 0 (s K g) = g) ∧
      (∀ (K₁ K₂ : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ i, Module.Free ℤ (K₁.X i)] [∀ i, Module.Finite ℤ (K₁.X i)]
          [K₁.IsStrictlyGE 0] [K₁.IsStrictlyLE 1]
          [∀ i, Module.Free ℤ (K₂.X i)] [∀ i, Module.Finite ℤ (K₂.X i)]
          [K₂.IsStrictlyGE 0] [K₂.IsStrictlyLE 1]
          (φ : K₁ ⟶ K₂) (g : K₂.homology 0 ⟶ ModuleCat.of ℤ ℤ),
        (homologyMap (linearHomComplexPrecomp ℤ φ
          ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ))) 0).hom (s K₂ g) =
            s K₁ (homologyMap φ 0 ≫ g)) := by
  rintro ⟨s, hs_sec, hs_nat⟩
  -- Map `mulTwoCochainComplex` to `ℤ[0]` by the identity in degree `0`.
  let φ : mulTwoCochainComplex ⟶ singleIntComplex :=
    HomologicalComplex.mkHomToSingle (doubleXIso₀ mulTwoHom up_rel_zero_one).hom (fun i hi ↦
      (mulTwoCochainComplex.isZero_of_isStrictlyGE 0 i
        (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _)
  let g₀ : singleIntComplex.homology 0 ⟶ ModuleCat.of ℤ ℤ :=
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom
  let L₁ := linearHomComplex ℤ mulTwoCochainComplex singleIntComplex
  let L₂ := linearHomComplex ℤ singleIntComplex singleIntComplex
  -- Lift `s ℤ[0] g₀` to a degree-0 cocycle `cyc₂` of `Hom(ℤ[0], ℤ[0])`.
  obtain ⟨cyc₂, hcyc₂⟩ :=
    HomologicalComplex.moduleCat_homologyπ_surjective L₂ 0 (s singleIntComplex g₀)
  have hf₂ := toSingleLinearEquiv_singleIntComplex_of_kronecker cyc₂
    (hcyc₂.symm ▸ hs_sec singleIntComplex g₀)
  -- Pull `cyc₂` back along `φ`; naturality and `H⁰(K₁) = 0` force it to be a coboundary.
  let cyc₁ : L₁.cycles 0 := cyclesMap (linearHomComplexPrecomp ℤ φ singleIntComplex) 0 cyc₂
  have hcyc₁ : (L₁.homologyπ 0).hom cyc₁ = 0 := by
    rw [← HomologicalComplex.moduleCat_homologyMap_homologyπ, hcyc₂, hs_nat,
      isZero_homology_zero_mulTwoCochainComplex.eq_of_src (homologyMap φ 0 ≫ g₀) 0, map_zero]
  obtain ⟨y, hy⟩ := (L₁.moduleCat_homologyπ_eq_zero_iff (m := -1) (by simp) cyc₁).1 hcyc₁
  have hdy : (L₁.d (-1) 0).hom y =
      ((linearHomComplexPrecomp ℤ φ singleIntComplex).f 0).hom ((L₂.iCycles 0).hom cyc₂) := by
    rw [← HomologicalComplex.moduleCat_iCycles_toCycles_apply, hy,
      HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  let g : mulTwoCochainComplex.X 1 ⟶ ModuleCat.of ℤ ℤ :=
    Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel (-1)) y
  have hd_eq : mulTwoCochainComplex.d 0 1 ≫ g = (doubleXIso₀ mulTwoHom up_rel_zero_one).hom := by
    have hpre := congrArg (Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)) hdy
    have hd : Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0) ((L₁.d (-1) 0).hom y) =
        mulTwoCochainComplex.d 0 1 ≫ g := by
      simpa [g, L₁] using toSingleLinearEquiv_linearHomComplex_d_apply (k := ℤ)
        mulTwoCochainComplex (ModuleCat.of ℤ ℤ) (-1) y
    have hpre_eq : Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)
          (((linearHomComplexPrecomp ℤ φ singleIntComplex).f 0).hom ((L₂.iCycles 0).hom cyc₂)) =
        φ.f 0 ≫ Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)
          ((L₂.iCycles 0).hom cyc₂) := by
      simpa using toSingleLinearEquiv_linearHomComplexPrecomp_f_apply (k := ℤ) φ
        (ModuleCat.of ℤ ℤ) 0 ((L₂.iCycles 0).hom cyc₂)
    rw [hd, hpre_eq, hf₂] at hpre
    refine hpre.trans ?_
    rw [HomologicalComplex.mkHomToSingle_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact not_exists_leftInverse_mulTwoCochainComplex_d ⟨g, hd_eq⟩

end NonNaturality

end TauCeti
