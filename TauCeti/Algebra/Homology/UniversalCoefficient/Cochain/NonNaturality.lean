/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Non-naturality of the cochain universal coefficient splitting

Although `TauCeti.cochainKroneckerSection` provides a splitting of the cochain universal
coefficient sequence that is natural in the coefficient object `Y`, no splitting can be chosen
naturally in the cochain complex `K`, even when restricted to strictly bounded finite free
`ℤ`-cochain complexes with dualizing target `ℤ`.

## Main results

* `TauCeti.not_exists_natural_section_cochainKronecker`: the chain map from
  `0 ⟶ ℤ xrightarrow{×2} ℤ ⟶ 0` (in degrees `0` and `1`) to `ℤ[0]` rules out any simultaneous
  natural additive section of `TauCeti.cochainKronecker` in degree `0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Example 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex

namespace TauCeti

section NonNaturality

private abbrev mulTwoObj (i : ℤ) : ModuleCat.{0} ℤ :=
  if i = 0 then ModuleCat.of ℤ ℤ else if i = 1 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit

/-- The two-term bounded finite free `ℤ`-cochain complex `0 ⟶ ℤ xrightarrow{×2} ℤ ⟶ 0` in degrees
`0` and `1` witnessing that the universal coefficient splitting cannot be chosen naturally. -/
private def mulTwoCochainComplex : CochainComplex (ModuleCat.{0} ℤ) ℤ where
  X := mulTwoObj
  d i j :=
    if hi : i = 0 then
      if hj : j = 1 then
        eqToHom (by subst hi; rfl) ≫
          ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ≫
          eqToHom (by subst hj; rfl)
      else 0
    else 0
  shape i j hij := by
    simp only [ComplexShape.up_Rel] at hij; split_ifs <;> first | omega | rfl
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    by_cases hi : i = 0
    · subst hi; obtain rfl : j = 1 := by omega
      obtain rfl : k = 2 := by omega
      simp
    · rw [dite_eq_right hi, zero_comp]

private def mulTwoX0Iso : mulTwoCochainComplex.X 0 ≅ ModuleCat.of ℤ ℤ := Iso.refl _

private def mulTwoX1Iso : mulTwoCochainComplex.X 1 ≅ ModuleCat.of ℤ ℤ := Iso.refl _

private lemma mulTwoCochainComplex_d_zero_one :
    mulTwoCochainComplex.d 0 1 =
      mulTwoX0Iso.hom ≫ ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ≫
        mulTwoX1Iso.inv := by
  simp [mulTwoCochainComplex, mulTwoX0Iso, mulTwoX1Iso, mulTwoObj]

private instance (i : ℤ) : Module.Free ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0; exact inferInstanceAs (Module.Free ℤ ℤ)
  · by_cases hi1 : i = 1
    · subst hi1; exact inferInstanceAs (Module.Free ℤ ℤ)
    · rw [show mulTwoCochainComplex.X i = ModuleCat.of ℤ PUnit by
        simp [mulTwoCochainComplex, mulTwoObj, hi0, hi1]]
      exact inferInstanceAs (Module.Free ℤ PUnit)

private instance (i : ℤ) : Module.Finite ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0; exact inferInstanceAs (Module.Finite ℤ ℤ)
  · by_cases hi1 : i = 1
    · subst hi1; exact inferInstanceAs (Module.Finite ℤ ℤ)
    · rw [show mulTwoCochainComplex.X i = ModuleCat.of ℤ PUnit by
        simp [mulTwoCochainComplex, mulTwoObj, hi0, hi1]]
      exact inferInstanceAs (Module.Finite ℤ PUnit)

private instance : mulTwoCochainComplex.IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦ by
    dsimp only [mulTwoCochainComplex, mulTwoObj]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ModuleCat.isZero_of_subsingleton _

private instance : mulTwoCochainComplex.IsStrictlyLE 1 :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦ by
    dsimp only [mulTwoCochainComplex, mulTwoObj]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ModuleCat.isZero_of_subsingleton _

private lemma isZero_homology_zero_mulTwoCochainComplex :
    IsZero (mulTwoCochainComplex.homology 0) := by
  have hmul2 : Mono (ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) :=
    (ModuleCat.mono_iff_injective _).2 fun a b hab ↦ by
      have h : (2 : ℤ) * (a : ℤ) = (2 : ℤ) * (b : ℤ) := by
        simpa only [ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearMap.id_apply,
          smul_eq_mul] using hab
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h
  have hmono : Mono (mulTwoCochainComplex.d 0 1) := by
    rw [mulTwoCochainComplex_d_zero_one]
    exact mono_comp _ _
  have hex : mulTwoCochainComplex.ExactAt 0 :=
    (HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)).2
      (((mulTwoCochainComplex.sc' (-1) 0 1).exact_iff_mono rfl).2 hmono)
  exact hex.isZero_homology

private lemma not_exists_leftInverse_mulTwoCochainComplex_d :
    ¬ ∃ g : mulTwoCochainComplex.X 1 ⟶ ModuleCat.of ℤ ℤ,
      mulTwoCochainComplex.d 0 1 ≫ g = mulTwoX0Iso.hom := by
  rintro ⟨g, hg⟩
  rw [mulTwoCochainComplex_d_zero_one, Category.assoc, Category.assoc] at hg
  have hg' : ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ≫
      (mulTwoX1Iso.inv ≫ g) = 𝟙 (ModuleCat.of ℤ ℤ) := by
    rw [← cancel_epi mulTwoX0Iso.hom, Category.comp_id]
    exact hg
  let f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := mulTwoX1Iso.inv ≫ g
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
private lemma toSingleLinearEquiv_singleIntComplex_of_cochainKronecker
    (cyc : (linearHomComplex ℤ singleIntComplex singleIntComplex).cycles 0)
    (hcyc : cochainKronecker ℤ singleIntComplex (ModuleCat.of ℤ ℤ) 0
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
    exact homologyπ_cochainKronecker (k := ℤ) (K := singleIntComplex)
      (Y := ModuleCat.of ℤ ℤ) 0 cyc
  have hkr' := congrArg
    ((singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).inv ≫ ·) hkr
  rw [homologyπ_singleObjHomologySelfIso_hom, Iso.inv_hom_id,
    singleObjCyclesSelfIso_inv_iCycles_assoc] at hkr'
  simpa using congrArg
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom ≫ ·) hkr'.symm

/-- **No simultaneous natural splitting of the cochain universal coefficient sequence exists.**
Even among strictly bounded finite free `ℤ`-cochain complexes with dualizing target `ℤ`, there is
no family of additive sections `s K : (H⁰(K) ⟶ ℤ) →+ H⁰(Hom(K, ℤ[0]))` of `cochainKronecker` in
degree `0` that commutes with chain maps. -/
theorem not_exists_natural_section_cochainKronecker :
    ¬ ∃ s : ∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
        [∀ i, Module.Free ℤ (K.X i)] [∀ i, Module.Finite ℤ (K.X i)]
        [K.IsStrictlyGE 0] [K.IsStrictlyLE 1],
        (K.homology 0 ⟶ ModuleCat.of ℤ ℤ) →+
          (linearHomComplex ℤ K ((singleFunctor (ModuleCat.{0} ℤ) 0).obj
            (ModuleCat.of ℤ ℤ))).homology 0,
      (∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ i, Module.Free ℤ (K.X i)] [∀ i, Module.Finite ℤ (K.X i)]
          [K.IsStrictlyGE 0] [K.IsStrictlyLE 1] (g : K.homology 0 ⟶ ModuleCat.of ℤ ℤ),
        cochainKronecker ℤ K (ModuleCat.of ℤ ℤ) 0 (s K g) = g) ∧
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
    HomologicalComplex.mkHomToSingle mulTwoX0Iso.hom (fun i hi ↦
      (mulTwoCochainComplex.isZero_of_isStrictlyGE 0 i
        (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _)
  let g₀ : singleIntComplex.homology 0 ⟶ ModuleCat.of ℤ ℤ :=
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom
  let L₁ := linearHomComplex ℤ mulTwoCochainComplex singleIntComplex
  let L₂ := linearHomComplex ℤ singleIntComplex singleIntComplex
  -- Lift `s ℤ[0] g₀` to a degree-0 cocycle `cyc₂` of `Hom(ℤ[0], ℤ[0])`.
  obtain ⟨cyc₂, hcyc₂⟩ := L₂.moduleCat_homologyπ_surjective 0 (s singleIntComplex g₀)
  have hf₂ := toSingleLinearEquiv_singleIntComplex_of_cochainKronecker cyc₂
    ((congrArg (cochainKronecker ℤ singleIntComplex (ModuleCat.of ℤ ℤ) 0) hcyc₂).trans
      (hs_sec singleIntComplex g₀))
  -- Naturality along `φ` forces the pullback of `cyc₂` to be a coboundary, since `H⁰(K₁) = 0`.
  have hpull := hs_nat mulTwoCochainComplex singleIntComplex φ g₀
  rw [← hcyc₂, isZero_homology_zero_mulTwoCochainComplex.eq_of_src (homologyMap φ 0 ≫ g₀) 0,
    map_zero, HomologicalComplex.moduleCat_homologyMap_homologyπ] at hpull
  obtain ⟨y, hy⟩ := (L₁.moduleCat_homologyπ_eq_zero_iff (m := -1) (by simp) _).1 hpull
  have hdy : (L₁.d (-1) 0).hom y =
      ((linearHomComplexPrecomp ℤ φ singleIntComplex).f 0).hom ((L₂.iCycles 0).hom cyc₂) := by
    simpa only [HomologicalComplex.moduleCat_iCycles_toCycles_apply,
      HomologicalComplex.moduleCat_iCycles_cyclesMap_apply] using congrArg (L₁.iCycles 0).hom hy
  -- Evaluating the coboundary relation in degree `0` produces a left inverse to `×2 : ℤ ⟶ ℤ`.
  have hpre : Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)
      (((linearHomComplexPrecomp ℤ φ singleIntComplex).f 0).hom ((L₂.iCycles 0).hom cyc₂)) =
      mulTwoX0Iso.hom := by
    rw [toSingleLinearEquiv_linearHomComplexPrecomp_f_apply, hf₂]
    exact (congrArg (· ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom)
      (HomologicalComplex.mkHomToSingle_f mulTwoX0Iso.hom _)).trans
        (by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hd : Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0) ((L₁.d (-1) 0).hom y) =
      mulTwoCochainComplex.d 0 1 ≫
        Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel (-1)) y := by
    have hd₀ := toSingleLinearEquiv_linearHomComplex_d_apply (k := ℤ) mulTwoCochainComplex
      (ModuleCat.of ℤ ℤ) (-1) y
    rw [show ((-1 : ℤ) + 1).negOnePow = 1 from rfl, one_smul] at hd₀
    exact hd₀
  rw [hdy, hpre] at hd
  exact not_exists_leftInverse_mulTwoCochainComplex_d
    ⟨Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel (-1)) y, hd.symm⟩

end NonNaturality

end TauCeti
