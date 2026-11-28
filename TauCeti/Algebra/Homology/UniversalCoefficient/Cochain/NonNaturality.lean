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
import TauCeti.Algebra.Homology.HomologicalComplex.Double
import TauCeti.Algebra.Homology.LinearHomComplex.Cohomology

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

private lemma mulTwoCochainComplex_free_and_finite (i : ℤ) :
    Module.Free ℤ (mulTwoCochainComplex.X i) ∧ Module.Finite ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0
    have e := (doubleXIso₀ mulTwoHom up_rel_zero_one).symm.toLinearEquiv
    exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
  · by_cases hi1 : i = 1
    · subst hi1
      have e := (doubleXIso₁ mulTwoHom up_rel_zero_one (by decide)).symm.toLinearEquiv
      exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
    · have : Subsingleton (mulTwoCochainComplex.X i) :=
        ModuleCat.isZero_iff_subsingleton.1 (isZero_double_X mulTwoHom up_rel_zero_one i hi0 hi1)
      exact ⟨inferInstance, inferInstance⟩

private instance (i : ℤ) : Module.Free ℤ (mulTwoCochainComplex.X i) :=
  (mulTwoCochainComplex_free_and_finite i).1

private instance (i : ℤ) : Module.Finite ℤ (mulTwoCochainComplex.X i) :=
  (mulTwoCochainComplex_free_and_finite i).2

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
  exact (isZero_zero _).of_iso
    (doubleHomologyIso₀ zero_ne_one (kernel.isLimitConeZeroCone mulTwoHom))

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

private lemma singleIntComplex_free_and_finite (i : ℤ) :
    Module.Free ℤ (singleIntComplex.X i) ∧ Module.Finite ℤ (singleIntComplex.X i) := by
  by_cases hi : i = 0
  · subst hi
    have e := (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).symm.toLinearEquiv
    exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
  · have : Subsingleton (singleIntComplex.X i) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi)
    exact ⟨inferInstance, inferInstance⟩

private instance (i : ℤ) : Module.Free ℤ (singleIntComplex.X i) :=
  (singleIntComplex_free_and_finite i).1

private instance (i : ℤ) : Module.Finite ℤ (singleIntComplex.X i) :=
  (singleIntComplex_free_and_finite i).2

private instance : singleIntComplex.IsStrictlyLE 1 :=
  CochainComplex.isStrictlyLE_of_le singleIntComplex 0 1 (by decide)

/-- Any degree-0 cocycle of `linearHomComplex ℤ ℤ[0] ℤ[0]` whose Kronecker evaluation is the
canonical isomorphism `H⁰(ℤ[0]) ≅ ℤ` has underlying degree-0 morphism equal to
`singleObjXSelf.hom`. -/
private lemma toSingleEquiv_singleIntComplex_of_kronecker
    (cyc : (linearHomComplex ℤ singleIntComplex singleIntComplex).cycles 0)
    (hcyc : linearHomComplexSingleKronecker ℤ singleIntComplex (ModuleCat.of ℤ ℤ) 0
        (((linearHomComplex ℤ singleIntComplex singleIntComplex).homologyπ 0).hom cyc) =
      (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom) :
    Cochain.toSingleEquiv (neg_add_cancel 0)
        (((linearHomComplex ℤ singleIntComplex singleIntComplex).iCycles 0).hom cyc) =
      (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom := by
  have hkr : singleIntComplex.homologyπ 0 ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom =
      singleIntComplex.iCycles 0 ≫
        Cochain.toSingleEquiv (neg_add_cancel 0)
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
    doubleπ₀ mulTwoHom up_rel_zero_one zero_ne_one
  let g₀ : singleIntComplex.homology 0 ⟶ ModuleCat.of ℤ ℤ :=
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom
  let L₂ := linearHomComplex ℤ singleIntComplex singleIntComplex
  -- Express `s ℤ[0] g₀` via `homologyLinearEquiv` and identify its cocycle using Kronecker.
  let D₂ := linearLeftHomologyData ℤ singleIntComplex singleIntComplex 0
  obtain ⟨c₂, hc₂⟩ := (homologyLinearEquiv ℤ singleIntComplex singleIntComplex 0).symm.surjective
    (s singleIntComplex g₀)
  induction c₂ using CohomologyClass.rec with | mk x => ?_
  have hcyc₂ : (L₂.homologyπ 0).hom (D₂.cyclesIso.inv.hom x) = s singleIntComplex g₀ := by
    rw [← hc₂, ← ModuleCat.comp_apply]
    dsimp only [HomologicalComplex.homologyπ, ShortComplex.homologyπ, L₂]
    rw [← Category.assoc, ← ShortComplex.LeftHomologyData.π_comp_leftHomologyIso_inv,
      Category.assoc]
    rfl
  have hf₂ := toSingleEquiv_singleIntComplex_of_kronecker (D₂.cyclesIso.inv.hom x)
    (by rw [hcyc₂, hs_sec])
  rw [← ModuleCat.comp_apply] at hf₂
  dsimp only [HomologicalComplex.iCycles] at hf₂
  rw [D₂.cyclesIso_inv_comp_iCycles] at hf₂
  dsimp only [D₂] at hf₂
  let x₀ : Cocycle singleIntComplex singleIntComplex 0 :=
    Cocycle.toSingleMk (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom
      (add_zero 0) (-1) (by decide) (by simp)
  have hx : x = x₀ := Cocycle.ext ((Cochain.toSingleEquiv (add_zero 0)).injective (by
    simpa [x₀] using hf₂))
  subst hx
  -- Naturality along `φ` forces the pulled-back cocycle to be a coboundary, since `H⁰(K₁) = 0`.
  have hpull := hs_nat mulTwoCochainComplex singleIntComplex φ g₀
  rw [isZero_homology_zero_mulTwoCochainComplex.eq_of_src (homologyMap φ 0 ≫ g₀) 0,
    map_zero, ← hc₂] at hpull
  let y₀ : Cocycle mulTwoCochainComplex singleIntComplex 0 :=
    Cocycle.toSingleMk (doubleXIso₀ mulTwoHom up_rel_zero_one).hom (add_zero 0) (-1) (by decide)
      (by rw [double_d_to₀_eq_zero mulTwoHom up_rel_zero_one zero_ne_one (-1), zero_comp])
  have hclass := congrArg (homologyLinearEquiv ℤ mulTwoCochainComplex singleIntComplex 0) hpull
  rw [map_zero, homologyLinearEquiv_homologyMap_symm_mk ℤ
      (linearHomComplexPrecomp ℤ φ singleIntComplex) x₀ y₀ (by
        have hpre := congrArg (fun (z : Cocycle mulTwoCochainComplex singleIntComplex 0) ↦
            (z : Cochain mulTwoCochainComplex singleIntComplex 0))
          (Cocycle.toSingleMk_precomp
            (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).hom
            (add_zero 0) (-1) (by decide) (by simp) φ)
        simpa [x₀, y₀, φ, doubleπ₀_f₀] using hpre),
    CohomologyClass.mk_eq_zero_iff] at hclass
  exact not_exists_leftInverse_mulTwoCochainComplex_d
    ((Cocycle.toSingleMk_mem_coboundaries_iff _ (add_zero 0) (-1) (by decide)
      (by rw [double_d_to₀_eq_zero mulTwoHom up_rel_zero_one zero_ne_one (-1), zero_comp])
      1 (by decide)).1 hclass)

end NonNaturality

end TauCeti
