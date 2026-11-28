/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Homology.LocalCohomology.RightDerived
public import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
public import TauCeti.RingTheory.DiscreteValuationRing.PrimaryComponent

/-!
# Local cohomology of a discrete valuation ring

For a discrete valuation ring `(R, 𝔪)` with fraction ring `K`, `K` and `K ⧸ R` are injective
`R`-modules, giving a two-term injective resolution `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0`. Since `R` and `K`
have no nonzero `𝔪`-power torsion while `K ⧸ R` is `𝔪`-power torsion,
`localCohomology.isoRightDerivedPrimaryComponent` gives `H⁰_𝔪(R) = 0`, `H¹_𝔪(R) ≅ K ⧸ R`, and
`H^{n+2}_𝔪(R) = 0` for all `n : ℕ`.

## Main definitions

* `localCohomology.maximalIdealOneObjIsoQuotientFractionRing R K` and
  `localCohomology.maximalIdealOneObjLinearEquivQuotientFractionRing R K`: for a discrete
  valuation ring `(R, 𝔪)` with fraction ring `K`, the isomorphism
  `(localCohomology 𝔪 1).obj (.of R R) ≅ .of R (K ⧸ R)` and its `R`-linear equivalence.

## Main results

* `localCohomology.isZero_obj_maximalIdeal_zero_of_isDiscreteValuationRing` and
  `localCohomology.isZero_obj_maximalIdeal_add_two_of_isDiscreteValuationRing`: for a discrete
  valuation ring `(R, 𝔪)`, `H⁰_𝔪(R) = 0` and `H^{n+2}_𝔪(R) = 0`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Exercise III.3.3.
* A. Grothendieck, *Local Cohomology* (notes by R. Hartshorne), Lecture Notes in Mathematics 41,
  Springer, 1967, Proposition 2.8.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace localCohomology

section DiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- The short exact sequence `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0` in `ModuleCat.{u} R`. -/
@[expose]
def fractionRingShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (Algebra.linearMap R K)
    (LinearMap.range (Algebra.linearMap R K)).mkQ
    (Algebra.linearMap R K).exact_map_mkQ_range.linearMap_comp_eq_zero

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Exactness of the short complex `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0` in `ModuleCat.{u} R`. -/
lemma fractionRingShortComplex_shortExact : (fractionRingShortComplex R K).ShortExact :=
  ModuleCat.shortComplex_shortExact (fractionRingShortComplex R K)
    (Algebra.linearMap R K).exact_map_mkQ_range (FaithfulSMul.algebraMap_injective R K)
    (Submodule.mkQ_surjective _)

private instance : Injective (fractionRingShortComplex R K).X₂ :=
  Module.injective_object_of_injective_module R K

private instance : Injective (fractionRingShortComplex R K).X₃ :=
  Module.injective_object_of_injective_module R _

/-- The two-term injective resolution `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0` of `R` as an `R`-module. -/
@[expose]
def fractionRingInjectiveResolution : InjectiveResolution (fractionRingShortComplex R K).X₁ :=
  letI : Injective (fractionRingShortComplex R K).X₂ :=
    Module.injective_object_of_injective_module R K
  letI : Injective (fractionRingShortComplex R K).X₃ :=
    Module.injective_object_of_injective_module R _
  (InjectiveResolution.self (fractionRingShortComplex R K).X₃).ofShortExact
    (fractionRingShortComplex_shortExact R K)

private lemma isZero_fractionRingCocomplex_zero :
    let 𝔪 := IsLocalRing.maximalIdeal R
    IsZero (((𝔪.primaryComponentFunctor.{u}.mapHomologicalComplex _).obj
      (fractionRingInjectiveResolution R K).cocomplex).X 0) := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  have : Subsingleton (𝔪.primaryComponent K) :=
    TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_fractionRing R K ▸ inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (𝔪.primaryComponentFunctorObjIso (.of R K))

private lemma isZero_fractionRingCocomplex_two :
    let 𝔪 := IsLocalRing.maximalIdeal R
    IsZero (((𝔪.primaryComponentFunctor.{u}.mapHomologicalComplex _).obj
      (fractionRingInjectiveResolution R K).cocomplex).X 2) :=
  (IsLocalRing.maximalIdeal R).primaryComponentFunctor.{u}.map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
      (fractionRingShortComplex R K).X₃ 1 (by decide))

/-- Over a discrete valuation ring `(R, 𝔪)`, `H⁰_𝔪(R) = 0`. -/
theorem isZero_obj_maximalIdeal_zero_of_isDiscreteValuationRing :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (.of R R)) := by
  have : Subsingleton ((IsLocalRing.maximalIdeal R).primaryComponent R) :=
    TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_self R ▸ inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (degreeZeroEquivPrimaryComponent (IsLocalRing.maximalIdeal R) (.of R R)).toModuleIso

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `H¹_𝔪(R) ≅ K ⧸ R`,
computed from the two-term injective resolution `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0`. -/
def maximalIdealOneObjIsoQuotientFractionRing :
    ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) ≅
      .of R (K ⧸ LinearMap.range (Algebra.linearMap R K)) :=
  let 𝔪 := IsLocalRing.maximalIdeal R; let I := fractionRingInjectiveResolution R K
  let C := (𝔪.primaryComponentFunctor.{u}.mapHomologicalComplex _).obj I.cocomplex
  ((isoRightDerivedPrimaryComponent 𝔪 1).app (fractionRingShortComplex R K).X₁) ≪≫
    I.isoRightDerivedObj 𝔪.primaryComponentFunctor.{u} 1 ≪≫
    (C.isoHomologyπ 0 1 (by simp) ((isZero_fractionRingCocomplex_zero R K).eq_of_src _ _)).symm ≪≫
    C.iCyclesIso 1 2 (by simp) ((isZero_fractionRingCocomplex_two R K).eq_of_tgt _ _) ≪≫
    𝔪.primaryComponentFunctorObjIso (fractionRingShortComplex R K).X₃ ≪≫
    (LinearEquiv.ofTop _
      (TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_quotient_fractionRing
        R K)).toModuleIso

/-- On the two-term injective resolution `fractionRingInjectiveResolution R K`,
`maximalIdealOneObjIsoQuotientFractionRing` sends the homology class of a `1`-cycle in
`Γ_𝔪(K ⧸ R)` to its underlying element in `K ⧸ R`. -/
lemma homologyπ_comp_maximalIdealOneObjIsoQuotientFractionRing_hom :
    let 𝔪 := IsLocalRing.maximalIdeal R
    let C := (𝔪.primaryComponentFunctor.{u}.mapHomologicalComplex _).obj
      (fractionRingInjectiveResolution R K).cocomplex
    C.homologyπ 1 ≫ ((fractionRingInjectiveResolution R K).isoRightDerivedObj
          𝔪.primaryComponentFunctor.{u} 1).inv ≫
        (isoRightDerivedPrimaryComponent 𝔪 1).inv.app (fractionRingShortComplex R K).X₁ ≫
        (maximalIdealOneObjIsoQuotientFractionRing R K).hom =
      C.iCycles 1 ≫ (𝔪.primaryComponentFunctorObjIso (fractionRingShortComplex R K).X₃).hom ≫
        (LinearEquiv.ofTop _
          (TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_quotient_fractionRing
            R K)).toModuleIso.hom := by
  intro 𝔪 C
  have h1 : ((fractionRingInjectiveResolution R K).isoRightDerivedObj
          𝔪.primaryComponentFunctor.{u} 1).inv ≫
        (isoRightDerivedPrimaryComponent 𝔪 1).inv.app (fractionRingShortComplex R K).X₁ ≫
        (maximalIdealOneObjIsoQuotientFractionRing R K).hom =
      (C.isoHomologyπ 0 1 (by simp)
          ((isZero_fractionRingCocomplex_zero R K).eq_of_src _ _)).inv ≫
        (C.iCyclesIso 1 2 (by simp)
          ((isZero_fractionRingCocomplex_two R K).eq_of_tgt _ _)).hom ≫
        (𝔪.primaryComponentFunctorObjIso (fractionRingShortComplex R K).X₃).hom ≫
        (LinearEquiv.ofTop _
          (TauCeti.IsDiscreteValuationRing.primaryComponent_maximalIdeal_quotient_fractionRing
            R K)).toModuleIso.hom :=
    (congrArg (((fractionRingInjectiveResolution R K).isoRightDerivedObj
        𝔪.primaryComponentFunctor.{u} 1).inv ≫ ·)
      (Iso.inv_hom_id_assoc ((isoRightDerivedPrimaryComponent 𝔪 1).app
        (fractionRingShortComplex R K).X₁) _)).trans
      (Iso.inv_hom_id_assoc ((fractionRingInjectiveResolution R K).isoRightDerivedObj
        𝔪.primaryComponentFunctor.{u} 1) _)
  rw [h1]
  simp only [HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, HomologicalComplex.iCyclesIso_hom]

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `H¹_𝔪(R)` is `R`-linearly
equivalent to `K ⧸ R`. -/
def maximalIdealOneObjLinearEquivQuotientFractionRing :
    ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) ≃ₗ[R]
      K ⧸ LinearMap.range (Algebra.linearMap R K) :=
  (maximalIdealOneObjIsoQuotientFractionRing R K).toLinearEquiv

/-- `maximalIdealOneObjLinearEquivQuotientFractionRing` acts by the forward map of
`maximalIdealOneObjIsoQuotientFractionRing`. -/
@[simp]
lemma maximalIdealOneObjLinearEquivQuotientFractionRing_apply
    (x : (localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) :
    maximalIdealOneObjLinearEquivQuotientFractionRing R K x =
      (maximalIdealOneObjIsoQuotientFractionRing R K).hom x := (rfl)

/-- Over a discrete valuation ring `(R, 𝔪)`, `H^{n+2}_𝔪(R) = 0` for every `n : ℕ`. -/
theorem isZero_obj_maximalIdeal_add_two_of_isDiscreteValuationRing (n : ℕ) :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) (n + 2)).obj (.of R R)) := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  refine IsZero.of_iso ?_ ((isoRightDerivedPrimaryComponent 𝔪 (n + 2)).app (.of R R) ≪≫
    𝔪.primaryComponentFunctor.{u}.rightDerivedObjX₁IsoOfShortExact
      (fractionRingShortComplex_shortExact R (FractionRing R)) n)
  exact Functor.isZero_rightDerived_obj_injective_succ 𝔪.primaryComponentFunctor.{u} n
    (fractionRingShortComplex R (FractionRing R)).X₃

end DiscreteValuationRing

end localCohomology
