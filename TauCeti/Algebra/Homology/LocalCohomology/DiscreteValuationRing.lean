/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Homology.LocalCohomology.RightDerived
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Local cohomology of a discrete valuation ring

For a discrete valuation ring `(R, 𝔪)` with fraction ring `K`, `K` and `K ⧸ R` are divisible,
hence injective `R`-modules, giving a two-term injective resolution `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0`.
Since `R` and `K` have no nonzero `𝔪`-power torsion while `K ⧸ R` is entirely `𝔪`-power torsion,
computing local cohomology via `localCohomology.isoRightDerivedPrimaryComponent` gives
`H⁰_𝔪(R) = 0`, `H¹_𝔪(R) ≅ K ⧸ R`, and `H^{n+2}_𝔪(R) = 0` for all `n : ℕ`.

## Main definitions

* `localCohomology.dvrDegreeOneIso R K` and `localCohomology.dvrDegreeOneLinearEquiv R K`: for a
  discrete valuation ring `(R, 𝔪)` with fraction ring `K`, the isomorphism
  `(localCohomology 𝔪 1).obj (.of R R) ≅ .of R (K ⧸ R)` and its `R`-linear equivalence.

## Main results

* `localCohomology.isZero_dvr_zero` and `localCohomology.isZero_dvr_add_two`: for a discrete
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

/-- Over a discrete valuation ring `(R, 𝔪)`, `R` itself has no nonzero `𝔪`-power torsion. -/
lemma primaryComponent_maximalIdeal_self :
    (IsLocalRing.maximalIdeal R).primaryComponent R = ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.primaryComponent_span_singleton_eq_bot_iff]
  exact fun _ _ hxy ↦ mul_left_cancel₀ hϖ.ne_zero hxy

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `K` has no nonzero `𝔪`-power
torsion because any uniformizer acts invertibly on `K`. -/
lemma primaryComponent_maximalIdeal_fractionRing :
    (IsLocalRing.maximalIdeal R).primaryComponent K = ⊥ := by
  let := IsFractionRing.toField R (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.primaryComponent_span_singleton_eq_bot_iff]
  intro x y hxy
  have hϖK : algebraMap R K ϖ ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hϖ.ne_zero
  simpa only [Algebra.smul_def, mul_eq_mul_left_iff, hϖK, or_false] using hxy

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, the quotient `K ⧸ R` is
entirely `𝔪`-power torsion: every fraction has denominator a unit times a power of a
uniformizer. -/
lemma primaryComponent_maximalIdeal_quotient_fractionRing :
    (IsLocalRing.maximalIdeal R).primaryComponent
      (K ⧸ LinearMap.range (Algebra.linearMap R K)) = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Submodule.eq_top_iff']
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨⟨a, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp hs) hϖ
  rw [Ideal.mem_primaryComponent_span_singleton_iff]
  refine ⟨k, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨↑u⁻¹ * a, ?_⟩
  have hspec := IsLocalization.mk'_spec' K a ⟨↑u * ϖ ^ k, hs⟩
  -- Multiply by `u⁻¹` in `R`: `(u * ϖ^k) • mk' K a _ = algebraMap R K a`.
  calc Algebra.linearMap R K (↑u⁻¹ * a)
    _ = (↑u⁻¹ : R) • algebraMap R K a := by
      rw [Algebra.linearMap_apply, map_mul, ← Algebra.smul_def]
    _ = (↑u⁻¹ : R) • ((↑u * ϖ ^ k) • IsLocalization.mk' K a ⟨↑u * ϖ ^ k, hs⟩) := by
      rw [← hspec, ← Algebra.smul_def]
    _ = ϖ ^ k • IsLocalization.mk' K a ⟨↑u * ϖ ^ k, hs⟩ := by
      rw [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul]

/-- The short exact sequence `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0` in `ModuleCat.{u} R`. -/
private def dvrShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (Algebra.linearMap R K))
    (ModuleCat.ofHom (LinearMap.range (Algebra.linearMap R K)).mkQ)
    (ModuleCat.hom_ext (LinearMap.ext fun r ↦ (Submodule.Quotient.mk_eq_zero _).mpr ⟨r, rfl⟩))

omit [IsDomain R] [IsDiscreteValuationRing R] in
private lemma dvrShortComplex_shortExact : (dvrShortComplex R K).ShortExact :=
  ModuleCat.shortComplex_shortExact (dvrShortComplex R K)
    (fun _ ↦ (Submodule.Quotient.mk_eq_zero _).trans LinearMap.mem_range)
    (FaithfulSMul.algebraMap_injective R K)
    (Submodule.mkQ_surjective _)

private instance injective_fractionRing_obj : Injective (ModuleCat.of R K) := by
  let := IsFractionRing.toField R (K := K)
  have : Module.Injective R K :=
    Module.Injective.of_ringEquiv (RingEquiv.refl R)
      (Submodule.quotEquivOfEqBot (⊥ : Submodule R K) rfl)
  exact Module.injective_object_of_injective_module R K

private instance injective_quotient_fractionRing_obj :
    Injective (ModuleCat.of R (K ⧸ LinearMap.range (Algebra.linearMap R K))) := by
  let := IsFractionRing.toField R (K := K)
  exact Module.injective_object_of_injective_module R _

/-- Over a discrete valuation ring `(R, 𝔪)`, `H⁰_𝔪(R) = 0`. -/
theorem isZero_dvr_zero :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (.of R R)) := by
  have : Subsingleton ((IsLocalRing.maximalIdeal R).primaryComponent R) :=
    primaryComponent_maximalIdeal_self R ▸ inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (degreeZeroEquivPrimaryComponent (IsLocalRing.maximalIdeal R) (.of R R)).toModuleIso

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `H¹_𝔪(R) ≅ K ⧸ R`,
computed from the two-term injective resolution `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0`. -/
def dvrDegreeOneIso :
    ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) ≅
      .of R (K ⧸ LinearMap.range (Algebra.linearMap R K)) := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  let S := dvrShortComplex R K
  have hS : S.ShortExact := dvrShortComplex_shortExact R K
  have : Injective S.X₂ := injective_fractionRing_obj R K
  have : Injective S.X₃ := injective_quotient_fractionRing_obj R K
  let I : InjectiveResolution S.X₁ := (InjectiveResolution.self S.X₃).ofShortExact hS
  let C := (𝔪.primaryComponentFunctor.{u}.mapHomologicalComplex _).obj I.cocomplex
  let T := C.sc' 0 1 2
  have : Subsingleton (𝔪.primaryComponent K) :=
    primaryComponent_maximalIdeal_fractionRing R K ▸ inferInstance
  have hX₁ : IsZero T.X₁ :=
    IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
      (𝔪.primaryComponentFunctorObjIso (.of R K))
  have hX₃ : IsZero T.X₃ :=
    𝔪.primaryComponentFunctor.{u}.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 S.X₃ 1 (by decide))
  exact ((isoRightDerivedPrimaryComponent 𝔪 1).app S.X₁) ≪≫
    I.isoRightDerivedObj 𝔪.primaryComponentFunctor.{u} 1 ≪≫
    C.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (ShortComplex.HomologyData.ofZeros T (hX₁.eq_of_src _ _)
      (hX₃.eq_of_tgt _ _)).left.homologyIso ≪≫
    𝔪.primaryComponentFunctorObjIso S.X₃ ≪≫
    (LinearEquiv.ofTop _ (primaryComponent_maximalIdeal_quotient_fractionRing R K)).toModuleIso

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `H¹_𝔪(R)` is `R`-linearly
equivalent to `K ⧸ R`. -/
def dvrDegreeOneLinearEquiv :
    ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) ≃ₗ[R]
      K ⧸ LinearMap.range (Algebra.linearMap R K) :=
  (dvrDegreeOneIso R K).toLinearEquiv

/-- Over a discrete valuation ring `(R, 𝔪)`, `H^{n+2}_𝔪(R) = 0` for every `n : ℕ`. -/
theorem isZero_dvr_add_two (n : ℕ) :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) (n + 2)).obj (.of R R)) := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  let S := dvrShortComplex R (FractionRing R)
  have hS : S.ShortExact := dvrShortComplex_shortExact R (FractionRing R)
  have : Injective S.X₂ := injective_fractionRing_obj R (FractionRing R)
  have : Injective S.X₃ := injective_quotient_fractionRing_obj R (FractionRing R)
  refine IsZero.of_iso ?_ ((isoRightDerivedPrimaryComponent 𝔪 (n + 2)).app S.X₁ ≪≫
    𝔪.primaryComponentFunctor.{u}.rightDerivedObjX₁IsoOfShortExact hS n)
  exact Functor.isZero_rightDerived_obj_injective_succ 𝔪.primaryComponentFunctor.{u} n S.X₃

end DiscreteValuationRing

end localCohomology
