/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Additive
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.RingTheory.DedekindDomain.AdicValuation.FaithfullyFlat

/-!
# Minimal Weierstrass equations under `v`-adic completion

Let `R` be a Dedekind domain with fraction field `K`, let `v` be a height-one prime of `R`, and
let `W` be a Weierstrass curve over `K`. Local minimality at `v` can be formulated either over the
algebraic localisation `Localization.AtPrime v.asIdeal` inside `K` (as in
`WeierstrassCurve.IsGlobalMinimal`), or after base change to `v.adicCompletion K` over the
completed valuation ring `v.adicCompletionIntegers K` (or equivalently over the ring of integers
`𝒪[v.adicCompletion K]` of its canonical valuative relation).

This file proves that these conditions are unconditionally equivalent, with no residue-field
finiteness or perfection assumptions:

* `WeierstrassCurve.isDiscreteValuationRing_integer_adicCompletion`,
  `WeierstrassCurve.isIntegral_integer_adicCompletion_iff`,
  `WeierstrassCurve.isMinimal_integer_adicCompletion_iff`, and
  `WeierstrassCurve.hasGoodReduction_integer_adicCompletion_iff` identify the discrete valuation
  ring structure, integrality, minimality, and good reduction over `𝒪[v.adicCompletion K]` with the
  same predicates over `v.adicCompletionIntegers K`;
* `WeierstrassCurve.isIntegral_adicCompletionIntegers_baseChange_iff` and
  `WeierstrassCurve.isMinimal_adicCompletionIntegers_baseChange_iff` show that `W.baseChange K_v`
  is integral or minimal over `v.adicCompletionIntegers K` if and only if `W` is integral or
  minimal over `Localization.AtPrime v.asIdeal`;
* `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletionIntegers_baseChange` and
  `WeierstrassCurve.isGlobalMinimal_iff_forall_isMinimal_adicCompletionIntegers` read global
  minimality at every completed valuation ring;
* `WeierstrassCurve.localMinimalDiscriminantValuation_adicCompletionIntegers` shows that
  completion preserves `WeierstrassCurve.localMinimalDiscriminantValuation`.

## Proof of completion invariance of minimality

Descent from the completion to the localisation compares the `v`-adic valuations of discriminants
directly. In the reverse direction, if `W` is minimal over `R_v` with `W.Δ ≠ 0` and its base
change were not minimal over `O_v`, the converse of Step 11 of Tate's algorithm
(`WeierstrassCurve.exists_variableChange_pow_dvd_a₁_a₂_a₃_a₄_a₆_of_not_isMinimal`) would produce a
translation over `O_v` whose coefficients `a₁, a₂, a₃, a₄, a₆` are divisible by the uniformiser
powers `ϖ, ϖ², ϖ³, ϖ⁴, ϖ⁶`. Approximating the translation parameters in `R` modulo `𝔪_v ^ 6` via
`IsDedekindDomain.HeightOneSpectrum.exists_valued_sub_le` yields an integral translation over
`R_v` with the same divisibilities modulo `𝔪_v ^ 6`, contradicting Step 11 over `R_v`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1 and VIII.8.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsDedekindDomain IsDiscreteValuationRing IsLocalRing ValuativeRel
open scoped WithZero

namespace WeierstrassCurve

section ValuativeInteger

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- The ring of integers `𝒪[v.adicCompletion K]` of the canonical valuative relation on `K_v` is a
discrete valuation ring, without any finiteness assumption on the residue field. -/
instance isDiscreteValuationRing_integer_adicCompletion :
    IsDiscreteValuationRing 𝒪[v.adicCompletion K] := by
  have hT : ∀ (T : ValuationSubring (v.adicCompletion K)),
      v.adicCompletionIntegers K = T → IsDiscreteValuationRing T := by
    rintro T rfl
    infer_instance
  exact hT (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
    (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)

/-- Integrality over `𝒪[v.adicCompletion K]` agrees with integrality over
`v.adicCompletionIntegers K`, as both are the same valuation subring of `v.adicCompletion K`. -/
theorem isIntegral_integer_adicCompletion_iff (V : WeierstrassCurve (v.adicCompletion K)) :
    IsIntegral 𝒪[v.adicCompletion K] V ↔ IsIntegral (v.adicCompletionIntegers K) V := by
  have hT : ∀ (T : ValuationSubring (v.adicCompletion K)),
      v.adicCompletionIntegers K = T →
        (IsIntegral T V ↔ IsIntegral (v.adicCompletionIntegers K) V) := by
    rintro T rfl
    exact Iff.rfl
  exact hT (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
    (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)

/-- Minimality over `𝒪[v.adicCompletion K]` agrees with minimality over
`v.adicCompletionIntegers K`. Stated as an equivalence rather than a pair of instances to avoid
typeclass synthesis cycles between the two rings of integers. -/
theorem isMinimal_integer_adicCompletion_iff (V : WeierstrassCurve (v.adicCompletion K)) :
    IsMinimal 𝒪[v.adicCompletion K] V ↔ IsMinimal (v.adicCompletionIntegers K) V := by
  have hR : IsDiscreteValuationRing
      (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
  have hT : ∀ (T : ValuationSubring (v.adicCompletion K)) [IsDiscreteValuationRing T],
      v.adicCompletionIntegers K = T →
        (IsMinimal T V ↔ IsMinimal (v.adicCompletionIntegers K) V) := by
    rintro T _ rfl
    exact Iff.rfl
  exact hT (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
    (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)

/-- Good reduction over `𝒪[v.adicCompletion K]` agrees with good reduction over
`v.adicCompletionIntegers K`. -/
theorem hasGoodReduction_integer_adicCompletion_iff (V : WeierstrassCurve (v.adicCompletion K)) :
    V.HasGoodReduction 𝒪[v.adicCompletion K] ↔
      V.HasGoodReduction (v.adicCompletionIntegers K) := by
  have hR : IsDiscreteValuationRing
      (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
  have hT : ∀ (T : ValuationSubring (v.adicCompletion K)) [IsDiscreteValuationRing T],
      v.adicCompletionIntegers K = T →
        (V.HasGoodReduction T ↔ V.HasGoodReduction (v.adicCompletionIntegers K)) := by
    rintro T _ rfl
    exact Iff.rfl
  exact hT (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
    (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)

end ValuativeInteger

section LocalizationComparison

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/- The canonical embedding `R_v → O_v` commutes with the inclusions into `K` and `K_v`. -/
private theorem algebraMap_comp_localization_adicCompletionIntegers :
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).comp
        (algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)) =
      (algebraMap K (v.adicCompletion K)).comp
        (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  refine IsLocalization.ringHom_ext v.asIdeal.primeCompl ?_
  ext x
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

/- An element of `K` comes from `R_v` if and only if its image in `K_v` comes from `O_v`. -/
private theorem exists_algebraMap_localizationAtPrime_iff (x : K) :
    (∃ a : Localization.AtPrime v.asIdeal, algebraMap _ K a = x) ↔
      ∃ b : v.adicCompletionIntegers K,
        algebraMap _ (v.adicCompletion K) b = algebraMap K (v.adicCompletion K) x := by
  have hv := v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal) (K := K)
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨algebraMap _ _ a,
      RingHom.congr_fun (algebraMap_comp_localization_adicCompletionIntegers v) a⟩
  · rintro ⟨b, hb⟩
    refine hv.exists_of_le_one ?_
    have hb' : Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1 := by
      rw [← hb]
      exact b.2
    rwa [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      v.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply] at hb'

/-- **Integrality under `v`-adic completion**: a Weierstrass equation over `K` becomes integral
over `v.adicCompletionIntegers K` after base change to `v.adicCompletion K` if and only if it is
integral over `Localization.AtPrime v.asIdeal`. -/
theorem isIntegral_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve K) :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsIntegral (Localization.AtPrime v.asIdeal) W := by
  constructor
  · intro hI
    obtain ⟨V, hV⟩ := hI.integral
    have hcoeff {x : K} {y : v.adicCompletionIntegers K}
        (hy : algebraMap _ (v.adicCompletion K) y = algebraMap K (v.adicCompletion K) x) :
        ∃ a : Localization.AtPrime v.asIdeal, algebraMap _ K a = x :=
      (exists_algebraMap_localizationAtPrime_iff v x).2 ⟨y, hy⟩
    refine isIntegral_of_exists_lift (Localization.AtPrime v.asIdeal)
      (hcoeff (y := V.a₁) (by simpa [baseChange] using (congrArg WeierstrassCurve.a₁ hV).symm))
      (hcoeff (y := V.a₂) (by simpa [baseChange] using (congrArg WeierstrassCurve.a₂ hV).symm))
      (hcoeff (y := V.a₃) (by simpa [baseChange] using (congrArg WeierstrassCurve.a₃ hV).symm))
      (hcoeff (y := V.a₄) (by simpa [baseChange] using (congrArg WeierstrassCurve.a₄ hV).symm))
      (hcoeff (y := V.a₆) (by simpa [baseChange] using (congrArg WeierstrassCurve.a₆ hV).symm))
  · intro hI
    exact IsIntegral.baseChange (algebraMap_comp_localization_adicCompletionIntegers v) W

/-- An equation integral over `Localization.AtPrime v.asIdeal` becomes integral over
`v.adicCompletionIntegers K` upon base change to `v.adicCompletion K`. -/
instance isIntegral_adicCompletionIntegers_baseChange (W : WeierstrassCurve K)
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isIntegral_adicCompletionIntegers_baseChange_iff v W).2 ‹_›

/- The discrete-valuation-ring valuations of `O_v` and `R_v` agree along `K → K_v`. -/
private theorem valuation_maximalIdeal_adicCompletionIntegers_algebraMap (z : K) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
        (v.adicCompletion K) (algebraMap K (v.adicCompletion K) z) =
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K z := by
  rw [v.valuation_maximalIdeal_adicCompletionIntegers,
    v.valuation_maximalIdeal_localizationAtPrime, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, v.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]

/- A uniformiser of `R_v` maps to a uniformiser of `O_v`, spanning its maximal ideal. -/
private theorem maximalIdeal_adicCompletionIntegers_eq_span_and_irreducible
    {ϖ : Localization.AtPrime v.asIdeal} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
        Ideal.span {v.localizationToCompletionIntegers (K := K) ϖ} ∧
      Irreducible (v.localizationToCompletionIntegers (K := K) ϖ) := by
  have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {v.localizationToCompletionIntegers (K := K) ϖ} := by
    rw [← v.maximalIdeal_map_completion (K := K),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  exact ⟨hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax⟩

/- Divisibility by `n`-th powers of a mapped uniformiser is reflected along `R_v → O_v`. -/
private theorem pow_dvd_localizationToCompletionIntegers_iff {ϖ : Localization.AtPrime v.asIdeal}
    (hϖ : Irreducible ϖ) (n : ℕ) (x : Localization.AtPrime v.asIdeal) :
    (v.localizationToCompletionIntegers (K := K) ϖ) ^ n ∣
        v.localizationToCompletionIntegers (K := K) x ↔
      ϖ ^ n ∣ x := by
  set f := v.localizationToCompletionIntegers (K := K)
  obtain ⟨hmax, hfϖ⟩ := maximalIdeal_adicCompletionIntegers_eq_span_and_irreducible (K := K) v hϖ
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow,
    ← Ideal.span_singleton_pow, ← hmax,
    ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  constructor
  · intro hx
    by_contra hnot
    rcases eq_or_ne x 0 with rfl | hx0
    · exact hnot (zero_mem _)
    obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
    have hmn : m < n := by
      by_contra! hle
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hnot
      exact hnot (dvd_mul_of_dvd_right (pow_dvd_pow ϖ hle) _)
    have hfx : f (↑u * ϖ ^ m) = (f ϖ) ^ m * ↑(Units.map f.toMonoidHom u) := by
      rw [map_mul, map_pow, mul_comm]
      rfl
    rw [hfx, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    have hdvd : (f ϖ) ^ n ∣ (f ϖ) ^ m :=
      (Units.isUnit (Units.map f.toMonoidHom u)).dvd_mul_right.mp hx
    exact (pow_dvd_pow_iff hfϖ.ne_zero hfϖ.not_isUnit).mp hdvd |>.not_gt hmn
  · intro hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    exact map_dvd f hx

/-- **Local minimality under `v`-adic completion**: a Weierstrass equation over `K` becomes
minimal over `v.adicCompletionIntegers K` after base change to `v.adicCompletion K` if and only if
it is minimal over `Localization.AtPrime v.asIdeal`. -/
theorem isMinimal_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve K) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  constructor
  · -- Descent: compare valuations of `Δ` along `K → K_v` on changes of variables over `K`.
    intro hmin
    have hI : IsIntegral (Localization.AtPrime v.asIdeal) W :=
      (isIntegral_adicCompletionIntegers_baseChange_iff v W).1 inferInstance
    refine ⟨⟨by simpa using hI, fun C hC hle ↦ ?_⟩⟩
    have : IsIntegral (Localization.AtPrime v.asIdeal) (C • W) := hC
    have hCK : IsIntegral (v.adicCompletionIntegers K)
        (C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) := by
      rw [baseChange_smul_baseChange]
      infer_instance
    have hle' : valuation_Δ_aux (v.adicCompletionIntegers K)
        ((1 : VariableChange (v.adicCompletion K)) • W.baseChange (v.adicCompletion K)) ≤
          valuation_Δ_aux (v.adicCompletionIntegers K)
            (C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) := by
      simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral] at hle ⊢
      rw [baseChange_smul_baseChange, baseChange, baseChange, map_Δ, map_Δ,
        valuation_maximalIdeal_adicCompletionIntegers_algebraMap v,
        valuation_maximalIdeal_adicCompletionIntegers_algebraMap v]
      exact hle
    have hge := hmin.val_Δ_maximal.2 hCK hle'
    simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral] at hge ⊢
    rw [baseChange_smul_baseChange, baseChange, baseChange, map_Δ, map_Δ,
      valuation_maximalIdeal_adicCompletionIntegers_algebraMap v,
      valuation_maximalIdeal_adicCompletionIntegers_algebraMap v] at hge
    exact hge
  · -- Ascent: approximate any Step-11 witness in `O_v` by elements of `R` modulo `𝔪_v ^ 6`.
    intro hmin
    by_cases hΔ : W.Δ = 0
    · refine ⟨⟨by simpa using (inferInstance : IsIntegral (v.adicCompletionIntegers K)
          (W.baseChange (v.adicCompletion K))), fun C hC _ ↦ ?_⟩⟩
      have : IsIntegral (v.adicCompletionIntegers K)
          (C • W.baseChange (v.adicCompletion K)) := hC
      have h0 : (W.baseChange (v.adicCompletion K)).Δ = 0 := by
        rw [baseChange, map_Δ, hΔ, map_zero]
      simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral,
        variableChange_Δ, h0, mul_zero, map_zero, le_refl]
    set R_v := Localization.AtPrime v.asIdeal
    set O_v := v.adicCompletionIntegers K
    set K_v := v.adicCompletion K
    set f := v.localizationToCompletionIntegers (K := K)
    set V₀ := W.integralModel R_v
    have hV₀ : V₀.baseChange K = W := baseChange_integralModel_eq R_v W
    have hV₀Δ : V₀.Δ ≠ 0 := fun h0 ↦ hΔ (by rw [← hV₀, baseChange, map_Δ, h0, map_zero])
    have hVf : (V₀.map f).baseChange K_v = W.baseChange K_v :=
      baseChange_map_integralModel (algebraMap_comp_localization_adicCompletionIntegers v) W
    rw [← hVf]
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R_v
    obtain ⟨hmax, hfϖ⟩ :=
      maximalIdeal_adicCompletionIntegers_eq_span_and_irreducible (K := K) v hϖ
    by_contra hnot
    obtain ⟨r, s, t, h₁, h₂, h₃, h₄, h₆⟩ :=
      exists_variableChange_pow_dvd_a₁_a₂_a₃_a₄_a₆_of_not_isMinimal hfϖ (V₀.map f) hnot
    -- Approximate `r, s, t ∈ O_v` modulo `𝔪_{O_v} ^ 6` by elements of `R`.
    have approx (x : O_v) : ∃ a : R_v,
        f a - x ∈ IsLocalRing.maximalIdeal O_v ^ 6 := by
      obtain ⟨a, ha⟩ := v.exists_valued_sub_le x 6
      refine ⟨algebraMap R R_v a, ?_⟩
      rw [v.localizationToCompletionIntegers_algebraMap, ← neg_sub, neg_mem_iff,
        v.mem_maximalIdeal_pow_iff]
      exact ha
    obtain ⟨r₀, hr₀⟩ := approx r
    obtain ⟨s₀, hs₀⟩ := approx s
    obtain ⟨t₀, ht₀⟩ := approx t
    set C₀ : VariableChange R_v := ⟨1, r₀, s₀, t₀⟩
    set C : VariableChange O_v := ⟨1, r, s, t⟩
    set q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O_v ^ 6)
    have hCq : (C₀.map f).map q = C.map q := by
      ext <;> simp only [VariableChange.map_u, map_one, VariableChange.map_r, VariableChange.map_s,
        VariableChange.map_t, C₀, C]
      exacts [Ideal.Quotient.eq.mpr hr₀, Ideal.Quotient.eq.mpr hs₀, Ideal.Quotient.eq.mpr ht₀]
    have hWq : ((C₀ • V₀).map f).map q = (C • V₀.map f).map q := by
      rw [← map_variableChange, ← map_variableChange, hCq, map_variableChange]
    have hdvd {i : ℕ} (hi : i ≤ 6) {x : R_v} {y : O_v} (hxy : q (f x) = q y)
        (hy : (f ϖ) ^ i ∣ y) : ϖ ^ i ∣ x := by
      rw [← pow_dvd_localizationToCompletionIntegers_iff (K := K) v hϖ i]
      have hsub : f x - y ∈ IsLocalRing.maximalIdeal O_v ^ i :=
        Ideal.pow_le_pow_right hi (Ideal.Quotient.eq.mp hxy)
      have hy' : y ∈ IsLocalRing.maximalIdeal O_v ^ i := by
        rwa [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have hmem : f x ∈ IsLocalRing.maximalIdeal O_v ^ i := by
        simpa only [sub_add_cancel] using add_mem hsub hy'
      rwa [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have hmin₀ : IsMinimal R_v (V₀.baseChange K) := hV₀.symm ▸ hmin
    exact (isMinimal_baseChange_iff_forall_not_pow_dvd_a₁_a₂_a₃_a₄_a₆ hϖ V₀ hV₀Δ).1 hmin₀ C₀
      ⟨pow_one ϖ ▸ hdvd (by decide) (by simpa using congrArg WeierstrassCurve.a₁ hWq)
          (pow_one (f ϖ) ▸ h₁),
        hdvd (by decide) (by simpa using congrArg WeierstrassCurve.a₂ hWq) h₂,
        hdvd (by decide) (by simpa using congrArg WeierstrassCurve.a₃ hWq) h₃,
        hdvd (by decide) (by simpa using congrArg WeierstrassCurve.a₄ hWq) h₄,
        hdvd (le_refl 6) (by simpa using congrArg WeierstrassCurve.a₆ hWq) h₆⟩

/-- An equation minimal over `Localization.AtPrime v.asIdeal` becomes minimal over
`v.adicCompletionIntegers K` upon base change to `v.adicCompletion K`. -/
instance isMinimal_adicCompletionIntegers_baseChange (W : WeierstrassCurve K)
    [IsMinimal (Localization.AtPrime v.asIdeal) W] :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_adicCompletionIntegers_baseChange_iff v W).2 ‹_›

/-- A globally minimal Weierstrass equation over `R` becomes minimal over
`v.adicCompletionIntegers K` at every height-one prime `v`. -/
theorem IsGlobalMinimal.isMinimal_adicCompletionIntegers_baseChange {W : WeierstrassCurve K}
    [W.IsElliptic] (hW : IsGlobalMinimal R W) (v : HeightOneSpectrum R) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  have := hW.isMinimal v
  inferInstance

/-- Global minimality over `R` is equivalent to local minimality over `v.adicCompletionIntegers K`
at every height-one prime `v`. -/
theorem isGlobalMinimal_iff_forall_isMinimal_adicCompletionIntegers (W : WeierstrassCurve K)
    [W.IsElliptic] :
    IsGlobalMinimal R W ↔ ∀ v : HeightOneSpectrum R,
      IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) := by
  simp only [isGlobalMinimal_iff, isMinimal_adicCompletionIntegers_baseChange_iff]

/-- **Completion preserves the local minimal discriminant valuation**: the minimal discriminant
exponent of `W.baseChange (v.adicCompletion K)` over `v.adicCompletionIntegers K` equals that of
`W` over `Localization.AtPrime v.asIdeal`. -/
@[simp]
theorem localMinimalDiscriminantValuation_adicCompletionIntegers (W : WeierstrassCurve K)
    [W.IsElliptic] :
    (W.baseChange (v.adicCompletion K)).localMinimalDiscriminantValuation
        (v.adicCompletionIntegers K) =
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  set R_v := Localization.AtPrime v.asIdeal
  set O_v := v.adicCompletionIntegers K
  set K_v := v.adicCompletion K
  set f := v.localizationToCompletionIntegers (K := K)
  set M := W.minimal R_v
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R_v
  have hCK : C.baseChange K_v • W.baseChange K_v = M.baseChange K_v := by
    rw [baseChange_smul_baseChange, hC]
  have hIM : (M.baseChange K_v).integralModel O_v = (M.integralModel R_v).map f :=
    integralModel_baseChange (algebraMap_comp_localization_adicCompletionIntegers v) M
  have hΔ0 : (M.integralModel R_v).Δ ≠ 0 := integralModel_minimal_Δ_ne_zero R_v W
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R_v
  obtain ⟨-, hfϖ⟩ := maximalIdeal_adicCompletionIntegers_eq_span_and_irreducible (K := K) v hϖ
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hΔ0 hϖ
  have haddVal : addVal O_v (f (M.integralModel R_v).Δ) = addVal R_v (M.integralModel R_v).Δ := by
    rw [hu, map_mul, map_pow, addVal_mul, addVal_mul,
      show f ↑u = ↑(Units.map f.toMonoidHom u) from rfl,
      addVal_eq_zero_of_unit (Units.map f.toMonoidHom u), addVal_eq_zero_of_unit u,
      zero_add, zero_add, addVal_pow, addVal_pow, addVal_uniformizer hfϖ, addVal_uniformizer hϖ]
  have h := (W.baseChange K_v).localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul O_v
    (C.baseChange K_v) hCK
  rw [hIM, map_Δ, haddVal,
    ← W.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul R_v C hC] at h
  exact_mod_cast h

end LocalizationComparison

end WeierstrassCurve

end
