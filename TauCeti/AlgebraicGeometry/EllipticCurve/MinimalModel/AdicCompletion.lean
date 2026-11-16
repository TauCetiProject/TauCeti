/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-!
# Integrality and minimality of Weierstrass equations over adic completions

Let `R` be a Dedekind domain with fraction field `K`, let `v` be a height-one prime of `R`, and
let `W` be a Weierstrass curve over `K`. Global and local invariants over `K` express integrality
and minimality at `v` over the discrete valuation ring `Localization.AtPrime v.asIdeal` inside `K`
(as in `WeierstrassCurve.IsGlobalMinimal`), whereas local completed invariants — formal-group
filtrations, reduction homomorphisms, and completed Tamagawa numbers — consume integrality or
minimality of `W.baseChange (v.adicCompletion K)` over `v.adicCompletionIntegers K` or over the
ring of integers `𝒪[v.adicCompletion K]` of the canonical valuative relation.

This file proves that these notions coincide.

## Main results

* `WeierstrassCurve.isIntegral_integer_adicCompletion_iff` and
  `WeierstrassCurve.isMinimal_integer_adicCompletion_iff`: for a Weierstrass equation over
  `v.adicCompletion K`, integrality and minimality over `𝒪[v.adicCompletion K]` agree with those
  over `v.adicCompletionIntegers K`.
* `WeierstrassCurve.isIntegral_baseChange_adicCompletionIntegers_iff` and
  `WeierstrassCurve.isIntegral_baseChange_integer_adicCompletion_iff`: `W.baseChange K_v` is
  integral over the completed valuation ring if and only if `W` is integral over
  `Localization.AtPrime v.asIdeal`.
* `WeierstrassCurve.isMinimal_baseChange_adicCompletionIntegers_iff` and
  `WeierstrassCurve.isMinimal_baseChange_integer_adicCompletion_iff`: `W.baseChange K_v` is minimal
  over the completed valuation ring if and only if `W` is minimal over
  `Localization.AtPrime v.asIdeal`. Preservation of minimality under completion approximates any
  integralising change of variables over `K_v` by one over `K` using the density of `K` in `K_v`.
* `WeierstrassCurve.IsGlobalMinimal.isMinimal_baseChange_adicCompletionIntegers` and
  `WeierstrassCurve.IsGlobalMinimal.isMinimal_baseChange_integer_adicCompletion`: a globally
  minimal equation over `R` remains minimal after base change to every adic completion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1 and VIII.8.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing ValuativeRel
open scoped WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The two valuation-ring spellings on an adic completion -/

/-- Integrality over `𝒪[v.adicCompletion K]` agrees with integrality over
`v.adicCompletionIntegers K`. -/
theorem isIntegral_integer_adicCompletion_iff (v : HeightOneSpectrum R)
    (V : WeierstrassCurve (v.adicCompletion K)) :
    IsIntegral 𝒪[v.adicCompletion K] V ↔ IsIntegral (v.adicCompletionIntegers K) V := by
  -- Stating this for every valuation subring `T` equal to `v.adicCompletionIntegers K` lets
  -- `integer_eq_adicCompletionIntegers` be substituted. The coercion of `valuationSubring` to a
  -- type is by definition that of `Valuation.integer`, which is `𝒪[v.adicCompletion K]`.
  suffices ∀ (T : ValuationSubring (v.adicCompletion K)),
      v.adicCompletionIntegers K = T →
        (IsIntegral T V ↔ IsIntegral (v.adicCompletionIntegers K) V) by
    exact this (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
      (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)
  rintro T rfl
  rfl

/-- Minimality over `𝒪[v.adicCompletion K]` agrees with minimality over
`v.adicCompletionIntegers K`. -/
theorem isMinimal_integer_adicCompletion_iff (v : HeightOneSpectrum R)
    (V : WeierstrassCurve (v.adicCompletion K)) :
    IsMinimal 𝒪[v.adicCompletion K] V ↔ IsMinimal (v.adicCompletionIntegers K) V := by
  -- As in `isIntegral_integer_adicCompletion_iff`, the coercion of `valuationSubring` to a type is
  -- definitionally `Valuation.integer`, i.e. `𝒪[v.adicCompletion K]`.
  suffices ∀ (T : ValuationSubring (v.adicCompletion K)) [IsDiscreteValuationRing T],
      v.adicCompletionIntegers K = T →
        (IsMinimal T V ↔ IsMinimal (v.adicCompletionIntegers K) V) by
    have hR : IsDiscreteValuationRing
        (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
    exact this (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
      (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)
  rintro T _ rfl
  rfl

/-! ### Integrality over `Localization.AtPrime` and the adic completion -/

/-- **Integrality of a base change to the adic completion.** A Weierstrass equation over `K`
becomes integral over `v.adicCompletionIntegers K` after base change to `v.adicCompletion K` if and
only if it is integral over `Localization.AtPrime v.asIdeal`. -/
@[simp]
theorem isIntegral_baseChange_adicCompletionIntegers_iff (v : HeightOneSpectrum R)
    (W : WeierstrassCurve K) :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsIntegral (Localization.AtPrime v.asIdeal) W := by
  constructor
  · intro hI
    let V := integralModel (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K))
    have hcoeff (a : K)
        (ha : IsLocalization.IsInteger (v.adicCompletionIntegers K)
          (algebraMap K (v.adicCompletion K) a)) :
        IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) a :=
      (v.isInteger_adicCompletionIntegers_algebraMap_iff a).mp ha
    exact isIntegral_of_exists_lift _
      (hcoeff W.a₁ ⟨V.a₁, by rw [integralModel_a₁_eq, baseChange, map_a₁]⟩)
      (hcoeff W.a₂ ⟨V.a₂, by rw [integralModel_a₂_eq, baseChange, map_a₂]⟩)
      (hcoeff W.a₃ ⟨V.a₃, by rw [integralModel_a₃_eq, baseChange, map_a₃]⟩)
      (hcoeff W.a₄ ⟨V.a₄, by rw [integralModel_a₄_eq, baseChange, map_a₄]⟩)
      (hcoeff W.a₆ ⟨V.a₆, by rw [integralModel_a₆_eq, baseChange, map_a₆]⟩)
  · intro hI
    let U := integralModel (Localization.AtPrime v.asIdeal) W
    have hcoeff (a : K) (ha : IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) a) :
        IsLocalization.IsInteger (v.adicCompletionIntegers K)
          (algebraMap K (v.adicCompletion K) a) :=
      (v.isInteger_adicCompletionIntegers_algebraMap_iff a).mpr ha
    exact isIntegral_of_exists_lift _
      (by rw [baseChange, map_a₁]; exact hcoeff W.a₁ ⟨U.a₁, integralModel_a₁_eq _ W⟩)
      (by rw [baseChange, map_a₂]; exact hcoeff W.a₂ ⟨U.a₂, integralModel_a₂_eq _ W⟩)
      (by rw [baseChange, map_a₃]; exact hcoeff W.a₃ ⟨U.a₃, integralModel_a₃_eq _ W⟩)
      (by rw [baseChange, map_a₄]; exact hcoeff W.a₄ ⟨U.a₄, integralModel_a₄_eq _ W⟩)
      (by rw [baseChange, map_a₆]; exact hcoeff W.a₆ ⟨U.a₆, integralModel_a₆_eq _ W⟩)

/-- A Weierstrass equation over `K` becomes integral over `𝒪[v.adicCompletion K]` after base change
to `v.adicCompletion K` if and only if it is integral over `Localization.AtPrime v.asIdeal`. -/
@[simp]
theorem isIntegral_baseChange_integer_adicCompletion_iff (v : HeightOneSpectrum R)
    (W : WeierstrassCurve K) :
    IsIntegral 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) ↔
      IsIntegral (Localization.AtPrime v.asIdeal) W :=
  (isIntegral_integer_adicCompletion_iff v _).trans
    (isIntegral_baseChange_adicCompletionIntegers_iff v W)

/-! ### Minimality over `Localization.AtPrime` and the adic completion -/

/-- Every integralising change of variables over `v.adicCompletion K` can be approximated by a
change of variables over `K` with the same scaling valuation that also keeps `W` integral at `v`. -/
private theorem exists_variableChange_isIntegral_localizationAtPrime_and_valued_u_eq
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K) (C : VariableChange (v.adicCompletion K))
    [IsIntegral (v.adicCompletionIntegers K) (C • W.baseChange (v.adicCompletion K))] :
    ∃ D : VariableChange K, IsIntegral (Localization.AtPrime v.asIdeal) (D • W) ∧
      Valued.v (algebraMap K (v.adicCompletion K) D.u) = Valued.v (C.u : v.adicCompletion K) := by
  set γ : ℤᵐ⁰ := Valued.v (C.u : v.adicCompletion K)
  have hγ : γ ≠ 0 := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).ne_zero_iff.mpr C.u.ne_zero
  have hγ_pos : 0 < γ := zero_lt_iff.mpr hγ
  -- Approximate `C.u`, `C.r`, `C.s`, `C.t` closely enough in `K` for
  -- `isIntegral_smul_of_valuation_sub_le` to transfer integrality from `C` to `D.baseChange K_v`.
  obtain ⟨u₀, hu₀_approx⟩ := v.exists_valued_algebraMap_sub_le (C.u : v.adicCompletion K)
    (mul_ne_zero hγ (WithZero.exp_ne_zero (a := (-1 : ℤ))))
  have hu₀_lt : Valued.v (algebraMap K (v.adicCompletion K) u₀ - C.u) < γ :=
    hu₀_approx.trans_lt <| by
      conv_rhs => rw [← mul_one γ]
      exact mul_lt_mul_of_pos_left (by simp [← WithZero.exp_zero]) hγ_pos
  have hu₀_val : Valued.v (algebraMap K (v.adicCompletion K) u₀) = γ :=
    Valuation.map_eq_of_sub_lt _ hu₀_lt
  have hu₀ : u₀ ≠ 0 := by
    rintro rfl
    exact hγ (by simpa using hu₀_val.symm)
  obtain ⟨r₀, hr₀⟩ := v.exists_valued_algebraMap_sub_le C.r (pow_ne_zero 2 hγ)
  obtain ⟨s₀, hs₀⟩ := v.exists_valued_algebraMap_sub_le C.s hγ
  obtain ⟨t₀, ht₀⟩ := v.exists_valued_algebraMap_sub_le
    (C.t + C.s * (algebraMap K (v.adicCompletion K) r₀ - C.r)) (pow_ne_zero 3 hγ)
  let D : VariableChange K := ⟨Units.mk0 u₀ hu₀, r₀, s₀, t₀⟩
  have hDInt : IsIntegral (v.adicCompletionIntegers K)
      (D.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) :=
    isIntegral_smul_of_valuation_sub_le (adicCompletionIntegers.integers K v)
      (W.baseChange (v.adicCompletion K)) (D.baseChange (v.adicCompletion K)) C
      (by simp [D, VariableChange.baseChange, hu₀_val, γ])
      (by simpa [D, VariableChange.baseChange] using hr₀)
      (by simpa [D, VariableChange.baseChange] using hs₀)
      (by simpa [D, VariableChange.baseChange, sub_sub] using ht₀)
  rw [baseChange_smul_baseChange, isIntegral_baseChange_adicCompletionIntegers_iff] at hDInt
  exact ⟨D, hDInt, hu₀_val⟩

/-- The `v`-adic discriminant valuation of a `K`-equation matches the completed discriminant
valuation of its base change. -/
private theorem valuation_maximalIdeal_adicCompletionIntegers_baseChange_Δ
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K) :
    (maximalIdeal (v.adicCompletionIntegers K)).valuation (v.adicCompletion K)
        (W.baseChange (v.adicCompletion K)).Δ =
      (maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K W.Δ := by
  simp [v.valuation_maximalIdeal_adicCompletionIntegers,
    v.valuation_maximalIdeal_localizationAtPrime, baseChange, algebraMap_adicCompletion]

/-- **Minimality of a base change to the adic completion.** A Weierstrass equation over `K` becomes
minimal over `v.adicCompletionIntegers K` after base change to `v.adicCompletion K` if and only if
it is minimal over `Localization.AtPrime v.asIdeal`. -/
@[simp]
theorem isMinimal_baseChange_adicCompletionIntegers_iff (v : HeightOneSpectrum R)
    (W : WeierstrassCurve K) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  constructor
  · intro hmin
    have hInt : IsIntegral (Localization.AtPrime v.asIdeal) W :=
      (isIntegral_baseChange_adicCompletionIntegers_iff v W).mp inferInstance
    refine ⟨⟨by simpa using hInt, fun {C} hC _ ↦ ?_⟩⟩
    dsimp only at hC ⊢
    have hC_comp : IsIntegral (v.adicCompletionIntegers K)
        (C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) := by
      rw [baseChange_smul_baseChange]
      exact (isIntegral_baseChange_adicCompletionIntegers_iff v (C • W)).mpr hC
    rw [← Subtype.coe_le_coe, one_smul,
      valuation_Δ_aux_eq_of_isIntegral (Localization.AtPrime v.asIdeal) (C • W),
      valuation_Δ_aux_eq_of_isIntegral (Localization.AtPrime v.asIdeal) W,
      ← valuation_maximalIdeal_adicCompletionIntegers_baseChange_Δ v (C • W),
      ← valuation_maximalIdeal_adicCompletionIntegers_baseChange_Δ v W,
      ← baseChange_smul_baseChange]
    exact valuation_Δ_le_of_isMinimal_smul (v.adicCompletionIntegers K)
      (C.baseChange (v.adicCompletion K)) rfl
  · intro hmin
    have hInt : IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
      (isIntegral_baseChange_adicCompletionIntegers_iff v W).mpr inferInstance
    refine ⟨⟨by simpa using hInt, fun {C} hC _ ↦ ?_⟩⟩
    dsimp only at hC ⊢
    let _ : IsIntegral (v.adicCompletionIntegers K) (C • W.baseChange (v.adicCompletion K)) := hC
    obtain ⟨D, hDInt, hDu⟩ :=
      exists_variableChange_isIntegral_localizationAtPrime_and_valued_u_eq v W C
    let _ := hDInt
    rw [← Subtype.coe_le_coe, one_smul,
      valuation_Δ_aux_eq_of_isIntegral (v.adicCompletionIntegers K)
        (C • W.baseChange (v.adicCompletion K)),
      valuation_Δ_aux_eq_of_isIntegral (v.adicCompletionIntegers K)
        (W.baseChange (v.adicCompletion K))]
    have hEqΔ : (maximalIdeal (v.adicCompletionIntegers K)).valuation (v.adicCompletion K)
        (C • W.baseChange (v.adicCompletion K)).Δ =
        (maximalIdeal (v.adicCompletionIntegers K)).valuation (v.adicCompletion K)
          ((D • W).baseChange (v.adicCompletion K)).Δ := by
      rw [← baseChange_smul_baseChange, v.valuation_maximalIdeal_adicCompletionIntegers,
        v.valuation_maximalIdeal_adicCompletionIntegers, variableChange_Δ, variableChange_Δ]
      simp [VariableChange.baseChange, hDu]
    rw [hEqΔ, valuation_maximalIdeal_adicCompletionIntegers_baseChange_Δ v (D • W),
      valuation_maximalIdeal_adicCompletionIntegers_baseChange_Δ v W]
    exact valuation_Δ_le_of_isMinimal_smul (Localization.AtPrime v.asIdeal) D rfl

/-- A Weierstrass equation over `K` becomes minimal over `𝒪[v.adicCompletion K]` after base change
to `v.adicCompletion K` if and only if it is minimal over `Localization.AtPrime v.asIdeal`. -/
@[simp]
theorem isMinimal_baseChange_integer_adicCompletion_iff (v : HeightOneSpectrum R)
    (W : WeierstrassCurve K) :
    IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W :=
  (isMinimal_integer_adicCompletion_iff v _).trans
    (isMinimal_baseChange_adicCompletionIntegers_iff v W)

/-- A globally minimal equation over `R` remains minimal over `v.adicCompletionIntegers K` at every
height-one prime `v`. -/
theorem IsGlobalMinimal.isMinimal_baseChange_adicCompletionIntegers {W : WeierstrassCurve K}
    [W.IsElliptic] (h : IsGlobalMinimal R W) (v : HeightOneSpectrum R) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_baseChange_adicCompletionIntegers_iff v W).mpr (h.isMinimal v)

/-- A globally minimal equation over `R` remains minimal over `𝒪[v.adicCompletion K]` at every
height-one prime `v`. -/
theorem IsGlobalMinimal.isMinimal_baseChange_integer_adicCompletion {W : WeierstrassCurve K}
    [W.IsElliptic] (h : IsGlobalMinimal R W) (v : HeightOneSpectrum R) :
    IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_baseChange_integer_adicCompletion_iff v W).mpr (h.isMinimal v)

end WeierstrassCurve

end
