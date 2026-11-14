/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
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
  `Localization.AtPrime v.asIdeal`. Descent of minimality from `Localization.AtPrime v.asIdeal` to
  the completion approximates any integralising change of variables over `K_v` by one over `K`
  using the density of `K` in `K_v`.
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
  -- Both rings coerce from equal `ValuationSubring`s of `v.adicCompletion K`.
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
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]]
    (V : WeierstrassCurve (v.adicCompletion K)) :
    IsMinimal 𝒪[v.adicCompletion K] V ↔ IsMinimal (v.adicCompletionIntegers K) V := by
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

/-- An element of `K` lifts to `v.adicCompletionIntegers K` in `v.adicCompletion K` if and only if
it lifts to `Localization.AtPrime v.asIdeal` in `K`. -/
private theorem exists_lift_adicCompletionIntegers_iff (v : HeightOneSpectrum R) (x : K) :
    (∃ y : v.adicCompletionIntegers K,
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y =
          algebraMap K (v.adicCompletion K) x) ↔
      ∃ r : Localization.AtPrime v.asIdeal,
        algebraMap (Localization.AtPrime v.asIdeal) K r = x := by
  have hv := v.integers_valuation_of_isLocalizationAtPrime (Localization.AtPrime v.asIdeal) (K := K)
  have hval : Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
    rw [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply]
  constructor
  · rintro ⟨y, hy⟩
    refine hv.exists_of_le_one ?_
    rw [← hval, ← hy]
    exact (mem_adicCompletionIntegers R K v).mp y.2
  · rintro ⟨r, rfl⟩
    refine ⟨⟨algebraMap K (v.adicCompletion K)
      (algebraMap (Localization.AtPrime v.asIdeal) K r), ?_⟩, rfl⟩
    rw [mem_adicCompletionIntegers, hval]
    exact hv.map_le_one r

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
    have hcoeff (a : K) (ha : ∃ y : v.adicCompletionIntegers K,
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y =
          algebraMap K (v.adicCompletion K) a) :
        ∃ r : Localization.AtPrime v.asIdeal,
          algebraMap (Localization.AtPrime v.asIdeal) K r = a :=
      (exists_lift_adicCompletionIntegers_iff v a).mp ha
    exact isIntegral_of_exists_lift _
      (hcoeff W.a₁ ⟨V.a₁, (integralModel_a₁_eq _ (W.baseChange (v.adicCompletion K))).trans rfl⟩)
      (hcoeff W.a₂ ⟨V.a₂, (integralModel_a₂_eq _ (W.baseChange (v.adicCompletion K))).trans rfl⟩)
      (hcoeff W.a₃ ⟨V.a₃, (integralModel_a₃_eq _ (W.baseChange (v.adicCompletion K))).trans rfl⟩)
      (hcoeff W.a₄ ⟨V.a₄, (integralModel_a₄_eq _ (W.baseChange (v.adicCompletion K))).trans rfl⟩)
      (hcoeff W.a₆ ⟨V.a₆, (integralModel_a₆_eq _ (W.baseChange (v.adicCompletion K))).trans rfl⟩)
  · intro hI
    have hcoeff (a : K) (ha : ∃ r : Localization.AtPrime v.asIdeal,
        algebraMap (Localization.AtPrime v.asIdeal) K r = a) :
        ∃ y : v.adicCompletionIntegers K,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y =
            algebraMap K (v.adicCompletion K) a :=
      (exists_lift_adicCompletionIntegers_iff v a).mpr ha
    exact isIntegral_of_exists_lift _
      (by simpa [baseChange] using hcoeff W.a₁ ⟨(integralModel _ W).a₁, integralModel_a₁_eq _ W⟩)
      (by simpa [baseChange] using hcoeff W.a₂ ⟨(integralModel _ W).a₂, integralModel_a₂_eq _ W⟩)
      (by simpa [baseChange] using hcoeff W.a₃ ⟨(integralModel _ W).a₃, integralModel_a₃_eq _ W⟩)
      (by simpa [baseChange] using hcoeff W.a₄ ⟨(integralModel _ W).a₄, integralModel_a₄_eq _ W⟩)
      (by simpa [baseChange] using hcoeff W.a₆ ⟨(integralModel _ W).a₆, integralModel_a₆_eq _ W⟩)

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

/-- Every element of `v.adicCompletion K` can be approximated within any nonzero valuation bound by
an element of `K`. -/
private theorem exists_valued_algebraMap_sub_le (v : HeightOneSpectrum R)
    (x : v.adicCompletion K) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ y : K, Valued.v (algebraMap K (v.adicCompletion K) y - x) ≤ γ := by
  have hU : IsOpen {z : v.adicCompletion K | Valued.v (z - x) ≤ γ} :=
    (v.isOpen_setOf_valued_le (K := K) hγ).preimage (continuous_sub_right x)
  exact (v.denseRange_algebraMap K).exists_mem_open hU ⟨x, by simp⟩

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
  -- Approximate `C.u`, `C.r`, `C.s`, `C.t` closely enough in `K` that `D.baseChange K_v * C⁻¹`
  -- has `u⁻¹`, `r`, `s`, `t` in `v.adicCompletionIntegers K`.
  obtain ⟨u₀, hu₀_approx⟩ := exists_valued_algebraMap_sub_le v (C.u : v.adicCompletion K)
    (mul_ne_zero hγ (WithZero.exp_ne_zero (a := (-1 : ℤ))))
  have hu₀_lt : Valued.v (algebraMap K (v.adicCompletion K) u₀ - C.u) < γ :=
    hu₀_approx.trans_lt <| by
      conv_rhs => rw [← mul_one γ]
      exact mul_lt_mul_of_pos_left (by simp [← WithZero.exp_zero]) hγ_pos
  have hu₀_val : Valued.v (algebraMap K (v.adicCompletion K) u₀) = γ := by
    have heq : algebraMap K (v.adicCompletion K) u₀ =
        (algebraMap K (v.adicCompletion K) u₀ - C.u) + C.u := (sub_add_cancel _ _).symm
    rw [heq, Valuation.map_add_of_distinct_val _ hu₀_lt.ne, max_eq_right hu₀_lt.le]
  have hu₀ : u₀ ≠ 0 := by
    rintro rfl
    exact hγ (by simpa using hu₀_val.symm)
  obtain ⟨r₀, hr₀⟩ := exists_valued_algebraMap_sub_le v C.r (pow_ne_zero 2 hγ)
  obtain ⟨s₀, hs₀⟩ := exists_valued_algebraMap_sub_le v C.s hγ
  obtain ⟨t₀, ht₀⟩ := exists_valued_algebraMap_sub_le v
    (C.t + C.s * (algebraMap K (v.adicCompletion K) r₀ - C.r)) (pow_ne_zero 3 hγ)
  let D : VariableChange K := ⟨Units.mk0 u₀ hu₀, r₀, s₀, t₀⟩
  let B : VariableChange (v.adicCompletion K) := D.baseChange (v.adicCompletion K) * C⁻¹
  have hlift (z : v.adicCompletion K) (hz : Valued.v z ≤ 1) :
      ∃ y : v.adicCompletionIntegers K,
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y = z :=
    ⟨⟨z, (mem_adicCompletionIntegers R K v).mpr hz⟩, rfl⟩
  have hBu : Valued.v (↑B.u⁻¹ : v.adicCompletion K) ≤ 1 := by
    have hBu_eq : (↑B.u⁻¹ : v.adicCompletion K) =
        (C.u : v.adicCompletion K) / algebraMap K (v.adicCompletion K) u₀ := by
      simp [B, D, VariableChange.baseChange, div_eq_mul_inv, mul_comm]
    rw [hBu_eq, map_div₀, hu₀_val, div_self hγ]
  have hBr : Valued.v B.r ≤ 1 := by
    have hBr_eq : B.r =
        (algebraMap K (v.adicCompletion K) r₀ - C.r) / (C.u : v.adicCompletion K) ^ 2 := by
      simp [B, D, VariableChange.mul_inv_r, VariableChange.baseChange, div_eq_mul_inv]
    rw [hBr_eq, map_div₀, map_pow]
    exact (div_le_one₀ (pow_pos hγ_pos 2)).mpr hr₀
  have hBs : Valued.v B.s ≤ 1 := by
    have hBs_eq : B.s =
        (algebraMap K (v.adicCompletion K) s₀ - C.s) / (C.u : v.adicCompletion K) := by
      simp [B, D, VariableChange.mul_inv_s, VariableChange.baseChange, div_eq_mul_inv]
    rw [hBs_eq, map_div₀]
    exact (div_le_one₀ hγ_pos).mpr hs₀
  have hBt : Valued.v B.t ≤ 1 := by
    have hBt_eq : B.t =
        (algebraMap K (v.adicCompletion K) t₀ -
            (C.t + C.s * (algebraMap K (v.adicCompletion K) r₀ - C.r))) /
          (C.u : v.adicCompletion K) ^ 3 := by
      simp [B, D, VariableChange.mul_inv_t, VariableChange.baseChange, div_eq_mul_inv, sub_sub]
    rw [hBt_eq, map_div₀, map_pow]
    exact (div_le_one₀ (pow_pos hγ_pos 3)).mpr ht₀
  have hBInt : IsIntegral (v.adicCompletionIntegers K)
      (B • (C • W.baseChange (v.adicCompletion K))) :=
    isIntegral_smul_of_exists_lift (hlift _ hBu) (hlift _ hBr) (hlift _ hBs) (hlift _ hBt)
  have hBC : B • (C • W.baseChange (v.adicCompletion K)) =
      (D • W).baseChange (v.adicCompletion K) := by
    rw [← mul_smul, show B * C = D.baseChange (v.adicCompletion K) from inv_mul_cancel_right _ _,
      baseChange_smul_baseChange]
  rw [hBC, isIntegral_baseChange_adicCompletionIntegers_iff] at hBInt
  exact ⟨D, hBInt, hu₀_val⟩

/-- The `v`-adic discriminant valuation of a `K`-equation matches the completed discriminant
valuation of its base change. -/
private theorem valuation_maximalIdeal_adicCompletionIntegers_baseChange_Δ
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K) :
    (maximalIdeal (v.adicCompletionIntegers K)).valuation (v.adicCompletion K)
        (W.baseChange (v.adicCompletion K)).Δ =
      (maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K W.Δ := by
  rw [v.valuation_maximalIdeal_adicCompletionIntegers, baseChange, map_Δ,
    algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    Algebra.algebraMap_self_apply, v.valuation_maximalIdeal_localizationAtPrime]

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
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]] (W : WeierstrassCurve K) :
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
    [W.IsElliptic] (h : IsGlobalMinimal R W) (v : HeightOneSpectrum R)
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]] :
    IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_baseChange_integer_adicCompletion_iff v W).mpr (h.isMinimal v)

end WeierstrassCurve

end
