/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Minimal Weierstrass equations over adic completions

Let `O` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of `O`.
The completion `K_v := v.adicCompletion K` carries the valuation ring
`O_v := v.adicCompletionIntegers K`, which coincides as a subring with `𝒪[K_v]`. This file proves
that integrality and minimality of a Weierstrass equation `W` over `K` are unchanged by base
change to `K_v`:

* `WeierstrassCurve.isIntegral_baseChange_adicCompletion_iff`: `W` is integral over `O_v` after
  base change to `K_v` if and only if `W` is integral over `Localization.AtPrime v.asIdeal`.
* `WeierstrassCurve.isMinimal_baseChange_adicCompletion_iff`: `W` is minimal over `O_v` after
  base change to `K_v` if and only if `W` is minimal over `Localization.AtPrime v.asIdeal`.
* `WeierstrassCurve.isMinimal_adicCompletionIntegers_iff_isMinimal_integer`: minimality over `O_v`
  and over the valuative integer ring `𝒪[K_v]` are equivalent.
* `WeierstrassCurve.isMinimal_baseChange_adicCompletion_integer_iff`: the combined equivalence
  between `𝒪[K_v]` and `Localization.AtPrime v.asIdeal`.
* `WeierstrassCurve.IsGlobalMinimal.isMinimal_baseChange_adicCompletion` and
  `WeierstrassCurve.IsGlobalMinimal.isMinimal_baseChange_adicCompletion_integer`: a globally
  minimal equation over `O` remains minimal at every adic completion.

The nontrivial direction approximates a change of variables `C` over `K_v` making `C • W_v`
integral by a change of variables `C'` over `K` using density of `K` in `K_v` so that
`C'_v * C⁻¹` is defined over `O_v` and has the same scaling valuation as `C`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel

variable {O : Type*} [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  (v : HeightOneSpectrum O)

/-- A Weierstrass equation over `K` is integral over `O_v` after base change to `K_v` if and only
if it is integral over the localization `Localization.AtPrime v.asIdeal`. -/
theorem isIntegral_baseChange_adicCompletion_iff (W : WeierstrassCurve K) :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsIntegral (Localization.AtPrime v.asIdeal) W := by
  set K_v := v.adicCompletion K
  set O_v := v.adicCompletionIntegers K
  have hloc := v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal) (K := K)
  have hcomp := adicCompletionIntegers.integers K v
  have hval (x : K) :
      (∃ r : O_v, algebraMap O_v K_v r = algebraMap K K_v x) ↔
      (∃ r : Localization.AtPrime v.asIdeal,
        algebraMap (Localization.AtPrime v.asIdeal) K r = x) := by
    have h1 : (∃ r : O_v, algebraMap O_v K_v r = algebraMap K K_v x) ↔
        Valued.v (algebraMap K K_v x) ≤ 1 :=
      ⟨fun ⟨r, hr⟩ ↦ hr ▸ hcomp.map_le_one r, fun hx ↦ hcomp.exists_of_le_one hx⟩
    have h2 : (∃ r : Localization.AtPrime v.asIdeal,
        algebraMap (Localization.AtPrime v.asIdeal) K r = x) ↔ v.valuation K x ≤ 1 :=
      ⟨fun ⟨r, hr⟩ ↦ hr ▸ hloc.map_le_one r, fun hx ↦ hloc.exists_of_le_one hx⟩
    rw [h1, h2, algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply]
  constructor
  · intro h
    refine isIntegral_of_exists_lift (Localization.AtPrime v.asIdeal)
      ((hval W.a₁).1 ⟨(integralModel O_v (W.baseChange K_v)).a₁,
        by simpa [baseChange] using integralModel_a₁_eq O_v (W.baseChange K_v)⟩)
      ((hval W.a₂).1 ⟨(integralModel O_v (W.baseChange K_v)).a₂,
        by simpa [baseChange] using integralModel_a₂_eq O_v (W.baseChange K_v)⟩)
      ((hval W.a₃).1 ⟨(integralModel O_v (W.baseChange K_v)).a₃,
        by simpa [baseChange] using integralModel_a₃_eq O_v (W.baseChange K_v)⟩)
      ((hval W.a₄).1 ⟨(integralModel O_v (W.baseChange K_v)).a₄,
        by simpa [baseChange] using integralModel_a₄_eq O_v (W.baseChange K_v)⟩)
      ((hval W.a₆).1 ⟨(integralModel O_v (W.baseChange K_v)).a₆,
        by simpa [baseChange] using integralModel_a₆_eq O_v (W.baseChange K_v)⟩)
  · intro h
    refine isIntegral_of_exists_lift O_v
      ((hval W.a₁).2 ⟨(integralModel (Localization.AtPrime v.asIdeal) W).a₁,
        integralModel_a₁_eq _ W⟩)
      ((hval W.a₂).2 ⟨(integralModel (Localization.AtPrime v.asIdeal) W).a₂,
        integralModel_a₂_eq _ W⟩)
      ((hval W.a₃).2 ⟨(integralModel (Localization.AtPrime v.asIdeal) W).a₃,
        integralModel_a₃_eq _ W⟩)
      ((hval W.a₄).2 ⟨(integralModel (Localization.AtPrime v.asIdeal) W).a₄,
        integralModel_a₄_eq _ W⟩)
      ((hval W.a₆).2 ⟨(integralModel (Localization.AtPrime v.asIdeal) W).a₆,
        integralModel_a₆_eq _ W⟩)

/-- Every change of variables `C` over `K_v` is approximated by a change of variables `C'` over `K`
with the same scaling valuation such that `C'_v * C⁻¹` descends to `O_v`. -/
private theorem exists_variableChange_approx (C : VariableChange (v.adicCompletion K)) :
    ∃ (C' : VariableChange K) (D₀ : VariableChange (v.adicCompletionIntegers K)),
      Valued.v (algebraMap K (v.adicCompletion K) (C'.u : K)) =
        Valued.v (C.u : v.adicCompletion K) ∧
      D₀.baseChange (v.adicCompletion K) = C'.baseChange (v.adicCompletion K) * C⁻¹ := by
  set K_v := v.adicCompletion K
  have hCu : Valued.v (C.u : K_v) ≠ 0 := (Valuation.ne_zero_iff _).2 C.u.ne_zero
  have hCu_pos : 0 < Valued.v (C.u : K_v) := zero_lt_iff.2 hCu
  have hexp_lt : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  obtain ⟨u', hu'⟩ := v.exists_valued_algebraMap_sub_le (C.u : K_v)
    (mul_ne_zero hCu (WithZero.exp_ne_zero (a := (-1 : ℤ))))
  have hu'_lt : Valued.v (algebraMap K K_v u' - (C.u : K_v)) < Valued.v (C.u : K_v) :=
    hu'.trans_lt (by simpa using mul_lt_mul_of_pos_left hexp_lt hCu_pos)
  have hu'_val : Valued.v (algebraMap K K_v u') = Valued.v (C.u : K_v) := by
    simpa [add_sub_cancel] using Valuation.map_add_eq_of_lt_left Valued.v hu'_lt
  have hu'_ne : u' ≠ 0 := fun h ↦ hCu (by rw [← hu'_val, h, map_zero, map_zero])
  obtain ⟨r', hr'⟩ := v.exists_valued_algebraMap_sub_le C.r (pow_ne_zero 2 hCu)
  obtain ⟨s', hs'⟩ := v.exists_valued_algebraMap_sub_le C.s hCu
  obtain ⟨t', ht'⟩ := v.exists_valued_algebraMap_sub_le
    (C.t + C.s * (algebraMap K K_v r' - C.r)) (pow_ne_zero 3 hCu)
  let C' : VariableChange K := ⟨Units.mk0 u' hu'_ne, r', s', t'⟩
  let D : VariableChange K_v := C'.baseChange K_v * C⁻¹
  have hcomp := adicCompletionIntegers.integers K v
  have hDu_val : Valued.v (D.u : K_v) = 1 := by
    have h : (D.u : K_v) = algebraMap K K_v u' / (C.u : K_v) := by
      simp [D, C', VariableChange.baseChange, VariableChange.mul_inv_u, div_eq_mul_inv]
    rw [h, map_div₀, hu'_val, div_self hCu]
  obtain ⟨u₀, hu₀⟩ := hcomp.exists_of_le_one (r := (D.u : K_v)) hDu_val.le
  obtain ⟨r₀, hr₀⟩ := hcomp.exists_of_le_one (r := D.r) <| by
    have h : D.r = (algebraMap K K_v r' - C.r) / (C.u : K_v) ^ 2 := by
      simp [D, C', VariableChange.baseChange, VariableChange.mul_inv_r, div_eq_mul_inv]
    rw [h, map_div₀, map_pow]; exact (div_le_one₀ (pow_pos hCu_pos 2)).2 hr'
  obtain ⟨s₀, hs₀⟩ := hcomp.exists_of_le_one (r := D.s) <| by
    have h : D.s = (algebraMap K K_v s' - C.s) / (C.u : K_v) := by
      simp [D, C', VariableChange.baseChange, VariableChange.mul_inv_s, div_eq_mul_inv]
    rw [h, map_div₀]; exact (div_le_one₀ hCu_pos).2 hs'
  obtain ⟨t₀, ht₀⟩ := hcomp.exists_of_le_one (r := D.t) <| by
    have h : D.t = (algebraMap K K_v t' - (C.t + C.s * (algebraMap K K_v r' - C.r))) /
        (C.u : K_v) ^ 3 := by
      simp [D, C', VariableChange.baseChange, VariableChange.mul_inv_t, div_eq_mul_inv,
        sub_add_eq_sub_sub]
    rw [h, map_div₀, map_pow]; exact (div_le_one₀ (pow_pos hCu_pos 3)).2 ht'
  refine ⟨C', ⟨(hcomp.isUnit_of_one' (by rw [hu₀, hDu_val])).unit, r₀, s₀, t₀⟩, hu'_val, ?_⟩
  exact VariableChange.ext (Units.ext hu₀) hr₀ hs₀ ht₀

/-- **A Weierstrass equation over `K` is minimal over the completed valuation ring `O_v` if and
only if it is minimal over the localization `Localization.AtPrime v.asIdeal`.** -/
theorem isMinimal_baseChange_adicCompletion_iff (W : WeierstrassCurve K) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  have hvalK (x : K) : Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
    rw [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply]
  constructor
  · intro _
    have hWint : IsIntegral (Localization.AtPrime v.asIdeal) W :=
      (isIntegral_baseChange_adicCompletion_iff v W).1 inferInstance
    refine ⟨⟨by simpa using hWint, fun {C} hC _ ↦ ?_⟩⟩
    have : IsIntegral (v.adicCompletionIntegers K)
        (C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) := by
      rw [baseChange_smul_baseChange]
      exact (isIntegral_baseChange_adicCompletion_iff v (C • W)).2 hC
    have hle := valuation_Δ_le_of_isMinimal_smul (v.adicCompletionIntegers K)
      (C.baseChange (v.adicCompletion K)) (W₁ := W.baseChange (v.adicCompletion K)) rfl
    rw [v.valuation_maximalIdeal_adicCompletionIntegers,
      v.valuation_maximalIdeal_adicCompletionIntegers,
      baseChange_smul_baseChange, baseChange, baseChange, map_Δ, map_Δ, hvalK, hvalK] at hle
    simpa [one_smul, ← Subtype.coe_le_coe,
      valuation_Δ_aux_eq_of_isIntegral (Localization.AtPrime v.asIdeal) (C • W),
      valuation_Δ_aux_eq_of_isIntegral (Localization.AtPrime v.asIdeal) W,
      v.valuation_maximalIdeal_localizationAtPrime] using hle
  · intro _
    have hWint : IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
      (isIntegral_baseChange_adicCompletion_iff v W).2 inferInstance
    refine ⟨⟨by simpa using hWint, fun {C} hC _ ↦ ?_⟩⟩
    obtain ⟨C', D₀, hu', hD₀⟩ := exists_variableChange_approx v C
    have hC'comp : IsIntegral (v.adicCompletionIntegers K)
        ((C' • W).baseChange (v.adicCompletion K)) := by
      have hCW : C'.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K) =
          D₀.baseChange (v.adicCompletion K) • (C • W.baseChange (v.adicCompletion K)) := by
        rw [hD₀, smul_smul, inv_mul_cancel_right]
      rw [← baseChange_smul_baseChange, hCW]
      exact ⟨D₀ • integralModel (v.adicCompletionIntegers K)
          (C • W.baseChange (v.adicCompletion K)), by
        rw [← baseChange_smul_baseChange, baseChange_integralModel_eq]⟩
    have : IsIntegral (Localization.AtPrime v.asIdeal) (C' • W) :=
      (isIntegral_baseChange_adicCompletion_iff v (C' • W)).1 hC'comp
    have hle := valuation_Δ_le_of_isMinimal_smul (Localization.AtPrime v.asIdeal) C' (W₁ := W) rfl
    rw [v.valuation_maximalIdeal_localizationAtPrime,
      v.valuation_maximalIdeal_localizationAtPrime] at hle
    have hΔ_eq : Valued.v (C • W.baseChange (v.adicCompletion K)).Δ = v.valuation K (C' • W).Δ := by
      rw [← hvalK, ← map_Δ, ← baseChange, ← baseChange_smul_baseChange,
        variableChange_Δ, variableChange_Δ, map_mul, map_mul, map_pow, map_pow,
        Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀]
      have huC' : ((C'.baseChange (v.adicCompletion K)).u : v.adicCompletion K) =
          algebraMap K (v.adicCompletion K) (C'.u : K) := rfl
      rw [huC', hu']
    simp only [one_smul, ← Subtype.coe_le_coe,
      valuation_Δ_aux_eq_of_isIntegral (v.adicCompletionIntegers K)
        (C • W.baseChange (v.adicCompletion K)),
      valuation_Δ_aux_eq_of_isIntegral (v.adicCompletionIntegers K)
        (W.baseChange (v.adicCompletion K)),
      v.valuation_maximalIdeal_adicCompletionIntegers]
    rw [hΔ_eq, baseChange, map_Δ, hvalK]
    exact hle

/-- Minimality over `v.adicCompletionIntegers K` is equivalent to minimality over the valuative
ring of integers `𝒪[v.adicCompletion K]`, since both are the same valuation subring of `K_v`. -/
theorem isMinimal_adicCompletionIntegers_iff_isMinimal_integer
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]]
    (W : WeierstrassCurve (v.adicCompletion K)) :
    IsMinimal (v.adicCompletionIntegers K) W ↔ IsMinimal 𝒪[v.adicCompletion K] W := by
  suffices ∀ (T : ValuationSubring (v.adicCompletion K)) [IsDiscreteValuationRing T],
      v.adicCompletionIntegers K = T →
        (IsMinimal (v.adicCompletionIntegers K) W ↔ IsMinimal T W) by
    have hR : IsDiscreteValuationRing
        (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
    exact this (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
      (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)
  rintro T _ rfl
  exact Iff.rfl

/-- A Weierstrass equation over `K` is minimal over `𝒪[K_v]` after base change to `K_v` if and
only if it is minimal over `Localization.AtPrime v.asIdeal`. -/
theorem isMinimal_baseChange_adicCompletion_integer_iff
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]] (W : WeierstrassCurve K) :
    IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W :=
  (isMinimal_adicCompletionIntegers_iff_isMinimal_integer v _).symm.trans
    (isMinimal_baseChange_adicCompletion_iff v W)

/-- A globally minimal equation over `O` remains minimal over `v.adicCompletionIntegers K` after
base change to any adic completion `v.adicCompletion K`. -/
theorem IsGlobalMinimal.isMinimal_baseChange_adicCompletion {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : IsGlobalMinimal O W) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_baseChange_adicCompletion_iff v W).2 (hW.isMinimal v)

/-- A globally minimal equation over `O` remains minimal over `𝒪[v.adicCompletion K]` after base
change to any adic completion `v.adicCompletion K`. -/
theorem IsGlobalMinimal.isMinimal_baseChange_adicCompletion_integer {W : WeierstrassCurve K}
    [W.IsElliptic] [IsDiscreteValuationRing 𝒪[v.adicCompletion K]]
    (hW : IsGlobalMinimal O W) :
    IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_baseChange_adicCompletion_integer_iff v W).2 (hW.isMinimal v)

end WeierstrassCurve
