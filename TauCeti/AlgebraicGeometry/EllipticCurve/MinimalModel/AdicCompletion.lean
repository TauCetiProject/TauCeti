/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Additive
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Localization

/-!
# Minimal equations under adic completion

Let `O` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of `O`.
A Weierstrass equation `W` over `K` has two natural local notions of integrality and minimality at
`v`: over the localization `Oᵥ = Localization.AtPrime v.asIdeal` inside `K`, and after base change
to the completion `K_v` over its ring of integers `O_v = v.adicCompletionIntegers K` (or, when the
residue field is finite, over `𝒪[K_v]`).

This file proves that both notions agree, without any residue-characteristic or perfectness
hypothesis:

* Integrality agrees coefficient by coefficient because `Valued.v` on `K_v` restricts to
  `v.valuation K` on `K`.
* Minimality agrees by Step 11 of Tate's algorithm
  (`WeierstrassCurve.isMinimal_baseChange_iff_forall_not_pow_dvd_a₁_a₂_a₃_a₄_a₆`): the canonical
  map `Oᵥ → O_v` carries a uniformizer to a uniformizer, reflects divisibility by its powers, and
  has dense image modulo `𝔪_v ^ 6`, so an obstruction to minimality over `O_v` can be approximated
  by one over `Oᵥ`.

Consequently, globally minimal equations over `O` remain minimal at every adic completion, and the
local minimal discriminant valuation is unchanged by completion.

## Main results

* `WeierstrassCurve.isIntegral_adicCompletionIntegers_baseChange_iff`: `W.baseChange K_v` is
  integral over `O_v` if and only if `W` is integral over `Oᵥ`.
* `WeierstrassCurve.isMinimal_adicCompletionIntegers_baseChange_iff`: for elliptic `W`,
  `W.baseChange K_v` is minimal over `O_v` if and only if `W` is minimal over `Oᵥ`.
* `WeierstrassCurve.isMinimal_adicCompletion_baseChange_iff`: when `O ⧸ v` is finite, minimality at
  `𝒪[K_v]` agrees with minimality at `Oᵥ`.
* `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletionIntegers` and
  `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletion`: a globally minimal equation over `O`
  remains minimal over `O_v` and `𝒪[K_v]`.
* `WeierstrassCurve.localMinimalDiscriminantValuation_baseChange_adicCompletion`: completion
  preserves the local minimal discriminant valuation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1, VII.2, VIII.8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing ValuativeRel WithZero

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  (v : HeightOneSpectrum O)

private theorem algebraMap_comp_localizationToCompletionIntegers :
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).comp
        (v.localizationToCompletionIntegers (K := K)) =
      (algebraMap K (v.adicCompletion K)).comp
        (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  refine IsLocalization.ringHom_ext v.asIdeal.primeCompl (RingHom.ext fun x ↦ ?_)
  simp only [RingHom.comp_apply, localizationToCompletionIntegers_algebraMap,
    ← IsScalarTower.algebraMap_apply O (Localization.AtPrime v.asIdeal) K]
  exact IsScalarTower.algebraMap_apply O (v.adicCompletionIntegers K) (v.adicCompletion K) x

private theorem isInteger_adicCompletionIntegers_algebraMap_iff (a : K) :
    (∃ r : v.adicCompletionIntegers K,
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r =
          algebraMap K (v.adicCompletion K) a) ↔
      ∃ r : Localization.AtPrime v.asIdeal,
        algebraMap (Localization.AtPrime v.asIdeal) K r = a := by
  have hv₁ := adicCompletionIntegers.integers K v
  have hv₂ := v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal) (K := K)
  have h₁ : (∃ r : v.adicCompletionIntegers K,
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r =
        algebraMap K (v.adicCompletion K) a) ↔
      Valued.v (algebraMap K (v.adicCompletion K) a) ≤ 1 :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ hv₁.map_le_one r, fun h ↦ hv₁.exists_of_le_one h⟩
  have h₂ : (∃ r : Localization.AtPrime v.asIdeal,
      algebraMap (Localization.AtPrime v.asIdeal) K r = a) ↔ v.valuation K a ≤ 1 :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ hv₂.map_le_one r, fun h ↦ hv₂.exists_of_le_one h⟩
  rw [h₁, h₂, algebraMap_adicCompletion, Function.comp_apply,
    valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]

/-- A Weierstrass equation over `K` becomes integral over `O_v` after base change to `K_v` if and
only if it is integral over the localization `Oᵥ`. -/
@[simp]
theorem isIntegral_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve K) :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsIntegral (Localization.AtPrime v.asIdeal) W := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine isIntegral_of_exists_lift (Localization.AtPrime v.asIdeal)
      ((isInteger_adicCompletionIntegers_algebraMap_iff v W.a₁).mp
        ⟨_, (integralModel_a₁_eq _ (W.baseChange (v.adicCompletion K))).trans (by simp)⟩)
      ((isInteger_adicCompletionIntegers_algebraMap_iff v W.a₂).mp
        ⟨_, (integralModel_a₂_eq _ (W.baseChange (v.adicCompletion K))).trans (by simp)⟩)
      ((isInteger_adicCompletionIntegers_algebraMap_iff v W.a₃).mp
        ⟨_, (integralModel_a₃_eq _ (W.baseChange (v.adicCompletion K))).trans (by simp)⟩)
      ((isInteger_adicCompletionIntegers_algebraMap_iff v W.a₄).mp
        ⟨_, (integralModel_a₄_eq _ (W.baseChange (v.adicCompletion K))).trans (by simp)⟩)
      ((isInteger_adicCompletionIntegers_algebraMap_iff v W.a₆).mp
        ⟨_, (integralModel_a₆_eq _ (W.baseChange (v.adicCompletion K))).trans (by simp)⟩)
  · let _ : Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
      (v.localizationToCompletionIntegers (K := K)).toAlgebra
    exact IsIntegral.baseChange
      (R := Localization.AtPrime v.asIdeal) (S := v.adicCompletionIntegers K)
      (algebraMap_comp_localizationToCompletionIntegers v) W

/-- An equation over `K` integral at `Oᵥ` becomes integral over `O_v` upon completion. -/
instance isIntegral_adicCompletionIntegers_baseChange (W : WeierstrassCurve K)
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isIntegral_adicCompletionIntegers_baseChange_iff v W).mpr inferInstance

private theorem irreducible_localizationToCompletionIntegers {ϖ : O}
    (hϖ : v.intValuation ϖ = exp (-1)) :
    Irreducible (v.localizationToCompletionIntegers (K := K)
      (algebraMap O (Localization.AtPrime v.asIdeal) ϖ)) := by
  have hϖ₁ : Irreducible (algebraMap O (Localization.AtPrime v.asIdeal) ϖ) :=
    v.irreducible_algebraMap_localizationAtPrime hϖ
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← Set.image_singleton,
    ← Ideal.map_span, ← hϖ₁.maximalIdeal_eq, v.maximalIdeal_map_completion]

private theorem pow_dvd_localizationToCompletionIntegers_iff {ϖ : O}
    (hϖ : v.intValuation ϖ = exp (-1)) (n : ℕ) (x : Localization.AtPrime v.asIdeal) :
    (v.localizationToCompletionIntegers (K := K)
        (algebraMap O (Localization.AtPrime v.asIdeal) ϖ)) ^ n ∣
      v.localizationToCompletionIntegers (K := K) x ↔
      (algebraMap O (Localization.AtPrime v.asIdeal) ϖ) ^ n ∣ x := by
  have hϖ₁ : Irreducible (algebraMap O (Localization.AtPrime v.asIdeal) ϖ) :=
    v.irreducible_algebraMap_localizationAtPrime hϖ
  have hϖ₂ : Irreducible (v.localizationToCompletionIntegers (K := K)
      (algebraMap O (Localization.AtPrime v.asIdeal) ϖ)) :=
    irreducible_localizationToCompletionIntegers v hϖ
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, ← hϖ₂.maximalIdeal_eq,
    ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, ← hϖ₁.maximalIdeal_eq,
    v.mem_maximalIdeal_pow_iff]
  have hx : (v.localizationToCompletionIntegers (K := K) x : v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) (algebraMap (Localization.AtPrime v.asIdeal) K x) :=
    RingHom.congr_fun (algebraMap_comp_localizationToCompletionIntegers v) x
  rw [hx, algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    Algebra.algebraMap_self_apply, ← v.valuation_maximalIdeal_localizationAtPrime]
  have hmax : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) := rfl
  rw [valuation_of_algebraMap, ← hmax, intValuation_le_pow_iff_mem _ x n]

private theorem exists_algebraMap_sub_mem_span_pow (x : v.adicCompletionIntegers K)
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∃ a : O, algebraMap O (v.adicCompletionIntegers K) a - x ∈ Ideal.span {ϖ ^ n} := by
  obtain ⟨a, ha⟩ := v.exists_valued_sub_le (K := K) x n
  refine ⟨a, ?_⟩
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, v.mem_maximalIdeal_pow_iff,
    AddSubgroupClass.coe_sub, Valuation.map_sub_swap]
  exact ha

private theorem pow_dvd_smul_of_sub_mem_span_pow_six {R : Type*} [CommRing R] {ϖ : R}
    {W : WeierstrassCurve R} {r s t r' s' t' : R}
    (hr : r' - r ∈ Ideal.span {ϖ ^ 6}) (hs : s' - s ∈ Ideal.span {ϖ ^ 6})
    (ht : t' - t ∈ Ideal.span {ϖ ^ 6})
    (h₁ : ϖ ∣ (VariableChange.mk 1 r s t • W).a₁)
    (h₂ : ϖ ^ 2 ∣ (VariableChange.mk 1 r s t • W).a₂)
    (h₃ : ϖ ^ 3 ∣ (VariableChange.mk 1 r s t • W).a₃)
    (h₄ : ϖ ^ 4 ∣ (VariableChange.mk 1 r s t • W).a₄)
    (h₆ : ϖ ^ 6 ∣ (VariableChange.mk 1 r s t • W).a₆) :
    ϖ ∣ (VariableChange.mk 1 r' s' t' • W).a₁ ∧
      ϖ ^ 2 ∣ (VariableChange.mk 1 r' s' t' • W).a₂ ∧
      ϖ ^ 3 ∣ (VariableChange.mk 1 r' s' t' • W).a₃ ∧
      ϖ ^ 4 ∣ (VariableChange.mk 1 r' s' t' • W).a₄ ∧
      ϖ ^ 6 ∣ (VariableChange.mk 1 r' s' t' • W).a₆ := by
  set I := Ideal.span {ϖ ^ 6}
  set π := Ideal.Quotient.mk I
  have hC : (VariableChange.mk 1 r' s' t').map π = (VariableChange.mk 1 r s t).map π := by
    ext <;> simp [VariableChange.map, π, Ideal.Quotient.eq, hr, hs, ht]
  have hW : (VariableChange.mk 1 r' s' t' • W).map π =
      (VariableChange.mk 1 r s t • W).map π := by
    rw [← map_variableChange, ← map_variableChange, hC]
  have key {i : ℕ} (hi : i ≤ 6) {x y : R} (hxy : π x = π y) (hd : ϖ ^ i ∣ y) : ϖ ^ i ∣ x := by
    have hsub : ϖ ^ 6 ∣ x - y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
    simpa only [sub_add_cancel] using dvd_add ((pow_dvd_pow ϖ hi).trans hsub) hd
  refine ⟨pow_one ϖ ▸ key (by omega) (by simpa using congrArg WeierstrassCurve.a₁ hW)
      (pow_one ϖ ▸ h₁),
    key (by omega) (by simpa using congrArg WeierstrassCurve.a₂ hW) h₂,
    key (by omega) (by simpa using congrArg WeierstrassCurve.a₃ hW) h₃,
    key (by omega) (by simpa using congrArg WeierstrassCurve.a₄ hW) h₄,
    key (by omega) (by simpa using congrArg WeierstrassCurve.a₆ hW) h₆⟩

private theorem exists_pow_dvd_localization_of_not_isMinimal {ϖ₀ : O}
    (hϖ₀ : v.intValuation ϖ₀ = exp (-1)) (Wo : WeierstrassCurve (Localization.AtPrime v.asIdeal))
    (hnot : ¬ IsMinimal (v.adicCompletionIntegers K)
      ((Wo.map (v.localizationToCompletionIntegers (K := K))).baseChange (v.adicCompletion K))) :
    ∃ C₀ : VariableChange (Localization.AtPrime v.asIdeal),
      algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀ ∣ (C₀ • Wo).a₁ ∧
      algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀ ^ 2 ∣ (C₀ • Wo).a₂ ∧
      algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀ ^ 3 ∣ (C₀ • Wo).a₃ ∧
      algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀ ^ 4 ∣ (C₀ • Wo).a₄ ∧
      algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀ ^ 6 ∣ (C₀ • Wo).a₆ := by
  set f := v.localizationToCompletionIntegers (K := K)
  set Wv := Wo.map f
  have hϖ₂ : Irreducible (f (algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀)) :=
    irreducible_localizationToCompletionIntegers v hϖ₀
  obtain ⟨r, s, t, d₁, d₂, d₃, d₄, d₆⟩ :=
    exists_variableChange_pow_dvd_a₁_a₂_a₃_a₄_a₆_of_not_isMinimal hϖ₂ Wv hnot
  obtain ⟨r₀, hr₀⟩ := exists_algebraMap_sub_mem_span_pow v r hϖ₂ 6
  obtain ⟨s₀, hs₀⟩ := exists_algebraMap_sub_mem_span_pow v s hϖ₂ 6
  obtain ⟨t₀, ht₀⟩ := exists_algebraMap_sub_mem_span_pow v t hϖ₂ 6
  set C₀ : VariableChange (Localization.AtPrime v.asIdeal) :=
    VariableChange.mk 1 (algebraMap O _ r₀) (algebraMap O _ s₀) (algebraMap O _ t₀)
  have hC₀ : (C₀ • Wo).map f =
      VariableChange.mk 1 (algebraMap O (v.adicCompletionIntegers K) r₀)
        (algebraMap O (v.adicCompletionIntegers K) s₀)
        (algebraMap O (v.adicCompletionIntegers K) t₀) • Wv := by
    rw [← map_variableChange]
    congr 1
    ext <;> simp [C₀, f]
  obtain ⟨d₁', d₂', d₃', d₄', d₆'⟩ :=
    pow_dvd_smul_of_sub_mem_span_pow_six hr₀ hs₀ ht₀ d₁ d₂ d₃ d₄ d₆
  rw [← hC₀] at d₁' d₂' d₃' d₄' d₆'
  exact ⟨C₀, by simpa using
      (pow_dvd_localizationToCompletionIntegers_iff v hϖ₀ 1 _).mp (by simpa using d₁'),
    (pow_dvd_localizationToCompletionIntegers_iff v hϖ₀ 2 _).mp d₂',
    (pow_dvd_localizationToCompletionIntegers_iff v hϖ₀ 3 _).mp d₃',
    (pow_dvd_localizationToCompletionIntegers_iff v hϖ₀ 4 _).mp d₄',
    (pow_dvd_localizationToCompletionIntegers_iff v hϖ₀ 6 _).mp d₆'⟩

/-- **Minimality is preserved and reflected by adic completion**: an elliptic Weierstrass equation
`W` over `K` becomes minimal over `O_v` upon base change to `K_v` if and only if `W` is minimal
over the localization `Oᵥ`. -/
@[simp]
theorem isMinimal_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  by_cases hint : IsIntegral (Localization.AtPrime v.asIdeal) W
  · have : IsIntegral (Localization.AtPrime v.asIdeal) W := hint
    let _ : Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
      (v.localizationToCompletionIntegers (K := K)).toAlgebra
    set f := algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)
    set Wo := W.integralModel (Localization.AtPrime v.asIdeal)
    set Wv := Wo.map f
    have hWo : Wo.baseChange K = W := baseChange_integralModel_eq _ W
    have hWv : Wv.baseChange (v.adicCompletion K) = W.baseChange (v.adicCompletion K) :=
      baseChange_map_integralModel (algebraMap_comp_localizationToCompletionIntegers v) W
    have hΔo : Wo.Δ ≠ 0 := fun h ↦ W.isUnit_Δ.ne_zero <| by
      rw [← integralModel_Δ_eq (Localization.AtPrime v.asIdeal) W, h, map_zero]
    have hΔv : Wv.Δ ≠ 0 := fun h ↦ (W.baseChange (v.adicCompletion K)).isUnit_Δ.ne_zero <| by
      rw [← hWv, baseChange, map_Δ, h, map_zero]
    obtain ⟨ϖ₀, hϖ₀⟩ := v.intValuation_exists_uniformizer
    have hϖ₁ : Irreducible (algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀) :=
      v.irreducible_algebraMap_localizationAtPrime hϖ₀
    have hϖ₂ : Irreducible (f (algebraMap O (Localization.AtPrime v.asIdeal) ϖ₀)) :=
      irreducible_localizationToCompletionIntegers v hϖ₀
    rw [← hWv, ← hWo,
      isMinimal_baseChange_iff_forall_not_pow_dvd_a₁_a₂_a₃_a₄_a₆ hϖ₂ Wv hΔv,
      isMinimal_baseChange_iff_forall_not_pow_dvd_a₁_a₂_a₃_a₄_a₆ hϖ₁ Wo hΔo]
    refine ⟨fun hv C ⟨h₁, h₂, h₃, h₄, h₆⟩ ↦ hv (C.map f) ?_, fun ho C hC ↦ ?_⟩
    · simp only [Wv, map_variableChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
      exact ⟨map_dvd f h₁, by simpa using map_dvd f h₂, by simpa using map_dvd f h₃,
        by simpa using map_dvd f h₄, by simpa using map_dvd f h₆⟩
    · obtain ⟨C₀, hC₀⟩ := exists_pow_dvd_localization_of_not_isMinimal v hϖ₀ Wo
        ((isMinimal_baseChange_iff_forall_not_pow_dvd_a₁_a₂_a₃_a₄_a₆ hϖ₂ Wv hΔv).not.mpr
          (not_forall.mpr ⟨C, not_not.mpr hC⟩))
      exact ho C₀ hC₀
  · refine ⟨fun h ↦ False.elim (hint ?_), fun h ↦ False.elim (hint inferInstance)⟩
    exact (isIntegral_adicCompletionIntegers_baseChange_iff v W).mp inferInstance

/-- An elliptic equation over `K` minimal at `Oᵥ` becomes minimal over `O_v` upon completion. -/
instance isMinimal_adicCompletionIntegers_baseChange (W : WeierstrassCurve K) [W.IsElliptic]
    [IsMinimal (Localization.AtPrime v.asIdeal) W] :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_adicCompletionIntegers_baseChange_iff v W).mpr inferInstance

/-- When the residue field `O ⧸ v` is finite, minimality of `W.baseChange K_v` at the valuative
ring of integers `𝒪[K_v]` agrees with minimality of `W` at `Oᵥ`. -/
theorem isMinimal_adicCompletion_baseChange_iff [Finite (O ⧸ v.asIdeal)]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (W.baseChange (v.adicCompletion K)).IsMinimal 𝒪[v.adicCompletion K] ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W :=
  (isMinimal_adicCompletion_iff (W.baseChange (v.adicCompletion K))).trans
    (isMinimal_adicCompletionIntegers_baseChange_iff v W)

/-- When `O ⧸ v` is finite, an elliptic equation minimal at `Oᵥ` becomes minimal at `𝒪[K_v]`. -/
instance isMinimal_adicCompletion_baseChange [Finite (O ⧸ v.asIdeal)]
    (W : WeierstrassCurve K) [W.IsElliptic] [IsMinimal (Localization.AtPrime v.asIdeal) W] :
    (W.baseChange (v.adicCompletion K)).IsMinimal 𝒪[v.adicCompletion K] :=
  (isMinimal_adicCompletion_baseChange_iff v W).mpr inferInstance

/-- A globally minimal equation over `O` is minimal over `O_v` at every height-one prime `v`. -/
theorem IsGlobalMinimal.isMinimal_adicCompletionIntegers {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) (v : HeightOneSpectrum O) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) := by
  have := h.isMinimal v
  infer_instance

/-- A globally minimal equation over `O` is minimal over `𝒪[K_v]` at every prime `v` with finite
residue field. -/
theorem IsGlobalMinimal.isMinimal_adicCompletion {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) (v : HeightOneSpectrum O) [Finite (O ⧸ v.asIdeal)] :
    (W.baseChange (v.adicCompletion K)).IsMinimal 𝒪[v.adicCompletion K] := by
  have := h.isMinimal v
  infer_instance

/-- Adic completion preserves the local minimal discriminant valuation. -/
@[simp]
theorem localMinimalDiscriminantValuation_baseChange_adicCompletion
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (W.baseChange (v.adicCompletion K)).localMinimalDiscriminantValuation
        (v.adicCompletionIntegers K) =
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  set M := W.minimal (Localization.AtPrime v.asIdeal)
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hCv : C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K) =
      M.baseChange (v.adicCompletion K) := by
    rw [baseChange_smul_baseChange, hC]
  have h₁ := (W.baseChange (v.adicCompletion K)).valuation_Δ_eq_exp_neg_of_isMinimal_smul
    (v.adicCompletionIntegers K) _ hCv
  have h₂ := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul
    (Localization.AtPrime v.asIdeal) C hC
  rw [v.valuation_maximalIdeal_adicCompletionIntegers, baseChange, map_Δ,
    algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    Algebra.algebraMap_self_apply] at h₁
  rw [v.valuation_maximalIdeal_localizationAtPrime] at h₂
  exact Nat.cast_inj.mp (neg_inj.mp (WithZero.exp_injective (h₁.symm.trans h₂)))

end WeierstrassCurve
