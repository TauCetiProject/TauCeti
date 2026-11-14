/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Topology.Constructions.SumProd
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-!
# Minimal Weierstrass equations under adic completion

Let `R` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of `R`.
Over `K`, local integrality and local minimality at `v` are phrased over the localization
`Localization.AtPrime v.asIdeal` (as in `WeierstrassCurve.IsGlobalMinimal`), whereas local
formal-group, Tamagawa, and Tate-module invariants at `v` are phrased over the ring of integers
`v.adicCompletionIntegers K` of the completion `v.adicCompletion K`.

Because `K` is dense in `v.adicCompletion K`, the valuation group onto `ℤᵐ⁰` is unchanged by
completion, and closed valuation balls around `0` are open, every integral change of variables of
`W.baseChange (v.adicCompletion K)` over the completed field can be approximated—after adjusting
its scaling factor by a completed unit—by a change of variables over `K` with the same discriminant
valuation. Consequently, both integrality and minimality are preserved and reflected by base change
to `v.adicCompletion K`.

## Main results

* `WeierstrassCurve.isIntegral_baseChange_adicCompletion_iff`: `W.baseChange (v.adicCompletion K)`
  is integral over `v.adicCompletionIntegers K` if and only if `W` is integral over
  `Localization.AtPrime v.asIdeal`.
* `WeierstrassCurve.exists_smul_isIntegral_localizationAtPrime_of_adicCompletion`: every completed
  integral change of variables of `W.baseChange (v.adicCompletion K)` can be approximated over `K`
  with the same discriminant valuation.
* `WeierstrassCurve.isMinimal_baseChange_adicCompletion_iff`: `W.baseChange (v.adicCompletion K)`
  is minimal over `v.adicCompletionIntegers K` if and only if `W` is minimal over
  `Localization.AtPrime v.asIdeal`.
* `WeierstrassCurve.isMinimal_baseChange_adicCompletion` and
  `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletion`: the forward direction as an instance
  and for globally minimal equations.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Chapter VII, §§1–2.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- A Weierstrass equation over `v.adicCompletion K` is integral over `v.adicCompletionIntegers K`
if and only if its five Weierstrass coefficients have valuation at most `1`. -/
theorem isIntegral_adicCompletionIntegers_iff (E : WeierstrassCurve (v.adicCompletion K)) :
    IsIntegral (v.adicCompletionIntegers K) E ↔
      Valued.v E.a₁ ≤ 1 ∧ Valued.v E.a₂ ≤ 1 ∧ Valued.v E.a₃ ≤ 1 ∧
        Valued.v E.a₄ ≤ 1 ∧ Valued.v E.a₆ ≤ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← integralModel_a₁_eq (v.adicCompletionIntegers K) E]
      exact (mem_adicCompletionIntegers R K v).mp
        (integralModel (v.adicCompletionIntegers K) E).a₁.2
    · rw [← integralModel_a₂_eq (v.adicCompletionIntegers K) E]
      exact (mem_adicCompletionIntegers R K v).mp
        (integralModel (v.adicCompletionIntegers K) E).a₂.2
    · rw [← integralModel_a₃_eq (v.adicCompletionIntegers K) E]
      exact (mem_adicCompletionIntegers R K v).mp
        (integralModel (v.adicCompletionIntegers K) E).a₃.2
    · rw [← integralModel_a₄_eq (v.adicCompletionIntegers K) E]
      exact (mem_adicCompletionIntegers R K v).mp
        (integralModel (v.adicCompletionIntegers K) E).a₄.2
    · rw [← integralModel_a₆_eq (v.adicCompletionIntegers K) E]
      exact (mem_adicCompletionIntegers R K v).mp
        (integralModel (v.adicCompletionIntegers K) E).a₆.2
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    exact isIntegral_of_exists_lift (v.adicCompletionIntegers K)
      ⟨⟨E.a₁, (mem_adicCompletionIntegers R K v).mpr h₁⟩, rfl⟩
      ⟨⟨E.a₂, (mem_adicCompletionIntegers R K v).mpr h₂⟩, rfl⟩
      ⟨⟨E.a₃, (mem_adicCompletionIntegers R K v).mpr h₃⟩, rfl⟩
      ⟨⟨E.a₄, (mem_adicCompletionIntegers R K v).mpr h₄⟩, rfl⟩
      ⟨⟨E.a₆, (mem_adicCompletionIntegers R K v).mpr h₆⟩, rfl⟩

/-- A Weierstrass equation over `K` is integral over `Localization.AtPrime v.asIdeal` if and only
if its five Weierstrass coefficients have `v`-adic valuation at most `1`. -/
theorem isIntegral_localizationAtPrime_iff (W : WeierstrassCurve K) :
    IsIntegral (Localization.AtPrime v.asIdeal) W ↔
      v.valuation K W.a₁ ≤ 1 ∧ v.valuation K W.a₂ ≤ 1 ∧ v.valuation K W.a₃ ≤ 1 ∧
        v.valuation K W.a₄ ≤ 1 ∧ v.valuation K W.a₆ ≤ 1 := by
  have hv := v.integers_valuation_of_isLocalizationAtPrime (Localization.AtPrime v.asIdeal) (K := K)
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← integralModel_a₁_eq (Localization.AtPrime v.asIdeal) W]
      exact hv.map_le_one _
    · rw [← integralModel_a₂_eq (Localization.AtPrime v.asIdeal) W]
      exact hv.map_le_one _
    · rw [← integralModel_a₃_eq (Localization.AtPrime v.asIdeal) W]
      exact hv.map_le_one _
    · rw [← integralModel_a₄_eq (Localization.AtPrime v.asIdeal) W]
      exact hv.map_le_one _
    · rw [← integralModel_a₆_eq (Localization.AtPrime v.asIdeal) W]
      exact hv.map_le_one _
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    exact isIntegral_of_exists_lift (Localization.AtPrime v.asIdeal)
      (hv.exists_of_le_one h₁) (hv.exists_of_le_one h₂) (hv.exists_of_le_one h₃)
      (hv.exists_of_le_one h₄) (hv.exists_of_le_one h₆)

/-- Base change from `K` to `v.adicCompletion K` preserves and reflects integrality at `v`. -/
@[simp]
theorem isIntegral_baseChange_adicCompletion_iff (W : WeierstrassCurve K) :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsIntegral (Localization.AtPrime v.asIdeal) W := by
  rw [isIntegral_adicCompletionIntegers_iff, isIntegral_localizationAtPrime_iff]
  simp [baseChange, algebraMap_adicCompletion]

/-- If `W` is integral over `Localization.AtPrime v.asIdeal`, its base change to
`v.adicCompletion K` is integral over `v.adicCompletionIntegers K`. -/
instance isIntegral_adicCompletionIntegers_baseChange (W : WeierstrassCurve K)
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isIntegral_baseChange_adicCompletion_iff v W).mpr inferInstance

private theorem exists_smul_isIntegral_adicCompletionIntegers_u_eq (W : WeierstrassCurve K)
    (C : VariableChange (v.adicCompletion K))
    [IsIntegral (v.adicCompletionIntegers K) (C • W.baseChange (v.adicCompletion K))] :
    ∃ (u₀ : Kˣ) (C' : VariableChange (v.adicCompletion K)),
      C'.u = Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u₀ ∧
      IsIntegral (v.adicCompletionIntegers K) (C' • W.baseChange (v.adicCompletion K)) ∧
      Valued.v (C • W.baseChange (v.adicCompletion K)).Δ =
        Valued.v (C' • W.baseChange (v.adicCompletion K)).Δ := by
  obtain ⟨u_raw, hu_raw⟩ := v.valuation_surjective K (Valued.v (C.u : v.adicCompletion K))
  have hu0 : u_raw ≠ 0 := fun h ↦ C.u.ne_zero <|
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).zero_iff.mp (by simpa [h] using hu_raw.symm)
  let u₀ : Kˣ := Units.mk0 u_raw hu0
  let u₀_v : (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u₀
  have hval_u : Valued.v (u₀_v : v.adicCompletion K) = Valued.v (C.u : v.adicCompletion K) := by
    simpa [u₀_v, u₀, algebraMap_adicCompletion] using hu_raw
  let ε_val : (v.adicCompletion K)ˣ := u₀_v * C.u⁻¹
  have hε₁ : Valued.v (ε_val : v.adicCompletion K) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval_u]
    exact mul_inv_cancel₀ ((Valued.v : Valuation _ ℤᵐ⁰).ne_zero_iff.mpr C.u.ne_zero)
  have hε_inv : Valued.v ((ε_val⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hε₁, inv_one]
  let ε : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨(ε_val : v.adicCompletion K), (mem_adicCompletionIntegers R K v).mpr hε₁.le⟩,
      ⟨((ε_val⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        (mem_adicCompletionIntegers R K v).mpr hε_inv.le⟩,
      Subtype.ext ε_val.mul_inv, Subtype.ext ε_val.inv_mul⟩
  let E₀ : VariableChange (v.adicCompletionIntegers K) := ⟨ε, 0, 0, 0⟩
  refine ⟨u₀, E₀.baseChange (v.adicCompletion K) * C, ?_, ?_, ?_⟩
  · have hE₀u : (E₀.baseChange (v.adicCompletion K)).u = ε_val := by ext; rfl
    rw [VariableChange.mul_def, hE₀u]
    exact inv_mul_cancel_right u₀_v C.u
  · rw [mul_smul]
    infer_instance
  · rw [mul_smul, ← v.valuation_maximalIdeal_adicCompletionIntegers,
      ← v.valuation_maximalIdeal_adicCompletionIntegers, valuation_Δ_baseChange_smul]

/-- Every completed change of variables carrying `W.baseChange (v.adicCompletion K)` to an equation
integral over `v.adicCompletionIntegers K` can be approximated by a change of variables over `K`
carrying `W` to an equation integral over `Localization.AtPrime v.asIdeal` with the same
discriminant valuation. -/
theorem exists_smul_isIntegral_localizationAtPrime_of_adicCompletion (W : WeierstrassCurve K)
    (C : VariableChange (v.adicCompletion K))
    [IsIntegral (v.adicCompletionIntegers K) (C • W.baseChange (v.adicCompletion K))] :
    ∃ D : VariableChange K, IsIntegral (Localization.AtPrime v.asIdeal) (D • W) ∧
      Valued.v (C • W.baseChange (v.adicCompletion K)).Δ = v.valuation K (D • W).Δ := by
  obtain ⟨u₀, C', hC'u, hC'int, hΔ₁⟩ :=
    exists_smul_isIntegral_adicCompletionIntegers_u_eq v W C
  let u₀_v : (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u₀
  let f : v.adicCompletion K × v.adicCompletion K × v.adicCompletion K →
      WeierstrassCurve (v.adicCompletion K) :=
    fun p ↦ VariableChange.mk u₀_v p.1 p.2.1 p.2.2 • W.baseChange (v.adicCompletion K)
  let B : Set (v.adicCompletion K) := {z | Valued.v z ≤ 1}
  have hB : IsOpen B := v.isOpen_setOf_valued_le one_ne_zero
  let U : Set (v.adicCompletion K × v.adicCompletion K × v.adicCompletion K) :=
    (fun p ↦ (f p).a₁) ⁻¹' B ∩ ((fun p ↦ (f p).a₂) ⁻¹' B ∩
      ((fun p ↦ (f p).a₃) ⁻¹' B ∩ ((fun p ↦ (f p).a₄) ⁻¹' B ∩ (fun p ↦ (f p).a₆) ⁻¹' B)))
  have hU : IsOpen U :=
    (hB.preimage (by simp only [f, variableChange_def]; fun_prop)).inter <|
      (hB.preimage (by simp only [f, variableChange_def]; fun_prop)).inter <|
        (hB.preimage (by simp only [f, variableChange_def]; fun_prop)).inter <|
          (hB.preimage (by simp only [f, variableChange_def]; fun_prop)).inter <|
            hB.preimage (by simp only [f, variableChange_def]; fun_prop)
  have hfC' : f (C'.r, C'.s, C'.t) = C' • W.baseChange (v.adicCompletion K) :=
    congrArg (· • W.baseChange (v.adicCompletion K)) (VariableChange.ext hC'u.symm rfl rfl rfl)
  have hmemC' : (C'.r, C'.s, C'.t) ∈ U := by
    obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := (isIntegral_adicCompletionIntegers_iff v _).mp hC'int
    simp only [U, B, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hfC']
    exact ⟨h₁, h₂, h₃, h₄, h₆⟩
  have hdense : DenseRange (Prod.map (algebraMap K (v.adicCompletion K))
      (Prod.map (algebraMap K (v.adicCompletion K)) (algebraMap K (v.adicCompletion K)))) :=
    (v.denseRange_algebraMap K).prodMap
      ((v.denseRange_algebraMap K).prodMap (v.denseRange_algebraMap K))
  obtain ⟨⟨r₀, s₀, t₀⟩, hp₀⟩ := hdense.exists_mem_open hU ⟨(C'.r, C'.s, C'.t), hmemC'⟩
  let D : VariableChange K := ⟨u₀, r₀, s₀, t₀⟩
  have hDf : (D • W).baseChange (v.adicCompletion K) =
      f (algebraMap K _ r₀, algebraMap K _ s₀, algebraMap K _ t₀) := by
    rw [← baseChange_smul_baseChange]
    rfl
  refine ⟨D, ?_, ?_⟩
  · rw [← isIntegral_baseChange_adicCompletion_iff, hDf, isIntegral_adicCompletionIntegers_iff]
    simpa only [U, B, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Prod.map_apply]
      using hp₀
  · rw [hΔ₁, variableChange_Δ, hC'u, variableChange_Δ, baseChange, map_Δ,
      map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
      map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    simp [D, Units.coe_map, algebraMap_adicCompletion]

/-- **Minimality is preserved and reflected by `v`-adic completion**:
`W.baseChange (v.adicCompletion K)` is minimal over `v.adicCompletionIntegers K` if and only if `W`
is minimal over `Localization.AtPrime v.asIdeal`. -/
@[simp]
theorem isMinimal_baseChange_adicCompletion_iff (W : WeierstrassCurve K) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  constructor
  · intro hmin
    have hint : IsIntegral (Localization.AtPrime v.asIdeal) W :=
      (isIntegral_baseChange_adicCompletion_iff v W).mp inferInstance
    refine ⟨⟨by simpa using hint, fun {D} hD _ ↦ ?_⟩⟩
    have hD' : IsIntegral (v.adicCompletionIntegers K)
        (D.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) := by
      rw [baseChange_smul_baseChange]
      exact (isIntegral_baseChange_adicCompletion_iff v (D • W)).mpr hD
    have hle := valuation_Δ_le_of_isMinimal_smul (v.adicCompletionIntegers K)
      (W₁ := W.baseChange (v.adicCompletion K)) (D.baseChange (v.adicCompletion K)) rfl
    rw [baseChange_smul_baseChange, v.valuation_maximalIdeal_adicCompletionIntegers,
      v.valuation_maximalIdeal_adicCompletionIntegers, baseChange, baseChange, map_Δ, map_Δ] at hle
    simp only [algebraMap_adicCompletion, Function.comp_apply,
      valuedAdicCompletion_eq_valuation'] at hle
    simp only [one_smul, ← Subtype.coe_le_coe,
      valuation_Δ_aux_eq_of_isIntegral (Localization.AtPrime v.asIdeal) (D • W),
      valuation_Δ_aux_eq_of_isIntegral (Localization.AtPrime v.asIdeal) W,
      v.valuation_maximalIdeal_localizationAtPrime]
    exact hle
  · intro hmin
    have hint : IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
      (isIntegral_baseChange_adicCompletion_iff v W).mpr inferInstance
    refine ⟨⟨by simpa using hint, fun {C} hC _ ↦ ?_⟩⟩
    have : IsIntegral (v.adicCompletionIntegers K) (C • W.baseChange (v.adicCompletion K)) := hC
    obtain ⟨D, hDint, hΔeq⟩ := exists_smul_isIntegral_localizationAtPrime_of_adicCompletion v W C
    have hle := valuation_Δ_le_of_isMinimal_smul (Localization.AtPrime v.asIdeal)
      (W₁ := W) D rfl
    rw [v.valuation_maximalIdeal_localizationAtPrime,
      v.valuation_maximalIdeal_localizationAtPrime] at hle
    simp only [one_smul, ← Subtype.coe_le_coe,
      valuation_Δ_aux_eq_of_isIntegral (v.adicCompletionIntegers K)
        (C • W.baseChange (v.adicCompletion K)),
      valuation_Δ_aux_eq_of_isIntegral (v.adicCompletionIntegers K)
        (W.baseChange (v.adicCompletion K)),
      v.valuation_maximalIdeal_adicCompletionIntegers, hΔeq]
    simpa [baseChange, algebraMap_adicCompletion] using hle

/-- If `W` is minimal over `Localization.AtPrime v.asIdeal`, its base change to
`v.adicCompletion K` is minimal over `v.adicCompletionIntegers K`. -/
instance isMinimal_baseChange_adicCompletion (W : WeierstrassCurve K)
    [IsMinimal (Localization.AtPrime v.asIdeal) W] :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_baseChange_adicCompletion_iff v W).mpr inferInstance

/-- A globally minimal Weierstrass equation over `R` remains minimal over
`v.adicCompletionIntegers K` at every height-one prime `v` of `R`. -/
theorem IsGlobalMinimal.isMinimal_adicCompletion {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal R W) (v : HeightOneSpectrum R) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  have := h.isMinimal v
  inferInstance

end WeierstrassCurve

end
