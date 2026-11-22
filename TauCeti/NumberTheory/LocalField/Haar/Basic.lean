/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.RingTheory.Valuation.ValuationRing
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic
import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology

/-!
# Normalized additive Haar measure and multiplication scaling on local fields

Building on `TauCeti.NumberTheory.LocalField.HaarCharacter` (which defines
`TauCeti.integerPositiveCompacts` and identifies `MeasureTheory.distribHaarChar E` with the
normalized absolute value `|·|_E`), this module introduces the canonical regular additive Haar
measure `TauCeti.localAddHaar E` on a nonarchimedean local field `E` normalized by
`(localAddHaar E) 𝒪[E] = 1`, together with uniqueness, ideal-power and unit-sphere volumes, and
multiplicative image, preimage, pushforward, and Lebesgue/Bochner integral change-of-variables
formulas for `(a * ·)`.

Concrete specializations live in sibling modules (`TauCeti.NumberTheory.LocalField.Haar.Padic`,
`TauCeti.NumberTheory.LocalField.Haar.LaurentSeries`, and
`TauCeti.NumberTheory.LocalField.Haar.AdicCompletion`).

## Main definitions

* `TauCeti.localAddHaar E`: the regular additive Haar measure on `E` normalized by `μ 𝒪[E] = 1`.

## Main results

* `TauCeti.mem_integerPositiveCompacts`: membership in `TauCeti.integerPositiveCompacts E`.
* `MeasureTheory.Measure.eq_smul_localAddHaar`, `MeasureTheory.Measure.eq_localAddHaar_iff`:
  characterization and scaling uniqueness of `TauCeti.localAddHaar E`.
* `MeasureTheory.Measure.measure_image_maximalIdeal_pow`,
  `MeasureTheory.Measure.measure_setOf_valuation_eq_one`,
  `TauCeti.localAddHaar_image_maximalIdeal_pow`, `TauCeti.localAddHaar_setOf_valuation_eq_one`:
  `𝓂[E] ^ n` has normalized measure `q ^ (-n)` and the unit sphere `{x : E | valuation E x = 1}`
  has normalized measure `1 - q⁻¹`.
* `Irreducible.distribHaarChar_unitsMk0`, `Units.distribHaarChar_map_subtype_eq_one`,
  `TauCeti.distribHaarChar_eq_one_of_mem_unitFiltration_zero`: character specializations on
  irreducible elements, valuation-ring units, and `unitFiltration E 0`.
* `MeasureTheory.Measure.addHaar_image_mul_left`, `MeasureTheory.Measure.addHaar_preimage_mul_left`,
  `MeasureTheory.Measure.map_mul_left_addHaar`,
  `MeasureTheory.Measure.map_units_mul_left_addHaar`,
  `MeasureTheory.Measure.map_mul_left_addHaar_of_isUniformizer`,
  `MeasureTheory.Measure.map_integerUnits_mul_left_addHaar`,
  `MeasureTheory.Measure.lintegral_mul_left_addHaar`,
  `MeasureTheory.Measure.integral_mul_left_addHaar`: image, pushforward, and integral change of
  variables under multiplication on `E`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Vol. I, Cambridge University Press, 2023, §3.5, pp. 186–187.
* A. Weil, *Basic Number Theory*, 3rd ed., Springer, 1974, Chapter I, §2.
-/

public section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace ValuativeRel
open scoped ENNReal NNReal NNRat Pointwise WithZero

namespace TauCeti

section LocalAddHaar

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- Membership in `TauCeti.integerPositiveCompacts E` is membership in `𝒪[E]`. -/
@[simp, grind =]
theorem mem_integerPositiveCompacts (x : E) : x ∈ integerPositiveCompacts E ↔ x ∈ 𝒪[E] := by
  rw [← SetLike.mem_coe, coe_integerPositiveCompacts, SetLike.mem_coe]

variable [MeasurableSpace E] [BorelSpace E]

/-- The canonical regular additive Haar measure on `E` normalized so that the valuation ring `𝒪[E]`
has measure one. -/
noncomputable def localAddHaar : Measure E :=
  addHaarMeasure (integerPositiveCompacts E)

/-- `TauCeti.localAddHaar E` is Mathlib's `addHaarMeasure` normalized at
`TauCeti.integerPositiveCompacts E`. -/
theorem localAddHaar_def : localAddHaar E = addHaarMeasure (integerPositiveCompacts E) :=
  (rfl)

instance isAddHaarMeasure_localAddHaar : (localAddHaar E).IsAddHaarMeasure := by
  rw [localAddHaar_def]
  infer_instance

instance regular_localAddHaar : (localAddHaar E).Regular := by
  rw [localAddHaar_def]
  infer_instance

instance sigmaFinite_localAddHaar : SigmaFinite (localAddHaar E) := by
  rw [localAddHaar_def]
  infer_instance

/-- The normalized additive Haar measure gives the valuation ring `𝒪[E]` mass one. -/
@[simp, grind =]
theorem localAddHaar_integer : localAddHaar E (𝒪[E] : Set E) = 1 := by
  rw [localAddHaar_def, ← coe_integerPositiveCompacts E]
  exact addHaarMeasure_self

end LocalAddHaar

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

section LocalFieldMeasures

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]

/-- Every σ-finite translation-invariant measure on a nonarchimedean local field `E` is its mass on
`𝒪[E]` times `TauCeti.localAddHaar E`. -/
theorem eq_smul_localAddHaar (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = μ (𝒪[E] : Set E) • localAddHaar E := by
  rw [localAddHaar_def, ← coe_integerPositiveCompacts E]
  exact addHaarMeasure_unique μ (integerPositiveCompacts E)

/-- A σ-finite translation-invariant measure on `E` equals `TauCeti.localAddHaar E` if and only if
it gives `𝒪[E]` mass one. -/
theorem eq_localAddHaar_iff (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = localAddHaar E ↔ μ (𝒪[E] : Set E) = 1 := by
  rw [localAddHaar_def, ← coe_integerPositiveCompacts E, eq_comm]
  exact addHaarMeasure_eq_iff (integerPositiveCompacts E) μ

/-- **Volume of powers of the maximal ideal.** For any left-invariant measure `μ` on a
nonarchimedean local field `E`, the `n`-th power `𝓂[E] ^ n` has `q ^ (-n)` times the measure of
`𝒪[E]`, where `q = Nat.card 𝓀[E]`. -/
theorem measure_image_maximalIdeal_pow (μ : Measure E) [μ.IsAddLeftInvariant] (n : ℕ) :
    μ (((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ n)) =
      1 / (Nat.card 𝓀[E] : ℝ≥0∞) ^ n * μ (𝒪[E] : Set E) := by
  -- Transport `μ` along `(Fin 1 → E) ≃L[E] E` and apply the coordinate-box formula.
  let e : (Fin 1 → E) ≃L[E] E := ContinuousLinearEquiv.funUnique (Fin 1) E E
  have he : MeasurableEmbedding (e.toAddMonoidHom : (Fin 1 → E) → E) :=
    e.toHomeomorph.measurableEmbedding
  let ν : Measure (Fin 1 → E) := μ.comap e.toAddMonoidHom
  have _ : ν.IsAddLeftInvariant := IsAddLeftInvariant.comap μ he
  have hpow : e.toAddMonoidHom '' (univ.pi fun _ : Fin 1 ↦ ((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ n)) =
      ((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ n) := by
    ext x
    simp only [mem_image, mem_univ_pi, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap,
      ContinuousLinearEquiv.coe_toLinearEquiv, e, ContinuousLinearEquiv.coe_funUnique,
      Function.eval, Fin.default_eq_zero]
    exact ⟨fun ⟨_, hf, hfx⟩ ↦ hfx ▸ hf 0, fun hx ↦ ⟨fun _ ↦ x, fun _ ↦ hx, rfl⟩⟩
  have hint : e.toAddMonoidHom '' integerBox E (Fin 1) = (𝒪[E] : Set E) := by
    ext x
    simp only [mem_image, mem_integerBox, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_toLinearMap, ContinuousLinearEquiv.coe_toLinearEquiv, e,
      ContinuousLinearEquiv.coe_funUnique, Function.eval, Fin.default_eq_zero]
    exact ⟨fun ⟨_, hf, hfx⟩ ↦ hfx ▸ hf 0, fun hx ↦ ⟨fun _ ↦ x, fun _ ↦ hx, rfl⟩⟩
  have h := measure_univ_pi_image_maximalIdeal_pow ν (fun _ : Fin 1 ↦ n)
  rw [he.comap_apply, he.comap_apply, hpow, hint, Finset.sum_const, Finset.card_fin,
    one_smul] at h
  exact h

/-- **Volume of the unit sphere.** For any left-invariant locally finite measure `μ` on `E`, the
elements of valuation one have `(1 - q⁻¹)` times the measure of `𝒪[E]`. -/
theorem measure_setOf_valuation_eq_one (μ : Measure E) [μ.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] :
    μ {x : E | valuation E x = 1} =
      (1 - 1 / (Nat.card 𝓀[E] : ℝ≥0∞)) * μ (𝒪[E] : Set E) := by
  have hO_comp : IsCompact (𝒪[E] : Set E) :=
    isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[E])
  have hsphere : {x : E | valuation E x = 1} =
      (𝒪[E] : Set E) \ (((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ 1)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, pow_one,
      Valuation.mem_integer_iff, ← valuation_lt_one_iff_mem_image_maximalIdeal, le_antisymm_iff,
      not_lt]
  have hsub : (((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ 1)) ⊆ (𝒪[E] : Set E) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.property
  have hO : μ (𝒪[E] : Set E) ≠ ∞ := hO_comp.measure_lt_top.ne
  have hfin : μ (((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ 1)) ≠ ∞ :=
    ((measure_mono hsub).trans_lt hO_comp.measure_lt_top).ne
  rw [hsphere, measure_sdiff hsub
    (isOpen_image_maximalIdeal_pow E 1).measurableSet.nullMeasurableSet hfin,
    measure_image_maximalIdeal_pow μ 1, pow_one, ENNReal.sub_mul fun _ _ ↦ hO, one_mul]

end LocalFieldMeasures

end MeasureTheory.Measure

namespace TauCeti

section Borel

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]

/-- Under `TauCeti.localAddHaar E`, the `n`-th power of the maximal ideal has measure `q ^ (-n)`. -/
@[simp, grind =]
theorem localAddHaar_image_maximalIdeal_pow (n : ℕ) :
    localAddHaar E (((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ n)) = ((Nat.card 𝓀[E] : ℝ≥0∞) ^ n)⁻¹ := by
  rw [Measure.measure_image_maximalIdeal_pow, localAddHaar_integer, mul_one, one_div]

/-- Under `TauCeti.localAddHaar E`, the maximal ideal `𝓂[E]` has measure `q⁻¹`. -/
@[simp, grind =]
theorem localAddHaar_image_maximalIdeal :
    localAddHaar E (((↑) : 𝒪[E] → E) '' (𝓂[E] : Set 𝒪[E])) = (Nat.card 𝓀[E] : ℝ≥0∞)⁻¹ := by
  simpa using localAddHaar_image_maximalIdeal_pow (E := E) 1

/-- Under `TauCeti.localAddHaar E`, the valuation-one elements (the units of `𝒪[E]`) have measure
`1 - q⁻¹`. -/
@[simp, grind =]
theorem localAddHaar_setOf_valuation_eq_one :
    localAddHaar E {x : E | valuation E x = 1} = 1 - (Nat.card 𝓀[E] : ℝ≥0∞)⁻¹ := by
  rw [Measure.measure_setOf_valuation_eq_one, localAddHaar_integer, mul_one, one_div]

end Borel

end TauCeti

section LocalHaarCharacter

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

namespace Irreducible

open TauCeti

/-- An irreducible element `π` of `𝒪[E]` viewed as a unit of `E` has distributive Haar character
`q⁻¹`. -/
@[grind =]
theorem distribHaarChar_unitsMk0 {π : 𝒪[E]} (hπ : Irreducible π) :
    distribHaarChar E (Units.mk0 (π : E) fun h ↦ hπ.ne_zero (Subtype.ext h)) =
      (Nat.card 𝓀[E] : ℝ≥0)⁻¹ := by
  rw [distribHaarChar_eq_zpow, normalizedValuation_irreducible hπ, toAdd_ofAdd, zpow_neg_one]

end Irreducible

namespace Units

open TauCeti

/-- **Character of a valuation-ring unit.** Every unit `u ∈ 𝒪[E]ˣ` has distributive Haar character
`1` on `E`. -/
@[grind =]
theorem distribHaarChar_map_subtype_eq_one (u : 𝒪[E]ˣ) :
    distribHaarChar E (Units.map (Subring.subtype 𝒪[E] : 𝒪[E] →* E) u) = 1 := by
  rw [distribHaarChar_eq_one_iff]
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation E))).1 u.isUnit

end Units

namespace TauCeti

/-- Every element of the depth-zero unit filtration `U(E, 0) = 𝒪[E]ˣ` has distributive Haar
character `1`. -/
@[grind =]
theorem distribHaarChar_eq_one_of_mem_unitFiltration_zero {u : Eˣ} (hu : u ∈ unitFiltration E 0) :
    distribHaarChar E u = 1 := by
  rw [distribHaarChar_eq_normalizedAbsoluteValue,
    (normalizedAbsoluteValue_eq_one_iff _).2
      ((normalizedValuation_eq_one_iff u).1
        (normalizedValuation_coe_unitFiltration_zero (K := E) ⟨u, hu⟩))]
  simp

end TauCeti

end LocalHaarCharacter

namespace MeasureTheory.Measure

open TauCeti

section Scaling

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Left multiplication by `a : E` multiplies the additive Haar measure of any subset of `E` by
`|a|_E`. -/
@[simp, grind =]
theorem addHaar_image_mul_left (a : E) (s : Set E) :
    μ ((a * ·) '' s) = ((normalizedAbsoluteValue E a : ℝ≥0) : ℝ≥0∞) * μ s := by
  simpa only [← smul_eq_mul, ← Set.image_smul] using
    addHaar_smul_eq_normalizedAbsoluteValue_mul μ a s

/-- Preimage under `x ↦ a * x` (`a ≠ 0`) multiplies any additive Haar measure on `E` by
`|a|_E⁻¹`. -/
@[simp, grind =]
theorem addHaar_preimage_mul_left {a : E} (ha : a ≠ 0) (s : Set E) :
    μ ((a * ·) ⁻¹' s) = ((normalizedAbsoluteValue E a : ℝ≥0) : ℝ≥0∞)⁻¹ * μ s := by
  have hpre : (a * ·) ⁻¹' s = (a⁻¹ * ·) '' s := by
    ext x
    simp [inv_mul_eq_iff_eq_mul₀ ha]
  have h0 : (normalizedAbsoluteValue E a : ℝ≥0) ≠ 0 := by
    exact_mod_cast (normalizedAbsoluteValue E).ne_zero_iff.2 ha
  rw [hpre, addHaar_image_mul_left, map_inv₀, NNRat.cast_inv, ENNReal.coe_inv h0]

/-- **Pushforward of additive Haar measure under multiplication.** For `a ≠ 0` in a nonarchimedean
local field `E`, pushing an additive Haar measure `μ` forward by `x ↦ a * x` rescales `μ` by
`|a|_E⁻¹`. -/
theorem map_mul_left_addHaar {a : E} (ha : a ≠ 0) :
    map (a * ·) μ = ((normalizedAbsoluteValue E a : ℝ≥0)⁻¹ : ℝ≥0) • μ := by
  have h0 : (normalizedAbsoluteValue E a : ℝ≥0) ≠ 0 := by
    exact_mod_cast (normalizedAbsoluteValue E).ne_zero_iff.2 ha
  ext s hs
  rw [map_apply (measurable_const_mul a) hs, addHaar_preimage_mul_left μ ha s, smul_apply,
    nnreal_smul_coe_apply, ENNReal.coe_inv h0]

/-- **Pushforward of additive Haar measure by a unit (valuation form).** For `a ∈ Eˣ` and any
additive Haar measure `μ` on `E`, `Measure.map (a * ·) μ = q ^ (v_E(a)) • μ`, where
`q = Nat.card 𝓀[E]`. -/
theorem map_units_mul_left_addHaar (a : Eˣ) :
    map ((a : E) * ·) μ =
      ((Nat.card 𝓀[E] : ℝ≥0) ^ (normalizedValuation E a).toAdd) • μ := by
  rw [map_mul_left_addHaar μ a.ne_zero, normalizedAbsoluteValue_coe]
  congr 1
  push_cast
  rw [zpow_neg, inv_inv]

/-- Multiplying by a uniformizer `ϖ ∈ Eˣ` pushes any additive Haar measure `μ` on `E` forward to
`q • μ`. -/
theorem map_mul_left_addHaar_of_isUniformizer {ϖ : Eˣ} (hϖ : IsUniformizer E ϖ) :
    map ((ϖ : E) * ·) μ = (Nat.card 𝓀[E] : ℝ≥0) • μ := by
  rw [map_units_mul_left_addHaar μ ϖ, (isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd, zpow_one]

/-- **Valuation-ring units preserve additive Haar measure.** Left multiplication by any `u ∈ 𝒪[E]ˣ`
leaves every additive Haar measure on `E` invariant. -/
@[simp, grind =]
theorem map_integerUnits_mul_left_addHaar (u : 𝒪[E]ˣ) :
    map (((u : 𝒪[E]) : E) * ·) μ = μ := by
  rw [map_mul_left_addHaar μ (by simp)]
  simp

/-- Lower Lebesgue change of variables on `E` under `x ↦ a * x` (`a ≠ 0`). -/
theorem lintegral_mul_left_addHaar {a : E} (ha : a ≠ 0) (f : E → ℝ≥0∞) :
    ∫⁻ x, f (a * x) ∂μ = ((normalizedAbsoluteValue E a : ℝ≥0) : ℝ≥0∞)⁻¹ * ∫⁻ x, f x ∂μ := by
  let e : E ≃ᵐ E := MeasurableEquiv.mulLeft₀ a ha
  have h := lintegral_map_equiv f e (μ := μ)
  have he : ⇑e = (a * ·) := funext fun x ↦ by simp [e]
  rw [he, map_mul_left_addHaar μ ha, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_inv] at h
  · exact h.symm
  · exact_mod_cast (normalizedAbsoluteValue E).ne_zero_iff.2 ha

/-- Bochner integral change of variables on `E` under `x ↦ a * x` (`a ≠ 0`). -/
theorem integral_mul_left_addHaar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : E} (ha : a ≠ 0) (f : E → F) :
    ∫ x, f (a * x) ∂μ = ((normalizedAbsoluteValue E a : ℝ)⁻¹) • ∫ x, f x ∂μ := by
  let e : E ≃ᵐ E := MeasurableEquiv.mulLeft₀ a ha
  have h := integral_map_equiv e f (μ := μ)
  have he : ⇑e = (a * ·) := funext fun x ↦ by simp [e]
  rw [he, map_mul_left_addHaar μ ha, integral_smul_nnreal_measure, NNReal.smul_def,
    NNReal.coe_inv] at h
  exact h.symm

end Scaling

end MeasureTheory.Measure
