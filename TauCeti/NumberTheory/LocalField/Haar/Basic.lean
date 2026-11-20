/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.Topology.Algebra.ValuativeRel.PuncturedNhds
import TauCeti.RingTheory.Valuation.ValuationRing
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic
import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology

/-!
# Normalized additive Haar measure and character of a nonarchimedean local field

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`, maximal ideal `𝓂[E]`, and
residue field `𝓀[E]` of cardinality `q = Nat.card 𝓀[E]`, and write `v_E : Eˣ → ℤ` for the additive
reading of `TauCeti.normalizedValuation E` (`v_E(ϖ) = 1` on uniformizers). Because `𝒪[E]` is a
compact open subring of `E`, Mathlib's `MeasureTheory.Measure.addHaarMeasure` attached to `𝒪[E]`
defines a canonical regular additive Haar measure `TauCeti.localAddHaar E` normalized by
`(localAddHaar E) 𝒪[E] = 1`, unique among regular additive Haar measures (and, by second
countability of `E`, among all additive Haar measures) with that normalization.

Left multiplication by `a ∈ Eˣ` rescales every additive Haar measure `μ` on `E` by the normalized
absolute value `|a|_E = q ^ (-v_E(a))` (`TauCeti.normalizedAbsoluteValue E`):
* the distributive Haar character `MeasureTheory.distribHaarChar E a` equals
  `|a|_E = q ^ (-v_E(a))`;
* for every `a : E` (including `a = 0`, where singletons are null by
  `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` and
  `TauCeti.instPuncturedNhdsNeBotOfIsValuativeTopology`) and every `s : Set E`,
  `μ ((a * ·) '' s) = |a|_E * μ s`;
* for `a ≠ 0`, the pushforward measure satisfies `Measure.map (a * ·) μ = |a|_E⁻¹ • μ`, so on units
  `Measure.map (a * ·) μ = q ^ (v_E(a)) • μ`.

In particular, valuation-ring units have character `1` and preserve additive Haar measure, whereas a
uniformizer has character `q⁻¹` and pushes `μ` forward to `q • μ`. Concrete specializations live in
sibling modules (`TauCeti.NumberTheory.LocalField.Haar.Padic`,
`TauCeti.NumberTheory.LocalField.Haar.LaurentSeries`, and
`TauCeti.NumberTheory.LocalField.Haar.AdicCompletion`).

## Main definitions

* `TauCeti.integerPositiveCompacts E`: the valuation ring `𝒪[E]` packaged as a
  `TopologicalSpace.PositiveCompacts E`.
* `TauCeti.localAddHaar E`: the regular additive Haar measure on `E` normalized by `μ 𝒪[E] = 1`.

## Main results

* `TauCeti.existsUnique_regular_addHaar_integer`, `TauCeti.existsUnique_addHaar_integer`:
  uniqueness of the additive Haar measure giving `𝒪[E]` mass one.
* `TauCeti.localAddHaar_image_maximalIdeal_pow`, `TauCeti.localAddHaar_setOf_valuation_eq_one`:
  `𝓂[E] ^ n` has normalized measure `q ^ (-n)` and the unit sphere `{x : E | valuation E x = 1}`
  has normalized measure `1 - q⁻¹`.
* `Units.distribHaarChar_eq_normalizedAbsoluteValue`, `Units.distribHaarChar_eq_zpow`:
  `MeasureTheory.distribHaarChar E a = |a|_E = q ^ (-v_E(a))` for `a ∈ Eˣ`.
* `MeasureTheory.Measure.addHaar_image_mul_left`, `MeasureTheory.Measure.map_mul_left_addHaar`,
  `MeasureTheory.Measure.map_units_mul_left_addHaar`: image and pushforward scaling of any additive
  Haar measure on `E` under multiplication.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Vol. I, Cambridge University Press, 2023, §3.5, pp. 186–187.
* A. Weil, *Basic Number Theory*, 3rd ed., Springer, 1974, Chapter I, §2.
-/

public section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace ValuativeRel
open scoped ENNReal NNReal NNRat Pointwise WithZero

namespace TauCeti

section CompactOpenInteger

variable (E : Type*) [Ring E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  [CompactSpace 𝒪[E]]

/-- The valuation ring `𝒪[E]` of a topological valuative ring with compact integer ring, packaged
as a compact subset with nonempty interior. -/
noncomputable def integerPositiveCompacts : PositiveCompacts E where
  carrier := (𝒪[E] : Set E)
  isCompact' := isCompact_iff_compactSpace.2 inferInstance
  interior_nonempty' := by
    rw [Valuation.isOpen_integer.interior_eq]
    exact ⟨0, zero_mem _⟩

/-- The underlying set of `TauCeti.integerPositiveCompacts E` is `(𝒪[E] : Set E)`. -/
@[simp, grind =]
theorem coe_integerPositiveCompacts : (integerPositiveCompacts E : Set E) = (𝒪[E] : Set E) :=
  (rfl)

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

/-- The normalized additive Haar measure gives the valuation ring `𝒪[E]` mass one. -/
@[simp, grind =]
theorem localAddHaar_integer : localAddHaar E (𝒪[E] : Set E) = 1 := by
  rw [localAddHaar_def]
  exact addHaarMeasure_self

end CompactOpenInteger

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

section RegularNormalization

variable {E : Type*} [Ring E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  [CompactSpace 𝒪[E]] [MeasurableSpace E] [BorelSpace E]

/-- Any regular left-invariant measure on `E` is its mass on `𝒪[E]` times `TauCeti.localAddHaar E`,
without assuming second countability. -/
theorem eq_smul_localAddHaar_of_regular (μ : Measure E) [μ.IsAddLeftInvariant] [μ.Regular] :
    μ = μ (𝒪[E] : Set E) • localAddHaar E := by
  have : LocallyCompactSpace E := (integerPositiveCompacts E).locallyCompactSpace_of_addGroup
  have h := isAddLeftInvariant_eq_smul_of_regular μ (localAddHaar E)
  have hc : (addHaarScalarFactor μ (localAddHaar E) : ℝ≥0∞) = μ (𝒪[E] : Set E) := by
    have h1 := congrArg (fun ν : Measure E ↦ ν (𝒪[E] : Set E)) h
    rw [_root_.smul_apply, nnreal_smul_coe_apply, localAddHaar_integer, mul_one] at h1
    exact h1.symm
  conv_lhs => rw [h]
  rw [ENNReal.smul_def, hc]

/-- Among regular left-invariant measures on `E`, `TauCeti.localAddHaar E` is characterized by
giving `𝒪[E]` measure one. -/
theorem eq_localAddHaar_iff_of_regular (μ : Measure E) [μ.IsAddLeftInvariant] [μ.Regular] :
    μ = localAddHaar E ↔ μ (𝒪[E] : Set E) = 1 := by
  refine ⟨fun h ↦ h ▸ localAddHaar_integer E, fun h ↦ ?_⟩
  rw [eq_smul_localAddHaar_of_regular μ, h, one_smul]

end RegularNormalization

section LocalFieldMeasures

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]

instance sigmaFinite_localAddHaar : SigmaFinite (localAddHaar E) := by
  rw [localAddHaar_def]
  infer_instance

/-- Every σ-finite translation-invariant measure on a nonarchimedean local field `E` is its mass on
`𝒪[E]` times `TauCeti.localAddHaar E`. -/
theorem eq_smul_localAddHaar (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = μ (𝒪[E] : Set E) • localAddHaar E := by
  rw [localAddHaar_def]
  exact addHaarMeasure_unique μ (integerPositiveCompacts E)

/-- A σ-finite translation-invariant measure on `E` equals `TauCeti.localAddHaar E` if and only if
it gives `𝒪[E]` mass one. -/
theorem eq_localAddHaar_iff (μ : Measure E) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    μ = localAddHaar E ↔ μ (𝒪[E] : Set E) = 1 := by
  rw [localAddHaar_def, eq_comm]
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

section Uniqueness

/-- **Uniqueness of normalized regular additive Haar measure.** There is a unique regular additive
Haar measure on `E` assigning measure one to `𝒪[E]`. -/
theorem existsUnique_regular_addHaar_integer (E : Type*) [Ring E] [ValuativeRel E]
    [TopologicalSpace E] [IsValuativeTopology E] [CompactSpace 𝒪[E]]
    [MeasurableSpace E] [BorelSpace E] :
    ∃! μ : Measure E, μ.IsAddHaarMeasure ∧ μ.Regular ∧ μ (𝒪[E] : Set E) = 1 := by
  refine ⟨localAddHaar E, ⟨inferInstance, inferInstance, localAddHaar_integer E⟩, ?_⟩
  rintro μ ⟨_, _, h1⟩
  exact (Measure.eq_localAddHaar_iff_of_regular μ).2 h1

end Uniqueness

end TauCeti

section LocalHaarCharacter

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

namespace TauCeti

section Borel

variable [MeasurableSpace E] [BorelSpace E]

variable (E) in
/-- **Uniqueness of normalized additive Haar measure** on a nonarchimedean local field: because `E`
is second countable, every additive Haar measure is σ-finite and regular, so there is a unique
additive Haar measure assigning mass one to `𝒪[E]`. -/
theorem existsUnique_addHaar_integer :
    ∃! μ : Measure E, μ.IsAddHaarMeasure ∧ μ (𝒪[E] : Set E) = 1 := by
  refine ⟨localAddHaar E, ⟨inferInstance, localAddHaar_integer E⟩, ?_⟩
  rintro μ ⟨_, h1⟩
  have : IsLocallyFiniteMeasure μ := inferInstance
  exact (Measure.eq_localAddHaar_iff μ).2 h1

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

namespace Irreducible

open TauCeti

/-- An irreducible element `π` of `𝒪[E]` viewed as a unit of `E` has distributive Haar character
`q⁻¹`. -/
@[simp, grind =]
theorem distribHaarChar_unitsMk0 {π : 𝒪[E]} (hπ : Irreducible π) :
    distribHaarChar E (Units.mk0 (π : E) fun h ↦ hπ.ne_zero (Subtype.ext h)) =
      (Nat.card 𝓀[E] : ℝ≥0)⁻¹ := by
  borelize E
  set ϖ : Eˣ := Units.mk0 (π : E) fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hsmul : ϖ • (𝒪[E] : Set E) = ((↑) : 𝒪[E] → E) '' ↑(𝓂[E] ^ 1) := by
    rw [hπ.image_maximalIdeal_pow_eq_smul, pow_one]
    ext x
    simp [ϖ, mem_smul_set, Units.smul_mk0]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := localAddHaar E) (s := (𝒪[E] : Set E))
    (by simp) (by simp) ?_
  rw [hsmul, localAddHaar_image_maximalIdeal_pow, pow_one, localAddHaar_integer, mul_one,
    ENNReal.coe_inv (Nat.cast_ne_zero.2 Nat.card_pos.ne'), ENNReal.coe_natCast]

end Irreducible

namespace Units

open TauCeti

/-- **Character of a valuation-ring unit.** Every unit `u ∈ 𝒪[E]ˣ` has distributive Haar character
`1` on `E`. -/
@[simp, grind =]
theorem distribHaarChar_map_subtype_eq_one (u : 𝒪[E]ˣ) :
    distribHaarChar E (Units.map (Subring.subtype 𝒪[E] : 𝒪[E] →* E) u) = 1 := by
  borelize E
  set u' : Eˣ := Units.map (Subring.subtype 𝒪[E] : 𝒪[E] →* E) u
  have hsmul : u' • (𝒪[E] : Set E) = (𝒪[E] : Set E) := by
    ext x
    simp only [mem_smul_set, Units.smul_def, _root_.smul_eq_mul, SetLike.mem_coe, u',
      Units.coe_map, MonoidHom.coe_ofClass, Subring.subtype_apply]
    refine ⟨fun ⟨y, hy, hxy⟩ ↦ hxy ▸ mul_mem u.val.property hy, fun hx ↦ ?_⟩
    refine ⟨(((u⁻¹ : 𝒪[E]ˣ) : 𝒪[E]) : E) * x, mul_mem (u⁻¹ : 𝒪[E]ˣ).val.property hx, ?_⟩
    rw [← mul_assoc, ← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one, one_mul]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := localAddHaar E) (s := (𝒪[E] : Set E))
    (by simp) (by simp) ?_
  rw [hsmul, ENNReal.coe_one, one_mul]

/-- **Local Haar character formula (power form).** For a nonarchimedean local field `E` with
residue field of cardinality `q = Nat.card 𝓀[E]`, left multiplication by `a ∈ Eˣ` has distributive
Haar character `q ^ (-v_E(a))`. -/
theorem distribHaarChar_eq_zpow (a : Eˣ) :
    distribHaarChar E a = (Nat.card 𝓀[E] : ℝ≥0) ^ (-(normalizedValuation E a).toAdd) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  conv_lhs => rw [← (unitsEquivProd hπ).symm_apply_apply a]
  rw [unitsEquivProd_symm_apply, unitsProdHom_apply, map_mul, map_zpow,
    hπ.distribHaarChar_unitsMk0, distribHaarChar_map_subtype_eq_one, mul_one, fst_unitsEquivProd,
    inv_zpow, ← zpow_neg]

/-- **Local Haar character equals normalized absolute value.** For every `a ∈ Eˣ`,
`MeasureTheory.distribHaarChar E a` coincides with `(TauCeti.normalizedAbsoluteValue E a : ℝ≥0)`. -/
@[grind =]
theorem distribHaarChar_eq_normalizedAbsoluteValue (a : Eˣ) :
    distribHaarChar E a = (normalizedAbsoluteValue E (a : E) : ℝ≥0) := by
  rw [a.distribHaarChar_eq_zpow, normalizedAbsoluteValue_coe]
  push_cast
  rfl

/-- A unit `a ∈ Eˣ` has distributive Haar character `1` if and only if its normalized valuation is
trivial, i.e., `a` is a unit of `𝒪[E]`. -/
@[simp, grind =]
theorem distribHaarChar_eq_one_iff (a : Eˣ) :
    distribHaarChar E a = 1 ↔ normalizedValuation E a = 1 := by
  rw [a.distribHaarChar_eq_normalizedAbsoluteValue]
  norm_cast
  rw [normalizedAbsoluteValue_eq_one_iff, ← normalizedValuation_eq_one_iff]

end Units

namespace TauCeti

/-- **Character of a uniformizer.** Any uniformizer `ϖ ∈ Eˣ` has distributive Haar character
`q⁻¹`, where `q = Nat.card 𝓀[E]`. -/
theorem distribHaarChar_of_isUniformizer {ϖ : Eˣ} (hϖ : IsUniformizer E ϖ) :
    distribHaarChar E ϖ = (Nat.card 𝓀[E] : ℝ≥0)⁻¹ := by
  rw [ϖ.distribHaarChar_eq_zpow, (isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd, zpow_neg_one]

/-- Every element of the depth-zero unit filtration `U(E, 0) = 𝒪[E]ˣ` has distributive Haar
character `1`. -/
@[grind =]
theorem distribHaarChar_eq_one_of_mem_unitFiltration_zero {u : Eˣ} (hu : u ∈ unitFiltration E 0) :
    distribHaarChar E u = 1 :=
  u.distribHaarChar_eq_one_iff.2 (normalizedValuation_coe_unitFiltration_zero (K := E) ⟨u, hu⟩)

end TauCeti

end LocalHaarCharacter

namespace MeasureTheory.Measure

open TauCeti

section Scaling

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Scalar multiplication by `a : E` scales any additive Haar measure on `E` by `|a|_E`, including
at `a = 0` where `0 • s` is at most `{0}` and singletons are null. -/
@[simp, grind =]
theorem addHaar_smul_of_isNonarchimedeanLocalField (a : E) (s : Set E) :
    μ (a • s) = ((normalizedAbsoluteValue E a : ℝ≥0) : ℝ≥0∞) * μ s := by
  rcases eq_or_ne a 0 with rfl | ha
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · simp [zero_smul_set hs, ← Set.singleton_zero]
  · let u : Eˣ := Units.mk0 a ha
    have hsmul : a • s = u • s := by
      ext x
      simp [u, mem_smul_set, Units.smul_mk0]
    rw [hsmul, ← distribHaarChar_mul μ u s, u.distribHaarChar_eq_normalizedAbsoluteValue,
      Units.val_mk0]

/-- Left multiplication by `a : E` multiplies the additive Haar measure of any subset of `E` by
`|a|_E`. -/
@[simp, grind =]
theorem addHaar_image_mul_left (a : E) (s : Set E) :
    μ ((a * ·) '' s) = ((normalizedAbsoluteValue E a : ℝ≥0) : ℝ≥0∞) * μ s := by
  simpa only [← smul_eq_mul, ← Set.image_smul] using
    addHaar_smul_of_isNonarchimedeanLocalField μ a s

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
