/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.NumberTheory.LocalField.Haar.Character
import TauCeti.NumberTheory.LocalField.Topology

/-!
# Normalized additive Haar measure on local fields

Building on `TauCeti.NumberTheory.LocalField.Haar.Character` (which defines
`TauCeti.integerPositiveCompacts` and identifies `MeasureTheory.distribHaarChar E` with the
normalized absolute value `|·|_E`), this module introduces the canonical regular additive Haar
measure `TauCeti.localAddHaar E` on a nonarchimedean local field `E` normalized by
`(localAddHaar E) 𝒪[E] = 1`, together with uniqueness and ideal-power and unit-sphere volumes.

Concrete specializations live in sibling modules (`TauCeti.NumberTheory.LocalField.Haar.Padic`,
`TauCeti.NumberTheory.LocalField.Haar.LaurentSeries`, and
`TauCeti.NumberTheory.LocalField.Haar.AdicCompletion`).

## Main definitions

* `TauCeti.localAddHaar E`: the regular additive Haar measure on `E` normalized by `μ 𝒪[E] = 1`.

## Main results

* `TauCeti.mem_integerPositiveCompacts`: membership in `TauCeti.integerPositiveCompacts E`.
* `MeasureTheory.Measure.eq_smul_localAddHaar`, `MeasureTheory.Measure.eq_localAddHaar_iff`:
  characterization and scaling uniqueness of `TauCeti.localAddHaar E`.
* `TauCeti.localAddHaar_image_maximalIdeal_pow`, `TauCeti.localAddHaar_image_maximalIdeal`,
  `TauCeti.localAddHaar_setOf_valuation_eq_one`: `𝓂[E] ^ n` has normalized measure `q ^ (-n)` and
  the unit sphere `{x : E | valuation E x = 1}` has normalized measure `1 - q⁻¹`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Vol. I, Cambridge University Press, 2023, §3.5, pp. 186–187.
* A. Weil, *Basic Number Theory*, 3rd ed., Springer, 1974, Chapter I, §2.
-/

public section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace ValuativeRel
open scoped ENNReal NNReal Pointwise

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
  simpa [integerBox_def, Measure.pi_pi, one_div] using
    Measure.measure_univ_pi_image_maximalIdeal_pow (Measure.pi fun _ : Unit ↦ localAddHaar E)
      (fun _ ↦ n)

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
  rw [Measure.addHaar_setOf_valuation_eq_one, localAddHaar_integer, mul_one]

end Borel

end TauCeti
