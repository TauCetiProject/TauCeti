/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# Negative powers of a function whose sublevel sets grow polynomially

Let `u ≥ 1` almost everywhere be a measurable real function on a measure space, and suppose that
its sublevel sets grow at most polynomially:

`ν {u ≤ R} ≤ R ^ ε * C` for every `R ≥ 1`.

Then for every exponent `A > ε`, `A > 0`, the negative power `u ^ (-A)` has lower integral at most
`A / (A - ε) * C`, and it is integrable when `C` is finite. The measure need not be finite: the
growth exponent `ε` controls the measure at infinity, and the bound `u ≥ 1` the behaviour near
`u = 0`.

The proof is the layer-cake formula for `u⁻¹ ≤ 1`: the superlevel set `{t < u⁻¹}` lies in
`{u ≤ t⁻¹}` for `0 < t < 1` and is null for `t ≥ 1`, so

`∫ u ^ (-A) = A ∫_0^∞ ν {t < u⁻¹} t ^ (A - 1) dt ≤ A C ∫_0^1 t ^ (A - 1 - ε) dt = A C / (A - ε)`.

Typical sublevel sets are the norm balls `{g | ‖g‖ ≤ R}` of a group of matrices under a Haar
measure, whose polynomial growth makes negative powers of the norm integrable.

## Main results

* `TauCeti.lintegral_ofReal_rpow_neg_le_of_measure_le_rpow`: the bound
  `∫⁻ u ^ (-A) ≤ A / (A - ε) * C`.
* `TauCeti.integrable_rpow_neg_of_measure_le_rpow`: integrability of `u ^ (-A)` for finite `C`.

## Provenance

`TauCeti.lintegral_ofReal_rpow_neg_le_of_measure_le_rpow` and
`TauCeti.integrable_rpow_neg_of_measure_le_rpow` are adapted from
`New.lintegral_rpow_neg_le_of_measure_sublevel_le` and
`New.integrable_rpow_neg_of_measure_sublevel_le` (file
`src/Lib/General/Measure/IntegralOperators.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The source
assumes `u ≥ 1` everywhere and a growth bound of the form `(K R ^ e) ^ d V` with natural exponents
and an auxiliary constant `c ≥ A / (A - e d)`; here `u ≥ 1` almost everywhere, the growth
exponent `ε` is real, and the constant is the exact value `A / (A - ε)` of the layer-cake integral.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd edition, AMS (2001), Theorem 1.13 (the layer-cake
  representation).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {u : α → ℝ} {ε A : ℝ} {C : ℝ≥0∞}

/-- **Negative powers under polynomial sublevel growth.** If `u ≥ 1` almost everywhere and
`ν {u ≤ R} ≤ R ^ ε * C` for every `R ≥ 1`, then for `0 < A` and `ε < A`,
`∫⁻ u ^ (-A) ∂ν ≤ A / (A - ε) * C`. -/
theorem lintegral_ofReal_rpow_neg_le_of_measure_le_rpow (hu : AEMeasurable u ν)
    (hu₁ : ∀ᵐ x ∂ν, 1 ≤ u x) (hA : 0 < A) (hεA : ε < A)
    (h : ∀ R, 1 ≤ R → ν {x | u x ≤ R} ≤ ENNReal.ofReal (R ^ ε) * C) :
    ∫⁻ x, ENNReal.ofReal (u x ^ (-A)) ∂ν ≤ ENNReal.ofReal (A / (A - ε)) * C := by
  have hnull : ν {x | u x < 1} = 0 := by simpa only [not_le] using ae_iff.1 hu₁
  -- For `0 < t`, the superlevel set `{t < u⁻¹}` lies in `{u ≤ t⁻¹}`, and in `{u < 1}` if `1 ≤ t`.
  have hlevel (t : ℝ) (ht : t ∈ Ioi 0) : ν {x | t < (u x)⁻¹} * ENNReal.ofReal (t ^ (A - 1)) ≤
      (Ioo 0 1).indicator (fun t ↦ ENNReal.ofReal (t ^ (A - 1 - ε)) * C) t := by
    have ht : 0 < t := ht
    have hpos {x : α} (hx : t < (u x)⁻¹) : 0 < u x := inv_pos.1 (ht.trans hx)
    by_cases ht₁ : t < 1
    · have hsub : {x | t < (u x)⁻¹} ⊆ {x | u x ≤ t⁻¹} := fun x hx ↦
        ((lt_inv_comm₀ ht (hpos hx)).1 hx).le
      rw [indicator_of_mem (show t ∈ Ioo 0 1 from ⟨ht, ht₁⟩)]
      calc _ ≤ ENNReal.ofReal (t⁻¹ ^ ε) * C * ENNReal.ofReal (t ^ (A - 1)) := by
            gcongr
            exact (measure_mono hsub).trans (h _ ((one_le_inv₀ ht).2 ht₁.le))
        _ = ENNReal.ofReal (t ^ (A - 1 - ε)) * C := by
            have hexp : A - 1 - ε = -ε + (A - 1) := by ring
            rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            simp [hexp, Real.rpow_add ht, Real.rpow_neg ht.le, Real.inv_rpow ht.le]
    · have hsub : {x | t < (u x)⁻¹} ⊆ {x | u x < 1} := fun x hx ↦
        (one_lt_inv₀ (hpos hx)).1 ((not_lt.1 ht₁).trans_lt hx)
      simp [measure_mono_null hsub hnull]
  calc ∫⁻ x, ENNReal.ofReal (u x ^ (-A)) ∂ν = ∫⁻ x, ENNReal.ofReal ((u x)⁻¹ ^ A) ∂ν := by
        refine lintegral_congr_ae (hu₁.mono fun x hx ↦ ?_)
        dsimp only
        rw [Real.inv_rpow (zero_le_one.trans hx), Real.rpow_neg (zero_le_one.trans hx)]
    _ = ENNReal.ofReal A *
          ∫⁻ t in Ioi 0, ν {x | t < (u x)⁻¹} * ENNReal.ofReal (t ^ (A - 1)) :=
        lintegral_rpow_eq_lintegral_meas_lt_mul ν
          (hu₁.mono fun x hx ↦ inv_nonneg.2 (zero_le_one.trans hx)) hu.inv hA
    _ ≤ ENNReal.ofReal A * ∫⁻ t in Ioi 0,
          (Ioo 0 1).indicator (fun t ↦ ENNReal.ofReal (t ^ (A - 1 - ε)) * C) t := by
        gcongr ENNReal.ofReal A * ?_
        exact setLIntegral_mono' measurableSet_Ioi hlevel
    _ = ENNReal.ofReal (A / (A - ε)) * C := by
        rw [setLIntegral_indicator measurableSet_Ioo,
          inter_eq_left.2 Ioo_subset_Ioi_self, lintegral_mul_const _ (by fun_prop),
          lintegral_ofReal_rpow_Ioo (by linarith) zero_le_one, ← mul_assoc,
          ← ENNReal.ofReal_mul hA.le]
        congr 2
        simp only [Real.one_rpow]
        congr 1; ring

/-- **Integrability of negative powers under polynomial sublevel growth.** If `u ≥ 1` almost
everywhere is measurable and `ν {u ≤ R} ≤ R ^ ε * C` for every `R ≥ 1`, with `C` finite, then
`u ^ (-A)` is integrable for `0 < A` and `ε < A`. -/
theorem integrable_rpow_neg_of_measure_le_rpow (hu : AEMeasurable u ν)
    (hu₁ : ∀ᵐ x ∂ν, 1 ≤ u x) (hA : 0 < A) (hεA : ε < A) (hC : C ≠ ∞)
    (h : ∀ R, 1 ≤ R → ν {x | u x ≤ R} ≤ ENNReal.ofReal (R ^ ε) * C) :
    Integrable (fun x ↦ u x ^ (-A)) ν := by
  refine ⟨(hu.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (hu₁.mono fun x hx ↦ Real.rpow_nonneg (zero_le_one.trans hx) _)]
  exact (lintegral_ofReal_rpow_neg_le_of_measure_le_rpow hu hu₁ hA hεA h).trans_lt
    (by finiteness)

end TauCeti
