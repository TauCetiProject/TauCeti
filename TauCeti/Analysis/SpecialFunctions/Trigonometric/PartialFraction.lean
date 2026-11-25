/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import TauCeti.Analysis.Normed.Field.PartialFraction
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.SpecialFunctions.Trigonometric.TanhSeries

/-!
# Locally uniform partial-fraction expansions of the cotangent and the tangent

The partial-fraction expansions of `π cot (π z)` and of `-π tan (π z)` pair each pole with its
negative:

`π cot (π z) = 1 / z + ∑_{n ≥ 1} (1 / (z - n) + 1 / (z + n))` for `z ∉ ℤ`,

`-π tan (π z) = ∑_{n ≥ 0} (1 / (z - (n + 1/2)) + 1 / (z + (n + 1/2)))` for `z ∉ ℤ + 1/2`

(the first is DLMF, eq. 4.22.3, at the argument `π z`). Both pole families are nonzero and
inverse-square summable, so both paired series converge locally uniformly on all of `ℂ`
(`TauCeti.hasSumLocallyUniformly_one_div_sub_add_one_div_add`).

For the cotangent, this upgrades Mathlib's pointwise expansion `cot_series_rep'` to locally
uniform convergence on the integer complement (`TauCeti.hasSumLocallyUniformlyOn_cotTerm`). For
the tangent, the pointwise expansion off the half-integer multiples `(1/2) ℤ` is the odd-pole part
of the cotangent expansion at `2 z` (`TauCeti.hasSum_cotTerm_two_mul`), with
`cot (2 w) = (cot w - tan w) / 2`. At the integers, where the cotangent expansions do not apply,
both sides are continuous on the complement of `ℤ + 1/2` and agree on a dense subset, so the
expansion holds there too (`TauCeti.hasSum_neg_pi_mul_tan`).

## Main results

* `TauCeti.hasSumLocallyUniformlyOn_cotTerm`: the cotangent expansion converges locally uniformly
  on `ℂ \ ℤ`.
* `TauCeti.hasSumLocallyUniformlyOn_neg_pi_mul_tan`, `TauCeti.hasSum_neg_pi_mul_tan`: the
  half-integer expansion of `-π tan (π z)`, locally uniformly on `ℂ \ (ℤ + 1/2)` and pointwise.

## References

* [NIST DLMF, §4.22](https://dlmf.nist.gov/4.22).
-/

public section

open Complex Filter Set
open scoped Real

namespace TauCeti

/-- **The cotangent expansion converges locally uniformly.** The paired series
`∑_{n ≥ 0} (1 / (z - (n + 1)) + 1 / (z + (n + 1)))` of Mathlib's `cot_series_rep'` converges to
`π cot (π z) - 1 / z` locally uniformly on `ℂ \ ℤ`. -/
theorem hasSumLocallyUniformlyOn_cotTerm :
    HasSumLocallyUniformlyOn (fun n z ↦ cotTerm z n) (fun z ↦ π * cot (π * z) - 1 / z)
      integerComplement := by
  have hnorm (n : ℕ) : ‖(n : ℂ) + 1‖ = n + 1 := by exact_mod_cast norm_natCast (n + 1)
  have ha : ∀ᶠ n : ℕ in cofinite, (n : ℂ) + 1 ≠ 0 :=
    .of_forall fun n ↦ by exact_mod_cast n.succ_ne_zero
  have hs : Summable fun n : ℕ ↦ (‖(n : ℂ) + 1‖ ^ 2)⁻¹ := by
    simpa only [hnorm, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
  refine ((hasSumLocallyUniformly_one_div_sub_add_one_div_add ha hs).hasSumLocallyUniformlyOn
    (s := integerComplement)).congr_right fun z hz ↦ (cot_series_rep' hz).symm

/-- The half-integer expansion of `-π tan (π z)` at the points `z` with `2 z ∉ ℤ`: it is twice the
odd-pole part of the cotangent expansion at `2 z`. -/
private theorem hasSum_neg_pi_mul_tan_of_two_mul_mem {z : ℂ} (hz : 2 * z ∈ integerComplement) :
    HasSum (fun n : ℕ ↦ 1 / (z - (n + 1 / 2)) + 1 / (z + (n + 1 / 2))) (-(π * tan (π * z))) := by
  have hsin : sin (π * z) ≠ 0 ∧ cos (π * z) ≠ 0 := by
    have h := sin_pi_mul_ne_zero hz
    rw [show (π : ℂ) * (2 * z) = 2 * (π * z) by ring, sin_two_mul] at h
    exact ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h), right_ne_zero_of_mul h⟩
  convert (hasSum_cotTerm_two_mul hz).mul_left 2 using 1
  · ext n
    have e₁ : 2 * z - (((2 * n : ℕ) : ℂ) + 1) = 2 * (z - (n + 1 / 2)) := by push_cast; ring
    have e₂ : 2 * z + (((2 * n : ℕ) : ℂ) + 1) = 2 * (z + (n + 1 / 2)) := by push_cast; ring
    simp only [cotTerm, e₁, e₂, one_div, mul_inv]
    ring
  · rw [show (π : ℂ) * (2 * z) = 2 * (π * z) by ring, show 2 * z / 2 = z by ring,
      cot_eq_cos_div_sin, cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_two_mul, cos_two_mul]
    field_simp [hsin.1, hsin.2]
    linear_combination -sin_sq_add_cos_sq (π * z)

/-- **The half-integer expansion of the tangent converges locally uniformly.** The paired series
`∑_{n ≥ 0} (1 / (z - (n + 1/2)) + 1 / (z + (n + 1/2)))` converges to `-π tan (π z)` locally
uniformly on `ℂ \ (ℤ + 1/2)`. -/
theorem hasSumLocallyUniformlyOn_neg_pi_mul_tan :
    HasSumLocallyUniformlyOn
      (fun (n : ℕ) (z : ℂ) ↦ 1 / (z - (n + 1 / 2)) + 1 / (z + (n + 1 / 2)))
      (fun z ↦ -(π * tan (π * z))) {z | ∀ k : ℤ, z ≠ k + 1 / 2} := by
  set U : Set ℂ := {z | ∀ k : ℤ, z ≠ k + 1 / 2}
  have hnorm (n : ℕ) : ‖(n : ℂ) + 1 / 2‖ = n + 1 / 2 := by
    rw [show (n : ℂ) + 1 / 2 = ((n + 1 / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  have ha : ∀ᶠ n : ℕ in cofinite, (n : ℂ) + 1 / 2 ≠ 0 :=
    .of_forall fun n ↦ norm_pos_iff.mp (by rw [hnorm]; positivity)
  have hs : Summable fun n : ℕ ↦ (‖(n : ℂ) + 1 / 2‖ ^ 2)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
      (((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)).mul_left 4)
    rw [hnorm, ← div_eq_mul_inv, ← one_div, Nat.cast_add, Nat.cast_one,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h := (hasSumLocallyUniformly_one_div_sub_add_one_div_add ha hs).hasSumLocallyUniformlyOn
    (s := U)
  refine h.congr_right ?_
  -- The sum and `-π tan (π z)` are continuous on `U` and agree off `(1/2) ℤ`, a dense set.
  have hterm (n : ℕ) : ContinuousOn
      (fun z : ℂ ↦ 1 / (z - ((n : ℂ) + 1 / 2)) + 1 / (z + ((n : ℂ) + 1 / 2))) U := by
    refine ContinuousOn.add ?_ ?_ <;>
      refine continuousOn_const.div (by fun_prop) fun z hz ↦ ?_
    · exact sub_ne_zero.mpr (by exact_mod_cast hz n)
    · have := hz (-(n : ℤ) - 1)
      push_cast at this
      exact fun h ↦ this (by linear_combination h)
  have hsum : ContinuousOn
      (fun z ↦ ∑' n : ℕ, (1 / (z - ((n : ℂ) + 1 / 2)) + 1 / (z + ((n : ℂ) + 1 / 2)))) U :=
    (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp h).continuousOn
      (Frequently.of_forall fun s ↦ continuousOn_finsetSum s fun n _ ↦ hterm n)
  have htan : ContinuousOn (fun z : ℂ ↦ -(π * tan (π * z))) U := by
    refine fun z hz ↦ (ContinuousAt.continuousWithinAt ?_)
    refine (continuous_const.continuousAt.mul
      ((continuousAt_tan.mpr fun hc ↦ ?_).comp (by fun_prop))).neg
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hc
    exact hz k (mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) (by linear_combination hk))
  set D : Set ℂ := (range fun k : ℤ ↦ (k : ℂ) / 2)ᶜ
  have hDU : D ⊆ U := fun z hz k hk ↦ hz ⟨2 * k + 1, by push_cast; linear_combination -hk⟩
  have hD : Dense D := (countable_range _).dense_compl ℝ
  refine EqOn.of_subset_closure (fun z hz ↦ ?_) hsum htan hDU (by simp [hD.closure_eq])
  exact (hasSum_neg_pi_mul_tan_of_two_mul_mem
    (mem_integerComplement_iff.mpr fun ⟨k, hk⟩ ↦ hz ⟨k, by linear_combination hk / 2⟩)).tsum_eq

/-- **The half-integer expansion of the tangent.** For every `z ∉ ℤ + 1/2`, including the
integers,
`-π tan (π z) = ∑_{n ≥ 0} (1 / (z - (n + 1/2)) + 1 / (z + (n + 1/2)))`. -/
theorem hasSum_neg_pi_mul_tan {z : ℂ} (hz : ∀ k : ℤ, z ≠ k + 1 / 2) :
    HasSum (fun n : ℕ ↦ 1 / (z - (n + 1 / 2)) + 1 / (z + (n + 1 / 2))) (-(π * tan (π * z))) :=
  hasSumLocallyUniformlyOn_neg_pi_mul_tan.hasSum hz

end TauCeti
