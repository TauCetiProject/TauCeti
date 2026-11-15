/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
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

(the first is DLMF, eq. 4.22.3, at the argument `π z`). The paired term
`1 / (z - a) + 1 / (z + a) = 2 z / (z² - a²)` is `O(|a|⁻²)` uniformly for `z` in a bounded set
(`TauCeti.norm_one_div_sub_add_one_div_add_le`). So for any family of poles `a i` with
`∑ |a i|⁻² < ∞`, the paired series converges locally uniformly on all of `ℂ`, the terms at the
poles taking their totalized values (`TauCeti.hasSumLocallyUniformly_one_div_sub_add_one_div_add`).
The pairing is essential: for the poles `a n = n + 1` the one-sided series `∑ 1 / (z - a n)`
diverges.

For the cotangent, this upgrades Mathlib's pointwise expansion `cot_series_rep'` to locally
uniform convergence on the integer complement (`TauCeti.hasSumLocallyUniformlyOn_cotTerm`). For
the tangent, the pointwise expansion off the half-integer multiples `(1/2) ℤ` is the odd-pole part
of the cotangent expansion at `2 z` (`TauCeti.hasSum_cotTerm_two_mul`), with
`cot (2 w) = (cot w - tan w) / 2`. At the integers, where the cotangent expansions do not apply,
both sides are continuous on the complement of `ℤ + 1/2` and agree on a dense subset, so the
expansion holds there too (`TauCeti.hasSum_neg_pi_mul_tan`).

## Main results

* `TauCeti.norm_one_div_sub_add_one_div_add_le`: the bound `4 R / |a|²` on the paired term.
* `TauCeti.hasSumLocallyUniformly_one_div_sub_add_one_div_add`: locally uniform convergence of
  paired series with inverse-square summable poles.
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

/-- The paired term `1 / (z - a) + 1 / (z + a)` is bounded by `4 R / ‖a‖²` when `‖z‖ ≤ R` and
`2 R ≤ ‖a‖`. -/
theorem norm_one_div_sub_add_one_div_add_le {z a : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R)
    (ha : 2 * R ≤ ‖a‖) : ‖1 / (z - a) + 1 / (z + a)‖ ≤ 4 * R / ‖a‖ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  rcases eq_or_ne a 0 with rfl | ha₀
  · obtain rfl : z = 0 := norm_le_zero_iff.mp (hz.trans (by rw [norm_zero] at ha; linarith))
    simp
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha₀
  have hza : ‖z‖ < ‖a‖ := by linarith
  have h₁ : z - a ≠ 0 := fun h ↦ hza.ne (by rw [sub_eq_zero.mp h])
  have h₂ : z + a ≠ 0 := fun h ↦ hza.ne (by rw [eq_neg_of_add_eq_zero_left h, norm_neg])
  have heq : 1 / (z - a) + 1 / (z + a) = 2 * z / ((z - a) * (z + a)) := by
    field_simp
    ring
  have hlow : 3 / 4 * ‖a‖ ^ 2 ≤ ‖(z - a) * (z + a)‖ := by
    have h := norm_sub_norm_le (a ^ 2) (z ^ 2)
    rw [norm_pow, norm_pow, norm_sub_rev, show z ^ 2 - a ^ 2 = (z - a) * (z + a) by ring] at h
    nlinarith [mul_self_le_mul_self (norm_nonneg z) (hz.trans (by linarith : R ≤ ‖a‖ / 2))]
  rw [heq, norm_div, norm_mul, RCLike.norm_ofNat,
    div_le_div_iff₀ (norm_pos_iff.mpr (mul_ne_zero h₁ h₂)) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ 4 * R),
    mul_le_mul_of_nonneg_right hz (sq_nonneg ‖a‖)]

/-- **Locally uniform convergence of paired partial-fraction series.** If the poles `a i` tend to
infinity and `∑ ‖a i‖⁻² < ∞`, then `∑ (1 / (z - a i) + 1 / (z + a i))` converges locally uniformly
on `ℂ`, the terms at the poles taking their totalized values. -/
theorem hasSumLocallyUniformly_one_div_sub_add_one_div_add {ι : Type*} {a : ι → ℂ}
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) (hs : Summable fun i ↦ (‖a i‖ ^ 2)⁻¹) :
    HasSumLocallyUniformly (fun i z ↦ 1 / (z - a i) + 1 / (z + a i))
      (fun z ↦ ∑' i, (1 / (z - a i) + 1 / (z + a i))) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hs.mul_left (4 * R)) ?_
  filter_upwards [ha.eventually_ge_atTop (2 * R)] with i hi z hz
  simpa only [div_eq_mul_inv] using norm_one_div_sub_add_one_div_add_le (hR z hz) hi

/-- **The cotangent expansion converges locally uniformly.** The paired series
`∑_{n ≥ 0} (1 / (z - (n + 1)) + 1 / (z + (n + 1)))` of Mathlib's `cot_series_rep'` converges to
`π cot (π z) - 1 / z` locally uniformly on `ℂ \ ℤ`. -/
theorem hasSumLocallyUniformlyOn_cotTerm :
    HasSumLocallyUniformlyOn (fun n z ↦ cotTerm z n) (fun z ↦ π * cot (π * z) - 1 / z)
      integerComplement := by
  have hnorm (n : ℕ) : ‖(n : ℂ) + 1‖ = n + 1 := by exact_mod_cast norm_natCast (n + 1)
  have ha : Tendsto (fun n : ℕ ↦ ‖(n : ℂ) + 1‖) cofinite atTop := by
    simp only [hnorm, Nat.cofinite_eq_atTop]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
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
  have ha : Tendsto (fun n : ℕ ↦ ‖(n : ℂ) + 1 / 2‖) cofinite atTop := by
    simp only [hnorm, Nat.cofinite_eq_atTop]
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
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
