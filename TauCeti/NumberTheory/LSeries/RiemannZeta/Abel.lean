/-
Copyright (c) 2026 Matteo Cipollina and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import TauCeti.Analysis.MellinTransform.UpperTail
import TauCeti.Analysis.Complex.HalfPlaneIdentity

/-!
# The ordinary Abel integral for the Riemann zeta function

The fractional-part integral isolates the simple pole of the Riemann zeta function and
bounds its analytic remainder throughout the right half-plane. Unlike the alternating-series
representation, this formula has no factor `1 - 2 ^ (1 - s)`, which vanishes at additional
points on `re s = 1`. It gives polynomial vertical growth bounds for the pole-subtracted
function and for `ζ` away from its pole.

## Main results

* `TauCeti.integrableOn_fract_mul_cpow`, `TauCeti.norm_integral_fract_mul_cpow_le` and
  `TauCeti.differentiableAt_integral_fract_mul_cpow`: absolute convergence, a quantitative bound
  and holomorphy of the fractional-part integral on `0 < re s`, including `s = 1`.

* `TauCeti.riemannZeta₀_eq_one_sub_mul_integral_fract`: on `0 < re s`, including `s = 1`,
  the entire pole-subtracted function satisfies `ζ₀(s) = 1 - s ∫₁^∞ {t} t^(-s-1) dt`.
* `TauCeti.norm_riemannZeta₀_le_of_re_pos`: `‖ζ₀(s)‖ ≤ 1 + ‖s‖ / re s` on that half-plane.
* `TauCeti.riemannZeta_eq_sub_integral_fract` and `TauCeti.norm_riemannZeta_le_of_re_pos`:
  the ordinary Abel formula when `0 < re s`, `s ≠ 1`, and a bound including the totalized value
  at `s = 1`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1.

## Provenance

The ordinary formula and its quantitative use were formalized by Matteo Cipollina in
[PNT+ RiemannZetaAbelKernel.lean](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/e316efa96ec1faa14c06dccf912b7f1bcefb4d2a/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelKernel.lean)
and [RiemannZetaAbelContinuation.lean](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/e316efa96ec1faa14c06dccf912b7f1bcefb4d2a/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelContinuation.lean),
the project of Alex Kontorovich and Terence Tao. The present proof uses the native Mellin and
Abel APIs.
-/

public section

open Set Filter Topology MeasureTheory Complex Asymptotics
open scoped Topology

namespace TauCeti

private theorem norm_fract_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  simpa only [norm_real, Real.norm_eq_abs, Int.abs_fract] using (Int.fract_lt_one t).le

private theorem locallyIntegrableOn_fract :
    LocallyIntegrableOn (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ)) (Ici 1) :=
  (locallyIntegrableOn_const (1 : ℝ)).mono measurable_fract.complex_ofReal.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ by simpa only [norm_one] using norm_fract_le t)

private theorem isBigO_fract :
    (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ)) =O[atTop] fun t ↦ t ^ (0 : ℝ) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ by
    simpa only [Real.rpow_zero, norm_one, one_mul] using norm_fract_le t)

/-- For `0 < s.re`, the fractional-part kernel in the Abel formula is integrable on
`(1, ∞)`, including when `s = 1`. -/
theorem integrableOn_fract_mul_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) :=
  integrableOn_mul_cpow_of_isBigO locallyIntegrableOn_fract isBigO_fract hs

/-- The fractional-part integral in the Abel formula has norm at most `1 / s.re`
on the right half-plane, including at `s = 1`. -/
theorem norm_integral_fract_mul_cpow_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 1 / s.re :=
  norm_integral_mul_cpow_le_of_bound (fun t _ ↦ norm_fract_le t) hs

/-- The fractional-part integral in the Abel formula is complex-differentiable throughout
the right half-plane, including at `s = 1`. -/
theorem differentiableAt_integral_fract_mul_cpow {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1))) s :=
  (differentiableOn_integral_mul_cpow_of_isBigO isBigO_fract).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

private theorem abel_initial (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s *
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ _k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    simp
  have H := LSeries_eq_mul_integral (1 : ℕ → ℂ) (by norm_num : (0 : ℝ) ≤ 1) hs
    (LSeriesSummable_one_iff.mpr hs) hO
  rw [LSeries_one_eq_riemannZeta hs] at H
  simp only [Pi.one_apply] at H
  have hfloor : (fun t : ℝ ↦ (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) *
      (t : ℂ) ^ (-(s + 1))) =ᵐ[volume.restrict (Ioi 1)]
      (fun t : ℝ ↦ (t : ℂ) ^ (-s) -
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Set.mem_Ioi] at ht
    have ht0 : 0 ≤ t := by linarith
    have hf : (⌊t⌋₊ : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      have hr : (⌊t⌋₊ : ℝ) = t - Int.fract t := by
        rw [natCast_floor_eq_intCast_floor ht0]
        linarith [Int.self_sub_floor t]
      exact_mod_cast hr
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, hf,
      sub_mul]
    congr 1
    calc
      (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ)^1 * (t : ℂ)^(-(s + 1)) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^(1 + (-(s + 1))) := (Complex.cpow_add _ _ (ofReal_ne_zero.mpr (by linarith))).symm
      _ = _ := by congr 1; ring
  rw [integral_congr_ae hfloor, integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one)
      (integrableOn_fract_mul_cpow (zero_lt_one.trans hs)),
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one] at H
  simp only [ofReal_one, one_cpow] at H
  rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq] at H
  rw [H]
  ring

/-- The Abel integral for the entire pole-subtracted zeta function on `0 < s.re`,
including `s = 1`. -/
theorem riemannZeta₀_eq_one_sub_mul_integral_fract {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s = 1 - s *
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let G : ℂ → ℂ := fun z ↦ 1 - z *
    ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1))
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.re} :=
    fun z hz ↦ ((differentiableAt_const (1 : ℂ)).sub
      (differentiableAt_id.mul
        (differentiableAt_integral_fract_mul_cpow hz))).differentiableWithinAt
  have heq : EqOn G riemannZeta₀ {z : ℂ | 1 < z.re} := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
    have hratio : z / (z - 1) = 1 + (z - 1)⁻¹ := by
      field_simp [sub_ne_zero.mpr hz1]
      ring
    have H := abel_initial z hz
    rw [riemannZeta_eq_inv_sub_add hz1, hratio] at H
    dsimp only [G]
    linear_combination -H
  exact (hG.eqOn_of_eqOn_re_gt differentiable_riemannZeta₀.differentiableOn heq hs).symm

/-- On the right half-plane, the pole-subtracted zeta function satisfies
`‖ζ₀(s)‖ ≤ 1 + ‖s‖ / s.re`, including at `s = 1`. -/
theorem norm_riemannZeta₀_le_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  rw [riemannZeta₀_eq_one_sub_mul_integral_fract hs]
  calc
    _ ≤ 1 + ‖s‖ * ‖∫ t in Ioi (1 : ℝ),
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ := by
      simpa only [norm_one, norm_mul] using norm_sub_le (1 : ℂ)
        (s * ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
    _ ≤ 1 + ‖s‖ * (1 / s.re) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_integral_fract_mul_cpow_le hs)
        (norm_nonneg s))
    _ = _ := by ring

/-- On `0 < s.re`, `s ≠ 1`, the ordinary Abel formula isolates the simple pole of `ζ`.
The identity excludes `s = 1`, where both expressions have totalized values. -/
theorem riemannZeta_eq_sub_integral_fract {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s *
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_inv_sub_add hs1, riemannZeta₀_eq_one_sub_mul_integral_fract hs]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- Mathlib's totalized value of the Riemann zeta function at its pole has norm at most two. -/
theorem norm_riemannZeta_one_le_two : ‖riemannZeta 1‖ ≤ 2 := by
  have hlog0 : 0 ≤ Real.log (4 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.two_le_pi])
  have hlog4 : Real.log (4 * Real.pi) ≤ 4 := by
    calc
      _ ≤ Real.log (2 ^ 4 : ℝ) :=
        Real.log_le_log (by positivity) (by nlinarith [Real.pi_le_four])
      _ = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 4 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have habs : |Real.eulerMascheroniConstant - Real.log (4 * Real.pi)| ≤ 4 :=
    abs_le.mpr ⟨by linarith [Real.one_half_lt_eulerMascheroniConstant],
      by linarith [Real.eulerMascheroniConstant_lt_two_thirds]⟩
  have hdiv : |Real.eulerMascheroniConstant - Real.log (4 * Real.pi)| / 2 ≤ 2 := by
    linarith
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = (Real.log (4 * Real.pi) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)).symm
  rw [riemannZeta_one, hlog, ← Complex.ofReal_sub, norm_div, norm_real,
    Real.norm_eq_abs, Complex.norm_ofNat]
  exact hdiv

/-- On the right half-plane `0 < s.re`,
`‖ζ(s)‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re`, including Mathlib's totalized value at `s = 1`. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := by
  by_cases hs1 : s = 1
  · subst s
    simp only [sub_self, inv_zero, norm_zero, add_zero, norm_one, one_re, div_one,
      one_add_one_eq_two]
    exact norm_riemannZeta_one_le_two
  · rw [riemannZeta_eq_inv_sub_add hs1]
    exact (norm_add_le _ _).trans (by linarith [norm_riemannZeta₀_le_of_re_pos hs])

end TauCeti
