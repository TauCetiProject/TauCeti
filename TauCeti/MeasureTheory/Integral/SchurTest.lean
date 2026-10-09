/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Schur's test and Young's inequality for integral operators

Let `k : α → β → ℝ≥0∞` be a jointly measurable kernel whose row integrals `∫⁻ y, k x y ∂ν` are
at most `A` and whose column integrals `∫⁻ x, k x y ∂μ` are at most `B`. Then, for `1 ≤ p`, the
integral operator `g ↦ (x ↦ ∫⁻ y, k x y * g y ∂ν)` satisfies

`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν`.

When `A` and `B` are finite, this says that it maps `Lᵖ(ν)` to `Lᵖ(μ)` with norm at most
`A ^ (1 - 1/p) * B ^ (1/p)`. For a translation-invariant kernel `k x y = K (x - y)` with `K`
integrable this is Young's inequality for convolution with an `L¹` function; a typical use is for
weakly singular kernels such as `‖x - y‖ ^ (1 - n)` restricted to a bounded set, which bound Riesz
potentials in `Lᵖ`.

More generally, for `1 ≤ p ≤ q` and `1/p + 1/r = 1 + 1/q`, bounds `A` and `B` on the row and
column integrals of `k ^ r` give

`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ ≤ A ^ (q (1 - 1/p)) * B * (∫⁻ y, g y ^ p ∂ν) ^ (q / p)`,

so that the operator maps `Lᵖ(ν)` to `L^q(μ)` with norm at most `A ^ (1 - 1/p) * B ^ (1/q)`. This
is the form needed for operators which improve integrability, such as Riesz potentials on sets
of finite measure. Schur's test is the case `p = q`, `r = 1`.

The proof writes `k g = (k ^ r g ^ p) ^ (1/q) (k ^ r) ^ (1 - 1/p) (g ^ p) ^ (1/p - 1/q)`, applies
Hölder's inequality with these three exponents for each fixed `x`, and then exchanges the order
of integration by Tonelli's theorem.

The statements are in `ℝ≥0∞`, so they need no integrability hypotheses, and the bounds on the row
and column integrals are only required almost everywhere.

## Main declarations

* `TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`: Young's inequality for integral
  kernels.
* `TauCeti.lintegral_rpow_lintegral_mul_le`: Schur's test.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18 and Proposition 6.36.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Hölder's inequality with the three exponents `1/q`, `1 - 1/p` and `1/p - 1/q`, which add up
to `1` when `1/p + 1/r = 1 + 1/q`, applied to the factorization
`k g = (k ^ r g ^ p) ^ (1/q) (k ^ r) ^ (1 - 1/p) (g ^ p) ^ (1/p - 1/q)`. -/
private theorem lintegral_mul_le_of_inv_add_inv_eq {k g : β → ℝ≥0∞} (hk : AEMeasurable k ν)
    (hg : AEMeasurable g ν) {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hr : p⁻¹ + r⁻¹ = 1 + q⁻¹) :
    ∫⁻ y, k y * g y ∂ν ≤ (∫⁻ y, k y ^ r * g y ^ p ∂ν) ^ q⁻¹ * (∫⁻ y, k y ^ r ∂ν) ^ (1 - p⁻¹) *
      (∫⁻ y, g y ^ p ∂ν) ^ (p⁻¹ - q⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hb : 0 ≤ 1 - p⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hp)
  have hc : 0 ≤ p⁻¹ - q⁻¹ := sub_nonneg.2 (inv_anti₀ hp0 hpq)
  have hr0 : 0 < r := inv_pos.1 (by linarith [inv_pos.2 hq0])
  have hkr : r * q⁻¹ + r * (1 - p⁻¹) = 1 := by
    rw [← mul_add, show q⁻¹ + (1 - p⁻¹) = r⁻¹ by linarith, mul_inv_cancel₀ hr0.ne']
  have hgp : p * q⁻¹ + p * (p⁻¹ - q⁻¹) = 1 := by field_simp; ring
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := ν) Finset.univ
    (f := ![fun y => k y ^ r * g y ^ p, fun y => k y ^ r, fun y => g y ^ p])
    (p := ![q⁻¹, 1 - p⁻¹, p⁻¹ - q⁻¹])
    (fun i _ => by
      fin_cases i
      · exact (hk.pow_const r).mul (hg.pow_const p)
      · exact hk.pow_const r
      · exact hg.pow_const p)
    (by simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; ring)
    (fun i _ => by fin_cases i <;> [exact ha; exact hb; exact hc])
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  refine le_trans (lintegral_mono fun y => le_of_eq ?_) h
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc k y * g y = k y ^ (r * q⁻¹ + r * (1 - p⁻¹)) * g y ^ (p * q⁻¹ + p * (p⁻¹ - q⁻¹)) := by
        rw [hkr, hgp, ENNReal.rpow_one, ENNReal.rpow_one]
    _ = _ := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hr0.le hb),
          ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hp0.le hc)]
        ring

/-- **Young's inequality for integral kernels.** Let `1 ≤ p ≤ q` and let `r` be the exponent with
`1/p + 1/r = 1 + 1/q`. If the `r`-th powers of the kernel `k` have row integrals
`∫⁻ y, k x y ^ r ∂ν` at most `A` for almost every `x` and column integrals `∫⁻ x, k x y ^ r ∂μ`
at most `B` for almost every `y`, then the integral operator with kernel `k` satisfies
`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ ≤ A ^ (q (1 - 1/p)) * B * (∫⁻ y, g y ^ p ∂ν) ^ (q / p)`.

For `p = q` this is Schur's test, `TauCeti.lintegral_rpow_lintegral_mul_le`. -/
theorem lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq [SFinite μ] [SFinite ν]
    {k : α → β → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {g : β → ℝ≥0∞}
    (hg : AEMeasurable g ν) {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hr : p⁻¹ + r⁻¹ = 1 + q⁻¹)
    {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ^ r ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ^ r ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ ≤
      A ^ (q * (1 - p⁻¹)) * B * (∫⁻ y, g y ^ p ∂ν) ^ (q / p) := by
  have hq0 : 0 < q := by linarith
  have hc : 0 ≤ p⁻¹ - q⁻¹ := sub_nonneg.2 (inv_anti₀ (by linarith) hpq)
  have hky : ∀ y, Measurable fun x => k x y := fun y => hk.comp measurable_prodMk_right
  set G := ∫⁻ y, g y ^ p ∂ν
  -- Hölder's inequality for each fixed `x`, then Tonelli's theorem.
  have hrow : ∀ x, ∫⁻ y, k x y * g y ∂ν ≤ (∫⁻ y, k x y ^ r * g y ^ p ∂ν) ^ q⁻¹ *
      (∫⁻ y, k x y ^ r ∂ν) ^ (1 - p⁻¹) * G ^ (p⁻¹ - q⁻¹) := fun x =>
    lintegral_mul_le_of_inv_add_inv_eq (hk.comp measurable_prodMk_left).aemeasurable hg hp hpq hr
  have hjoint : AEMeasurable (Function.uncurry fun x y => k x y ^ r * g y ^ p) (μ.prod ν) :=
    (hk.pow_const r).aemeasurable.mul (hg.pow_const p).comp_snd
  calc
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ
        ≤ ∫⁻ x, A ^ (q * (1 - p⁻¹)) * G ^ (q * (p⁻¹ - q⁻¹)) *
            ∫⁻ y, k x y ^ r * g y ^ p ∂ν ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [hA] with x hx
      calc
        _ ≤ ((∫⁻ y, k x y ^ r * g y ^ p ∂ν) ^ q⁻¹ * (∫⁻ y, k x y ^ r ∂ν) ^ (1 - p⁻¹) *
              G ^ (p⁻¹ - q⁻¹)) ^ q := ENNReal.rpow_le_rpow (hrow x) hq0.le
        _ = (∫⁻ y, k x y ^ r * g y ^ p ∂ν) * (∫⁻ y, k x y ^ r ∂ν) ^ (q * (1 - p⁻¹)) *
              G ^ (q * (p⁻¹ - q⁻¹)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one, mul_comm (1 - p⁻¹), mul_comm (p⁻¹ - q⁻¹)]
        _ ≤ (∫⁻ y, k x y ^ r * g y ^ p ∂ν) * A ^ (q * (1 - p⁻¹)) * G ^ (q * (p⁻¹ - q⁻¹)) := by
          have := mul_nonneg hq0.le (sub_nonneg.2 (inv_le_one_of_one_le₀ hp))
          gcongr
        _ = _ := by ring
    _ = A ^ (q * (1 - p⁻¹)) * G ^ (q * (p⁻¹ - q⁻¹)) *
          ∫⁻ y, ∫⁻ x, k x y ^ r * g y ^ p ∂μ ∂ν := by
      have hmeas : AEMeasurable (fun x => ∫⁻ y, k x y ^ r * g y ^ p ∂ν) μ :=
        hjoint.lintegral_prod_right'
      rw [lintegral_const_mul'' _ hmeas, lintegral_lintegral_swap hjoint]
    _ = A ^ (q * (1 - p⁻¹)) * G ^ (q * (p⁻¹ - q⁻¹)) *
          ∫⁻ y, (∫⁻ x, k x y ^ r ∂μ) * g y ^ p ∂ν := by
      simp_rw [lintegral_mul_const _ ((hky _).pow_const r)]
    _ ≤ A ^ (q * (1 - p⁻¹)) * G ^ (q * (p⁻¹ - q⁻¹)) * ∫⁻ y, B * g y ^ p ∂ν := by
      gcongr 1
      refine lintegral_mono_ae ?_
      filter_upwards [hB] with y hy
      gcongr
    _ = A ^ (q * (1 - p⁻¹)) * B * G ^ (q / p) := by
      rw [lintegral_const_mul'' _ (hg.pow_const p),
        show q / p = q * (p⁻¹ - q⁻¹) + 1 by field_simp; ring,
        ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hq0.le hc) zero_le_one, ENNReal.rpow_one]
      ring

/-- **Schur's test.** If the kernel `k` has row integrals `∫⁻ y, k x y ∂ν` at most `A` for almost
every `x` and column integrals `∫⁻ x, k x y ∂μ` at most `B` for almost every `y`, then for
`1 ≤ p` the integral operator with kernel `k` satisfies
`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν`. -/
theorem lintegral_rpow_lintegral_mul_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) {g : β → ℝ≥0∞} (hg : AEMeasurable g ν) {p : ℝ}
    (hp : 1 ≤ p) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν := by
  have h := lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq (r := 1) hk hg hp le_rfl
    (by rw [inv_one, add_comm]) (by simpa only [ENNReal.rpow_one] using hA)
    (by simpa only [ENNReal.rpow_one] using hB)
  rwa [mul_one_sub, mul_inv_cancel₀ (by linarith), div_self (by linarith), ENNReal.rpow_one] at h

end TauCeti
