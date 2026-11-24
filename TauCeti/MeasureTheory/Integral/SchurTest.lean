/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Schur's test and Young's inequality for integral operators

Let `k : α → β → ℝ≥0∞` be an a.e. measurable kernel whose row integrals `∫⁻ y, k x y ∂ν` are
at most `A` and whose column integrals `∫⁻ x, k x y ∂μ` are at most `B`. Then, for `1 ≤ p`, the
integral operator `g ↦ (x ↦ ∫⁻ y, k x y * g y ∂ν)` satisfies

`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν`.

When `A` and `B` are finite, this says that it maps `Lᵖ(ν)` to `Lᵖ(μ)` with norm at most
`A ^ (1 - 1/p) * B ^ (1/p)`; `TauCeti.eLpNorm_lintegral_mul_le` states this for `1 ≤ p ≤ ∞`,
where for `p = ∞` only the row bound is used. For a translation-invariant kernel
`k x y = K (x - y)` with `K` integrable this is Young's inequality for convolution with an `L¹`
function; a typical use is for weakly singular kernels such as `‖x - y‖ ^ (1 - n)` restricted to
a bounded set, which bound Riesz potentials in `Lᵖ`.

More generally, for `1 ≤ p ≤ q` and `1/p + 1/r = 1 + 1/q`, bounds `A` and `B` on the row and
column integrals of `k ^ r` give

`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ ≤ A ^ (q (1 - 1/p)) * B * (∫⁻ y, g y ^ p ∂ν) ^ (q / p)`,

so that the operator maps `Lᵖ(ν)` to `L^q(μ)` with norm at most `A ^ (1 - 1/p) * B ^ (1/q)`. This
is the form needed for operators which improve integrability, such as Riesz potentials on sets
of finite measure. Schur's test is the case `p = q`, `r = 1`.

The proof writes `k g = (k ^ r g ^ p) ^ (1/q) (k ^ r) ^ (1 - 1/p) (g ^ p) ^ (1/p - 1/q)`, applies
Hölder's inequality with these three exponents for each fixed `x`
(`TauCeti.lintegral_mul_le_of_inv_add_inv_eq`), and then exchanges the order of integration by
Tonelli's theorem.

The statements are in `ℝ≥0∞`, so they need no integrability hypotheses, and the bounds on the row
and column integrals are only required almost everywhere.

## Main declarations

* `TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`: Young's inequality for integral
  kernels.
* `TauCeti.lintegral_rpow_lintegral_mul_le`: Schur's test.
* `TauCeti.eLpNorm_lintegral_mul_le_of_le`, `TauCeti.memLp_lintegral_mul_of_le`: Young's
  inequality as an `Lᵖ → L^q` bound and membership for `1 ≤ p ≤ q ≤ ∞` with `(p, q) ≠ (1, ∞)`.
* `TauCeti.eLpNorm_lintegral_mul_le`: Schur's test as an `Lᵖ` bound, including `p = ∞`.
* `TauCeti.rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top`: finiteness of the constant
  `A ^ (1 - 1/p) * B ^ (1/q)` for finite `A` and `B`.
* `TauCeti.memLp_lintegral_mul`: hence the kernel maps `Lᵖ` to `Lᵖ` for finite `A` and `B`.
* `TauCeti.lintegral_lintegral_mul_mul_le`: Schur's test for the bilinear form
  `∫∫ f(x) k(x, y) g(y)`, bounded by `‖f‖_p ‖g‖_q` for Hölder conjugate `p` and `q`.
* `TauCeti.tsum_tsum_mul_mul_le`: the bilinear form of a convolution kernel on a countable group.
* `TauCeti.lintegral_lintegral_mul_indicator_ball_mul_le`: the bilinear form for the kernel
  `1_{|x - y| < R}` on the real line, whose rows and columns have length `2R`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18 and Proposition 6.36.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal NNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Young's inequality for integral kernels for a jointly measurable kernel; see
`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq` for the a.e. measurable case. -/
private theorem lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq_of_measurable
    [SFinite μ] [SFinite ν]
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

/-- **Young's inequality for integral kernels.** Let `1 ≤ p ≤ q` and let `r` be the exponent with
`1/p + 1/r = 1 + 1/q`. If the `r`-th powers of the kernel `k` have row integrals
`∫⁻ y, k x y ^ r ∂ν` at most `A` for almost every `x` and column integrals `∫⁻ x, k x y ^ r ∂μ`
at most `B` for almost every `y`, then the integral operator with kernel `k` satisfies
`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ ≤ A ^ (q (1 - 1/p)) * B * (∫⁻ y, g y ^ p ∂ν) ^ (q / p)`.

The kernel need only be a.e. measurable: the proof applies the measurable case to a measurable
modification of `k`, which agrees with `k` on almost every row and on almost every column.
For `p = q` this is Schur's test, `TauCeti.lintegral_rpow_lintegral_mul_le`. -/
theorem lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq [SFinite μ] [SFinite ν]
    {k : α → β → ℝ≥0∞} (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {g : β → ℝ≥0∞}
    (hg : AEMeasurable g ν) {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hr : p⁻¹ + r⁻¹ = 1 + q⁻¹)
    {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ^ r ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ^ r ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q ∂μ ≤
      A ^ (q * (1 - p⁻¹)) * B * (∫⁻ y, g y ^ p ∂ν) ^ (q / p) := by
  set k' : α → β → ℝ≥0∞ := Function.curry (hk.mk _)
  have hrow : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, k x y = k' x y := Measure.ae_ae_of_ae_prod hk.ae_eq_mk
  have hcol : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, k x y = k' x y := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hk.ae_eq_mk)
  have h := lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq_of_measurable (k := k')
    hk.measurable_mk hg hp hpq hr
    (by
      filter_upwards [hA, hrow] with x hx hx'
      rwa [lintegral_congr_ae (hx'.mono fun y hy ↦ by rw [hy])] at hx)
    (by
      filter_upwards [hB, hcol] with y hy hy'
      rwa [lintegral_congr_ae (hy'.mono fun x hx ↦ by rw [hx])] at hy)
  refine le_of_eq_of_le (lintegral_congr_ae ?_) h
  filter_upwards [hrow] with x hx
  rw [lintegral_congr_ae (hx.mono fun y hy ↦ by rw [hy])]

/-- **Schur's test.** If the kernel `k` has row integrals `∫⁻ y, k x y ∂ν` at most `A` for almost
every `x` and column integrals `∫⁻ x, k x y ∂μ` at most `B` for almost every `y`, then for
`1 ≤ p` the integral operator with kernel `k` satisfies
`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν`. -/
theorem lintegral_rpow_lintegral_mul_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {g : β → ℝ≥0∞} (hg : AEMeasurable g ν)
    {p : ℝ} (hp : 1 ≤ p) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν := by
  have h := lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq (r := 1) hk hg hp le_rfl
    (by rw [inv_one, add_comm]) (by simpa only [ENNReal.rpow_one] using hA)
    (by simpa only [ENNReal.rpow_one] using hB)
  rwa [mul_one_sub, mul_inv_cancel₀ (by linarith), div_self (by linarith), ENNReal.rpow_one] at h

/-- For finite `A` and `B`, the constant `A ^ (1 - 1/p) * B ^ (1/q)` of Young's inequality is the
coercion of the same expression in `ℝ≥0`. -/
theorem coe_rpow_one_sub_toReal_inv_mul_rpow_toReal_inv {p q : ℝ≥0∞} (hp : 1 ≤ p) (A B : ℝ≥0) :
    ((A ^ (1 - p.toReal⁻¹) * B ^ q.toReal⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (A : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * (B : ℝ≥0∞) ^ q.toReal⁻¹ := by
  have h₀ : 0 ≤ 1 - p.toReal⁻¹ := by
    simpa only [one_div] using ENNReal.one_sub_one_div_toReal_nonneg hp
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ h₀,
    ENNReal.coe_rpow_of_nonneg _ (by positivity)]

/-- The constant `A ^ (1 - 1/p) * B ^ (1/q)` of Young's inequality is finite for finite `A`
and `B`. -/
theorem rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (A B : ℝ≥0) : (A : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * (B : ℝ≥0∞) ^ q.toReal⁻¹ < ∞ :=
  coe_rpow_one_sub_toReal_inv_mul_rpow_toReal_inv hp A B ▸ ENNReal.coe_lt_top

/-- **Young's inequality for integral kernels** as an `Lᵖ → L^q` bound: for `1 ≤ p ≤ q ≤ ∞` with
`p.toReal⁻¹ - q.toReal⁻¹ < 1` (excluding only `(p, q) = (1, ∞)`) and
`r = (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹`, if the `r`-th powers of `k` have row integrals at most `A`
almost everywhere and column integrals at most `B` almost everywhere, then
`‖x ↦ ∫⁻ y, k x y * g y ∂ν‖_q ≤ A ^ (1 - 1/p) * B ^ (1/q) * ‖g‖_p`.
For `q = ∞` the exponent `1/q` is `0`, so only the row bound is used. -/
theorem eLpNorm_lintegral_mul_le_of_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {g : β → ℝ≥0∞} (hg : AEMeasurable g ν)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hδ : p.toReal⁻¹ - q.toReal⁻¹ < 1) {A B : ℝ≥0∞}
    (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ^ (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ^ (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹ ∂μ ≤ B) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * g y ∂ν) q μ ≤
      A ^ (1 - p.toReal⁻¹) * B ^ q.toReal⁻¹ * eLpNorm g p ν := by
  have hmeas : AEMeasurable (fun x ↦ ∫⁻ y, k x y * g y ∂ν) μ :=
    (hk.mul hg.comp_snd).lintegral_prod_right'
  rcases eq_or_ne q ∞ with rfl | hq_top
  · rcases hp.eq_or_lt with rfl | hp1
    · norm_num at hδ
    have h0 : 0 ≤ 1 - p.toReal⁻¹ := by
      simpa only [one_div] using ENNReal.one_sub_one_div_toReal_nonneg hp
    simp only [eLpNorm_exponent_top hmeas.aestronglyMeasurable, ENNReal.toReal_top, inv_zero,
      sub_zero, ENNReal.rpow_zero, mul_one] at hA ⊢
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hA, Measure.ae_ae_of_ae_prod hk.ae_eq_mk] with x hx hx'
    have hkx : AEMeasurable (k x) ν :=
      (hk.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr (hx'.mono fun _ ↦ Eq.symm)
    rw [eNorm_eq_self]
    exact (lintegral_mul_le_rpow_mul_eLpNorm hkx hp1).trans
      (mul_le_mul_left (ENNReal.rpow_le_rpow hx h0) _)
  have hp_top : p ≠ ∞ := (hpq.trans_lt hq_top.lt_top).ne
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (hp.trans hpq)).ne'
  have hp_real : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  have hq_pos : 0 < q.toReal := by linarith
  have hr_eq : p.toReal⁻¹ + ((1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹)⁻¹ = 1 + q.toReal⁻¹ := by
    rw [inv_inv]; ring
  have hexp₁ : q.toReal * (1 - p.toReal⁻¹) * (1 / q.toReal) = 1 - p.toReal⁻¹ := by field_simp
  have hexp₂ : q.toReal / p.toReal * (1 / q.toReal) = 1 / p.toReal := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq_top hmeas.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hg.aestronglyMeasurable]
  simp only [eNorm_eq_self]
  calc (∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ (A ^ (q.toReal * (1 - p.toReal⁻¹)) * B *
          (∫⁻ y, g y ^ p.toReal ∂ν) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
        gcongr
        exact lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq hk hg hp_real hpq_real hr_eq hA hB
    _ = A ^ (1 - p.toReal⁻¹) * B ^ q.toReal⁻¹ *
          (∫⁻ y, g y ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          hexp₁, hexp₂, one_div q.toReal]

/-- **Young's inequality for integral kernels** as `Lᵖ → L^q` membership: for `1 ≤ p ≤ q ≤ ∞` with
`p.toReal⁻¹ - q.toReal⁻¹ < 1`, if the `(1 - (1/p - 1/q))⁻¹`-th powers of `k` have row integrals at
most `A < ∞` almost everywhere and column integrals at most `B < ∞` almost everywhere, then
`x ↦ ∫⁻ y, k x y * g y ∂ν` lies in `L^q(μ)` whenever `g ∈ Lᵖ(ν)`. -/
theorem memLp_lintegral_mul_of_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {p q : ℝ≥0∞} {g : β → ℝ≥0∞}
    (hg : MemLp g p ν) (hp : 1 ≤ p) (hpq : p ≤ q) (hδ : p.toReal⁻¹ - q.toReal⁻¹ < 1) {A B : ℝ≥0}
    (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ^ (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹ ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ^ (1 - (p.toReal⁻¹ - q.toReal⁻¹))⁻¹ ∂μ ≤ B) :
    MemLp (fun x ↦ ∫⁻ y, k x y * g y ∂ν) q μ :=
  (eLpNorm_lintegral_mul_le_of_le hk hg.aestronglyMeasurable.aemeasurable hp hpq hδ hA hB).trans_lt
    (ENNReal.mul_lt_top (rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top hp A B)
      hg.eLpNorm_lt_top)

/-- **Schur's test** as an `Lᵖ` bound: if the kernel `k` has row integrals `∫⁻ y, k x y ∂ν` at
most `A` for almost every `x` and column integrals `∫⁻ x, k x y ∂μ` at most `B` for almost every
`y`, then for `1 ≤ p ≤ ∞`,
`‖x ↦ ∫⁻ y, k x y * g y ∂ν‖_p ≤ A ^ (1 - 1/p) * B ^ (1/p) * ‖g‖_p`.
For `p = ∞` the exponent `1/p` is `0`, so the bound is `A * ‖g‖_∞`. -/
theorem eLpNorm_lintegral_mul_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {g : β → ℝ≥0∞} (hg : AEMeasurable g ν)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * g y ∂ν) p μ ≤
      A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ * eLpNorm g p ν :=
  eLpNorm_lintegral_mul_le_of_le hk hg hp le_rfl (by simp)
    (by simpa only [sub_self, sub_zero, inv_one, ENNReal.rpow_one] using hA)
    (by simpa only [sub_self, sub_zero, inv_one, ENNReal.rpow_one] using hB)

/-- **Schur's test** as `Lᵖ` membership: if the kernel `k` has row integrals `∫⁻ y, k x y ∂ν` at
most `A < ∞` for almost every `x` and column integrals `∫⁻ x, k x y ∂μ` at most `B < ∞` for almost
every `y`, then for `1 ≤ p ≤ ∞` and `g ∈ Lᵖ(ν)` the function `x ↦ ∫⁻ y, k x y * g y ∂ν` is in
`Lᵖ(μ)`. -/
theorem memLp_lintegral_mul [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {p : ℝ≥0∞} {g : β → ℝ≥0∞}
    (hg : MemLp g p ν) (hp : 1 ≤ p) {A B : ℝ≥0} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B) :
    MemLp (fun x ↦ ∫⁻ y, k x y * g y ∂ν) p μ :=
  (eLpNorm_lintegral_mul_le hk hg.aestronglyMeasurable.aemeasurable hp hA hB).trans_lt
    (ENNReal.mul_lt_top (rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top hp A B)
      hg.eLpNorm_lt_top)

/-- **Schur's test** for the bilinear form of a kernel: if `k` has row integrals
`∫⁻ y, k x y ∂ν` at most `A` for almost every `x` and column integrals `∫⁻ x, k x y ∂μ` at most
`B` for almost every `y`, then for Hölder conjugate `p` and `q`,
`∫∫ f(x) k(x, y) g(y) ≤ A ^ (1 - 1/q) * B ^ (1/q) * ‖f‖_p * ‖g‖_q`. -/
theorem lintegral_lintegral_mul_mul_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : AEMeasurable (Function.uncurry k) (μ.prod ν)) {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B) :
    ∫⁻ x, ∫⁻ y, f x * (k x y * g y) ∂ν ∂μ ≤
      A ^ (1 - q.toReal⁻¹) * B ^ q.toReal⁻¹ * eLpNorm f p μ * eLpNorm g q ν := by
  have hkg : AEMeasurable (Function.uncurry fun x y ↦ k x y * g y) (μ.prod ν) :=
    hk.mul hg.comp_snd
  set H := fun x ↦ ∫⁻ y, k x y * g y ∂ν
  have hH : AEMeasurable H μ := hkg.lintegral_prod_right'
  calc ∫⁻ x, ∫⁻ y, f x * (k x y * g y) ∂ν ∂μ = eLpNorm (f * H) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm (hf.mul hH).aestronglyMeasurable]
        refine lintegral_congr_ae ?_
        filter_upwards [hkg.prodMk_left] with x hx
        rw [eNorm_eq_self, Pi.mul_apply]
        exact lintegral_const_mul'' _ hx
    _ ≤ eLpNorm f p μ * eLpNorm H q μ := eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal_of_pos one_pos
    _ ≤ eLpNorm f p μ * (A ^ (1 - q.toReal⁻¹) * B ^ q.toReal⁻¹ * eLpNorm g q ν) := by
        gcongr
        exact eLpNorm_lintegral_mul_le hk hg (ENNReal.HolderConjugate.one_le (p := q) (q := p))
          hA hB
    _ = _ := by ring

/-- The kernel `1_{dist x y < R}` is measurable. -/
theorem measurable_uncurry_indicator_ball {γ : Type*} [PseudoMetricSpace γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] [SecondCountableTopology γ] (R : ℝ) :
    Measurable (Function.uncurry fun x y : γ ↦ (Metric.ball x R).indicator (1 : γ → ℝ≥0∞) y) := by
  have : (Function.uncurry fun x y : γ ↦ (Metric.ball x R).indicator (1 : γ → ℝ≥0∞) y) =
      {p : γ × γ | dist p.2 p.1 < R}.indicator 1 := by
    ext p
    simp [Set.indicator, Metric.mem_ball, Function.uncurry]
  rw [this]
  exact measurable_one.indicator
    (measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const)

/-- **Schur's test for a convolution kernel on a countable group**: for `w, y, z : G → ℝ≥0∞`,
`∑_{k, l} w(k - l) yₖ zₗ ≤ (∑ₘ w(m)) (∑ₖ yₖ²)^{1/2} (∑ₗ zₗ²)^{1/2}`. This is
`TauCeti.lintegral_lintegral_mul_mul_le` for the counting measure, whose rows and columns all have
sum `∑ₘ w(m)`. -/
theorem tsum_tsum_mul_mul_le {G : Type*} [AddGroup G] [Countable G] (w y z : G → ℝ≥0∞) :
    ∑' k, ∑' l, w (k - l) * (y k * z l) ≤
      (∑' m, w m) * (∑' k, y k ^ 2) ^ (2⁻¹ : ℝ) * (∑' l, z l ^ 2) ^ (2⁻¹ : ℝ) := by
  let _ : MeasurableSpace G := ⊤
  set W := ∑' m, w m
  have hrow (k : G) : ∫⁻ l, w (k - l) ∂Measure.count ≤ W := by
    rw [lintegral_count]; exact ((Equiv.subLeft k).tsum_eq w).le
  have hcol (l : G) : ∫⁻ k, w (k - l) ∂Measure.count ≤ W := by
    rw [lintegral_count]; exact ((Equiv.subRight l).tsum_eq w).le
  have hnorm (y : G → ℝ≥0∞) : eLpNorm y 2 Measure.count = (∑' k, y k ^ 2) ^ (2⁻¹ : ℝ) := by
    rw [← lintegral_count,
      ← eLpNorm_two_sq_eq_lintegral_sq (measurable_of_countable y).aemeasurable,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h := lintegral_lintegral_mul_mul_le (μ := Measure.count) (ν := Measure.count)
    (k := fun k l : G ↦ w (k - l)) (measurable_of_countable _).aemeasurable
    (measurable_of_countable y).aemeasurable (measurable_of_countable z).aemeasurable
    (p := 2) (q := 2) (ae_of_all _ hrow) (ae_of_all _ hcol)
  simp only [lintegral_count] at h
  refine (h.trans_eq ?_).trans_eq' (tsum_congr fun k ↦ tsum_congr fun l ↦ by ring)
  rw [hnorm y, hnorm z, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- **Schur's test** for the kernel `1_{|x - y| < R}` on the real line: its rows and columns have
length `2R`, so for Hölder conjugate `p` and `q`,
`∫∫_{|x - y| < R} f(x) g(y) dx dy ≤ 2R ‖f‖_p ‖g‖_q`. -/
theorem lintegral_lintegral_mul_indicator_ball_mul_le {f g : ℝ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] (R : ℝ) :
    ∫⁻ x, ∫⁻ y, f x * ((Metric.ball x R).indicator (1 : ℝ → ℝ≥0∞) y * g y) ≤
      ENNReal.ofReal (2 * R) * eLpNorm f p * eLpNorm g q := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 hR]
  have hrow (x : ℝ) :
      ∫⁻ y, (Metric.ball x R).indicator (1 : ℝ → ℝ≥0∞) y = ENNReal.ofReal (2 * R) := by
    rw [lintegral_indicator_one measurableSet_ball, Real.volume_ball]
  have hcol (y : ℝ) :
      ∫⁻ x, (Metric.ball x R).indicator (1 : ℝ → ℝ≥0∞) y = ENNReal.ofReal (2 * R) := by
    have : (fun x : ℝ ↦ (Metric.ball x R).indicator (1 : ℝ → ℝ≥0∞) y) =
        (Metric.ball y R).indicator 1 := by
      ext x
      simp only [Set.indicator, Pi.one_apply, Metric.mem_ball, dist_comm]
    rw [this, hrow]
  have h := lintegral_lintegral_mul_mul_le (measurable_uncurry_indicator_ball R).aemeasurable
    hf hg (p := p) (q := q) (ae_of_all _ fun x ↦ (hrow x).le) (ae_of_all _ fun y ↦ (hcol y).le)
  rwa [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top,
    sub_add_cancel, ENNReal.rpow_one] at h

end TauCeti
