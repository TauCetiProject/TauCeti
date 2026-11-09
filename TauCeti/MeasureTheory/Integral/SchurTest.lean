/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.MeasureTheory.Integral.MeanInequalities

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
* `TauCeti.eLpNorm_lintegral_mul_le`: Schur's test as an `Lᵖ` bound, including `p = ∞`.
* `TauCeti.rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top`: the constant
  `A ^ (1 - 1/p) * B ^ (1/p)` of this bound is finite for finite `A` and `B`.
* `TauCeti.memLp_lintegral_mul`: hence the kernel maps `Lᵖ` to `Lᵖ` for finite `A` and `B`.

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

/-- For `1 ≤ p ≤ ∞` the exponent `1 - 1/p` in Schur's test is nonnegative; for `p = ∞` it is `1`,
as `ENNReal.toReal ∞ = 0`. -/
theorem one_sub_toReal_inv_nonneg {p : ℝ≥0∞} (hp : 1 ≤ p) : 0 ≤ 1 - p.toReal⁻¹ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp
  · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hp_top hp))

/-- For finite `A` and `B`, the constant `A ^ (1 - 1/p) * B ^ (1/p)` of Schur's test is the
coercion of the same expression in `ℝ≥0`. -/
theorem coe_rpow_one_sub_toReal_inv_mul_rpow_toReal_inv {p : ℝ≥0∞} (hp : 1 ≤ p) (A B : ℝ≥0) :
    ((A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (A : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * (B : ℝ≥0∞) ^ p.toReal⁻¹ := by
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (one_sub_toReal_inv_nonneg hp),
    ENNReal.coe_rpow_of_nonneg _ (by positivity)]

/-- The constant `A ^ (1 - 1/p) * B ^ (1/p)` of Schur's test is finite for finite `A` and `B`. -/
theorem rpow_one_sub_toReal_inv_mul_rpow_toReal_inv_lt_top {p : ℝ≥0∞} (hp : 1 ≤ p)
    (A B : ℝ≥0) : (A : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * (B : ℝ≥0∞) ^ p.toReal⁻¹ < ∞ :=
  coe_rpow_one_sub_toReal_inv_mul_rpow_toReal_inv hp A B ▸ ENNReal.coe_lt_top

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
      A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ * eLpNorm g p ν := by
  have hmeas : AEMeasurable (fun x ↦ ∫⁻ y, k x y * g y ∂ν) μ :=
    (hk.mul hg.comp_snd).lintegral_prod_right'
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp only [eLpNorm_exponent_top hmeas.aestronglyMeasurable,
      eLpNorm_exponent_top hg.aestronglyMeasurable, ENNReal.toReal_top, inv_zero, sub_zero,
      ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards [hA, Measure.ae_ae_of_ae_prod hk.ae_eq_mk] with x hx hx'
    have hkx : AEMeasurable (k x) ν :=
      (hk.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr (hx'.mono fun _ ↦ Eq.symm)
    calc ‖(∫⁻ y, k x y * g y ∂ν : ℝ≥0∞)‖ₑ ≤ ∫⁻ y, k x y * eLpNormEssSup g ν ∂ν := by
          rw [enorm_eq_self]
          refine lintegral_mono_ae ?_
          filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := ν)] with y hy
          gcongr
          simpa only [enorm_eq_self] using hy
      _ = (∫⁻ y, k x y ∂ν) * eLpNormEssSup g ν := lintegral_mul_const'' _ hkx
      _ ≤ A * eLpNormEssSup g ν := by gcongr
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hmeas.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hg.aestronglyMeasurable]
  simp only [enorm_eq_self]
  calc (∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p.toReal ∂μ) ^ (1 / p.toReal)
      ≤ (A ^ (p.toReal - 1) * B * ∫⁻ y, g y ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        gcongr
        exact lintegral_rpow_lintegral_mul_le hk hg hr hA hB
    _ = A ^ (1 - p.toReal⁻¹) * B ^ p.toReal⁻¹ *
          (∫⁻ y, g y ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
        have hr0 : 0 < p.toReal := zero_lt_one.trans_le hr
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div,
          show (p.toReal - 1) * p.toReal⁻¹ = 1 - p.toReal⁻¹ by field_simp]

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

end TauCeti
