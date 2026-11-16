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
# Minkowski's integral inequality

For `1 ≤ p` and a jointly a.e. measurable `f : α → β → ℝ≥0∞` on a product of two s-finite measure
spaces,

`(∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν`:

the `Lᵖ(μ)` seminorm of an integral over `ν` is at most the integral over `ν` of the `Lᵖ(μ)`
seminorms. This is the continuous form of Minkowski's inequality
`ENNReal.lintegral_Lp_add_le` for a sum of two functions. A typical use bounds the `Lᵖ` size of a
quantity accumulated along a time interval, such as the length `∫ |γ'|(t) dt` of a random curve,
by the time integral of the `Lᵖ` sizes of the integrand.

The statement is in `ℝ≥0∞`, so it needs no integrability hypotheses.

The proof is by duality. Write `G x = ∫⁻ y, f x y ∂ν` and let `R` be the right-hand side. Hölder's
inequality in `x` for each `y`, followed by Tonelli's theorem, gives
`∫⁻ x, G x * h x ∂μ ≤ R * (∫⁻ x, h x ^ q ∂μ) ^ (1 / q)` for every measurable `h`, where `q` is the
conjugate exponent. When `μ` is finite, testing against `min G n ^ (p - 1)` bounds the integrals
of the truncations `min G n ^ p`, which are finite, and monotone convergence removes the
truncation. An s-finite `μ` is the supremum of finite measures below it, and both sides of the
inequality are monotone in `μ`.

A typical consequence bounds a weighted `Lʳ` norm, over a parameter `t`, of the integrals of `g`
over a family of sets `{x | R t x}`: pulling the power inside makes it an integral of `g` against
the `Lʳ` norms in `t` of the truncated weights (`TauCeti.lintegral_mul_setLIntegral_rpow_le`).
Off-diagonal Marcinkiewicz interpolation uses it with the sets cut out by a height `c * t ^ γ`.

## Main declarations

* `TauCeti.lintegral_Lp_lintegral_le`: Minkowski's integral inequality.
* `TauCeti.lintegral_mul_setLIntegral_rpow_le`: Minkowski's integral inequality for weighted
  truncations.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.19.
-/

public section

namespace TauCeti

open MeasureTheory Set Function
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- The duality bound behind Minkowski's integral inequality: by Hölder's inequality in `x` for
each `y` and Tonelli's theorem, pairing `x ↦ ∫⁻ y, f x y ∂ν` with `h` costs at most the right-hand
side of Minkowski's inequality times the `L^q` seminorm of `h`. -/
private lemma lintegral_lintegral_mul_le [SFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) {h : α → ℝ≥0∞} (hh : Measurable h) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∫⁻ x, (∫⁻ y, f x y ∂ν) * h x ∂μ ≤
      (∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν) * (∫⁻ x, h x ^ q ∂μ) ^ (1 / q) := by
  calc ∫⁻ x, (∫⁻ y, f x y ∂ν) * h x ∂μ = ∫⁻ x, ∫⁻ y, f x y * h x ∂ν ∂μ :=
        lintegral_congr fun x ↦ (lintegral_mul_const _ (hf.comp measurable_prodMk_left)).symm
    _ = ∫⁻ y, ∫⁻ x, f x y * h x ∂μ ∂ν :=
        lintegral_lintegral_swap (hf.mul (hh.comp measurable_fst)).aemeasurable
    _ ≤ ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) * (∫⁻ x, h x ^ q ∂μ) ^ (1 / q) ∂ν :=
        lintegral_mono fun y ↦ ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
          (hf.comp measurable_prodMk_right).aemeasurable hh.aemeasurable
    _ = _ := lintegral_mul_const _ (((hf.pow_const p).lintegral_prod_left' (μ := μ)).pow_const _)

/-- Minkowski's integral inequality for a jointly measurable integrand, a finite measure `μ` and
`1 < p`. Testing the duality bound against `min (∫⁻ y, f x y ∂ν) n ^ (p - 1)` bounds the integrals
of the truncations `min (∫⁻ y, f x y ∂ν) n ^ p`, which are finite, and monotone convergence removes
the truncation. -/
private lemma lintegral_Lp_lintegral_le_of_isFiniteMeasure [IsFiniteMeasure μ] [SFinite ν]
    {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f)) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set R := ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν
  set G : α → ℝ≥0∞ := fun x ↦ ∫⁻ y, f x y ∂ν
  have hG : Measurable G := hf.lintegral_prod_right' (ν := ν)
  have hp0 : 0 < p := one_pos.trans hp
  have hpq : p.HolderConjugate p.conjExponent := .conjExponent hp
  have hT (n : ℕ) : Measurable fun x ↦ min (G x) n := hG.min measurable_const
  have hN (n : ℕ) : ∫⁻ x, min (G x) n ^ p ∂μ ≤ R ^ p := by
    set N := ∫⁻ x, min (G x) n ^ p ∂μ
    have hfin : N ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_
        (lintegral_mono fun x ↦ ENNReal.rpow_le_rpow (min_le_right (G x) n) hp0.le)
      simpa [lintegral_const] using
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top n))
          (measure_ne_top μ univ)
    have h1 : N ≤ R * N ^ (1 / p.conjExponent) := by
      calc N ≤ ∫⁻ x, G x * min (G x) n ^ (p - 1) ∂μ := lintegral_mono fun x ↦ by
            calc min (G x) n ^ p = min (G x) n * min (G x) n ^ (p - 1) := by
                  conv_lhs => rw [← add_sub_cancel 1 p, ENNReal.rpow_add_of_nonneg _ _ zero_le_one
                    (sub_nonneg.2 hp.le), ENNReal.rpow_one]
              _ ≤ _ := by gcongr; exact min_le_left _ _
        _ ≤ R * (∫⁻ x, (min (G x) n ^ (p - 1)) ^ p.conjExponent ∂μ) ^ (1 / p.conjExponent) :=
            lintegral_lintegral_mul_le hf ((hT n).pow_const _) hpq
        _ = _ := by simp_rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj, N]
    -- `N ≤ R * N ^ (1 / q)` with `N` finite gives `N ^ (1 / p) ≤ R`.
    rw [← ENNReal.rpow_inv_le_iff hp0, ← one_div]
    rcases eq_or_ne N 0 with hN0 | hN0
    · simp [hN0, hp0]
    have hsplit : N ^ (1 / p) * N ^ (1 / p.conjExponent) = N := by
      rw [← ENNReal.rpow_add _ _ hN0 hfin, one_div, one_div, hpq.inv_add_inv_eq_one,
        ENNReal.rpow_one]
    exact (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 hN0) hfin).ne'
      (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.2 hpq.symm.pos).le hfin)).1 (hsplit.trans_le h1)
  have hsup (x : α) : G x ^ p = ⨆ n : ℕ, min (G x) n ^ p := by
    rw [← ENNReal.iSup_rpow_of_pos hp0, ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  rw [one_div, ENNReal.rpow_inv_le_iff hp0, lintegral_congr hsup,
    lintegral_iSup (fun n ↦ (hT n).pow_const p) fun n m hnm x ↦ by dsimp only; gcongr]
  exact iSup_le hN

/-- Minkowski's integral inequality for a jointly measurable integrand. An s-finite measure `μ` is
the supremum of finite measures below it, so the bound follows from the finite case. -/
private lemma lintegral_Lp_lintegral_le_of_measurable [SFinite μ] [SFinite ν]
    {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  rcases hp.eq_or_lt with rfl | hp1
  · simpa using (lintegral_lintegral_swap hf.aemeasurable).le
  have hp0 : 0 < p := one_pos.trans hp1
  -- The finite partial sums `m s` of a sequence of finite measures adding up to `μ`.
  set m : Finset ℕ → Measure α := fun s ↦ ∑ i ∈ s, sfiniteSeq μ i
  have hμ (g : α → ℝ≥0∞) : ∫⁻ x, g x ∂μ = ⨆ s, ∫⁻ x, g x ∂m s := by
    conv_lhs => rw [← sum_sfiniteSeq μ, lintegral_sum_measure, tsum_eq_iSup_sum]
    simp_rw [m, lintegral_finsetSum_measure]
  have hm (s : Finset ℕ) (g : α → ℝ≥0∞) : ∫⁻ x, g x ∂m s ≤ ∫⁻ x, g x ∂μ :=
    hμ g ▸ le_iSup (fun s ↦ ∫⁻ x, g x ∂m s) s
  rw [one_div, ENNReal.rpow_inv_le_iff hp0, hμ]
  refine iSup_le fun s ↦ ?_
  rw [← ENNReal.rpow_inv_le_iff hp0, ← one_div]
  exact (lintegral_Lp_lintegral_le_of_isFiniteMeasure hf hp1).trans
    (lintegral_mono fun y ↦ ENNReal.rpow_le_rpow (hm s _) (one_div_pos.2 hp0).le)


/-- **Minkowski's integral inequality.** For `1 ≤ p` and a jointly a.e. measurable
`f : α → β → ℝ≥0∞`, the `Lᵖ(μ)` seminorm of `x ↦ ∫⁻ y, f x y ∂ν` is at most the integral over `ν`
of the `Lᵖ(μ)` seminorms of the functions `x ↦ f x y`:
`(∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤ ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν`. -/
theorem lintegral_Lp_lintegral_le [SFinite μ] [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, f x y ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, f x y ^ p ∂μ) ^ (1 / p) ∂ν := by
  set g : α → β → ℝ≥0∞ := curry (hf.mk _)
  have hg : Measurable (uncurry g) := by simpa [g] using hf.measurable_mk
  have hfg : ∀ᵐ z ∂μ.prod ν, uncurry f z = uncurry g z := by
    filter_upwards [hf.ae_eq_mk] with z hz
    simpa [g] using hz
  -- Replace `f` by its measurable modification `g` on both sides.
  have hL : ∀ᵐ x ∂μ, ∫⁻ y, f x y ∂ν = ∫⁻ y, g x y ∂ν := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with x hx using lintegral_congr_ae hx
  have hR : ∀ᵐ y ∂ν, ∫⁻ x, f x y ^ p ∂μ = ∫⁻ x, g x y ^ p ∂μ := by
    have hswap : ∀ᵐ z ∂ν.prod μ, uncurry f z.swap = uncurry g z.swap :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hfg
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
    exact lintegral_congr_ae (hy.mono fun x hx ↦ by simpa using congrArg (· ^ p) hx)
  rw [lintegral_congr_ae (hL.mono fun x hx ↦ by rw [hx]),
    lintegral_congr_ae (hR.mono fun y hy ↦ by rw [hy])]
  exact lintegral_Lp_lintegral_le_of_measurable hg hp

/-- **Minkowski's integral inequality for weighted truncations.** For `1 ≤ r`, a weight `w` and a
measurable relation `R`, the weighted `Lʳ(ν)` norm in `t` of the truncated integrals
`∫⁻ x in {x | R t x}, g x ∂μ` is at most the integral of `g` against the `Lʳ(ν)` norms in `t` of
the truncations of the weight:

`∫⁻ t, w t * (∫⁻ x in {R t ·}, g ∂μ) ^ r ∂ν ≤
  (∫⁻ x, g x * (∫⁻ t in {R · x}, w ∂ν) ^ r⁻¹ ∂μ) ^ r`. -/
theorem lintegral_mul_setLIntegral_rpow_le [SFinite ν] [SFinite μ] {R : β → α → Prop}
    (hR : MeasurableSet {z : β × α | R z.1 z.2}) {w : β → ℝ≥0∞} (hw : AEMeasurable w ν)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ t, w t * (∫⁻ x in {x | R t x}, g x ∂μ) ^ r ∂ν ≤
      (∫⁻ x, g x * (∫⁻ t, {t | R t x}.indicator w t ∂ν) ^ r⁻¹ ∂μ) ^ r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  -- The integrand `F t x = w t ^ r⁻¹ * g x` on the relation, and `0` off it.
  set F : β → α → ℝ≥0∞ := fun t x ↦
    {z : β × α | R z.1 z.2}.indicator (fun z ↦ w z.1 ^ r⁻¹ * g z.2) (t, x)
  have hF : AEMeasurable (uncurry F) (ν.prod μ) :=
    ((hw.pow_const _).comp_fst.mul hg.comp_snd).indicator hR
  have hRx : ∀ t, MeasurableSet {x | R t x} := fun t ↦ measurable_prodMk_left hR
  have hRt : ∀ x, MeasurableSet {t | R t x} := fun x ↦ measurable_prodMk_right hR
  have hFR : ∀ t x, F t x = {x | R t x}.indicator (fun x ↦ w t ^ r⁻¹ * g x) x :=
    fun _ _ ↦ rfl
  have hFR' : ∀ t x, F t x = {t | R t x}.indicator (fun t ↦ w t ^ r⁻¹ * g x) t :=
    fun _ _ ↦ rfl
  -- The integral of `F` over the space at a fixed parameter.
  have hslice : ∀ t, ∫⁻ x, F t x ∂μ = w t ^ r⁻¹ * ∫⁻ x in {x | R t x}, g x ∂μ := fun t ↦ by
    simp_rw [hFR, lintegral_indicator (hRx t), lintegral_const_mul'' _ hg.restrict]
  -- The integral of `F ^ r` over the parameters at a fixed point.
  have hsec : ∀ x, ∫⁻ t, F t x ^ r ∂ν = g x ^ r * ∫⁻ t, {t | R t x}.indicator w t ∂ν :=
    fun x ↦ by
      rw [← lintegral_const_mul'' _ (hw.indicator (hRt x))]
      refine lintegral_congr fun t ↦ ?_
      by_cases h : R t x
      · rw [hFR', indicator_of_mem (s := {t | R t x}) h, indicator_of_mem (s := {t | R t x}) h,
          ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.rpow_inv_rpow hr0.ne', mul_comm]
      · rw [hFR', indicator_of_notMem (s := {t | R t x}) h,
          indicator_of_notMem (s := {t | R t x}) h, mul_zero, ENNReal.zero_rpow_of_pos hr0]
  have hmink := lintegral_Lp_lintegral_le (μ := ν) (ν := μ) (f := F) hF hr
  rw [one_div, ENNReal.rpow_inv_le_iff hr0] at hmink
  calc ∫⁻ t, w t * (∫⁻ x in {x | R t x}, g x ∂μ) ^ r ∂ν = ∫⁻ t, (∫⁻ x, F t x ∂μ) ^ r ∂ν := by
        refine lintegral_congr fun t ↦ ?_
        rw [hslice, ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.rpow_inv_rpow hr0.ne']
    _ ≤ _ := hmink
    _ = _ := by
        congr 1
        refine lintegral_congr fun x ↦ ?_
        rw [hsec, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hr0.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hr0.ne', ENNReal.rpow_one]

end TauCeti
