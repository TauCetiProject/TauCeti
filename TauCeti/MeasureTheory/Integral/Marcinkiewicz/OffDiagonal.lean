/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General
public import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# The off-diagonal Marcinkiewicz interpolation theorem

Let `T` be a subadditive operator of **weak type `(p₀, q₀)`** and of **weak type `(p₁, q₁)`**,

`r ^ qᵢ * ν {T g > r} ≤ Aᵢ * (∫⁻ ‖g‖ ^ pᵢ ∂μ) ^ (qᵢ / pᵢ)`,

with finite exponents `0 < pᵢ ≤ qᵢ`, `p₀ ≠ p₁` and `q₀ ≠ q₁`. For `0 < θ < 1` define `p` and `q`
by `1 / p = (1 - θ) / p₀ + θ / p₁` and `1 / q = (1 - θ) / q₀ + θ / q₁`. Then `T` is of **strong
type `(p, q)`**:

`∫⁻ (T v) ^ q ∂ν ≤ C * (∫⁻ ‖v‖ ^ p ∂μ) ^ (q / p)`,

with `C = q / |q - q₀| * A₀ * d ^ (-q₀) + q / |q - q₁| * A₁ * e ^ (-q₁)` for any splitting
parameters `d, e > 0` with `d + e ≤ 1` (`TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow`).
The source and target exponents move along two different segments; when `p₀ = q₀` and `p₁ = q₁`
they coincide, and that diagonal case is also
`TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le`, whose weak-type hypotheses carry no outer
power. The hypothesis `pᵢ ≤ qᵢ` is what makes the exponent `qᵢ / pᵢ` at least `1` in the
argument below. Typical applications are the Hardy–Littlewood–Sobolev inequality and other bounds
`L^p → L^q` with `p < q` for operators that are only known to be of weak type at the endpoints.

## The argument

Let `p₀ < p₁`. Split `v` at the height `c * t ^ γ`, where `γ` is fixed by
`(q - q₀) / γ = q₀ (p - p₀) / p₀`; the interpolation relations then also give
`(q - q₁) / γ = q₁ (p - p₁) / p₁`. Its part above the height lies in `L^{p₀}` and its part below
lies in `L^{p₁}`, and the two weak-type bounds give, for every `t > 0`,

`ν {T v > t} ≤ A₀ (d t) ^ (-q₀) (∫⁻_{‖v‖ > c t ^ γ} ‖v‖ ^ p₀) ^ (q₀ / p₀) +
  A₁ (e t) ^ (-q₁) (∫⁻_{‖v‖ ≤ c t ^ γ} ‖v‖ ^ p₁) ^ (q₁ / p₁)`

(`TauCeti.meas_ofReal_lt_le_add_setLIntegral_rpow`). Integrating against `q t ^ (q - 1)` with the
layer cake formula leaves the two integrals `∫ t ^ (q - qᵢ - 1) (∫⁻_{…} ‖v‖ ^ pᵢ) ^ (qᵢ / pᵢ) dt`.
Since `qᵢ / pᵢ ≥ 1`, Minkowski's integral inequality `TauCeti.lintegral_Lp_lintegral_le` moves the
power `qᵢ / pᵢ` inside the integral over the space, and for a fixed point the integral in `t` is
elementary (`TauCeti.lintegral_indicator_ofReal_mul_rpow_lt_le` and
`TauCeti.lintegral_indicator_le_ofReal_mul_rpow_le`). The choice of `γ` makes both terms
integrals of `‖v‖ ^ p`, and the result is the distributional estimate
`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le_rpow`:

`∫⁻ (T v) ^ q ≤ q c ^ (q₀ (p₀ - p) / p₀) / |q - q₀| · A₀' (∫⁻ ‖v‖ ^ p) ^ (q₀ / p₀) +
  q c ^ (q₁ (p₁ - p) / p₁) / |q - q₁| · A₁' (∫⁻ ‖v‖ ^ p) ^ (q₁ / p₁)`,

where `A₀' = A₀ d ^ (-q₀)` and `A₁' = A₁ e ^ (-q₁)`.

Both terms become multiples of `(∫⁻ ‖v‖ ^ p) ^ (q / p)` for `c = (∫⁻ ‖v‖ ^ p) ^ ((1 - γ) / p)`.
The case `p₁ < p₀` follows by exchanging the endpoints.

## Main declarations

* `TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le_rpow`: the distributional interpolation estimate
  between two off-diagonal endpoints.
* `TauCeti.meas_ofReal_lt_le_add_setLIntegral_rpow`: the truncation argument from subadditivity
  and two off-diagonal weak-type bounds.
* `TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow`: the **off-diagonal Marcinkiewicz
  interpolation theorem** for finite exponents.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 1.4.4.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter V, §2.
* A. Zygmund, *Trigonometric Series*, Vol. II, Chapter XII, §4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → ℝ≥0∞} {u : β → ℝ≥0∞} {p p₀ p₁ q q₀ q₁ γ c : ℝ} {A₀ A₁ : ℝ≥0∞}

/-- **Minkowski's integral inequality for weighted truncations.** For `r ≥ 1`, a weighted
`L^r` norm in `t` of the truncated integrals `∫⁻ x in {R t ·}, g x` is at most the integral of `g`
against the `L^r` norms in `t` of the truncations of the weight. -/
private theorem lintegral_mul_setLIntegral_rpow_le [SFinite μ] {R : ℝ → α → Prop}
    (hR : MeasurableSet {z : ℝ × α | R z.1 z.2}) {g : α → ℝ≥0∞} (hg : Measurable g) {r s : ℝ}
    (hr : 1 ≤ r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) * (∫⁻ x in {x | R t x}, g x ∂μ) ^ r ≤
      (∫⁻ x, g x * (∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t) ^ r⁻¹ ∂μ) ^ r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (s / r)) with hwdef
  have hw : Measurable w := (measurable_id.pow_const _).ennreal_ofReal
  have hws : Measurable fun t : ℝ => ENNReal.ofReal (t ^ s) :=
    (measurable_id.pow_const _).ennreal_ofReal
  set F : ℝ → α → ℝ≥0∞ := fun t x =>
    {z : ℝ × α | R z.1 z.2}.indicator (fun z => w z.1 * g z.2) (t, x) with hFdef
  have hF : Measurable (Function.uncurry F) :=
    ((hw.comp measurable_fst).mul (hg.comp measurable_snd)).indicator hR
  have hRx : ∀ t, MeasurableSet {x | R t x} := fun t => measurable_prodMk_left hR
  have hRt : ∀ x, MeasurableSet {t : ℝ | R t x} := fun x => measurable_prodMk_right hR
  have hFmem : ∀ {t x}, R t x → F t x = w t * g x := fun h =>
    indicator_of_mem (show (_, _) ∈ {z : ℝ × α | R z.1 z.2} from h) _
  have hFnot : ∀ {t x}, ¬R t x → F t x = 0 := fun h =>
    indicator_of_notMem (show (_, _) ∉ {z : ℝ × α | R z.1 z.2} from h) _
  -- The weight raised to the power `r` is `t ^ s` at every positive `t`.
  have hwr : ∀ t : ℝ, 0 < t → w t ^ r = ENNReal.ofReal (t ^ s) := fun t ht => by
    rw [hwdef, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) hr0.le,
      ← Real.rpow_mul ht.le, div_mul_cancel₀ s hr0.ne']
  -- The integral of `F` over the space at a fixed height.
  have hslice : ∀ t, ∫⁻ x, F t x ∂μ = w t * ∫⁻ x in {x | R t x}, g x ∂μ := fun t => by
    rw [← lintegral_indicator (hRx t), ← lintegral_const_mul _ (hg.indicator (hRx t))]
    refine lintegral_congr fun x => ?_
    by_cases h : R t x
    · rw [hFmem h, indicator_of_mem (show x ∈ {x | R t x} from h)]
    · rw [hFnot h, indicator_of_notMem (show x ∉ {x | R t x} from h), mul_zero]
  -- The integral of `F ^ r` over the heights at a fixed point.
  have hsec : ∀ x, ∫⁻ t in Ioi (0 : ℝ), F t x ^ r =
      g x ^ r * ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t := fun x => by
    rw [← lintegral_const_mul _ (hws.indicator (hRt x))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    by_cases h : R t x
    · rw [hFmem h, indicator_of_mem (show t ∈ {t | R t x} from h),
        ENNReal.mul_rpow_of_nonneg _ _ hr0.le, hwr t ht, mul_comm]
    · rw [hFnot h, indicator_of_notMem (show t ∉ {t | R t x} from h), mul_zero,
        ENNReal.zero_rpow_of_pos hr0]
  have hmink := lintegral_Lp_lintegral_le (μ := volume.restrict (Ioi (0 : ℝ))) (ν := μ) (f := F)
    hF.aemeasurable hr
  have hL : ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, F t x ∂μ) ^ r =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) * (∫⁻ x in {x | R t x}, g x ∂μ) ^ r :=
    setLIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [hslice, ENNReal.mul_rpow_of_nonneg _ _ hr0.le, hwr t ht]
  have hR' : ∀ x, (∫⁻ t in Ioi (0 : ℝ), F t x ^ r) ^ (1 / r) =
      g x * (∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t) ^ r⁻¹ := fun x => by
    rw [hsec, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
      mul_one_div_cancel hr0.ne', ENNReal.rpow_one, one_div]
  rw [hL, lintegral_congr hR', one_div, ENNReal.rpow_inv_le_iff hr0] at hmink
  exact hmink

/-- A truncated weighted integral, for one endpoint of the interpolation. If the truncation of the
weight `t ^ s` at each point `x` is at most `K f(x) ^ (qᵢ (p - pᵢ) / pᵢ)`, then the weighted
`L^{qᵢ / pᵢ}` norm in `t` of the truncated integrals of `f ^ pᵢ` is at most
`K (∫⁻ f ^ p) ^ (qᵢ / pᵢ)`. -/
private theorem lintegral_mul_setLIntegral_rpow_le_of_le [SFinite μ] {R : ℝ → α → Prop}
    (hR : MeasurableSet {z : ℝ × α | R z.1 z.2}) (hf : Measurable f) {pᵢ qᵢ s K : ℝ}
    (hpᵢ : 0 < pᵢ) (hpq : pᵢ ≤ qᵢ)
    (hinner : ∀ x, ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t ≤
      ENNReal.ofReal K * f x ^ (qᵢ * (p - pᵢ) / pᵢ)) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        (∫⁻ x in {x | R t x}, f x ^ pᵢ ∂μ) ^ (qᵢ / pᵢ) ≤
      ENNReal.ofReal K * (∫⁻ x, f x ^ p ∂μ) ^ (qᵢ / pᵢ) := by
  have hqᵢ : 0 < qᵢ := hpᵢ.trans_le hpq
  have hr : 1 ≤ qᵢ / pᵢ := (one_le_div hpᵢ).2 hpq
  have hr0 : 0 < qᵢ / pᵢ := by positivity
  have hexp : qᵢ * (p - pᵢ) / pᵢ * (qᵢ / pᵢ)⁻¹ = p - pᵢ := by
    field_simp
  have hpt : ∀ x, f x ^ pᵢ * (∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | R t x}.indicator (fun t => ENNReal.ofReal (t ^ s)) t) ^ (qᵢ / pᵢ)⁻¹ ≤
      ENNReal.ofReal K ^ (qᵢ / pᵢ)⁻¹ * f x ^ p := fun x =>
    calc _ ≤ f x ^ pᵢ * (ENNReal.ofReal K * f x ^ (qᵢ * (p - pᵢ) / pᵢ)) ^ (qᵢ / pᵢ)⁻¹ := by
          gcongr
          exact hinner x
      _ = ENNReal.ofReal K ^ (qᵢ / pᵢ)⁻¹ * (f x ^ pᵢ * f x ^ (p - pᵢ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, hexp]
          ring
      _ ≤ ENNReal.ofReal K ^ (qᵢ / pᵢ)⁻¹ * f x ^ p := by
          gcongr
          simpa using ENNReal.le_rpow_add (f x) hpᵢ (p - pᵢ)
  calc _ ≤ _ := lintegral_mul_setLIntegral_rpow_le hR (hf.pow_const pᵢ) hr
    _ ≤ (∫⁻ x, ENNReal.ofReal K ^ (qᵢ / pᵢ)⁻¹ * f x ^ p ∂μ) ^ (qᵢ / pᵢ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) hr0.le
    _ = ENNReal.ofReal K * (∫⁻ x, f x ^ p ∂μ) ^ (qᵢ / pᵢ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity)
          ENNReal.ofReal_ne_top), ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul,
          inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one]

/-- The exponent relations of the interpolation force `γ ≠ 0`, and they place the target exponent
`q` strictly between `q₀` and `q₁`, so that `0 < q`. -/
private theorem ne_zero_and_pos_of_div_eq (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hpq₀ : p₀ ≤ q₀) (hpq₁ : p₁ ≤ q₁) (hγ₀ : (q - q₀) / γ = q₀ * (p - p₀) / p₀)
    (hγ₁ : (q - q₁) / γ = q₁ * (p - p₁) / p₁) :
    γ ≠ 0 ∧ 0 < q ∧ q - q₀ ≠ 0 ∧ q - q₁ ≠ 0 := by
  have hp₁ : 0 < p₁ := by linarith
  have hq₀ : 0 < q₀ := hp₀.trans_le hpq₀
  have hq₁ : 0 < q₁ := hp₁.trans_le hpq₁
  have hX : 0 < (q - q₀) / γ := by rw [hγ₀]; exact div_pos (mul_pos hq₀ (by linarith)) hp₀
  have hY : (q - q₁) / γ < 0 := by
    rw [hγ₁]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq₁ (by linarith)) hp₁
  have hγ : γ ≠ 0 := by rintro rfl; simp at hX
  have e₀ : q - q₀ = (q - q₀) / γ * γ := (div_mul_cancel₀ _ hγ).symm
  have e₁ : q - q₁ = (q - q₁) / γ * γ := (div_mul_cancel₀ _ hγ).symm
  refine ⟨hγ, ?_, fun h => by simp [h] at hX, fun h => by simp [h] at hY⟩
  rcases hγ.lt_or_gt with hγ | hγ
  · nlinarith [mul_pos_of_neg_of_neg hY hγ]
  · nlinarith [mul_pos hX hγ]

/-- The off-diagonal interpolation estimate for a measurable `f` and an s-finite `μ`, which is the
generality in which Minkowski's integral inequality applies; both hypotheses are removed below. -/
private theorem lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_of_measurable_of_sFinite [SFinite μ]
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hpq₀ : p₀ ≤ q₀) (hpq₁ : p₁ ≤ q₁) (hγ₀ : (q - q₀) / γ = q₀ * (p - p₀) / p₀)
    (hγ₁ : (q - q₁) / γ = q₁ * (p - p₁) / p₁) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < u y} ≤
      A₀ * ENNReal.ofReal (t ^ (-q₀)) *
          (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < f x}, f x ^ p₀ ∂μ) ^ (q₀ / p₀) +
        A₁ * ENNReal.ofReal (t ^ (-q₁)) *
          (∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t ^ γ)}, f x ^ p₁ ∂μ) ^ (q₁ / p₁)) :
    ∫⁻ y, u y ^ q ∂ν ≤
      ENNReal.ofReal (q * c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) * A₀ *
          (∫⁻ x, f x ^ p ∂μ) ^ (q₀ / p₀) +
        ENNReal.ofReal (q * c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) * A₁ *
          (∫⁻ x, f x ^ p ∂μ) ^ (q₁ / p₁) := by
  obtain ⟨-, hq, -, -⟩ := ne_zero_and_pos_of_div_eq hp₀ hlt₀ hlt₁ hpq₀ hpq₁ hγ₀ hγ₁
  have hp : 0 < p := hp₀.trans hlt₀
  have hthr : Measurable fun z : ℝ × α => ENNReal.ofReal (c * z.1 ^ γ) :=
    ((measurable_fst.pow_const γ).const_mul c).ennreal_ofReal
  have hR₀ : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1 ^ γ) < f z.2} :=
    measurableSet_lt hthr (hf.comp measurable_snd)
  have hR₁ : MeasurableSet {z : ℝ × α | f z.2 ≤ ENNReal.ofReal (c * z.1 ^ γ)} :=
    measurableSet_le (hf.comp measurable_snd) hthr
  -- The weighted truncated integrals of the two endpoints, and their bounds.
  set I₀ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (q - q₀ - 1)) *
    (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < f x}, f x ^ p₀ ∂μ) ^ (q₀ / p₀) with hI₀
  set I₁ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (q - q₁ - 1)) *
    (∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t ^ γ)}, f x ^ p₁ ∂μ) ^ (q₁ / p₁) with hI₁
  have hmeas₀ : Measurable I₀ := (measurable_id.pow_const _).ennreal_ofReal.mul
    ((measurable_setLIntegral_of_measurableSet hR₀ (hf.pow_const p₀).aemeasurable).pow_const _)
  have hmeas₁ : Measurable I₁ := (measurable_id.pow_const _).ennreal_ofReal.mul
    ((measurable_setLIntegral_of_measurableSet hR₁ (hf.pow_const p₁).aemeasurable).pow_const _)
  have hbound₀ : ∫⁻ t in Ioi (0 : ℝ), I₀ t ≤
      ENNReal.ofReal (c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) * (∫⁻ x, f x ^ p ∂μ) ^ (q₀ / p₀) := by
    refine lintegral_mul_setLIntegral_rpow_le_of_le hR₀ hf hp₀ hpq₀ fun x => ?_
    have hin := lintegral_indicator_ofReal_mul_rpow_lt_le (s := q - q₀ - 1) hc
      (by rw [sub_add_cancel, hγ₀]; exact div_pos (mul_pos (hp₀.trans_le hpq₀) (by linarith)) hp₀)
      (f x)
    rwa [sub_add_cancel, hγ₀, ← neg_div, ← mul_neg, neg_sub] at hin
  have hbound₁ : ∫⁻ t in Ioi (0 : ℝ), I₁ t ≤
      ENNReal.ofReal (c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) * (∫⁻ x, f x ^ p ∂μ) ^ (q₁ / p₁) := by
    have hp₁ : 0 < p₁ := hp.trans hlt₁
    refine lintegral_mul_setLIntegral_rpow_le_of_le hR₁ hf hp₁ hpq₁ fun x => ?_
    have hin := lintegral_indicator_le_ofReal_mul_rpow_le (s := q - q₁ - 1) hc
      (by
        rw [sub_add_cancel, hγ₁]
        exact div_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (hp₁.trans_le hpq₁) (by linarith)) hp₁)
      (f x)
    rwa [sub_add_cancel, hγ₁, ← neg_div, ← mul_neg, neg_sub] at hin
  -- Multiplying the hypothesis by `t ^ (q - 1)` turns it into a bound by the two integrands.
  have hpt : ∀ t : ℝ, 0 < t →
      ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (q - 1)) ≤ A₀ * I₀ t + A₁ * I₁ t := by
    intro t ht
    have hpow : ∀ r : ℝ, ENNReal.ofReal (t ^ (-r)) * ENNReal.ofReal (t ^ (q - 1)) =
        ENNReal.ofReal (t ^ (q - r - 1)) := fun r => by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
      congr 2
      ring
    calc _ ≤ _ * ENNReal.ofReal (t ^ (q - 1)) := mul_le_mul_left (h t ht) _
      _ = _ := by
        simp only [hI₀, hI₁, ← hpow q₀, ← hpow q₁]
        ring
  rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul ν hu hq]
  calc ENNReal.ofReal q *
        ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (q - 1))
      ≤ ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ), (A₀ * I₀ t + A₁ * I₁ t) := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hpt t ht
    _ = ENNReal.ofReal q *
          (A₀ * (∫⁻ t in Ioi (0 : ℝ), I₀ t) + A₁ * ∫⁻ t in Ioi (0 : ℝ), I₁ t) := by
        rw [lintegral_add_left (hmeas₀.const_mul _), lintegral_const_mul _ hmeas₀,
          lintegral_const_mul _ hmeas₁]
    _ ≤ ENNReal.ofReal q *
          (A₀ * (ENNReal.ofReal (c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) *
              (∫⁻ x, f x ^ p ∂μ) ^ (q₀ / p₀)) +
            A₁ * (ENNReal.ofReal (c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) *
              (∫⁻ x, f x ^ p ∂μ) ^ (q₁ / p₁))) :=
        mul_le_mul_right (add_le_add (mul_le_mul_right hbound₀ _) (mul_le_mul_right hbound₁ _)) _
    _ = _ := by
        have hsplit : ∀ a k : ℝ, ENNReal.ofReal (q * a / k) =
            ENNReal.ofReal q * ENNReal.ofReal (a / k) := fun a k => by
          rw [mul_div_assoc, ENNReal.ofReal_mul hq.le]
        rw [hsplit, hsplit]
        ring

/-- The off-diagonal interpolation estimate for a measurable `f` and an arbitrary measure `μ`.

Only the part of `μ` carried by `{f > 0}` enters either side, and once `f` has finite `L^p` norm
that part is σ-finite by `TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`. So the
s-finite case applies to `μ` restricted to `{f > 0}`, after the two degenerate cases (two
vanishing endpoint constants and an infinite right-hand side) are disposed of. -/
private theorem lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_of_measurable
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hpq₀ : p₀ ≤ q₀) (hpq₁ : p₁ ≤ q₁) (hγ₀ : (q - q₀) / γ = q₀ * (p - p₀) / p₀)
    (hγ₁ : (q - q₁) / γ = q₁ * (p - p₁) / p₁) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < u y} ≤
      A₀ * ENNReal.ofReal (t ^ (-q₀)) *
          (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < f x}, f x ^ p₀ ∂μ) ^ (q₀ / p₀) +
        A₁ * ENNReal.ofReal (t ^ (-q₁)) *
          (∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t ^ γ)}, f x ^ p₁ ∂μ) ^ (q₁ / p₁)) :
    ∫⁻ y, u y ^ q ∂ν ≤
      ENNReal.ofReal (q * c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) * A₀ *
          (∫⁻ x, f x ^ p ∂μ) ^ (q₀ / p₀) +
        ENNReal.ofReal (q * c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) * A₁ *
          (∫⁻ x, f x ^ p ∂μ) ^ (q₁ / p₁) := by
  obtain ⟨-, hq, hq₀', hq₁'⟩ := ne_zero_and_pos_of_div_eq hp₀ hlt₀ hlt₁ hpq₀ hpq₁ hγ₀ hγ₁
  have hp : 0 < p := hp₀.trans hlt₀
  have hp₁ : 0 < p₁ := hp.trans hlt₁
  have hq₀ : 0 < q₀ := hp₀.trans_le hpq₀
  have hq₁ : 0 < q₁ := hp₁.trans_le hpq₁
  by_cases hA : A₀ = 0 ∧ A₁ = 0
  · -- Both endpoint constants vanish, and the hypothesis already forces `u` to vanish.
    have hzero := lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_of_measurable_of_sFinite
      (μ := (0 : Measure α)) (A₀ := A₀) (A₁ := A₁) hf hu hp₀ hlt₀ hlt₁ hpq₀ hpq₁ hγ₀ hγ₁ hc
      fun t ht => by simpa [hA.1, hA.2] using h t ht
    simpa [hA.1, hA.2] using hzero
  rcases eq_or_ne (∫⁻ x, f x ^ p ∂μ) ∞ with htop | htop
  · -- The right-hand side is infinite.
    have hK₀ : ENNReal.ofReal (q * c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (div_pos (mul_pos hq (Real.rpow_pos_of_pos hc _))
        (abs_pos.2 hq₀'))).ne'
    have hK₁ : ENNReal.ofReal (q * c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (div_pos (mul_pos hq (Real.rpow_pos_of_pos hc _))
        (abs_pos.2 hq₁'))).ne'
    rw [htop, ENNReal.top_rpow_of_pos (div_pos hq₀ hp₀), ENNReal.top_rpow_of_pos (div_pos hq₁ hp₁)]
    refine le_top.trans_eq ?_
    rcases not_and_or.1 hA with hA₀ | hA₁
    · simp [ENNReal.mul_top, hK₀, hA₀]
    · simp [ENNReal.mul_top, hK₁, hA₁]
  -- `μ` restricted to `{f > 0}` is σ-finite, so in particular s-finite.
  have hσ : SigmaFinite (μ.restrict {x | 0 < f x}) :=
    sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top hf.aemeasurable hp htop
  have hpos : MeasurableSet {x | 0 < f x} := measurableSet_lt measurable_const hf
  -- A positive power of `f` vanishes off `{f > 0}`, so no truncated integral sees the complement.
  have key : ∀ r : ℝ, 0 < r → ∀ S : Set α,
      ∫⁻ x in S, f x ^ r ∂(μ.restrict {x | 0 < f x}) = ∫⁻ x in S, f x ^ r ∂μ := by
    intro r hr S
    have hsupp : Function.support (fun x => f x ^ r) ⊆ {x | 0 < f x} := by
      refine Function.support_subset_iff'.2 fun x hx => ?_
      have hx0 : f x = 0 := by simpa [Set.mem_ofPred, nonpos_iff_eq_zero] using hx
      simp [hx0, ENNReal.zero_rpow_of_pos hr]
    rw [Measure.restrict_restrict' hpos, Set.inter_comm, ← Measure.restrict_restrict hpos]
    exact setLIntegral_eq_of_support_subset hsupp
  have ep : ∫⁻ x, f x ^ p ∂(μ.restrict {x | 0 < f x}) = ∫⁻ x, f x ^ p ∂μ := by
    simpa using key p hp Set.univ
  have hmain := lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_of_measurable_of_sFinite
    (μ := μ.restrict {x | 0 < f x}) hf hu hp₀ hlt₀ hlt₁ hpq₀ hpq₁ hγ₀ hγ₁ hc fun t ht => by
      rw [key p₀ hp₀, key p₁ hp₁]; exact h t ht
  rwa [ep] at hmain

/-- **Off-diagonal Marcinkiewicz interpolation**, in distributional form.

Let `0 < p₀ < p < p₁`, `p₀ ≤ q₀` and `p₁ ≤ q₁`, and let `γ` and `q` satisfy
`(q - q₀) / γ = q₀ (p - p₀) / p₀` and `(q - q₁) / γ = q₁ (p - p₁) / p₁`. Suppose that for every
height `t > 0` the superlevel set `{u > t}` obeys the bound

`ν {u > t} ≤ A₀ t ^ (-q₀) (∫⁻ x in {f > c t ^ γ}, f ^ p₀ ∂μ) ^ (q₀ / p₀) +
  A₁ t ^ (-q₁) (∫⁻ x in {f ≤ c t ^ γ}, f ^ p₁ ∂μ) ^ (q₁ / p₁)`,

in which the part of `f` above the height `c t ^ γ` is measured in `L^{p₀}` and the part below it
in `L^{p₁}`. Then

`∫⁻ u ^ q ∂ν ≤ q c ^ (q₀ (p₀ - p) / p₀) / |q - q₀| · A₀ (∫⁻ f ^ p ∂μ) ^ (q₀ / p₀) +
  q c ^ (q₁ (p₁ - p) / p₁) / |q - q₁| · A₁ (∫⁻ f ^ p ∂μ) ^ (q₁ / p₁)`.

The two relations for `γ` say that `1 / p` and `1 / q` divide the segments from `1 / p₀` to
`1 / p₁` and from `1 / q₀` to `1 / q₁` in the same ratio; they force `γ ≠ 0` and put `q` strictly
between `q₀` and `q₁`. Applied with `u = T f` for a subadditive `T`, the hypothesis is what two
off-diagonal weak-type bounds give after splitting `f` at the height `c t ^ γ`
(`TauCeti.meas_ofReal_lt_le_add_setLIntegral_rpow`). The diagonal case `pᵢ = qᵢ`, `γ = 1` is
`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`. -/
theorem lintegral_rpow_le_of_meas_ofReal_lt_le_rpow
    (hf : AEMeasurable f μ) (hu : AEMeasurable u ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hpq₀ : p₀ ≤ q₀) (hpq₁ : p₁ ≤ q₁) (hγ₀ : (q - q₀) / γ = q₀ * (p - p₀) / p₀)
    (hγ₁ : (q - q₁) / γ = q₁ * (p - p₁) / p₁) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < u y} ≤
      A₀ * ENNReal.ofReal (t ^ (-q₀)) *
          (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < f x}, f x ^ p₀ ∂μ) ^ (q₀ / p₀) +
        A₁ * ENNReal.ofReal (t ^ (-q₁)) *
          (∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t ^ γ)}, f x ^ p₁ ∂μ) ^ (q₁ / p₁)) :
    ∫⁻ y, u y ^ q ∂ν ≤
      ENNReal.ofReal (q * c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) * A₀ *
          (∫⁻ x, f x ^ p ∂μ) ^ (q₀ / p₀) +
        ENNReal.ofReal (q * c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) * A₁ *
          (∫⁻ x, f x ^ p ∂μ) ^ (q₁ / p₁) := by
  have hae := hf.ae_eq_mk
  have hpow : ∀ r : ℝ, (fun x => f x ^ r) =ᵐ[μ] fun x => hf.mk f x ^ r := fun r =>
    hae.mono fun x hx => congrArg (fun z : ℝ≥0∞ => z ^ r) hx
  have hset₀ : ∀ a : ℝ≥0∞, ∫⁻ x in {x | a < f x}, f x ^ p₀ ∂μ =
      ∫⁻ x in {x | a < hf.mk f x}, hf.mk f x ^ p₀ ∂μ := by
    intro a
    have hsets : {x | a < f x} =ᵐ[μ] {x | a < hf.mk f x} := by
      filter_upwards [hae] with x hx
      exact congrArg (fun z : ℝ≥0∞ => a < z) hx
    rw [Measure.restrict_congr_set hsets]
    exact lintegral_congr_ae (ae_restrict_of_ae (hpow p₀))
  have hset₁ : ∀ a : ℝ≥0∞, ∫⁻ x in {x | f x ≤ a}, f x ^ p₁ ∂μ =
      ∫⁻ x in {x | hf.mk f x ≤ a}, hf.mk f x ^ p₁ ∂μ := by
    intro a
    have hsets : {x | f x ≤ a} =ᵐ[μ] {x | hf.mk f x ≤ a} := by
      filter_upwards [hae] with x hx
      exact congrArg (fun z : ℝ≥0∞ => z ≤ a) hx
    rw [Measure.restrict_congr_set hsets]
    exact lintegral_congr_ae (ae_restrict_of_ae (hpow p₁))
  rw [lintegral_congr_ae (hpow p)]
  refine lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_of_measurable hf.measurable_mk hu hp₀ hlt₀
    hlt₁ hpq₀ hpq₁ hγ₀ hγ₁ hc fun t ht => ?_
  rw [← hset₀, ← hset₁]
  exact h t ht

section Operator

variable {G : Type*} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G]
  [ESeminormedAddMonoid G] {T : (α → G) → β → ℝ≥0∞} {v : α → G} {d e t : ℝ}

/-- The operator-level truncation argument for off-diagonal Marcinkiewicz interpolation.

Suppose `T` is subadditive, of weak type `(p₀, q₀)` with constant `A₀` and of weak type `(p₁, q₁)`
with constant `A₁`. Split `v` according to whether its extended norm exceeds a level `a`. If
`d + e ≤ 1`, then `T v > t` forces the image of the high part to exceed `d * t` or the image of
the low part to exceed `e * t`, and applying the two weak-type bounds to the two pieces gives

`ν {T v > t} ≤ A₀ d ^ (-q₀) t ^ (-q₀) (∫⁻ x in {‖v‖ₑ > a}, ‖v x‖ₑ ^ p₀ ∂μ) ^ (q₀ / p₀) +
  A₁ e ^ (-q₁) t ^ (-q₁) (∫⁻ x in {‖v‖ₑ ≤ a}, ‖v x‖ₑ ^ p₁ ∂μ) ^ (q₁ / p₁)`.

Off-diagonal interpolation takes the level `a = c t ^ γ`; the diagonal case is
`TauCeti.meas_ofReal_lt_le_add_setLIntegral`. -/
theorem meas_ofReal_lt_le_add_setLIntegral_rpow (hv : AEMeasurable v μ) (ht : 0 < t)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hd : 0 < d) (he : 0 < e) (hde : d + e ≤ 1) (a : ℝ≥0∞)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak₀ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ q₀ * ν {y | r < T g y} ≤ A₀ * (∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ) ^ (q₀ / p₀))
    (hweak₁ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ q₁ * ν {y | r < T g y} ≤ A₁ * (∫⁻ x, ‖g x‖ₑ ^ p₁ ∂μ) ^ (q₁ / p₁)) :
    ν {y | ENNReal.ofReal t < T v y} ≤
      A₀ * ENNReal.ofReal (d ^ (-q₀)) * ENNReal.ofReal (t ^ (-q₀)) *
          (∫⁻ x in {x | a < ‖v x‖ₑ}, ‖v x‖ₑ ^ p₀ ∂μ) ^ (q₀ / p₀) +
        A₁ * ENNReal.ofReal (e ^ (-q₁)) * ENNReal.ofReal (t ^ (-q₁)) *
          (∫⁻ x in {x | ‖v x‖ₑ ≤ a}, ‖v x‖ₑ ^ p₁ ∂μ) ^ (q₁ / p₁) := by
  set g : α → G := hv.mk v with _
  have hgmeas : Measurable g := hv.measurable_mk
  set S : Set α := {x | a < ‖g x‖ₑ} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hgmeas.enorm
  set g₁ : α → G := S.indicator v with hg₁def
  set g₂ : α → G := Sᶜ.indicator v with hg₂def
  have hg₁meas : AEMeasurable g₁ μ := hv.indicator hSmeas
  have hg₂meas : AEMeasurable g₂ μ := hv.indicator hSmeas.compl
  have hTv : T v ≤ᵐ[ν] T g₁ + T g₂ := by
    have hsplit : g₁ + g₂ = v := by rw [hg₁def, hg₂def, Set.indicator_self_add_compl]
    rw [← hsplit]
    exact hadd g₁ g₂ hg₁meas hg₂meas
  have hS₀ : ∫⁻ x, ‖g₁ x‖ₑ ^ p₀ ∂μ = ∫⁻ x in {x | a < ‖v x‖ₑ}, ‖v x‖ₑ ^ p₀ ∂μ := by
    rw [lintegral_enorm_rpow_eq_setLIntegral hSmeas Filter.EventuallyEq.rfl hp₀]
    exact setLIntegral_congr (hv.ae_eq_mk.fun_comp fun z => a < ‖z‖ₑ).symm
  have hS₁ : ∫⁻ x, ‖g₂ x‖ₑ ^ p₁ ∂μ = ∫⁻ x in {x | ‖v x‖ₑ ≤ a}, ‖v x‖ₑ ^ p₁ ∂μ := by
    have hSc : Sᶜ = {x | ‖g x‖ₑ ≤ a} := by
      ext x
      simp [hSdef]
    rw [lintegral_enorm_rpow_eq_setLIntegral hSmeas.compl Filter.EventuallyEq.rfl hp₁, hSc]
    exact setLIntegral_congr (hv.ae_eq_mk.fun_comp fun z => ‖z‖ₑ ≤ a).symm
  -- A weak-type bound at a positive height `r` bounds the measure of the superlevel set.
  have hweak' : ∀ {r q : ℝ} {m B : ℝ≥0∞}, ENNReal.ofReal r ^ q * m ≤ B → 0 < r →
      m ≤ ENNReal.ofReal (r ^ (-q)) * B := fun h hr => by
    rw [← ENNReal.ofReal_rpow_of_pos hr]
    exact ENNReal.le_rpow_neg_mul_of_rpow_mul_le (ENNReal.ofReal_pos.2 hr).ne'
      ENNReal.ofReal_ne_top h
  have hsplit : ∀ (k r : ℝ), 0 < k → ENNReal.ofReal ((k * t) ^ (-r)) =
      ENNReal.ofReal (k ^ (-r)) * ENNReal.ofReal (t ^ (-r)) := fun k r hk => by
    rw [Real.mul_rpow hk.le ht.le, ENNReal.ofReal_mul (Real.rpow_nonneg hk.le _)]
  calc ν {y | ENNReal.ofReal t < T v y}
      ≤ ν ({y | ENNReal.ofReal (d * t) < T g₁ y} ∪ {y | ENNReal.ofReal (e * t) < T g₂ y}) :=
        measure_mono_ae (setOf_ofReal_lt_ae_le_union ht.le hd.le he.le hde hTv)
    _ ≤ ν {y | ENNReal.ofReal (d * t) < T g₁ y} + ν {y | ENNReal.ofReal (e * t) < T g₂ y} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((d * t) ^ (-q₀)) * (A₀ * (∫⁻ x, ‖g₁ x‖ₑ ^ p₀ ∂μ) ^ (q₀ / p₀)) +
          ENNReal.ofReal ((e * t) ^ (-q₁)) * (A₁ * (∫⁻ x, ‖g₂ x‖ₑ ^ p₁ ∂μ) ^ (q₁ / p₁)) :=
        add_le_add (hweak' (hweak₀ g₁ hg₁meas _) (mul_pos hd ht))
          (hweak' (hweak₁ g₂ hg₂meas _) (mul_pos he ht))
    _ = _ := by
        rw [hS₀, hS₁, hsplit d q₀ hd, hsplit e q₁ he]
        ring

/-- The exponents of off-diagonal interpolation with `p₀ < p₁`: `p` lies strictly between `p₀` and
`p₁`, `q` is positive and different from `q₀`, and the height exponent
`γ = (q - q₀) p₀ / (q₀ (p - p₀))` satisfies the two relations of
`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le_rpow`. -/
private theorem interpolation_exponents (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀)
    (hq₁ : 0 < q₁) (hpp : p₀ < p₁) (hqq : q₀ ≠ q₁) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp : p⁻¹ = (1 - θ) / p₀ + θ / p₁) (hq : q⁻¹ = (1 - θ) / q₀ + θ / q₁) :
    p₀ < p ∧ p < p₁ ∧ 0 < q ∧
      (q - q₀) / ((q - q₀) * p₀ / (q₀ * (p - p₀))) = q₀ * (p - p₀) / p₀ ∧
      (q - q₁) / ((q - q₀) * p₀ / (q₀ * (p - p₀))) = q₁ * (p - p₁) / p₁ := by
  have hinv : p₁⁻¹ < p₀⁻¹ := inv_strictAnti₀ hp₀ hpp
  have hp' : p⁻¹ = (1 - θ) * p₀⁻¹ + θ * p₁⁻¹ := by rw [hp]; ring
  have hq' : q⁻¹ = (1 - θ) * q₀⁻¹ + θ * q₁⁻¹ := by rw [hq]; ring
  have h₁ : p₁⁻¹ < p⁻¹ := by rw [hp']; nlinarith
  have h₂ : p⁻¹ < p₀⁻¹ := by rw [hp']; nlinarith
  have hp0 : 0 < p := inv_pos.1 ((inv_pos.2 hp₁).trans h₁)
  have hq0 : 0 < q := inv_pos.1 (by
    rw [hq']; have := inv_pos.2 hq₀; have := inv_pos.2 hq₁; nlinarith)
  have hlt₀ : p₀ < p := (inv_lt_inv₀ hp0 hp₀).1 h₂
  have hqq₀ : q - q₀ ≠ 0 := by
    intro h
    rw [show q = q₀ by linarith] at hq'
    have : θ * (q₁⁻¹ - q₀⁻¹) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact hqq (inv_injective (by linarith))
  have hpp₀ : p - p₀ ≠ 0 := by linarith
  have hγ0 : (q - q₀) * p₀ / (q₀ * (p - p₀)) ≠ 0 :=
    div_ne_zero (mul_ne_zero hqq₀ hp₀.ne') (mul_ne_zero hq₀.ne' hpp₀)
  have key : (q₁⁻¹ - q⁻¹) * (p₀⁻¹ - p⁻¹) = (q₀⁻¹ - q⁻¹) * (p₁⁻¹ - p⁻¹) := by rw [hp, hq]; ring
  refine ⟨hlt₀, (inv_lt_inv₀ hp₁ hp0).1 h₁, hq0, by field_simp, ?_⟩
  rw [div_eq_iff hγ0]
  field_simp at key ⊢
  linear_combination key

/-- For the height constant `c = N ^ ((1 - γ) / p)` of a finite nonzero `N`, the power of `c` and
the power `N ^ (qᵢ / pᵢ)` of one endpoint term combine to `N ^ (q / p)`. -/
private theorem ofReal_mul_rpow_div_mul_rpow_eq {pᵢ qᵢ k : ℝ} (hp : 0 < p) (hpᵢ : 0 < pᵢ)
    (hγ : γ ≠ 0) (hq : 0 < q) (hk : 0 ≤ k) (A : ℝ≥0∞) (hγᵢ : (q - qᵢ) / γ = qᵢ * (p - pᵢ) / pᵢ)
    {N : ℝ≥0∞} (hN0 : N ≠ 0) (hNt : N ≠ ∞) :
    ENNReal.ofReal (q * (N.toReal ^ ((1 - γ) / p)) ^ (qᵢ * (pᵢ - p) / pᵢ) / k) * A *
        N ^ (qᵢ / pᵢ) =
      ENNReal.ofReal (q / k) * A * N ^ (q / p) := by
  have hexp : (1 - γ) / p * (qᵢ * (pᵢ - p) / pᵢ) + qᵢ / pᵢ = q / p := by
    rw [div_eq_div_iff hγ hpᵢ.ne'] at hγᵢ
    field_simp
    linear_combination -hγᵢ
  have hNr : 0 < N.toReal := ENNReal.toReal_pos hN0 hNt
  rw [← Real.rpow_mul hNr.le, mul_div_right_comm, ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos hNr, ENNReal.ofReal_toReal hNt, ← hexp,
    ENNReal.rpow_add _ _ hN0 hNt]
  ring

/-- Off-diagonal Marcinkiewicz interpolation with `p₀ < p₁`; the general case exchanges the
endpoints. -/
private theorem lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow_of_lt (hv : AEMeasurable v μ)
    (hTv : AEMeasurable (T v) ν) (hpp : p₀ < p₁) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hpq₀ : p₀ ≤ q₀) (hpq₁ : p₁ ≤ q₁) (hqq : q₀ ≠ q₁)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : p⁻¹ = (1 - θ) / p₀ + θ / p₁)
    (hq : q⁻¹ = (1 - θ) / q₀ + θ / q₁) (hd : 0 < d) (he : 0 < e) (hde : d + e ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak₀ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ q₀ * ν {y | r < T g y} ≤ A₀ * (∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ) ^ (q₀ / p₀))
    (hweak₁ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ q₁ * ν {y | r < T g y} ≤ A₁ * (∫⁻ x, ‖g x‖ₑ ^ p₁ ∂μ) ^ (q₁ / p₁)) :
    ∫⁻ y, T v y ^ q ∂ν ≤
      (ENNReal.ofReal (q / |q - q₀|) * (A₀ * ENNReal.ofReal (d ^ (-q₀))) +
        ENNReal.ofReal (q / |q - q₁|) * (A₁ * ENNReal.ofReal (e ^ (-q₁)))) *
        (∫⁻ x, ‖v x‖ₑ ^ p ∂μ) ^ (q / p) := by
  have hq₀ : 0 < q₀ := hp₀.trans_le hpq₀
  have hq₁ : 0 < q₁ := hp₁.trans_le hpq₁
  obtain ⟨hlt₀, hlt₁, hq0, hγ₀, hγ₁⟩ :=
    interpolation_exponents hp₀ hp₁ hq₀ hq₁ hpp hqq hθ₀ hθ₁ hp hq
  set γ := (q - q₀) * p₀ / (q₀ * (p - p₀)) with hγdef
  obtain ⟨hγ, -, hqq₀, hqq₁⟩ := ne_zero_and_pos_of_div_eq hp₀ hlt₀ hlt₁ hpq₀ hpq₁ hγ₀ hγ₁
  have hp0 : 0 < p := hp₀.trans hlt₀
  set N := ∫⁻ x, ‖v x‖ₑ ^ p ∂μ with hN
  -- The distributional estimate at the height `c t ^ γ`, for any `c > 0`.
  have hmain : ∀ c : ℝ, 0 < c → ∫⁻ y, T v y ^ q ∂ν ≤
      ENNReal.ofReal (q * c ^ (q₀ * (p₀ - p) / p₀) / |q - q₀|) *
          (A₀ * ENNReal.ofReal (d ^ (-q₀))) * N ^ (q₀ / p₀) +
        ENNReal.ofReal (q * c ^ (q₁ * (p₁ - p) / p₁) / |q - q₁|) *
          (A₁ * ENNReal.ofReal (e ^ (-q₁))) * N ^ (q₁ / p₁) := fun c hc =>
    lintegral_rpow_le_of_meas_ofReal_lt_le_rpow hv.enorm hTv hp₀ hlt₀ hlt₁ hpq₀ hpq₁ hγ₀ hγ₁ hc
      fun t ht => meas_ofReal_lt_le_add_setLIntegral_rpow hv ht hp₀ hp₁ hd he hde _ hadd hweak₀
        hweak₁
  by_cases hNfin : N = 0 ∨ N = ∞
  · -- For `N ∈ {0, ∞}` every positive power of `N` is `N ^ (q / p)`, and `c = 1` will do.
    have hpow : ∀ r : ℝ, 0 < r → N ^ r = N ^ (q / p) := fun r hr => by
      rcases hNfin with h | h
      · rw [h, ENNReal.zero_rpow_of_pos hr, ENNReal.zero_rpow_of_pos (div_pos hq0 hp0)]
      · rw [h, ENNReal.top_rpow_of_pos hr, ENNReal.top_rpow_of_pos (div_pos hq0 hp0)]
    refine (hmain 1 one_pos).trans_eq ?_
    rw [Real.one_rpow, Real.one_rpow, mul_one, hpow _ (div_pos hq₀ hp₀),
      hpow _ (div_pos hq₁ hp₁)]
    ring
  obtain ⟨hN0, hNt⟩ := not_or.1 hNfin
  -- Otherwise the height constant `c = N ^ ((1 - γ) / p)` balances the two terms.
  refine (hmain (N.toReal ^ ((1 - γ) / p))
    (Real.rpow_pos_of_pos (ENNReal.toReal_pos hN0 hNt) _)).trans_eq ?_
  rw [ofReal_mul_rpow_div_mul_rpow_eq hp0 hp₀ hγ hq0 (abs_nonneg _) _ hγ₀ hN0 hNt,
    ofReal_mul_rpow_div_mul_rpow_eq hp0 hp₁ hγ hq0 (abs_nonneg _) _ hγ₁ hN0 hNt]
  ring

/-- **The off-diagonal Marcinkiewicz interpolation theorem.** Let `T` be a subadditive operator of
weak type `(p₀, q₀)` with constant `A₀` and of weak type `(p₁, q₁)` with constant `A₁`:

`r ^ qᵢ * ν {T g > r} ≤ Aᵢ * (∫⁻ ‖g‖ ^ pᵢ ∂μ) ^ (qᵢ / pᵢ)` for every `g` and every `r`,

with `0 < pᵢ ≤ qᵢ < ∞`, `p₀ ≠ p₁` and `q₀ ≠ q₁`. For `0 < θ < 1` let
`1 / p = (1 - θ) / p₀ + θ / p₁` and `1 / q = (1 - θ) / q₀ + θ / q₁`. Then `T` is of strong
type `(p, q)`:

`∫⁻ (T v) ^ q ∂ν ≤ (q / |q - q₀| · A₀ d ^ (-q₀) + q / |q - q₁| · A₁ e ^ (-q₁)) *
  (∫⁻ ‖v‖ ^ p ∂μ) ^ (q / p)`,

for any splitting parameters `d, e > 0` with `d + e ≤ 1`. -/
theorem lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow (hv : AEMeasurable v μ)
    (hTv : AEMeasurable (T v) ν) (hpp : p₀ ≠ p₁) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hpq₀ : p₀ ≤ q₀) (hpq₁ : p₁ ≤ q₁) (hqq : q₀ ≠ q₁)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : p⁻¹ = (1 - θ) / p₀ + θ / p₁)
    (hq : q⁻¹ = (1 - θ) / q₀ + θ / q₁) (hd : 0 < d) (he : 0 < e) (hde : d + e ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak₀ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ q₀ * ν {y | r < T g y} ≤ A₀ * (∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ) ^ (q₀ / p₀))
    (hweak₁ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ q₁ * ν {y | r < T g y} ≤ A₁ * (∫⁻ x, ‖g x‖ₑ ^ p₁ ∂μ) ^ (q₁ / p₁)) :
    ∫⁻ y, T v y ^ q ∂ν ≤
      (ENNReal.ofReal (q / |q - q₀|) * (A₀ * ENNReal.ofReal (d ^ (-q₀))) +
        ENNReal.ofReal (q / |q - q₁|) * (A₁ * ENNReal.ofReal (e ^ (-q₁)))) *
        (∫⁻ x, ‖v x‖ₑ ^ p ∂μ) ^ (q / p) := by
  rcases hpp.lt_or_gt with hpp | hpp
  · exact lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow_of_lt hv hTv hpp hp₀ hp₁ hpq₀ hpq₁ hqq
      hθ₀ hθ₁ hp hq hd he hde hadd hweak₀ hweak₁
  · have h := lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow_of_lt hv hTv hpp hp₁ hp₀ hpq₁ hpq₀
      hqq.symm (θ := 1 - θ) (by linarith) (by linarith) (by rw [hp]; ring) (by rw [hq]; ring) he hd
      (by linarith) hadd hweak₁ hweak₀
    rwa [add_comm] at h

end Operator

end TauCeti
