/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.Basic
public import TauCeti.MeasureTheory.Integral.Prod

/-!
# Marcinkiewicz interpolation between two finite exponents

A **sublinear** operator `T` that is simultaneously of **weak type `(p₀, p₀)`** and of **weak type
`(p₁, p₁)`**, for `0 < p₀ < p₁ < ∞`, is bounded on `L^p` for every `p₀ < p < p₁`. This is the
Marcinkiewicz interpolation theorem in the case of two finite endpoints; the case `p₀ = 1`,
`p₁ = ∞`, where the second endpoint is an `L^∞` bound rather than a weak-type bound, is
`TauCeti.MeasureTheory.Integral.Marcinkiewicz.Basic`.

Source and target exponents agree at both endpoints here: the hypotheses are weak type
`(p₀, p₀)` and `(p₁, p₁)`, and the conclusion is strong type `(p, p)`. The off-diagonal theorem,
which interpolates weak type `(p₀, q₀)` and `(p₁, q₁)` with `pᵢ ≤ qᵢ` into strong type `(p, q)`
along the line `1 / q = (1 - θ) / q₀ + θ / q₁`, is not proved here.

## The statements proved here

As in the diagonal case, the analytic engine is stated in terms of the **distribution functions**
of `T f` and of `f`. For each height `t`, splitting `f` at the height `c * t` and applying the two
endpoint bounds to the two pieces produces the single inequality

`ν {T f > t} ≤ A₀ t ^ (-p₀) * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ^ p₀ ∂μ +
  A₁ t ^ (-p₁) * ∫⁻ x in {‖f‖ ≤ c * t}, ‖f‖ ^ p₁ ∂μ`,

which says that the part of `f` above the height `c * t` can only push `T f` above `t` through the
first endpoint, and the part below it only through the second. That inequality is the hypothesis
of `TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`, and its conclusion is the `L^p` bound

`∫⁻ (T f) ^ p ∂ν ≤ (p c ^ (p₀ - p) / (p - p₀) * A₀ + p c ^ (p₁ - p) / (p₁ - p) * A₁) *
  ∫⁻ ‖f‖ ^ p ∂μ`.

Both constants degenerate as `p` approaches an endpoint, exactly as they must: an operator of
weak type `(p₀, p₀)` need not be bounded on `L^{p₀}`. Keeping the two endpoint constants separate
records which endpoint each half of the bound comes from, and makes the splitting parameter `c`
available for optimizing the total constant.

## The proof

The layer cake formula (`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`) converts the
left-hand side into an integral in the height variable `t`. Multiplied by `t ^ (p - 1)`, the two
terms of the hypothesis become the two truncated double integrals

`∫⁻ t in (0, ∞), t ^ (p - p₀ - 1) * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ^ p₀ ∂μ`  and
`∫⁻ t in (0, ∞), t ^ (p - p₁ - 1) * ∫⁻ x in {‖f‖ ≤ c * t}, ‖f‖ ^ p₁ ∂μ`.

Tonelli's theorem exchanges the two integrations in each, and for a fixed `x` the inner integral
in `t` is elementary: over the region where `c * t` stays below `‖f x‖` it is
`TauCeti.lintegral_indicator_ofReal_rpow_Ioi`, which converges because `p₀ < p`, and over the
complementary region it is `TauCeti.lintegral_indicator_le_ofReal_rpow_Ioi`, which converges
because `p < p₁`. Both reassemble into a multiple of `‖f x‖ ^ p`.

Tonelli's theorem needs `μ` to be s-finite, but the statement does not: both sides ignore the part
of `μ` outside `{f > 0}`, and once `∫⁻ f ^ p ∂μ` is finite that part is σ-finite, by
`TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`.

## Main declarations

* `TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`: the interpolation estimate.
* `TauCeti.meas_ofReal_lt_le_add_setLIntegral`: the reusable truncation argument from
  subadditivity and the two weak-type endpoint bounds.
* `TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le`: operator-level Marcinkiewicz interpolation
  between two finite exponents.

## References

* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.2.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → ℝ≥0∞} {u : β → ℝ≥0∞} {p p₀ p₁ q s c : ℝ} {A₀ A₁ : ℝ≥0∞}

/-- **The weighted mass of the part of `f` above the height `c * t`.** For `-1 < s` the weight
`t ^ s` is integrable at the origin, and the double integral of the upper truncations of `f ^ q`
against it is exactly a multiple of `∫⁻ f ^ (q + (s + 1))`. -/
private theorem lintegral_mul_setLIntegral_lt_of_measurable [SFinite μ] (hf : Measurable f)
    (hq : 0 ≤ q)
    (hs : -1 < s) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  have hs1 : (0 : ℝ) ≤ s + 1 := by linarith
  have hR : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1) < f z.2} :=
    measurableSet_lt ((measurable_fst.const_mul c).ennreal_ofReal) (hf.comp measurable_snd)
  rw [lintegral_mul_setLIntegral_eq (κ := volume.restrict (Ioi (0 : ℝ)))
      (w := fun t : ℝ => ENNReal.ofReal (t ^ s))
      (R := fun t x => ENNReal.ofReal (c * t) < f x) hR (hf.pow_const q).aemeasurable
      ((measurable_id.pow measurable_const).ennreal_ofReal.aemeasurable),
    ← lintegral_const_mul _ (hf.pow_const _)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_indicator_ofReal_rpow_Ioi hs hc (f x), ENNReal.rpow_add_of_nonneg q (s + 1) hq hs1]
  ring

/-- **The weighted mass of the part of `f` above the height `c * t`.** For `-1 < s` the weight
`t ^ s` is integrable at the origin, and the double integral of the upper truncations of `f ^ q`
against it is exactly a multiple of `∫⁻ f ^ (q + (s + 1))`. -/
theorem lintegral_mul_setLIntegral_lt [SFinite μ] (hf : AEMeasurable f μ) (hq : 0 ≤ q)
    (hs : -1 < s) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  let g := hf.mk f
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have hinner : ∀ t : ℝ,
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < g x}, g x ^ q ∂μ := by
    intro t
    have hset : {x | ENNReal.ofReal (c * t) < f x} =ᵐ[μ]
        {x | ENNReal.ofReal (c * t) < g x} :=
      hfg.mono fun _ hx => by simp only [Set.mem_ofPred_eq]; rw [hx]
    rw [Measure.restrict_congr_set hset]
    exact lintegral_congr_ae (ae_restrict_of_ae (hfg.fun_comp fun z => z ^ q))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
          ∫⁻ x in {x | ENNReal.ofReal (c * t) < g x}, g x ^ q ∂μ := by
      exact lintegral_congr fun t => congrArg (ENNReal.ofReal (t ^ s) * ·) (hinner t)
    _ = ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) *
        ∫⁻ x, g x ^ (q + (s + 1)) ∂μ :=
      lintegral_mul_setLIntegral_lt_of_measurable hf.measurable_mk hq hs hc
    _ = ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) *
        ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
      exact congrArg (ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * ·)
        (lintegral_congr_ae (hfg.fun_comp fun z => z ^ (q + (s + 1)))).symm

/-- **The weighted mass of the part of `f` below the height `c * t`.** For `s < -1` the weight
`t ^ s` is integrable at infinity, and the double integral of the lower truncations of `f ^ q`
against it is at most a multiple of `∫⁻ f ^ (q + (s + 1))`.

The bound is not an equality: where `f` is infinite the left-hand side sees nothing, because no
finite height `c * t` reaches it, while the right-hand side is infinite as soon as
`0 < q + (s + 1)`. -/
private theorem lintegral_mul_setLIntegral_le_le_of_measurable [SFinite μ] (hf : Measurable f)
    (hq : 0 ≤ q)
    (hs : s < -1) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ q ∂μ ≤
      ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) * ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  have hs1 : s + 1 < 0 := by linarith
  -- The pointwise step, which is an equality away from the two extreme values.
  have hmul : ∀ z : ℝ≥0∞, z ^ (s + 1) * z ^ q ≤ z ^ (q + (s + 1)) := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz0
    · rcases hq.eq_or_lt with rfl | hq'
      · simp
      · rw [ENNReal.zero_rpow_of_pos hq', mul_zero]
        exact zero_le
    rcases eq_or_ne z ∞ with rfl | hztop
    · rw [ENNReal.top_rpow_of_neg hs1, zero_mul]
      exact zero_le
    · conv_rhs => rw [ENNReal.rpow_add _ _ hz0 hztop]
      exact le_of_eq (mul_comm _ _)
  have hR : MeasurableSet {z : ℝ × α | f z.2 ≤ ENNReal.ofReal (c * z.1)} :=
    measurableSet_le (hf.comp measurable_snd) ((measurable_fst.const_mul c).ennreal_ofReal)
  rw [lintegral_mul_setLIntegral_eq (κ := volume.restrict (Ioi (0 : ℝ)))
      (w := fun t : ℝ => ENNReal.ofReal (t ^ s))
      (R := fun t x => f x ≤ ENNReal.ofReal (c * t)) hR (hf.pow_const q).aemeasurable
      ((measurable_id.pow measurable_const).ennreal_ofReal.aemeasurable),
    ← lintegral_const_mul _ (hf.pow_const _)]
  refine lintegral_mono fun x => ?_
  rw [lintegral_indicator_le_ofReal_rpow_Ioi hs hc (f x), mul_assoc]
  exact mul_le_mul_right (hmul (f x)) _

/-- **The weighted mass of the part of `f` below the height `c * t`.** For `s < -1` the weight
`t ^ s` is integrable at infinity, and the double integral of the lower truncations of `f ^ q`
against it is at most a multiple of `∫⁻ f ^ (q + (s + 1))`.

The bound is not an equality: where `f` is infinite the left-hand side sees nothing, because no
finite height `c * t` reaches it, while the right-hand side is infinite as soon as
`0 < q + (s + 1)`. -/
theorem lintegral_mul_setLIntegral_le_le [SFinite μ] (hf : AEMeasurable f μ) (hq : 0 ≤ q)
    (hs : s < -1) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ q ∂μ ≤
      ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) *
        ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  let g := hf.mk f
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have hinner : ∀ t : ℝ,
      ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ q ∂μ =
        ∫⁻ x in {x | g x ≤ ENNReal.ofReal (c * t)}, g x ^ q ∂μ := by
    intro t
    have hset : {x | f x ≤ ENNReal.ofReal (c * t)} =ᵐ[μ]
        {x | g x ≤ ENNReal.ofReal (c * t)} :=
      hfg.mono fun _ hx => by simp only [Set.mem_ofPred_eq]; rw [hx]
    rw [Measure.restrict_congr_set hset]
    exact lintegral_congr_ae (ae_restrict_of_ae (hfg.fun_comp fun z => z ^ q))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ q ∂μ =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
          ∫⁻ x in {x | g x ≤ ENNReal.ofReal (c * t)}, g x ^ q ∂μ := by
      exact lintegral_congr fun t => congrArg (ENNReal.ofReal (t ^ s) * ·) (hinner t)
    _ ≤ ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) *
        ∫⁻ x, g x ^ (q + (s + 1)) ∂μ :=
      lintegral_mul_setLIntegral_le_le_of_measurable hf.measurable_mk hq hs hc
    _ = ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) *
        ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
      exact congrArg (ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) * ·)
        (lintegral_congr_ae (hfg.fun_comp fun z => z ^ (q + (s + 1)))).symm

/-- The interpolation estimate for a measurable `f` and an s-finite `μ`, which is the generality
in which Tonelli's theorem is available; both hypotheses are removed below. -/
private theorem lintegral_rpow_le_of_meas_ofReal_lt_le_of_measurable_of_sFinite [SFinite μ]
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < u y} ≤
      A₀ * ENNReal.ofReal (t ^ (-p₀)) * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ +
        A₁ * ENNReal.ofReal (t ^ (-p₁)) *
          ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      (ENNReal.ofReal (p * c ^ (p₀ - p) / (p - p₀)) * A₀ +
        ENNReal.ofReal (p * c ^ (p₁ - p) / (p₁ - p)) * A₁) * ∫⁻ x, f x ^ p ∂μ := by
  have hp : (0 : ℝ) < p := hp₀.trans hlt₀
  have hp₁ : (0 : ℝ) < p₁ := hp.trans hlt₁
  have hR₀ : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1) < f z.2} :=
    measurableSet_lt ((measurable_fst.const_mul c).ennreal_ofReal) (hf.comp measurable_snd)
  have hR₁ : MeasurableSet {z : ℝ × α | f z.2 ≤ ENNReal.ofReal (c * z.1)} :=
    measurableSet_le (hf.comp measurable_snd) ((measurable_fst.const_mul c).ennreal_ofReal)
  have hI₀ : Measurable fun t => ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ :=
    measurable_setLIntegral_of_measurableSet (R := fun t x => ENNReal.ofReal (c * t) < f x) hR₀
      (hf.pow_const p₀).aemeasurable
  have hI₁ : Measurable fun t => ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ :=
    measurable_setLIntegral_of_measurableSet (R := fun t x => f x ≤ ENNReal.ofReal (c * t)) hR₁
      (hf.pow_const p₁).aemeasurable
  have hw₀ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - p₀ - 1)) :=
    (measurable_id.pow measurable_const).ennreal_ofReal
  have hw₁ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - p₁ - 1)) :=
    (measurable_id.pow measurable_const).ennreal_ofReal
  -- Multiplying the hypothesis by `t ^ (p - 1)` absorbs the two negative powers of the height
  -- into the two weights of the truncated integrals.
  have hkey : ∀ t ∈ Ioi (0 : ℝ),
      ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1)) ≤
        A₀ * (ENNReal.ofReal (t ^ (p - p₀ - 1)) *
            ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ) +
          A₁ * (ENNReal.ofReal (t ^ (p - p₁ - 1)) *
            ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hpow : ∀ r : ℝ, ENNReal.ofReal (t ^ (-r)) * ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal (t ^ (p - r - 1)) := by
      intro r
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht'.le _), ← Real.rpow_add ht']
      congr 2
      ring
    calc ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1))
        ≤ (A₀ * ENNReal.ofReal (t ^ (-p₀)) *
              ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ +
            A₁ * ENNReal.ofReal (t ^ (-p₁)) *
              ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ) *
            ENNReal.ofReal (t ^ (p - 1)) := mul_le_mul_left (h t ht') _
      _ = A₀ * (ENNReal.ofReal (t ^ (-p₀)) * ENNReal.ofReal (t ^ (p - 1))) *
              ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ +
            A₁ * (ENNReal.ofReal (t ^ (-p₁)) * ENNReal.ofReal (t ^ (p - 1))) *
              ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ := by ring
      _ = _ := by rw [hpow p₀, hpow p₁]; ring
  -- The two truncated double integrals, evaluated by the two halves of the truncation estimate.
  have hlow : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - p₀ - 1)) *
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ ≤
      ENNReal.ofReal (c ^ (p₀ - p) / (p - p₀)) * ∫⁻ x, f x ^ p ∂μ := by
    have hmain := (lintegral_mul_setLIntegral_lt (μ := μ) (f := f) (q := p₀)
      (s := p - p₀ - 1) (c := c) hf.aemeasurable hp₀.le (by linarith) hc).le
    have hneg : -(p - p₀) = p₀ - p := by ring
    have hden : p - p₀ - 1 + 1 = p - p₀ := by ring
    have hexp : p₀ + (p - p₀) = p := by ring
    simpa only [hden, hneg, hexp] using hmain
  have hhigh : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - p₁ - 1)) *
      ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ ≤
      ENNReal.ofReal (c ^ (p₁ - p) / (p₁ - p)) * ∫⁻ x, f x ^ p ∂μ := by
    have hmain := lintegral_mul_setLIntegral_le_le (μ := μ) (f := f) (q := p₁)
      (s := p - p₁ - 1) (c := c) hf.aemeasurable hp₁.le (by linarith) hc
    have hnorm : -(p - p₁ - 1 + 1) = p₁ - p := by ring
    have hexp : p₁ + (p - p₁ - 1 + 1) = p := by ring
    simpa only [hnorm, hexp] using hmain
  have hg₀ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - p₀ - 1)) *
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ := hw₀.mul hI₀
  have hg₁ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - p₁ - 1)) *
      ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ := hw₁.mul hI₁
  have hm₀ : Measurable fun t : ℝ => A₀ * (ENNReal.ofReal (t ^ (p - p₀ - 1)) *
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ) := measurable_const.mul hg₀
  rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul ν hu hp]
  calc ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          (A₀ * (ENNReal.ofReal (t ^ (p - p₀ - 1)) *
              ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ) +
            A₁ * (ENNReal.ofReal (t ^ (p - p₁ - 1)) *
              ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ)) := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hkey t ht
    _ = ENNReal.ofReal p *
          ((A₀ * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - p₀ - 1)) *
              ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ) +
            (A₁ * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - p₁ - 1)) *
              ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ)) := by
        rw [lintegral_add_left hm₀, lintegral_const_mul _ hg₀, lintegral_const_mul _ hg₁]
    _ ≤ ENNReal.ofReal p *
          ((A₀ * (ENNReal.ofReal (c ^ (p₀ - p) / (p - p₀)) * ∫⁻ x, f x ^ p ∂μ)) +
            (A₁ * (ENNReal.ofReal (c ^ (p₁ - p) / (p₁ - p)) * ∫⁻ x, f x ^ p ∂μ))) :=
        mul_le_mul_right
          (add_le_add (mul_le_mul_right hlow _) (mul_le_mul_right hhigh _)) _
    _ = _ := by
        have hcoef₀ : p * c ^ (p₀ - p) / (p - p₀) =
            p * (c ^ (p₀ - p) / (p - p₀)) := by ring
        have hcoef₁ : p * c ^ (p₁ - p) / (p₁ - p) =
            p * (c ^ (p₁ - p) / (p₁ - p)) := by ring
        rw [hcoef₀, hcoef₁]
        rw [ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hp.le]
        ring

/-- The interpolation estimate for a measurable `f` and an arbitrary measure `μ`.

Only the part of `μ` carried by `{f > 0}` enters either side, and once `f` has finite `L^p` norm
that part is σ-finite by `TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`. So the
s-finite case applies to `μ` restricted to `{f > 0}`, after the two degenerate cases — two
vanishing endpoint constants and an infinite right-hand side — are disposed of. -/
private theorem lintegral_rpow_le_of_meas_ofReal_lt_le_of_measurable
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < u y} ≤
      A₀ * ENNReal.ofReal (t ^ (-p₀)) * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ +
        A₁ * ENNReal.ofReal (t ^ (-p₁)) *
          ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      (ENNReal.ofReal (p * c ^ (p₀ - p) / (p - p₀)) * A₀ +
        ENNReal.ofReal (p * c ^ (p₁ - p) / (p₁ - p)) * A₁) * ∫⁻ x, f x ^ p ∂μ := by
  have hp : (0 : ℝ) < p := hp₀.trans hlt₀
  have hp₁ : (0 : ℝ) < p₁ := hp.trans hlt₁
  have hK₀ : (0 : ℝ) < p * c ^ (p₀ - p) / (p - p₀) := by
    have hd : (0 : ℝ) < p - p₀ := by linarith
    positivity
  have hK₁ : (0 : ℝ) < p * c ^ (p₁ - p) / (p₁ - p) := by
    have hd : (0 : ℝ) < p₁ - p := by linarith
    positivity
  rcases eq_or_ne (ENNReal.ofReal (p * c ^ (p₀ - p) / (p - p₀)) * A₀ +
      ENNReal.ofReal (p * c ^ (p₁ - p) / (p₁ - p)) * A₁) 0 with hA | hA
  · -- Both endpoint constants vanish, and the hypothesis already forces `u` to vanish.
    obtain ⟨hz₀, hz₁⟩ := add_eq_zero.1 hA
    have hA₀ : A₀ = 0 :=
      (mul_eq_zero.1 hz₀).resolve_left (ENNReal.ofReal_pos.2 hK₀).ne'
    have hA₁ : A₁ = 0 :=
      (mul_eq_zero.1 hz₁).resolve_left (ENNReal.ofReal_pos.2 hK₁).ne'
    have hzero := lintegral_rpow_le_of_meas_ofReal_lt_le_of_measurable_of_sFinite
      (μ := (0 : Measure α)) (A₀ := A₀) (A₁ := A₁) hf hu hp₀ hlt₀ hlt₁ hc
      fun t ht => by simpa [hA₀, hA₁] using h t ht
    simpa [hA] using hzero
  rcases eq_or_ne (∫⁻ x, f x ^ p ∂μ) ∞ with htop | htop
  · -- The right-hand side is infinite.
    rw [htop, ENNReal.mul_top hA]
    exact le_top
  -- `μ` restricted to `{f > 0}` is σ-finite, so in particular s-finite.
  have hσ : SigmaFinite (μ.restrict {x | 0 < f x}) :=
    sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top hf.aemeasurable hp htop
  have hpos : MeasurableSet {x | 0 < f x} := measurableSet_lt measurable_const hf
  -- A positive power of `f` vanishes off `{f > 0}`, so no truncated integral sees the complement.
  have key : ∀ r : ℝ, 0 < r → ∀ S : Set α,
      ∫⁻ x in S ∩ {x | 0 < f x}, f x ^ r ∂μ = ∫⁻ x in S, f x ^ r ∂μ := by
    intro r hr S
    have hsupp : Function.support (fun x => f x ^ r) ⊆ {x | 0 < f x} := by
      refine Function.support_subset_iff'.2 fun x hx => ?_
      have hx0 : f x = 0 := by simpa [Set.mem_ofPred, nonpos_iff_eq_zero] using hx
      simp [hx0, ENNReal.zero_rpow_of_pos hr]
    rw [Set.inter_comm, ← Measure.restrict_restrict hpos]
    exact setLIntegral_eq_of_support_subset hsupp
  have e₀ : ∀ t : ℝ, ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀
        ∂(μ.restrict {x | 0 < f x}) =
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ := fun t => by
    rw [Measure.restrict_restrict (measurableSet_lt measurable_const hf)]
    exact key p₀ hp₀ _
  have e₁ : ∀ t : ℝ, ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁
        ∂(μ.restrict {x | 0 < f x}) =
      ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ := fun t => by
    rw [Measure.restrict_restrict (measurableSet_le hf measurable_const)]
    exact key p₁ hp₁ _
  have ep : ∫⁻ x, f x ^ p ∂(μ.restrict {x | 0 < f x}) = ∫⁻ x, f x ^ p ∂μ := by
    have := key p hp Set.univ
    rwa [Set.univ_inter, Measure.restrict_univ] at this
  have hmain := lintegral_rpow_le_of_meas_ofReal_lt_le_of_measurable_of_sFinite
    (μ := μ.restrict {x | 0 < f x}) hf hu hp₀ hlt₀ hlt₁ hc fun t ht => by
      rw [e₀ t, e₁ t]; exact h t ht
  rwa [ep] at hmain

/-- **Marcinkiewicz interpolation between two finite exponents**, in distributional form.

Suppose that for every height `t > 0` the superlevel set `{u > t}` obeys the two-sided bound

`ν {u > t} ≤ A₀ t ^ (-p₀) * ∫⁻ x in {f > c * t}, f ^ p₀ ∂μ +
  A₁ t ^ (-p₁) * ∫⁻ x in {f ≤ c * t}, f ^ p₁ ∂μ`,

in which the part of `f` above the height `c * t` is measured in `L^{p₀}` and the part below it
in `L^{p₁}`. Then for every `p₀ < p < p₁`

`∫⁻ u ^ p ∂ν ≤ (p c ^ (p₀ - p) / (p - p₀) * A₀ + p c ^ (p₁ - p) / (p₁ - p) * A₁) * ∫⁻ f ^ p ∂μ`.

Applied with `u = T f` for a sublinear `T`, the hypothesis is what the weak `(p₀, p₀)` and weak
`(p₁, p₁)` endpoint bounds for `T` give after splitting `f` at the height `c * t`, and the
conclusion is the strong type `(p, p)` bound. Each constant degenerates as `p` approaches its own
endpoint, as it must. -/
theorem lintegral_rpow_le_of_meas_ofReal_lt_le
    (hf : AEMeasurable f μ) (hu : AEMeasurable u ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p)
    (hlt₁ : p < p₁) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ν {y | ENNReal.ofReal t < u y} ≤
      A₀ * ENNReal.ofReal (t ^ (-p₀)) * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ p₀ ∂μ +
        A₁ * ENNReal.ofReal (t ^ (-p₁)) *
          ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ p₁ ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      (ENNReal.ofReal (p * c ^ (p₀ - p) / (p - p₀)) * A₀ +
        ENNReal.ofReal (p * c ^ (p₁ - p) / (p₁ - p)) * A₁) * ∫⁻ x, f x ^ p ∂μ := by
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
  refine lintegral_rpow_le_of_meas_ofReal_lt_le_of_measurable hf.measurable_mk hu hp₀ hlt₀ hlt₁ hc
    fun t ht => ?_
  rw [← hset₀, ← hset₁]
  exact h t ht

section Operator

variable {G : Type*} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G]
  [ESeminormedAddMonoid G] {T : (α → G) → β → ℝ≥0∞} {v : α → G} {d e t : ℝ}

/-- The reusable operator-level truncation argument for Marcinkiewicz interpolation between two
finite exponents.

Suppose `T` is subadditive and of weak type `(p₀, p₀)` with constant `A₀` and of weak type
`(p₁, p₁)` with constant `A₁`. Split `v` according to whether its extended norm exceeds `c * t`.
If `d + e ≤ 1`, then `T v > t` forces the image of the high part to exceed `d * t` or the image of
the low part to exceed `e * t`, and applying the two weak-type bounds to the two pieces gives

`ν {T v > t} ≤ A₀ d ^ (-p₀) t ^ (-p₀) * ∫⁻ x in {‖v‖ₑ > c * t}, ‖v x‖ₑ ^ p₀ ∂μ +
  A₁ e ^ (-p₁) t ^ (-p₁) * ∫⁻ x in {‖v‖ₑ ≤ c * t}, ‖v x‖ₑ ^ p₁ ∂μ`.

The parameters `c`, `d` and `e` expose the choice of truncation rather than fixing the customary
`c = 1`, `d = e = 1 / 2`. -/
theorem meas_ofReal_lt_le_add_setLIntegral (hv : AEMeasurable v μ) (ht : 0 < t) (hp₀ : 0 < p₀)
    (hp₁ : 0 < p₁) (hd : 0 < d) (he : 0 < e) (hde : d + e ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak₀ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ p₀ * ν {y | r < T g y} ≤ A₀ * ∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ)
    (hweak₁ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ p₁ * ν {y | r < T g y} ≤ A₁ * ∫⁻ x, ‖g x‖ₑ ^ p₁ ∂μ) :
    ν {y | ENNReal.ofReal t < T v y} ≤
      A₀ * ENNReal.ofReal (d ^ (-p₀)) * ENNReal.ofReal (t ^ (-p₀)) *
          ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ^ p₀ ∂μ +
        A₁ * ENNReal.ofReal (e ^ (-p₁)) * ENNReal.ofReal (t ^ (-p₁)) *
          ∫⁻ x in {x | ‖v x‖ₑ ≤ ENNReal.ofReal (c * t)}, ‖v x‖ₑ ^ p₁ ∂μ := by
  set g : α → G := hv.mk v with hgdef
  have hvg : v =ᵐ[μ] g := hv.ae_eq_mk
  have hgmeas : Measurable g := hv.measurable_mk
  set S : Set α := {x | ENNReal.ofReal (c * t) < ‖g x‖ₑ} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hgmeas.enorm
  set g₁ : α → G := S.indicator v with hg₁def
  set g₂ : α → G := Sᶜ.indicator v with hg₂def
  have hg₁meas : AEMeasurable g₁ μ := hv.indicator hSmeas
  have hg₂meas : AEMeasurable g₂ μ := hv.indicator hSmeas.compl
  have hTv : T v ≤ᵐ[ν] T g₁ + T g₂ := by
    have hsplit : g₁ + g₂ = v := by rw [hg₁def, hg₂def, Set.indicator_self_add_compl]
    rw [← hsplit]
    exact hadd g₁ g₂ hg₁meas hg₂meas
  -- The superlevel set of `T v` splits between the two pieces.
  have hincl : {y | ENNReal.ofReal t < T v y} ≤ᵐ[ν]
      {y | ENNReal.ofReal (d * t) < T g₁ y} ∪ {y | ENNReal.ofReal (e * t) < T g₂ y} := by
    filter_upwards [hTv] with y hsum hy
    rcases lt_or_ge (ENNReal.ofReal (d * t)) (T g₁ y) with h₁ | h₁
    · exact Or.inl (Set.mem_ofPred.2 h₁)
    rcases lt_or_ge (ENNReal.ofReal (e * t)) (T g₂ y) with h₂ | h₂
    · exact Or.inr (Set.mem_ofPred.2 h₂)
    have hy' : ENNReal.ofReal t < T v y := hy
    have hle : T v y ≤ ENNReal.ofReal t :=
      calc T v y ≤ ENNReal.ofReal (d * t) + ENNReal.ofReal (e * t) :=
            hsum.trans (add_le_add h₁ h₂)
        _ = ENNReal.ofReal (d * t + e * t) :=
            (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal (by nlinarith)
    exact absurd (hy'.trans_le hle) (lt_irrefl _)
  -- Each weak-type bound turns into a bound on the measure of a superlevel set.
  have hdiv : ∀ (r q : ℝ) (B : ℝ≥0∞) (w : α → G) (hw : AEMeasurable w μ) (hq : 0 < q),
      (∀ (h : α → G), AEMeasurable h μ → ∀ r' : ℝ≥0∞,
        r' ^ q * ν {y | r' < T h y} ≤ B * ∫⁻ x, ‖h x‖ₑ ^ q ∂μ) → 0 < r →
      ν {y | ENNReal.ofReal r < T w y} ≤
        B * ENNReal.ofReal (r ^ (-q)) * ∫⁻ x, ‖w x‖ₑ ^ q ∂μ := by
    intro r q B w hw hq hweak hr
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal r ^ q :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top
    have htop : ENNReal.ofReal r ^ q ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top
    have hinv : (ENNReal.ofReal r ^ q)⁻¹ = ENNReal.ofReal (r ^ (-q)) := by
      rw [← ENNReal.rpow_neg, ENNReal.ofReal_rpow_of_pos hr]
    calc ν {y | ENNReal.ofReal r < T w y}
        = (ENNReal.ofReal r ^ q)⁻¹ *
            (ENNReal.ofReal r ^ q * ν {y | ENNReal.ofReal r < T w y}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos.ne' htop, one_mul]
      _ ≤ (ENNReal.ofReal r ^ q)⁻¹ * (B * ∫⁻ x, ‖w x‖ₑ ^ q ∂μ) :=
          mul_le_mul_right (hweak w hw _) _
      _ = B * ENNReal.ofReal (r ^ (-q)) * ∫⁻ x, ‖w x‖ₑ ^ q ∂μ := by rw [hinv]; ring
  -- The truncated pieces have the truncated integrals of `v` as their norms.
  have hint : ∀ (q : ℝ), 0 < q → ∀ (R : Set α), MeasurableSet R →
      ∫⁻ x, ‖R.indicator v x‖ₑ ^ q ∂μ = ∫⁻ x in R, ‖v x‖ₑ ^ q ∂μ := by
    intro q hq R hR
    rw [← lintegral_indicator hR]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ R
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero,
        ENNReal.zero_rpow_of_pos hq]
  have henorm : (fun x => ‖v x‖ₑ) =ᵐ[μ] fun x => ‖g x‖ₑ := hvg.mono fun _ hx => congrArg enorm hx
  have hS₀ : ∫⁻ x in S, ‖v x‖ₑ ^ p₀ ∂μ =
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ^ p₀ ∂μ := by
    have hsets : {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ} =ᵐ[μ] S := by
      filter_upwards [henorm] with x hx
      exact congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (c * t) < z) hx
    rw [Measure.restrict_congr_set hsets]
  have hS₁ : ∫⁻ x in Sᶜ, ‖v x‖ₑ ^ p₁ ∂μ =
      ∫⁻ x in {x | ‖v x‖ₑ ≤ ENNReal.ofReal (c * t)}, ‖v x‖ₑ ^ p₁ ∂μ := by
    have hsets : {x | ‖v x‖ₑ ≤ ENNReal.ofReal (c * t)} =ᵐ[μ] Sᶜ := by
      filter_upwards [henorm] with x hx
      simp only [hSdef, Set.mem_compl_iff, Set.mem_ofPred, not_lt, hx]
    rw [Measure.restrict_congr_set hsets]
  calc ν {y | ENNReal.ofReal t < T v y}
      ≤ ν ({y | ENNReal.ofReal (d * t) < T g₁ y} ∪ {y | ENNReal.ofReal (e * t) < T g₂ y}) :=
        measure_mono_ae hincl
    _ ≤ ν {y | ENNReal.ofReal (d * t) < T g₁ y} + ν {y | ENNReal.ofReal (e * t) < T g₂ y} :=
        measure_union_le _ _
    _ ≤ A₀ * ENNReal.ofReal ((d * t) ^ (-p₀)) * ∫⁻ x, ‖g₁ x‖ₑ ^ p₀ ∂μ +
          A₁ * ENNReal.ofReal ((e * t) ^ (-p₁)) * ∫⁻ x, ‖g₂ x‖ₑ ^ p₁ ∂μ :=
        add_le_add (hdiv _ _ _ _ hg₁meas hp₀ hweak₀ (by positivity))
          (hdiv _ _ _ _ hg₂meas hp₁ hweak₁ (by positivity))
    _ = _ := by
        rw [hint p₀ hp₀ S hSmeas, hint p₁ hp₁ Sᶜ hSmeas.compl, hS₀, hS₁,
          Real.mul_rpow hd.le ht.le, Real.mul_rpow he.le ht.le,
          ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
          ENNReal.ofReal_mul (Real.rpow_nonneg he.le _)]
        ring

/-- **Marcinkiewicz interpolation at operator level**, between two finite exponents.

A subadditive operator of weak type `(p₀, p₀)` with constant `A₀` and of weak type `(p₁, p₁)`
with constant `A₁` is of strong type `(p, p)` for every `p₀ < p < p₁`. The positive splitting
parameters `c`, `d`, `e` may be chosen arbitrarily subject to `d + e ≤ 1`. -/
theorem lintegral_rpow_le_of_rpow_mul_meas_lt_le (hv : AEMeasurable v μ)
    (hTv : AEMeasurable (T v) ν) (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < p₁)
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hde : d + e ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak₀ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ p₀ * ν {y | r < T g y} ≤ A₀ * ∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ)
    (hweak₁ : ∀ (g : α → G), AEMeasurable g μ → ∀ r : ℝ≥0∞,
      r ^ p₁ * ν {y | r < T g y} ≤ A₁ * ∫⁻ x, ‖g x‖ₑ ^ p₁ ∂μ) :
    ∫⁻ y, T v y ^ p ∂ν ≤
      (ENNReal.ofReal (p * c ^ (p₀ - p) / (p - p₀)) * (A₀ * ENNReal.ofReal (d ^ (-p₀))) +
        ENNReal.ofReal (p * c ^ (p₁ - p) / (p₁ - p)) * (A₁ * ENNReal.ofReal (e ^ (-p₁)))) *
        ∫⁻ x, ‖v x‖ₑ ^ p ∂μ :=
  lintegral_rpow_le_of_meas_ofReal_lt_le hv.enorm hTv hp₀ hlt₀ hlt₁ hc fun _t ht =>
    meas_ofReal_lt_le_add_setLIntegral hv ht hp₀ (hp₀.trans (hlt₀.trans hlt₁)) hd he hde hadd
      hweak₀ hweak₁

end Operator

end TauCeti
