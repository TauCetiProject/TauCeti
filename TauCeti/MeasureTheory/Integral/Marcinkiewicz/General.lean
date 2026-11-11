/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
public import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.Basic
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.OffDiagonal
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.Superlevel
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
along the line `1 / q = (1 - θ) / q₀ + θ / q₁`, is
`TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow` in
`TauCeti.MeasureTheory.Integral.Marcinkiewicz.OffDiagonal`.

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

Both statements are the diagonal case `qᵢ = pᵢ`, `γ = 1` of their off-diagonal counterparts in
`TauCeti.MeasureTheory.Integral.Marcinkiewicz.OffDiagonal`: the distributional estimate is
`TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le_rpow` and the truncation argument is
`TauCeti.meas_ofReal_lt_le_add_setLIntegral_rpow` at the level `c * t`. With these exponents the
outer powers `qᵢ / pᵢ` are `1`, the height `c * t ^ γ` is `c * t`, and the constants
`q c ^ (qᵢ (pᵢ - p) / pᵢ) / |q - qᵢ|` become `p c ^ (pᵢ - p) / |p - pᵢ|`.

The layer cake formula, Minkowski's integral inequality and the elementary integrals in the height
variable `t` all enter through the off-diagonal estimate. For a fixed `x`, the integral in `t` over
the region where `c * t` stays below `‖f x‖` converges because `p₀ < p`, and the integral over its
complement converges because `p < p₁`. The two weighted truncated double integrals of the diagonal
case are also available on their own: `TauCeti.lintegral_mul_setLIntegral_lt` evaluates the upper
one and `TauCeti.lintegral_mul_setLIntegral_le_le` bounds the lower one.

## Bounded linear operators

The operator-level theorem above asks for `T` on all measurable functions. A bounded linear
operator `T` on `L^{p₁}` is defined only there, but splitting `f ∈ L^{p₁}` at a height keeps both
pieces in `L^{p₁}`, and the `L^{p₁}` bound implies weak type `(p₁, p₁)` by Chebyshev's inequality.
So if `T` is of weak type `(p₀, p₀)` on `L^{p₁}`, then `‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L^{p₁}`
and every `p₀ < p < p₁` (`ContinuousLinearMap.eLpNorm_le_of_rpow_mul_meas_lt_le`). This is the
form in which the weak type `(1, 1)` bound for a singular integral operator on `L²` becomes an
`Lᵖ` bound for `1 < p < 2`.

## Main declarations

* `TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le`: the interpolation estimate.
* `TauCeti.meas_ofReal_lt_le_add_setLIntegral`: the reusable truncation argument from
  subadditivity and the two weak-type endpoint bounds.
* `TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le`: operator-level Marcinkiewicz interpolation
  between two finite exponents.
* `ContinuousLinearMap.eLpNorm_le_of_rpow_mul_meas_lt_le`: a bounded linear operator on `L^{p₁}`
  of weak type `(p₀, p₀)` is of strong type `(p, p)` for `p₀ < p < p₁`.

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
    (hs : s < -1) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ q ∂μ ≤
      ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) * ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  have hs1 : s + 1 < 0 := by linarith
  have hR : MeasurableSet {z : ℝ × α | f z.2 ≤ ENNReal.ofReal (c * z.1)} :=
    measurableSet_le (hf.comp measurable_snd) ((measurable_fst.const_mul c).ennreal_ofReal)
  rw [lintegral_mul_setLIntegral_eq (κ := volume.restrict (Ioi (0 : ℝ)))
      (w := fun t : ℝ => ENNReal.ofReal (t ^ s))
      (R := fun t x => f x ≤ ENNReal.ofReal (c * t)) hR (hf.pow_const q).aemeasurable
      ((measurable_id.pow measurable_const).ennreal_ofReal.aemeasurable),
    ← lintegral_const_mul _ (hf.pow_const _)]
  refine lintegral_mono fun x => ?_
  rw [lintegral_indicator_le_ofReal_rpow_Ioi hs hc (f x), mul_assoc]
  exact mul_le_mul_right ((ENNReal.le_rpow_add (f x) (s + 1) q).trans_eq (by rw [add_comm])) _

/-- **The weighted mass of the part of `f` below the height `c * t`.** For `s < -1` the weight
`t ^ s` is integrable at infinity, and the double integral of the lower truncations of `f ^ q`
against it is at most a multiple of `∫⁻ f ^ (q + (s + 1))`.

The bound is not an equality: where `f` is infinite the left-hand side sees nothing, because no
finite height `c * t` reaches it, while the right-hand side is infinite as soon as
`0 < q + (s + 1)`. -/
theorem lintegral_mul_setLIntegral_le_le [SFinite μ] (hf : AEMeasurable f μ) (hs : s < -1)
    (hc : 0 < c) :
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
      lintegral_mul_setLIntegral_le_le_of_measurable hf.measurable_mk hs hc
    _ = ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) *
        ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
      exact congrArg (ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) * ·)
        (lintegral_congr_ae (hfg.fun_comp fun z => z ^ (q + (s + 1)))).symm

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
  have hp₁ : 0 < p₁ := hp₀.trans (hlt₀.trans hlt₁)
  have key := lintegral_rpow_le_of_meas_ofReal_lt_le_rpow (q₀ := p₀) (q₁ := p₁) (γ := 1) hf hu
    hp₀ hlt₀ hlt₁ le_rfl le_rfl (by rw [div_one, mul_div_cancel_left₀ _ hp₀.ne'])
    (by rw [div_one, mul_div_cancel_left₀ _ hp₁.ne']) hc fun t ht => by
      simpa only [Real.rpow_one, div_self hp₀.ne', div_self hp₁.ne', ENNReal.rpow_one] using h t ht
  rw [mul_div_cancel_left₀ _ hp₀.ne', mul_div_cancel_left₀ _ hp₁.ne', abs_of_pos (sub_pos.2 hlt₀),
    abs_of_neg (sub_neg.2 hlt₁), neg_sub, div_self hp₀.ne', div_self hp₁.ne', ENNReal.rpow_one,
    ← add_mul] at key
  exact key

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
  simpa only [div_self hp₀.ne', div_self hp₁.ne', ENNReal.rpow_one] using
    meas_ofReal_lt_le_add_setLIntegral_rpow (q₀ := p₀) (q₁ := p₁) hv ht hp₀ hp₁ hd he hde
      (ENNReal.ofReal (c * t)) hadd
      (fun g hg r => by simpa only [div_self hp₀.ne', ENNReal.rpow_one] using hweak₀ g hg r)
      (fun g hg r => by simpa only [div_self hp₁.ne', ENNReal.rpow_one] using hweak₁ g hg r)

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

namespace ContinuousLinearMap

open MeasureTheory Set TauCeti
open scoped ENNReal

section Interpolation

variable {α β 𝕜 E F : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p₀ p p₁ : ℝ≥0∞} [Fact (1 ≤ p₁)]

/-- The distributional estimate behind the interpolation theorem. Split `f` at the height `s`
into the part where `‖f‖ > s` and the part where `‖f‖ ≤ s`. Where `‖T f‖ > s`, the image of one of
the two parts exceeds `s / 2`: the weak-type bound controls the first, Chebyshev's inequality and
the `L^{p₁}` bound the second. -/
private theorem meas_lt_enorm_le_add_setLIntegral (T : Lp E p₁ μ →L[𝕜] Lp F p₁ ν)
    (hp₀ : 0 < p₀) (hp₀' : p₀ ≠ ∞) (hp₁ : p₁ ≠ ∞) {A : ℝ≥0∞}
    (hweak : ∀ (g : Lp E p₁ μ) (s : ℝ≥0∞),
      s ^ p₀.toReal * ν {y | s < ‖T g y‖ₑ} ≤ A * ∫⁻ x, ‖g x‖ₑ ^ p₀.toReal ∂μ)
    (f : Lp E p₁ μ) {s : ℝ≥0∞} (hs : s ≠ 0) (hs' : s ≠ ∞) :
    ν {y | s < ‖T f y‖ₑ} ≤
      2 ^ p₀.toReal * A * (s ^ p₀.toReal)⁻¹ *
          ∫⁻ x in {x | s < ‖f x‖ₑ}, ‖f x‖ₑ ^ p₀.toReal ∂μ +
        2 ^ p₁.toReal * ‖T‖ₑ ^ p₁.toReal * (s ^ p₁.toReal)⁻¹ *
          ∫⁻ x in {x | ‖f x‖ₑ ≤ s}, ‖f x‖ₑ ^ p₁.toReal ∂μ := by
  have hq₀ : 0 < p₀.toReal := ENNReal.toReal_pos hp₀.ne' hp₀'
  have hp₁0 : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  have hq₁ : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁
  set S := {x | s < ‖f x‖ₑ}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (Lp.stronglyMeasurable f).enorm
  have hm₁ := (Lp.memLp f).indicator hS.nullMeasurableSet
  have hm₂ := (Lp.memLp f).indicator hS.compl.nullMeasurableSet
  set f₁ := hm₁.toLp (S.indicator f)
  set f₂ := hm₂.toLp (Sᶜ.indicator f)
  have hTf : T f = T f₁ + T f₂ := by
    rw [← map_add]
    congr 1
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add f₁ f₂, hm₁.coeFn_toLp, hm₂.coeFn_toLp] with x hx h₁ h₂
    rw [hx, Pi.add_apply, h₁, h₂, indicator_self_add_compl_apply]
  -- The part of `f` above the height `s`, through the weak-type bound.
  have h₁ : ν {y | s / 2 < ‖T f₁ y‖ₑ} ≤
      2 ^ p₀.toReal * (s ^ p₀.toReal)⁻¹ * (A * ∫⁻ x in S, ‖f x‖ₑ ^ p₀.toReal ∂μ) := by
    refine ENNReal.le_two_rpow_mul_inv_rpow_mul hs hs' ?_
    rw [← lintegral_enorm_rpow_eq_setLIntegral hS hm₁.coeFn_toLp hq₀]
    exact hweak f₁ (s / 2)
  -- The part of `f` below the height `s`, through Chebyshev's inequality and the `L^{p₁}` bound.
  have h₂ : ν {y | s / 2 ≤ ‖T f₂ y‖ₑ} ≤
      2 ^ p₁.toReal * (s ^ p₁.toReal)⁻¹ *
        (‖T‖ₑ ^ p₁.toReal * ∫⁻ x in Sᶜ, ‖f x‖ₑ ^ p₁.toReal ∂μ) := by
    refine ENNReal.le_two_rpow_mul_inv_rpow_mul hs hs'
      ((mul_meas_ge_le_pow_eLpNorm' (μ := ν) hp₁0 hp₁ _).trans ?_)
    rw [← Lp.enorm_def, ← lintegral_enorm_rpow_eq_setLIntegral hS.compl hm₂.coeFn_toLp hq₁,
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hq₁, ← eLpNorm_eq_eLpNorm' hp₁0 hp₁
        (Lp.aestronglyMeasurable _), ← Lp.enorm_def, ← ENNReal.mul_rpow_of_nonneg _ _ hq₁.le]
    exact ENNReal.rpow_le_rpow (T.le_opENorm _) hq₁.le
  have hSc : Sᶜ = {x | ‖f x‖ₑ ≤ s} := by
    ext x
    simp [S]
  -- Where `‖T f‖ > s`, one of the two images exceeds `s / 2`.
  have hsub : {y | s < ‖T f y‖ₑ} ≤ᵐ[ν]
      {y | s / 2 < ‖T f₁ y‖ₑ} ∪ {y | s / 2 ≤ ‖T f₂ y‖ₑ} := by
    filter_upwards [Lp.coeFn_add (T f₁) (T f₂)] with y hy hlt
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_le] at hnot hlt
    refine (hlt.trans_le ?_).false
    rw [hTf, hy, Pi.add_apply, ← ENNReal.add_halves s]
    exact (enorm_add_le _ _).trans (add_le_add hnot.1 hnot.2.le)
  calc ν {y | s < ‖T f y‖ₑ}
      ≤ ν {y | s / 2 < ‖T f₁ y‖ₑ} + ν {y | s / 2 ≤ ‖T f₂ y‖ₑ} :=
        (measure_mono_ae hsub).trans (measure_union_le _ _)
    _ ≤ _ := by
        refine (add_le_add h₁ h₂).trans_eq ?_
        rw [← hSc]
        ring

/-- **Marcinkiewicz interpolation for a bounded linear operator on `L^{p₁}`.** Let `T` be a
bounded linear operator on `L^{p₁}`, `1 ≤ p₁ < ∞`, that is also of weak type `(p₀, p₀)` with
constant `A` on `L^{p₁}`, `0 < p₀ < p₁`: for every `g ∈ L^{p₁}` and every height `s`,

`s ^ p₀ · ν {‖T g‖ > s} ≤ A ∫ ‖g‖ ^ p₀`.

Then for every `p₀ < p < p₁` and every `f ∈ L^{p₁}`,

`‖T f‖_p ≤ (p / (p - p₀) · 2 ^ p₀ A + p / (p₁ - p) · 2 ^ p₁ ‖T‖ ^ p₁) ^ (1 / p) ‖f‖_p`.

The bound is vacuous unless `f` also lies in `L^p`. -/
theorem eLpNorm_le_of_rpow_mul_meas_lt_le (T : Lp E p₁ μ →L[𝕜] Lp F p₁ ν) (hp₀ : 0 < p₀)
    (hlt₀ : p₀ < p) (hlt₁ : p < p₁) (hp₁ : p₁ ≠ ∞) {A : ℝ≥0∞}
    (hweak : ∀ (g : Lp E p₁ μ) (s : ℝ≥0∞),
      s ^ p₀.toReal * ν {y | s < ‖T g y‖ₑ} ≤ A * ∫⁻ x, ‖g x‖ₑ ^ p₀.toReal ∂μ)
    (f : Lp E p₁ μ) :
    eLpNorm (T f) p ν ≤
      (ENNReal.ofReal (p.toReal / (p.toReal - p₀.toReal)) * (2 ^ p₀.toReal * A) +
        ENNReal.ofReal (p.toReal / (p₁.toReal - p.toReal)) *
          (2 ^ p₁.toReal * ‖T‖ₑ ^ p₁.toReal)) ^ (1 / p.toReal) * eLpNorm f p μ := by
  have hp_top : p ≠ ∞ := (hlt₁.trans_le le_top).ne
  have hp₀' : p₀ ≠ ∞ := (hlt₀.trans_le le_top).ne
  have hp0 : p ≠ 0 := (hp₀.trans hlt₀).ne'
  have hlt₀' : p₀.toReal < p.toReal := ENNReal.toReal_strict_mono hp_top hlt₀
  have hlt₁' : p.toReal < p₁.toReal := ENNReal.toReal_strict_mono hp₁ hlt₁
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have key := lintegral_rpow_le_of_meas_ofReal_lt_le (Lp.aestronglyMeasurable f).enorm
    (Lp.aestronglyMeasurable (T f)).enorm (ENNReal.toReal_pos hp₀.ne' hp₀') hlt₀' hlt₁' one_pos
    (A₀ := 2 ^ p₀.toReal * A) (A₁ := 2 ^ p₁.toReal * ‖T‖ₑ ^ p₁.toReal) fun t ht => by
      have hinv (q : ℝ) : ENNReal.ofReal (t ^ (-q)) = (ENNReal.ofReal t ^ q)⁻¹ := by
        rw [← ENNReal.ofReal_rpow_of_pos ht, ENNReal.rpow_neg]
      simp only [one_mul, hinv]
      refine (meas_lt_enorm_le_add_setLIntegral T hp₀ hp₀' hp₁ hweak f
        (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top).trans_eq ?_
      ring
  simp only [Real.one_rpow, mul_one] at key
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top (Lp.aestronglyMeasurable _),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top (Lp.aestronglyMeasurable _),
    ← ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hq.le)]
  exact ENNReal.rpow_le_rpow key (one_div_nonneg.2 hq.le)

end Interpolation

end ContinuousLinearMap
