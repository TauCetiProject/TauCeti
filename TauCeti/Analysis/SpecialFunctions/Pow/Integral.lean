/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
-- `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` is imported privately: it supplies
-- `not_integrableOn_Ioi_rpow`, used only inside the proof of
-- `TauCeti.lintegral_ofReal_rpow_Ioi`.
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- `Mathlib.Analysis.SpecialFunctions.Integrals.Basic` is imported privately: it supplies the
-- interval integral of `t ^ s`, used only inside the proof of
-- `TauCeti.lintegral_ofReal_rpow_Ioo`.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lower integrals of a real power, and the layer cake formula in `ℝ≥0∞`

This file collects the two lower integrals of `t ↦ t ^ s` on a half-line that the real
interpolation method needs, and uses them to transport Mathlib's layer cake formula from
real-valued to `ℝ≥0∞`-valued functions.

For `-1 < s` the function `t ↦ t ^ s` is integrable near `0` and not integrable near `∞`, and the
two computations below are the two halves of that dichotomy:
`TauCeti.lintegral_ofReal_rpow_Ioo` evaluates `∫⁻ t in (0, a), t ^ s` to the expected
antiderivative for such an `s`, while `TauCeti.lintegral_ofReal_rpow_Ioi` records that
`∫⁻ t in (0, ∞), t ^ s` diverges — the latter for *every* exponent `s`, since a power that is
integrable at the origin is not integrable at infinity and conversely.

`TauCeti.lintegral_indicator_ofReal_rpow_Ioi` packages the two together as the single formula the
real interpolation method uses: the integral over `(0, ∞)` of `t ^ s` cut off at the height where
`c * t` reaches a threshold `a : ℝ≥0∞`, which is the finite antiderivative when `a` is finite and
`∞` when it is not.

`TauCeti.lintegral_indicator_le_ofReal_rpow_Ioi` is the companion over the complementary region,
where `c * t` has already passed the threshold. There the roles of the two endpoints are
exchanged: the integral converges at infinity and diverges at the origin, so the exponent range is
`s < -1` and the value is `∞` exactly when the threshold is `0`. The two together are what the
real interpolation method between two finite exponents integrates against, the first for the part
of a function above a height and the second for the part below it.

The layer cake formula `∫⁻ u ^ p = p * ∫⁻ t in (0, ∞), ν {u > t} * t ^ (p - 1)` is in Mathlib as
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`, but only for a nonnegative *real-valued*
`u`. Analysis in `ℝ≥0∞` — where the operators of interpolation theory naturally land, since a
supremum of averages such as the Hardy–Littlewood maximal function is defined without any
finiteness hypothesis — needs the version for `u : β → ℝ≥0∞`, which is
`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul` below. The superlevel sets there are cut
at the `ℝ≥0∞`-valued threshold `ENNReal.ofReal t`, which is what distinguishes the statement from
Mathlib's.

The passage between the two is by `ENNReal.toReal`, which is faithful exactly where `u` is finite.
Where `u = ∞` on a set of positive measure both sides are `∞`: the left because `u ^ p = ∞`
there, and the right because every superlevel set then has measure at least that of `{u = ∞}`,
and `∫⁻ t in (0, ∞), t ^ (p - 1)` diverges. That is where `TauCeti.lintegral_ofReal_rpow_Ioi` is
used, and it is why the statement needs no finiteness hypothesis on `u`.

## Main declarations

* `TauCeti.lintegral_ofReal_rpow_Ioo`: `∫⁻ t in (0, a), t ^ s = a ^ (s + 1) / (s + 1)` for
  `-1 < s` and `0 ≤ a`.
* `TauCeti.lintegral_ofReal_rpow_Ioi`: `∫⁻ t in (0, ∞), t ^ s = ∞`, for every `s`.
* `TauCeti.lintegral_indicator_ofReal_rpow_Ioi`: the same integral truncated at the height where
  `c * t` reaches `a : ℝ≥0∞`, evaluated to `c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.
* `TauCeti.lintegral_indicator_le_ofReal_rpow_Ioi`: the integral over the complementary region,
  where `c * t` is at least `a`, evaluated to `c ^ (-(s + 1)) / (-(s + 1)) * a ^ (s + 1)` for
  `s < -1`.
* `TauCeti.setLIntegral_Ioc_ite_rpow_le`: an upper-tail bound for a negative power restricted by
  a linear threshold.
* `TauCeti.setLIntegral_Ioc_rpow_mul_ite_le`: the same bound with constant and linear weights.
* `TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`: the layer cake formula for an
  `ℝ≥0∞`-valued function.
* `TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`: a function with finite positive
  power integral is carried by a σ-finite part of the measure.

## References

* L. Grafakos, *Classical Fourier Analysis*, Proposition 1.1.4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {s : ℝ}

/-- The lower integral of `t ^ s` over a bounded interval `(0, a)`, for `-1 < s` and `0 ≤ a`: the
power is integrable at the origin and the value is the expected antiderivative.

Nonnegativity of `a` is needed: for `a < 0` the interval is empty while `a ^ (s + 1)`, a real power
at a negative base, need not vanish. -/
theorem lintegral_ofReal_rpow_Ioo (hs : -1 < s) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ t in Ioo (0 : ℝ) a, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (a ^ (s + 1) / (s + 1)) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ s) (Ioo 0 a) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hs
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at h
    exact h.mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le s
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hs), Real.zero_rpow hs1.ne',
    sub_zero]

/-- The lower integral of `t ^ s` over `(0, ∞)` diverges, for every exponent `s`: the power fails
to be integrable at the origin or at infinity, according as `s ≤ -1` or `-1 < s`. -/
theorem lintegral_ofReal_rpow_Ioi (s : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) = ∞ := by
  by_contra hne
  have hmeas : Measurable fun t : ℝ => t ^ s := measurable_id.pow measurable_const
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt ht) s
  exact not_integrableOn_Ioi_rpow s
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hne)⟩

/-- The tail integral `∫_{r / D}^∞ t ^ (-n - 1) dt = D ^ n r ^ (-n) / n` bounds the integral of
`t ^ (-n - 1)` over those `t ∈ (0, 1]` with `r ≤ t * D`. -/
theorem setLIntegral_Ioc_ite_rpow_le {n : ℕ} (hn : 0 < n) {r D : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioc (0 : ℝ) 1, (if r ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) else 0) ≤
      ENNReal.ofReal (D ^ n / n) * ENNReal.ofReal (r ^ (-(n : ℝ))) := by
  rcases le_or_gt D 0 with hD | hD
  · have hzero : ∀ t ∈ Ioc (0 : ℝ) 1,
        (if r ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) else 0) = 0 := fun t ht =>
      ite_eq_right (by nlinarith [ht.1])
    rw [setLIntegral_congr_fun measurableSet_Ioc hzero]
    simp
  have hc : 0 < r / D := div_pos hr hD
  have hn' : -(n : ℝ) - 1 < -1 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∫⁻ t, (Ici (r / D)).indicator (fun t => ENNReal.ofReal (t ^ (-(n : ℝ) - 1))) t := by
      refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun t => ?_)
      split_ifs with h
      · have hmem : t ∈ Ici (r / D) := mem_Ici.2 ((div_le_iff₀ hD).2 h)
        rw [indicator_of_mem hmem]
      · exact bot_le
    _ = ∫⁻ t in Ioi (r / D), ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) := by
      rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici]
    _ = ENNReal.ofReal (∫ t in Ioi (r / D), t ^ (-(n : ℝ) - 1)) := by
      rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hn' hc)]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (hc.trans ht).le _
    _ = ENNReal.ofReal (D ^ n / n) * ENNReal.ofReal (r ^ (-(n : ℝ))) := by
      rw [integral_Ioi_rpow_of_lt hn' hc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hexp : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
      rw [hexp, Real.div_rpow hr.le hD.le, Real.rpow_neg hD.le, Real.rpow_natCast]
      field_simp

/-- The bound of `setLIntegral_Ioc_ite_rpow_le`, multiplied by the length `r` of a segment and by
a weight `a`, gives the kernel `r ^ (1 - n)`. -/
theorem setLIntegral_Ioc_rpow_mul_ite_le {n : ℕ} (hn : 0 < n) (a : ℝ≥0∞) {r : ℝ}
    (hr : 0 ≤ r) (D : ℝ) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
        (a * if r ≤ t * D then ENNReal.ofReal r else 0) ≤
      ENNReal.ofReal (D ^ n / n) * (a * ENNReal.ofReal r ^ (1 - (n : ℝ))) := by
  have hL : ∀ t : ℝ, ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
      (a * if r ≤ t * D then ENNReal.ofReal r else 0) = a * ENNReal.ofReal r *
        if r ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) else 0 := by
    intro t
    split_ifs <;> ring
  simp_rw [hL]
  rw [lintegral_const_mul _ (Measurable.ite (measurableSet_le measurable_const (by fun_prop))
    (by fun_prop) measurable_const)]
  rcases hr.eq_or_lt with rfl | hr
  · simp
  calc
    _ ≤ a * ENNReal.ofReal r *
        (ENNReal.ofReal (D ^ n / n) * ENNReal.ofReal (r ^ (-(n : ℝ)))) := by
      gcongr
      exact setLIntegral_Ioc_ite_rpow_le hn hr
    _ = _ := by
      have hexp : (1 : ℝ) - n = 1 + -(n : ℝ) := by ring
      rw [ENNReal.ofReal_rpow_of_pos hr, hexp, Real.rpow_add hr, Real.rpow_one,
        ENNReal.ofReal_mul hr.le]
      ring

/-- **A finite threshold on `c * t` cuts `(0, ∞)` down to a bounded interval.** For `0 < c` and
`a ≠ ∞`, the indicator of `{t | ENNReal.ofReal (c * t) < a}` agrees at every positive `t` with the
indicator of `(0, a.toReal / c)`, whatever the integrand. -/
private theorem indicator_ofReal_mul_lt_eq_indicator_Ioo {a : ℝ≥0∞} (ha : a ≠ ∞) {c : ℝ}
    (hc : 0 < c) (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator f t =
      (Ioo (0 : ℝ) (a.toReal / c)).indicator f t := by
  have ht' : (0 : ℝ) < t := ht
  have hiff : t ∈ {t : ℝ | ENNReal.ofReal (c * t) < a} ↔ t ∈ Ioo (0 : ℝ) (a.toReal / c) := by
    rw [Set.mem_ofPred, Set.mem_Ioo, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ha,
      lt_div_iff₀ hc, mul_comm c t]
    exact ⟨fun h => ⟨ht', h⟩, fun h => h.2⟩
  by_cases hmem : t ∈ Ioo (0 : ℝ) (a.toReal / c)
  · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem fun h => hmem (hiff.1 h), Set.indicator_of_notMem hmem]

/-- The lower integral of `t ^ s` over `(0, ∞)`, truncated at the height where `c * t` reaches a
threshold `a : ℝ≥0∞`: for `-1 < s` and `0 < c`,

`∫⁻ t in (0, ∞), [c * t < a] * t ^ s = c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.

For a finite `a` the cut-off makes this the integral over `(0, a / c)` evaluated by
`TauCeti.lintegral_ofReal_rpow_Ioo`; for `a = ∞` the cut-off is vacuous and both sides are `∞`, by
`TauCeti.lintegral_ofReal_rpow_Ioi`. This is the inner integral of the real interpolation method,
where `a` is the value of the function being interpolated at a point. -/
theorem lintegral_indicator_ofReal_rpow_Ioi (hs : -1 < s) {c : ℝ} (hc : 0 < c) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator (fun t => ENNReal.ofReal (t ^ s)) t =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * a ^ (s + 1) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have hconst : (0 : ℝ) < c ^ (-(s + 1)) / (s + 1) := by positivity
  rcases eq_or_ne a ∞ with rfl | ha
  · -- The cut-off is vacuous and the integral diverges.
    have hmem : ∀ t : ℝ, t ∈ {t : ℝ | ENNReal.ofReal (c * t) < ∞} := fun t =>
      Set.mem_ofPred.2 ENNReal.ofReal_lt_top
    rw [setLIntegral_congr_fun measurableSet_Ioi
        (fun t _ => Set.indicator_of_mem (hmem t) _),
      lintegral_ofReal_rpow_Ioi, ENNReal.top_rpow_of_pos hs1,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hconst).ne']
  rcases eq_or_ne a 0 with rfl | ha0
  · -- The cut-off is empty and both sides vanish.
    simp [ENNReal.zero_rpow_of_pos hs1]
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun t ht => indicator_ofReal_mul_lt_eq_indicator_Ioo ha hc _ ht)]
  -- abbreviate only now: `set` folds `a.toReal`, which the cut-off lemma above spells out
  set b : ℝ := a.toReal
  have hb0 : 0 < b := ENNReal.toReal_pos ha0 ha
  have hab : a = ENNReal.ofReal b := (ENNReal.ofReal_toReal ha).symm
  -- The elementary real identity behind the constant `c ^ (-(s + 1))`.
  have hreal : (b / c) ^ (s + 1) / (s + 1) = c ^ (-(s + 1)) / (s + 1) * b ^ (s + 1) := by
    have hcp : c ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    rw [Real.div_rpow hb0.le hc.le, Real.rpow_neg hc.le]
    field_simp
  rw [lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left Ioo_subset_Ioi_self,
    lintegral_ofReal_rpow_Ioo hs (by positivity), hab,
    ENNReal.ofReal_rpow_of_nonneg hb0.le hs1.le, ← ENNReal.ofReal_mul hconst.le, hreal]

/-- **A threshold already passed by `c * t` cuts `(0, ∞)` down to a half-line.** For `0 < c` and
`a ≠ ∞`, the indicator of `{t | a ≤ ENNReal.ofReal (c * t)}` agrees at every positive `t` with the
indicator of `[a.toReal / c, ∞)`, whatever the integrand. -/
private theorem indicator_le_ofReal_mul_eq_indicator_Ici {a : ℝ≥0∞} (ha : a ≠ ∞) {c : ℝ}
    (hc : 0 < c) (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    {t : ℝ | a ≤ ENNReal.ofReal (c * t)}.indicator f t =
      (Ici (a.toReal / c)).indicator f t := by
  have ht' : (0 : ℝ) < t := ht
  have hiff : t ∈ {t : ℝ | a ≤ ENNReal.ofReal (c * t)} ↔ t ∈ Ici (a.toReal / c) := by
    rw [Set.mem_ofPred, Set.mem_Ici,
      ENNReal.le_ofReal_iff_toReal_le ha (by positivity), div_le_iff₀ hc, mul_comm c t]
  by_cases hmem : t ∈ Ici (a.toReal / c)
  · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem fun h => hmem (hiff.1 h), Set.indicator_of_notMem hmem]

/-- The lower integral of `t ^ s` over `(0, ∞)`, restricted to the heights at which `c * t` has
already reached a threshold `a : ℝ≥0∞`: for `s < -1` and `0 < c`,

`∫⁻ t in (0, ∞), [a ≤ c * t] * t ^ s = c ^ (-(s + 1)) / (-(s + 1)) * a ^ (s + 1)`.

For a nonzero `a` this is the convergent tail integral over `[a / c, ∞)`; for `a = 0` the
restriction is vacuous and both sides are `∞`, by `TauCeti.lintegral_ofReal_rpow_Ioi`, while for
`a = ∞` the region is empty and both sides vanish. This is the inner integral that the real
interpolation method pairs with the part of a function *below* the height `c * t`, the exponent
range `s < -1` being the one in which the power is integrable at infinity; the complementary
region is `TauCeti.lintegral_indicator_ofReal_rpow_Ioi`. -/
theorem lintegral_indicator_le_ofReal_rpow_Ioi (hs : s < -1) {c : ℝ} (hc : 0 < c) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | a ≤ ENNReal.ofReal (c * t)}.indicator (fun t => ENNReal.ofReal (t ^ s)) t =
      ENNReal.ofReal (c ^ (-(s + 1)) / (-(s + 1))) * a ^ (s + 1) := by
  have hs1 : s + 1 < 0 := by linarith
  have hs1' : (0 : ℝ) < -(s + 1) := by linarith
  have hconst : (0 : ℝ) < c ^ (-(s + 1)) / (-(s + 1)) := by positivity
  rcases eq_or_ne a ∞ with rfl | ha
  · -- No positive `t` reaches the threshold, and `∞ ^ (s + 1) = 0`.
    have hempty : ∀ t : ℝ, t ∉ {t : ℝ | (∞ : ℝ≥0∞) ≤ ENNReal.ofReal (c * t)} := fun t ht =>
      absurd (top_le_iff.1 ht) ENNReal.ofReal_ne_top
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun t _ => Set.indicator_of_notMem (hempty t) _)]
    simp [ENNReal.top_rpow_of_neg hs1]
  rcases eq_or_ne a 0 with rfl | ha0
  · -- Every positive `t` reaches the threshold, and the integral diverges at the origin.
    have hall : ∀ t : ℝ, t ∈ {t : ℝ | (0 : ℝ≥0∞) ≤ ENNReal.ofReal (c * t)} := fun _ =>
      Set.mem_ofPred.2 zero_le
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun t _ => Set.indicator_of_mem (hall t) _),
      lintegral_ofReal_rpow_Ioi, ENNReal.zero_rpow_of_neg hs1,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hconst).ne']
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun t ht => indicator_le_ofReal_mul_eq_indicator_Ici ha hc _ ht)]
  -- abbreviate only now: `set` folds `a.toReal`, which the cut-off lemma above spells out
  set b : ℝ := a.toReal
  have hb0 : 0 < b := ENNReal.toReal_pos ha0 ha
  have hbc : 0 < b / c := by positivity
  have hab : a = ENNReal.ofReal b := (ENNReal.ofReal_toReal ha).symm
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (b / c))] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hbc.trans ht).le s
  -- The elementary real identity behind the constant `c ^ (-(s + 1))`.
  have hreal : -(b / c) ^ (s + 1) / (s + 1) = c ^ (-(s + 1)) / (-(s + 1)) * b ^ (s + 1) := by
    have hcp : c ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    rw [Real.div_rpow hb0.le hc.le, Real.rpow_neg hc.le]
    field_simp
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_self_of_subset_left (Set.Ici_subset_Ioi.2 hbc),
    ← setLIntegral_congr Ioi_ae_eq_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hs hbc) hnn,
    integral_Ioi_rpow_of_lt hs hbc, hreal, hab, ENNReal.ofReal_rpow_of_pos hb0,
    ← ENNReal.ofReal_mul hconst.le]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞} {p : ℝ}

/-- A function with a finite `L^p` norm is carried by a σ-finite part of the measure: the level
sets `{f ≥ 1 / (n + 1)}` have finite measure by Chebyshev's inequality applied to `f ^ p`, and they
exhaust `{f > 0}`. -/
theorem sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top (hf : AEMeasurable f μ)
    (hp : 0 < p) (htop : ∫⁻ x, f x ^ p ∂μ ≠ ∞) : SigmaFinite (μ.restrict {x | 0 < f x}) := by
  let g := hf.mk f
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have htopg : ∫⁻ x, g x ^ p ∂μ ≠ ∞ := by
    have heq : ∫⁻ x, f x ^ p ∂μ = ∫⁻ x, g x ^ p ∂μ :=
      lintegral_congr_ae (hfg.fun_comp fun z => z ^ p)
    rwa [← heq]
  have hsigma : SigmaFinite (μ.restrict {x | 0 < g x}) := by
    have hg : Measurable g := hf.measurable_mk
    have hsmeas : MeasurableSet {x | 0 < g x} := measurableSet_lt measurable_const hg
    have hlevel : ∀ n : ℕ, μ {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x} ≠ ∞ := by
      intro n
      have hne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
      have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
        ENNReal.inv_pos.2 (by simp [ENNReal.natCast_ne_top])
      have hεpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ ^ p := ENNReal.rpow_pos hpos hne
      have hset : {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x} =
          {x | ((n : ℝ≥0∞) + 1)⁻¹ ^ p ≤ g x ^ p} :=
        Set.ext fun x => (ENNReal.rpow_le_rpow_iff hp).symm
      rw [hset]
      refine ne_top_of_le_ne_top (ENNReal.div_lt_top htopg hεpos.ne').ne
        (meas_ge_le_lintegral_div (hg.pow_const p).aemeasurable hεpos.ne'
          (ENNReal.rpow_ne_top_of_nonneg hp.le hne))
    refine ⟨⟨⟨fun n => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x} ∪ {x | 0 < g x}ᶜ,
      fun _ => trivial, ?_, ?_⟩⟩⟩
    · intro n
      have hcompl : μ.restrict {x | 0 < g x} {x | 0 < g x}ᶜ = 0 := by
        rw [Measure.restrict_apply hsmeas.compl, Set.compl_inter_self, measure_empty]
      refine lt_of_le_of_lt (measure_union_le _ _) ?_
      rw [hcompl, add_zero]
      exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (lt_top_iff_ne_top.2 (hlevel n))
    · refine Set.eq_univ_of_forall fun x => ?_
      rcases eq_or_ne (g x) 0 with hx | hx
      · exact Set.mem_iUnion.2 ⟨0, Set.mem_union_right _ (by simp [hx])⟩
      · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
        exact Set.mem_iUnion.2
          ⟨n, Set.mem_union_left _ ((ENNReal.inv_le_inv' le_self_add).trans hn.le)⟩
  have hpos : {x | 0 < f x} =ᵐ[μ] {x | 0 < g x} :=
    hfg.mono fun _ hx => by simp only [Set.mem_ofPred_eq]; rw [hx]
  rw [Measure.restrict_congr_set hpos]
  exact hsigma

variable {β : Type*} [MeasurableSpace β]

/-- **The layer cake formula** for an `ℝ≥0∞`-valued function: for `0 < p`,

`∫⁻ u ^ p ∂ν = p * ∫⁻ t in (0, ∞), ν {u > t} * t ^ (p - 1)`,

where the superlevel set is cut at the threshold `ENNReal.ofReal t`.

This is `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` for a function that is allowed to
take the value `∞`; no finiteness hypothesis is needed, because both sides are `∞` as soon as
`{u = ∞}` has positive measure. -/
theorem lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul (ν : Measure β) {u : β → ℝ≥0∞}
    (hu : AEMeasurable u ν) {p : ℝ} (hp : 0 < p) :
    ∫⁻ y, u y ^ p ∂ν = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1)) := by
  rcases eq_or_ne (ν {y | u y = ∞}) 0 with hnull | hnull
  · -- `u` is finite almost everywhere, so `ENNReal.toReal` transports Mathlib's formula.
    have hfin : ∀ᵐ y ∂ν, u y ≠ ∞ := by rw [ae_iff]; simpa using hnull
    have hg : AEMeasurable (fun y => (u y).toReal) ν := hu.ennreal_toReal
    have hnn : 0 ≤ᵐ[ν] fun y => (u y).toReal := .of_forall fun _ => ENNReal.toReal_nonneg
    have hL : ∫⁻ y, u y ^ p ∂ν = ∫⁻ y, ENNReal.ofReal ((u y).toReal ^ p) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfin] with y hy
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, ENNReal.ofReal_toReal hy]
    rw [hL, lintegral_rpow_eq_lintegral_meas_lt_mul ν hnn hg hp]
    refine congrArg _ (setLIntegral_congr_fun measurableSet_Ioi fun t ht => congrArg₂ _ ?_ rfl)
    refine measure_congr ?_
    filter_upwards [hfin] with y hy
    exact propext (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) hy).symm
  · -- `u = ∞` on a set of positive measure: both sides are `∞`.
    have hL : ∫⁻ y, u y ^ p ∂ν = ∞ := by
      have hlevel : {y | u y ^ p = ∞} = {y | u y = ∞} :=
        Set.ext fun y => ENNReal.rpow_eq_top_iff_of_pos hp
      refine lintegral_eq_top_of_measure_eq_top_ne_zero (hu.pow_const p) ?_
      rwa [hlevel]
    have hR : ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} *
        ENNReal.ofReal (t ^ (p - 1)) = ∞ := by
      have hsub : ∀ {t : ℝ}, {y | u y = ∞} ⊆ {y | ENNReal.ofReal t < u y} := by
        intro t y (hy : u y = ∞)
        rw [Set.mem_ofPred_eq, hy]
        exact ENNReal.ofReal_lt_top
      refine top_le_iff.1 ?_
      calc (∞ : ℝ≥0∞)
          = ν {y | u y = ∞} * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) := by
            rw [lintegral_ofReal_rpow_Ioi (p - 1), ENNReal.mul_top hnull]
        _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | u y = ∞} * ENNReal.ofReal (t ^ (p - 1)) :=
            (lintegral_const_mul _ ((measurable_id.pow measurable_const).ennreal_ofReal)).symm
        _ ≤ _ := lintegral_mono fun t => mul_le_mul_left (measure_mono hsub) _
    rw [hL, hR, ENNReal.mul_top (ENNReal.ofReal_pos.2 hp).ne']

end TauCeti
