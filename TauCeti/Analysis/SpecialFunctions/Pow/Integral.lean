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
-- `TauCeti.MeasureTheory.Integral.Average` is imported privately: it supplies
-- `setLIntegral_comp_preimage_of_map_eq_smul`, used only inside the proof of
-- `TauCeti.setLIntegral_comp_mul_left_mul_rpow`.
import TauCeti.MeasureTheory.Integral.Average

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
* `TauCeti.lintegral_ofReal_pow_Ioo`: `∫⁻ t in (0, a), t ^ k = a ^ (k + 1) / (k + 1)` for a natural
  number `k` and `0 ≤ a`.
* `TauCeti.lintegral_ofReal_rpow_Ioi`: `∫⁻ t in (0, ∞), t ^ s = ∞`, for every `s`.
* `TauCeti.lintegral_ofReal_rpow_Ioi_of_lt`: `∫⁻ t in (c, ∞), t ^ s = -c ^ (s + 1) / (s + 1)` for
  `s < -1` and `0 < c`.
* `TauCeti.lintegral_indicator_ofReal_rpow_Ioi`: the same integral truncated at the height where
  `c * t` reaches `a : ℝ≥0∞`, evaluated to `c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.
* `TauCeti.lintegral_indicator_le_ofReal_rpow_Ioi`: the integral over the complementary region,
  where `c * t` is at least `a`, evaluated to `c ^ (-(s + 1)) / (-(s + 1)) * a ^ (s + 1)` for
  `s < -1`.
* `TauCeti.setLIntegral_Ioi_rpow_mul_ite_le`: an upper bound for the kernel `t ^ (-s - 1)`
  restricted by a linear threshold, with constant and linear weights.

* `TauCeti.setLIntegral_Ioc_ite_rpow_le`: an upper-tail bound for a negative power restricted by
  a linear threshold.
* `TauCeti.setLIntegral_Ioc_rpow_mul_ite_le`: the same bound with constant and linear weights.
* `TauCeti.setLIntegral_comp_mul_left_mul_rpow`: the substitution `t = c s` in a lower integral
  against the weight `t ^ q`.
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

/-- The lower integral of `t ^ k` over `(0, a)` for a natural exponent `k` is
`a ^ (k + 1) / (k + 1)`: the natural-exponent case of `TauCeti.lintegral_ofReal_rpow_Ioo`. -/
theorem lintegral_ofReal_pow_Ioo (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ t in Ioo (0 : ℝ) a, ENNReal.ofReal (t ^ k) =
      ENNReal.ofReal (a ^ (k + 1) / (k + 1)) := by
  have h := lintegral_ofReal_rpow_Ioo (s := k) (by linarith [k.cast_nonneg (α := ℝ)]) ha
  have ha' : a ^ ((k : ℝ) + 1) = a ^ (k + 1) := by exact_mod_cast Real.rpow_natCast a (k + 1)
  simp_rw [Real.rpow_natCast] at h
  rw [h, ha']

/-- The lower integral of `t ^ s` over `(0, ∞)` diverges, for every exponent `s`: the power fails
to be integrable at the origin or at infinity, according as `s ≤ -1` or `-1 < s`. -/
theorem lintegral_ofReal_rpow_Ioi (s : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) = ∞ := by
  by_contra hne
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg ht.le s
  exact not_integrableOn_Ioi_rpow s
    ((lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hnn).1 hne)

/-- The lower integral of `t ^ s` over a half-line `(c, ∞)`, for `s < -1` and `0 < c`: the power
is integrable at infinity and the value is `-c ^ (s + 1) / (s + 1)`, as for the Bochner integral
`integral_Ioi_rpow_of_lt`. -/
theorem lintegral_ofReal_rpow_Ioi_of_lt (hs : s < -1) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (-c ^ (s + 1) / (s + 1)) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.trans ht).le s
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hs hc) hnn,
    integral_Ioi_rpow_of_lt hs hc]

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
  simp only [Set.indicator_apply, hiff]

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
  simp only [Set.indicator_apply, hiff]

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
  -- The elementary real identity behind the constant `c ^ (-(s + 1))`.
  have hreal : -(b / c) ^ (s + 1) / (s + 1) = c ^ (-(s + 1)) / (-(s + 1)) * b ^ (s + 1) := by
    have hcp : c ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    rw [Real.div_rpow hb0.le hc.le, Real.rpow_neg hc.le]
    field_simp
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_self_of_subset_left (Set.Ici_subset_Ioi.2 hbc),
    ← setLIntegral_congr Ioi_ae_eq_Ici, lintegral_ofReal_rpow_Ioi_of_lt hs hbc, hreal, hab,
    ENNReal.ofReal_rpow_of_pos hb0, ← ENNReal.ofReal_mul hconst.le]

/-- The kernel `t ^ (-s - 1)`, integrated against the weight `a * r` over those `t ∈ (0, ∞)` with
`r ≤ t * D`, is at most `D ^ s / s * a * r ^ (1 - s)`, for `0 < s` and `0 ≤ r`. For `0 < D` and
`0 < r` the region is the half-line `[r / D, ∞)` and the bound is attained, the tail integral
`∫_{r / D}^∞ t ^ (-s - 1) dt` being `D ^ s r ^ (-s) / s`; for `D ≤ 0` and `0 < r` the region is
empty. For `r = 0` the weight `a * r` vanishes, so the integral is `0`. -/
theorem setLIntegral_Ioi_rpow_mul_ite_le (hs : 0 < s) (a : ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) (D : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-s - 1)) *
        (a * if r ≤ t * D then ENNReal.ofReal r else 0) ≤
      ENNReal.ofReal (D ^ s / s) * (a * ENNReal.ofReal r ^ (1 - s)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rcases le_or_gt D 0 with hD | hD
  · -- No positive `t` reaches the threshold.
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun t (ht : 0 < t) => by
      simp [show ¬r ≤ t * D by nlinarith]]
    simp
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-s - 1)) *
      (a * if r ≤ t * D then ENNReal.ofReal r else 0) = a * ENNReal.ofReal r *
        {t : ℝ | ENNReal.ofReal r ≤ ENNReal.ofReal (D * t)}.indicator
          (fun t => ENNReal.ofReal (t ^ (-s - 1))) t := fun t _ => by
    simp only [indicator_apply, mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff', hr.not_ge, or_false,
      mul_comm D t]
    split_ifs <;> ring
  have hmeas : Measurable ({t : ℝ | ENNReal.ofReal r ≤ ENNReal.ofReal (D * t)}.indicator
      fun t => ENNReal.ofReal (t ^ (-s - 1))) :=
    (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-s - 1))).indicator
      (measurableSet_le measurable_const (by fun_prop))
  -- Evaluate the integral with the tail-integral formula.
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _ hmeas,
    lintegral_indicator_le_ofReal_rpow_Ioi (by linarith) hD]
  -- What remains is algebra; splitting `r ^ (1 - s)` needs `r ≠ 0, ∞` in `ℝ≥0∞`.
  have hsplit : ENNReal.ofReal r ^ (1 - s) = ENNReal.ofReal r * ENNReal.ofReal r ^ (-s) := by
    rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top,
      ENNReal.rpow_one]
  simp only [sub_add_cancel, neg_neg, hsplit]
  exact le_of_eq (by ring)

/-- Substituting `t = c s`, for `c > 0`, in a lower integral against the weight `t ^ q` over a set
of nonnegative reals: the weight is homogeneous of degree `q`, so the substitution costs the factor
`c ^ (-(q + 1))`. Here `T` is the preimage of `S` under `s ↦ c s`. -/
theorem setLIntegral_comp_mul_left_mul_rpow (g : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    {S T : Set ℝ} (hT : MeasurableSet T) (hST : ∀ s, s ∈ T ↔ c * s ∈ S) (hT0 : T ⊆ Ici 0)
    (q : ℝ) :
    ∫⁻ s in T, g (c * s) * ENNReal.ofReal (s ^ q) =
      ENNReal.ofReal (c ^ (-(q + 1))) * ∫⁻ t in S, g t * ENNReal.ofReal (t ^ q) := by
  set e := (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv
  set G : ℝ → ℝ≥0∞ := fun t => g t * ENNReal.ofReal (t ^ q)
  have he : volume.map e = ENNReal.ofReal |c⁻¹| • volume := Real.map_volume_mul_left hc.ne'
  have h : ∫⁻ s in e ⁻¹' S, G (e s) = ENNReal.ofReal |c⁻¹| * ∫⁻ t in S, G t :=
    setLIntegral_comp_preimage_of_map_eq_smul he G S
  have hT' : e ⁻¹' S = T := by
    ext s
    exact (hST s).symm
  rw [hT'] at h
  simp only [e, G, Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft₀, abs_inv,
    abs_of_pos hc] at h
  have hcongr : ∫⁻ s in T, g (c * s) * ENNReal.ofReal ((c * s) ^ q) =
      ∫⁻ s in T, ENNReal.ofReal (c ^ q) * (g (c * s) * ENNReal.ofReal (s ^ q)) :=
    setLIntegral_congr_fun hT fun s hs => by
      rw [Real.mul_rpow hc.le (hT0 hs), ENNReal.ofReal_mul (Real.rpow_nonneg hc.le q)]
      ring
  rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  have hinv : ENNReal.ofReal (c ^ (-q)) * ENNReal.ofReal (c ^ q) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hc]
    simp
  calc ∫⁻ s in T, g (c * s) * ENNReal.ofReal (s ^ q)
      = ENNReal.ofReal (c ^ (-q)) *
          (ENNReal.ofReal (c ^ q) * ∫⁻ s in T, g (c * s) * ENNReal.ofReal (s ^ q)) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = ENNReal.ofReal (c ^ (-q)) * ENNReal.ofReal c⁻¹ *
          ∫⁻ t in S, g t * ENNReal.ofReal (t ^ q) := by
        rw [h, mul_assoc]
    _ = ENNReal.ofReal (c ^ (-(q + 1))) * ∫⁻ t in S, g t * ENNReal.ofReal (t ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_neg_one, ← Real.rpow_add hc,
          neg_add]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞} {p : ℝ}

/-- A function with a finite `L^p` norm is carried by a σ-finite part of the measure: the level
sets `{f ≥ 1 / (n + 1)}` have finite measure by Chebyshev's inequality applied to `f ^ p`, and they
exhaust `{f > 0}`. -/
theorem sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top (hf : AEMeasurable f μ)
    (hp : 0 < p) (htop : ∫⁻ x, f x ^ p ∂μ ≠ ∞) : SigmaFinite (μ.restrict {x | 0 < f x}) := by
  have hlevel : ∀ n : ℕ, μ {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ f x} < ∞ := by
    intro n
    have hne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    have hε : ((n : ℝ≥0∞) + 1)⁻¹ ^ p ≠ 0 := (ENNReal.rpow_pos (by simp) hne).ne'
    have hset : {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ f x} = {x | ((n : ℝ≥0∞) + 1)⁻¹ ^ p ≤ f x ^ p} :=
      Set.ext fun x => (ENNReal.rpow_le_rpow_iff hp).symm
    rw [hset]
    exact (meas_ge_le_lintegral_div (hf.pow_const p) hε
      (ENNReal.rpow_ne_top_of_nonneg hp.le hne)).trans_lt (ENNReal.div_lt_top htop hε)
  have hs : NullMeasurableSet {x | 0 < f x} μ := nullMeasurableSet_lt aemeasurable_const hf
  refine ⟨⟨⟨fun n => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ f x} ∪ {x | 0 < f x}ᶜ,
    fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [Measure.restrict_apply₀' hs]
    refine (measure_mono ?_).trans_lt (hlevel n)
    rintro x ⟨hx | hx, hx'⟩
    exacts [hx, absurd hx' hx]
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne (f x) 0 with hx | hx
    · exact Set.mem_iUnion.2 ⟨0, Set.mem_union_right _ (by simp [hx])⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx
      exact Set.mem_iUnion.2
        ⟨n, Set.mem_union_left _ ((ENNReal.inv_le_inv' le_self_add).trans hn.le)⟩

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
            (lintegral_const_mul _ (by fun_prop)).symm
        _ ≤ _ := lintegral_mono fun t => mul_le_mul_left (measure_mono hsub) _
    rw [hL, hR, ENNReal.mul_top (ENNReal.ofReal_pos.2 hp).ne']

end TauCeti
