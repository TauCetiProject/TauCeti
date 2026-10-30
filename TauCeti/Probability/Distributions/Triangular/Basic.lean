/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The triangular distribution

For endpoints `a < b` and a mode `c` with `a ≤ c ≤ b`, the triangular law has the tent-shaped
density which rises linearly from `0` at `a` towards the value `2 / (b - a)` at `c` and falls
linearly back to `0` at `b`:

* `2 * (x - a) / ((b - a) * (c - a))` on `(a, c)`;
* `2 * (b - x) / ((b - a) * (b - c))` on `[c, b) ∩ (a, b)`;
* `0` off the open interval `(a, b)`, including at both endpoints.

When `a < c < b` the peak `2 / (b - a)` is attained at the mode. When the mode sits at an endpoint
(`c = a` or `c = b`) only the nonempty branch is present, so the density is a single linear ramp on
the open interval `(a, b)`; it vanishes at the endpoints themselves, and `2 / (b - a)` is then only
its supremum, approached but not attained.

This file defines the law by its density, which vanishes at invalid parameters, and proves its
density API, normalization, support, and parameter measurability. The cumulative distribution
function is the piecewise quadratic `(x - a) ^ 2 / ((b - a) * (c - a))` on `[a, c]` and
`1 - (b - x) ^ 2 / ((b - a) * (b - c))` on `[c, b]`; it is obtained from the fundamental theorem of
calculus, using that the density is the right derivative of this quadratic spline inside `(a, b)`.
The same computation at `x = b` gives the normalization.

## Main definitions

* `TauCeti.Probability.triangularMeasure` — the triangular law;
* `TauCeti.Probability.triangularPDFReal` and `TauCeti.Probability.triangularPDF` — its
  densities.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_triangularMeasure_iff` — the law is a probability
  measure exactly when `a < b` and `a ≤ c ≤ b`;
* `TauCeti.Probability.support_triangularMeasure` — the topological support is `[a, b]`;
* `TauCeti.Probability.integrable_triangularMeasure_iff` and
  `TauCeti.Probability.integral_triangularMeasure_eq` — integrability and integration against the
  law, transferred to the real density;
* `TauCeti.Probability.cdf_triangularMeasure_eq` — the piecewise-quadratic cdf;
* `TauCeti.Probability.measurable_triangularMeasure` — joint measurability in the parameters.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 26, Section 9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace TauCeti.Probability

variable {a b c x : ℝ}

/-! ### Density -/

/-- The real-valued triangular density with endpoints `a`, `b` and mode `c`: it is
`2 * (x - a) / ((b - a) * (c - a))` on `(a, c)`, `2 * (b - x) / ((b - a) * (b - c))` on
`[c, b) ∩ (a, b)`, and zero off `(a, b)` (in particular at both endpoints, even when the mode is an
endpoint). It vanishes identically unless `a ≤ c ≤ b`. -/
def triangularPDFReal (a b c x : ℝ) : ℝ :=
  if a ≤ c ∧ c ≤ b ∧ x ∈ Ioo a b then
    if x < c then 2 * (x - a) / ((b - a) * (c - a)) else 2 * (b - x) / ((b - a) * (b - c))
  else 0

/-- The defining piecewise formula of the real triangular density, including its zero value
outside the support or at invalid parameters. -/
theorem triangularPDFReal_def (a b c x : ℝ) :
    triangularPDFReal a b c x = if a ≤ c ∧ c ≤ b ∧ x ∈ Ioo a b then
      if x < c then 2 * (x - a) / ((b - a) * (c - a)) else 2 * (b - x) / ((b - a) * (b - c))
    else 0 := (rfl)

/-- The extended-nonnegative-valued triangular density. -/
def triangularPDF (a b c x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (triangularPDFReal a b c x)

/-- The triangular density is the nonnegative coercion of its real-valued version. -/
theorem triangularPDF_eq_ofReal (a b c x : ℝ) :
    triangularPDF a b c x = ENNReal.ofReal (triangularPDFReal a b c x) := (rfl)

/-- On the rising branch `(a, c)`, the real triangular density is
`2 * (x - a) / ((b - a) * (c - a))`. -/
theorem triangularPDFReal_of_mem_Ioo_left (hcb : c ≤ b) (hx : x ∈ Ioo a c) :
    triangularPDFReal a b c x = 2 * (x - a) / ((b - a) * (c - a)) := by
  rw [triangularPDFReal,
    ite_eq_left ⟨hx.1.le.trans hx.2.le, hcb, hx.1, hx.2.trans_le hcb⟩, ite_eq_left hx.2]

/-- On the falling branch `[c, b)`, away from the lower endpoint, the real triangular density is
`2 * (b - x) / ((b - a) * (b - c))`. -/
theorem triangularPDFReal_of_mem_Ico_right (hac : a ≤ c) (hax : a < x) (hx : x ∈ Ico c b) :
    triangularPDFReal a b c x = 2 * (b - x) / ((b - a) * (b - c)) := by
  rw [triangularPDFReal, ite_eq_left ⟨hac, hx.1.trans hx.2.le, hax, hx.2⟩,
    ite_eq_right (not_lt.2 hx.1)]

/-- The real triangular density vanishes outside the open interval `(a, b)`. -/
@[simp]
theorem triangularPDFReal_of_notMem_Ioo (hx : x ∉ Ioo a b) (c : ℝ) :
    triangularPDFReal a b c x = 0 :=
  ite_eq_right fun h ↦ hx h.2.2

/-- The real triangular density vanishes unless the mode lies between the endpoints. -/
@[simp]
theorem triangularPDFReal_of_not_le (h : ¬ (a ≤ c ∧ c ≤ b)) (x : ℝ) :
    triangularPDFReal a b c x = 0 :=
  ite_eq_right fun h' ↦ h ⟨h'.1, h'.2.1⟩

/-- The real triangular density is positive on the open interval `(a, b)` whenever the mode lies
between the endpoints. -/
theorem triangularPDFReal_pos (hac : a ≤ c) (hcb : c ≤ b) (hx : x ∈ Ioo a b) :
    0 < triangularPDFReal a b c x := by
  have hab : 0 < b - a := sub_pos.2 (hx.1.trans hx.2)
  rcases lt_or_ge x c with hxc | hcx
  · rw [triangularPDFReal_of_mem_Ioo_left hcb ⟨hx.1, hxc⟩]
    have : 0 < c - a := sub_pos.2 (hx.1.trans hxc)
    have : 0 < x - a := sub_pos.2 hx.1
    positivity
  · rw [triangularPDFReal_of_mem_Ico_right hac hx.1 ⟨hcx, hx.2⟩]
    have : 0 < b - c := sub_pos.2 (hcx.trans_lt hx.2)
    have : 0 < b - x := sub_pos.2 hx.2
    positivity

/-- When the mode lies between the endpoints, the real triangular density is positive exactly on
the open interval `(a, b)`. -/
theorem triangularPDFReal_pos_iff (hac : a ≤ c) (hcb : c ≤ b) :
    0 < triangularPDFReal a b c x ↔ x ∈ Ioo a b := by
  refine ⟨fun h ↦ ?_, triangularPDFReal_pos hac hcb⟩
  by_contra hx
  rw [triangularPDFReal_of_notMem_Ioo hx] at h
  exact h.false

/-- The real triangular density is nonnegative. -/
theorem triangularPDFReal_nonneg (a b c x : ℝ) : 0 ≤ triangularPDFReal a b c x := by
  by_cases h : a ≤ c ∧ c ≤ b ∧ x ∈ Ioo a b
  · exact (triangularPDFReal_pos h.1 h.2.1 h.2.2).le
  · rw [triangularPDFReal, ite_eq_right h]

/-- The real triangular density is bounded by `2 / (b - a)`. This is its value at the mode when
`a < c < b`, and its supremum whenever `a < b` and `a ≤ c ≤ b`; for other modes the density is
identically zero. -/
theorem triangularPDFReal_le (hab : a ≤ b) (c x : ℝ) :
    triangularPDFReal a b c x ≤ 2 / (b - a) := by
  by_cases h : a ≤ c ∧ c ≤ b ∧ x ∈ Ioo a b
  · obtain ⟨hac, hcb, hx⟩ := h
    have hab : 0 < b - a := sub_pos.2 (hx.1.trans hx.2)
    rcases lt_or_ge x c with hxc | hcx
    · rw [triangularPDFReal_of_mem_Ioo_left hcb ⟨hx.1, hxc⟩]
      have hca : 0 < c - a := sub_pos.2 (hx.1.trans hxc)
      rw [div_le_div_iff₀ (mul_pos hab hca) hab]
      nlinarith
    · rw [triangularPDFReal_of_mem_Ico_right hac hx.1 ⟨hcx, hx.2⟩]
      have hbc : 0 < b - c := sub_pos.2 (hcx.trans_lt hx.2)
      rw [div_le_div_iff₀ (mul_pos hab hbc) hab]
      nlinarith
  · rw [triangularPDFReal, ite_eq_right h]
    exact div_nonneg zero_le_two (sub_nonneg.2 hab)

/-- Converting the triangular density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_triangularPDF (a b c x : ℝ) :
    (triangularPDF a b c x).toReal = triangularPDFReal a b c x :=
  ENNReal.toReal_ofReal (triangularPDFReal_nonneg a b c x)

/-- The triangular density vanishes outside the open interval `(a, b)`. -/
@[simp]
theorem triangularPDF_of_notMem_Ioo (hx : x ∉ Ioo a b) (c : ℝ) : triangularPDF a b c x = 0 := by
  rw [triangularPDF_eq_ofReal, triangularPDFReal_of_notMem_Ioo hx, ENNReal.ofReal_zero]

/-- The triangular density vanishes unless the mode lies between the endpoints. -/
@[simp]
theorem triangularPDF_of_not_le (h : ¬ (a ≤ c ∧ c ≤ b)) (x : ℝ) : triangularPDF a b c x = 0 := by
  rw [triangularPDF_eq_ofReal, triangularPDFReal_of_not_le h, ENNReal.ofReal_zero]

/-- The triangular density is jointly measurable in its three parameters and the sample point. -/
@[fun_prop]
theorem measurable_uncurry_triangularPDFReal :
    Measurable fun q : (ℝ × ℝ × ℝ) × ℝ ↦ triangularPDFReal q.1.1 q.1.2.1 q.1.2.2 q.2 := by
  have ha : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ ↦ q.1.1 := measurable_fst.fst
  have hb : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ ↦ q.1.2.1 := measurable_fst.snd.fst
  have hc : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ ↦ q.1.2.2 := measurable_fst.snd.snd
  have hx : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ ↦ q.2 := measurable_snd
  unfold triangularPDFReal
  refine Measurable.ite ?_ (Measurable.ite (measurableSet_lt hx hc) (by fun_prop) (by fun_prop))
    measurable_const
  exact (measurableSet_le ha hc).inter
    ((measurableSet_le hc hb).inter ((measurableSet_lt ha hx).inter (measurableSet_lt hx hb)))

/-- The extended-nonnegative triangular density is jointly measurable in its three parameters and
the sample point. -/
@[fun_prop]
theorem measurable_uncurry_triangularPDF :
    Measurable fun q : (ℝ × ℝ × ℝ) × ℝ ↦ triangularPDF q.1.1 q.1.2.1 q.1.2.2 q.2 :=
  measurable_uncurry_triangularPDFReal.ennreal_ofReal

/-- The real triangular density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_triangularPDFReal (a b c : ℝ) : Measurable (triangularPDFReal a b c) :=
  measurable_uncurry_triangularPDFReal.comp (measurable_prodMk_left (x := (a, b, c)))

/-- The triangular density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_triangularPDF (a b c : ℝ) : Measurable (triangularPDF a b c) :=
  (measurable_triangularPDFReal a b c).ennreal_ofReal

/-- The real triangular density is Lebesgue integrable. -/
theorem integrable_triangularPDFReal (a b c : ℝ) : Integrable (triangularPDFReal a b c) := by
  have hsupp : Function.support (triangularPDFReal a b c) ⊆ Icc a b := fun x hx ↦ by
    by_contra h
    exact hx (triangularPDFReal_of_notMem_Ioo (fun h' ↦ h (Ioo_subset_Icc_self h')) c)
  rcases lt_or_ge b a with hba | hab
  · have hzero : triangularPDFReal a b c = 0 := funext fun x ↦
      triangularPDFReal_of_notMem_Ioo (fun hx ↦ (hx.1.trans hx.2).not_gt hba) c
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
  refine Measure.integrableOn_of_bounded (M := 2 / (b - a)) measure_Icc_lt_top.ne
    (measurable_triangularPDFReal a b c).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (triangularPDFReal_nonneg a b c x)]
  exact triangularPDFReal_le hab c x

/-! ### The cumulative quadratic spline -/

/-- The cumulative quadratic spline of the triangular law: `0` up to `a`, then
`(x - a) ^ 2 / ((b - a) * (c - a))` up to `c`, then `1 - (b - x) ^ 2 / ((b - a) * (b - c))` up
to `b`, and `1` afterwards. It is the cumulative distribution function of the law. -/
private def triangularSpline (a b c x : ℝ) : ℝ :=
  if x ≤ a then 0
  else if x ≤ c then (x - a) ^ 2 / ((b - a) * (c - a))
  else if x ≤ b then 1 - (b - x) ^ 2 / ((b - a) * (b - c))
  else 1

/-- Both quadratic pieces of the spline take the value `(c - a) / (b - a)` at the mode. -/
private theorem rising_eq_falling (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    (c - a) ^ 2 / ((b - a) * (c - a)) = 1 - (b - c) ^ 2 / ((b - a) * (b - c)) := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  rcases hac.eq_or_lt with rfl | hac
  · rcases hcb.eq_or_lt with rfl | hcb
    · exact absurd hab (lt_irrefl _)
    · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      field_simp
      ring
  rcases hcb.eq_or_lt with rfl | hcb
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      div_zero, sub_zero]
    field_simp
  have hca : c - a ≠ 0 := (sub_pos.2 hac).ne'
  have hbc : b - c ≠ 0 := (sub_pos.2 hcb).ne'
  field_simp
  ring

/-- From the upper endpoint on, the cumulative quadratic spline is one. -/
private theorem triangularSpline_of_le (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) (hbx : b ≤ x) :
    triangularSpline a b c x = 1 := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  rw [triangularSpline, ite_eq_right (hab.trans_le hbx).not_ge]
  split_ifs with hxc hxb
  · obtain rfl : c = b := le_antisymm hcb (hbx.trans hxc)
    obtain rfl : x = c := le_antisymm hxc hbx
    field_simp
  · obtain rfl : x = b := le_antisymm hxb hbx
    simp
  · rfl

/-- The cumulative quadratic spline is continuous. -/
private theorem continuous_triangularSpline (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    Continuous (triangularSpline a b c) := by
  have hfalling : (b - b) ^ 2 / ((b - a) * (b - c)) = 0 := by simp
  refine Continuous.if_le continuous_const ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const ?_
      rintro x rfl
      rw [hfalling, sub_zero]
    · rintro x rfl
      rw [ite_eq_left hcb, rising_eq_falling hab hac hcb]
  · rintro x rfl
    rw [ite_eq_left hac, sub_self]
    simp

/-- Inside `(a, b)`, the triangular density is the right derivative of the cumulative quadratic
spline. -/
private theorem hasDerivWithinAt_triangularSpline (hac : a ≤ c) (hcb : c ≤ b)
    (hx : x ∈ Ioo a b) :
    HasDerivWithinAt (triangularSpline a b c) (triangularPDFReal a b c x) (Ici x) x := by
  rcases lt_or_ge x c with hxc | hcx
  · -- On the rising branch the spline is the quadratic `(y - a) ^ 2 / ((b - a) * (c - a))`.
    have hderiv : HasDerivAt (fun y ↦ (y - a) ^ 2 / ((b - a) * (c - a)))
        (2 * (x - a) / ((b - a) * (c - a))) x := by
      simpa using (((hasDerivAt_id x).sub_const a).pow 2).div_const ((b - a) * (c - a))
    rw [triangularPDFReal_of_mem_Ioo_left hcb ⟨hx.1, hxc⟩]
    refine hderiv.hasDerivWithinAt.congr_of_eventuallyEq_of_mem ?_ (mem_Ici.2 le_rfl)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hxc)] with y hy hyc
    rw [triangularSpline, ite_eq_right (hx.1.trans_le hy).not_ge, ite_eq_left hyc.le]
  · -- On the falling branch the spline is `1 - (b - y) ^ 2 / ((b - a) * (b - c))`.
    have hderiv : HasDerivAt (fun y ↦ 1 - (b - y) ^ 2 / ((b - a) * (b - c)))
        (2 * (b - x) / ((b - a) * (b - c))) x := by
      have h := ((((hasDerivAt_id x).const_sub b).pow 2).div_const
        ((b - a) * (b - c))).const_sub 1
      convert h using 1
      · funext y
        simp only [Pi.pow_apply, id_eq]
      · simp only [id_eq, Nat.cast_ofNat]
        ring
    rw [triangularPDFReal_of_mem_Ico_right hac hx.1 ⟨hcx, hx.2⟩]
    refine hderiv.hasDerivWithinAt.congr_of_eventuallyEq_of_mem ?_ (mem_Ici.2 le_rfl)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hx.2)] with y hy hyb
    rw [triangularSpline, ite_eq_right (hx.1.trans_le hy).not_ge]
    by_cases hyc : y ≤ c
    · -- The two quadratic pieces agree at the mode.
      obtain rfl : y = c := le_antisymm hyc (hcx.trans hy)
      rw [ite_eq_left le_rfl, rising_eq_falling (hx.1.trans hx.2) hac hcb]
    · rw [ite_eq_right hyc, ite_eq_left hyb.le]

/-- The integral of the triangular density over `(-∞, x]` is the cumulative quadratic spline. -/
private theorem integral_Iic_triangularPDFReal (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b)
    (x : ℝ) : ∫ y in Iic x, triangularPDFReal a b c y = triangularSpline a b c x := by
  set L := min a x with hL
  have hint := integrable_triangularPDFReal a b c
  have hlow : ∫ y in Iic L, triangularPDFReal a b c y = 0 := by
    rw [setIntegral_congr_set Iio_ae_eq_Iic.symm]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ ?_
    exact triangularPDFReal_of_notMem_Ioo (fun h ↦ (hy.out.trans_le (min_le_left a x)).not_gt
      h.1) c
  have hsplineL : triangularSpline a b c L = 0 := ite_eq_left (min_le_left a x)
  have hftc : ∫ y in L..x, triangularPDFReal a b c y = triangularSpline a b c x - 0 := by
    rw [← hsplineL]
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (min_le_right a x)
      (continuous_triangularSpline hab hac hcb).continuousOn (fun y hy ↦ ?_)
      (hint.intervalIntegrable)
    rcases le_or_gt b y with hby | hyb
    · -- Beyond the upper endpoint the spline is constant and the density vanishes.
      rw [triangularPDFReal_of_notMem_Ioo (fun h ↦ h.2.not_ge hby)]
      refine (hasDerivWithinAt_const y _ (1 : ℝ)).congr_of_eventuallyEq ?_
        (triangularSpline_of_le hab hac hcb hby)
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact triangularSpline_of_le hab hac hcb (hby.trans hz.out.le)
    · have hay : a < y := (min_lt_iff.1 hy.1).resolve_right (not_lt.2 hy.2.le)
      exact (hasDerivWithinAt_triangularSpline hac hcb ⟨hay, hyb⟩).mono Ioi_subset_Ici_self
  rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hlow,
    sub_zero] at hftc
  rw [hftc, sub_zero]

/-! ### The law -/

/-- The triangular law with endpoints `a`, `b` and mode `c`: Lebesgue measure weighted by
`triangularPDF a b c`. It is zero unless `a < b` and `a ≤ c ≤ b`. -/
def triangularMeasure (a b c : ℝ) : Measure ℝ :=
  volume.withDensity (triangularPDF a b c)

/-- The triangular law is Lebesgue measure weighted by its density. -/
theorem triangularMeasure_eq_withDensity (a b c : ℝ) :
    triangularMeasure a b c = volume.withDensity (triangularPDF a b c) := (rfl)

/-- At invalid parameters, the triangular law is zero. -/
@[simp]
theorem triangularMeasure_eq_zero_of_not (h : ¬ (a < b ∧ a ≤ c ∧ c ≤ b)) :
    triangularMeasure a b c = 0 := by
  have hpdf : triangularPDF a b c = 0 := by
    funext x
    by_cases hmode : a ≤ c ∧ c ≤ b
    · exact triangularPDF_of_notMem_Ioo (fun hx ↦ h ⟨hx.1.trans hx.2, hmode⟩) c
    · exact triangularPDF_of_not_le hmode x
  rw [triangularMeasure_eq_withDensity, hpdf, withDensity_zero]

/-- A triangular law lies almost everywhere in the open interval `(a, b)`, for all parameter
values. -/
theorem ae_mem_Ioo_triangularMeasure (a b c : ℝ) :
    ∀ᵐ x ∂triangularMeasure a b c, x ∈ Ioo a b := by
  rw [triangularMeasure_eq_withDensity, ae_withDensity_iff (measurable_triangularPDF a b c)]
  exact ae_of_all _ fun x hx ↦ by_contra fun h ↦ hx (triangularPDF_of_notMem_Ioo h c)

/-- A triangular law is carried by the closed interval `[a, b]`. -/
theorem ae_mem_Icc_triangularMeasure (a b c : ℝ) :
    ∀ᵐ x ∂triangularMeasure a b c, x ∈ Icc a b := by
  filter_upwards [ae_mem_Ioo_triangularMeasure a b c] with x hx
  exact Ioo_subset_Icc_self hx

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against a triangular law exactly when
its density-weighted version is Lebesgue integrable. This holds at every parameter, the zero
measure included. -/
theorem integrable_triangularMeasure_iff {g : ℝ → E} :
    Integrable g (triangularMeasure a b c) ↔
      Integrable (fun x ↦ triangularPDFReal a b c x • g x) := by
  rw [triangularMeasure_eq_withDensity, funext (triangularPDF_eq_ofReal a b c)]
  exact Probability.integrable_withDensity_ofReal_iff
    (measurable_triangularPDFReal a b c).aemeasurable
    (ae_of_all _ (triangularPDFReal_nonneg a b c))

/-- **Integral transfer.** An integral against a triangular law is the density-weighted Lebesgue
integral. This holds at every parameter, the zero measure included. -/
theorem integral_triangularMeasure_eq (a b c : ℝ) (g : ℝ → E) :
    ∫ x, g x ∂triangularMeasure a b c = ∫ x, triangularPDFReal a b c x • g x := by
  rw [triangularMeasure_eq_withDensity, funext (triangularPDF_eq_ofReal a b c)]
  exact Probability.integral_withDensity_ofReal (measurable_triangularPDFReal a b c).aemeasurable
    (ae_of_all _ (triangularPDFReal_nonneg a b c)) g

end Transfer

/-- The triangular law gives the ray `(-∞, x]` the mass of the cumulative quadratic spline. -/
private theorem measure_Iic_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b)
    (x : ℝ) :
    triangularMeasure a b c (Iic x) = ENNReal.ofReal (triangularSpline a b c x) := by
  rw [← integral_Iic_triangularPDFReal hab hac hcb, ofReal_integral_eq_lintegral_ofReal
    (integrable_triangularPDFReal a b c).integrableOn
    (ae_of_all _ (triangularPDFReal_nonneg a b c)), triangularMeasure_eq_withDensity,
    withDensity_apply _ measurableSet_Iic, funext (triangularPDF_eq_ofReal a b c)]

/-- The triangular law is a probability measure when `a < b` and `a ≤ c ≤ b`. -/
theorem isProbabilityMeasure_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    IsProbabilityMeasure (triangularMeasure a b c) := by
  constructor
  have hnull : triangularMeasure a b c (Iic b)ᶜ = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_mem_Ioo_triangularMeasure a b c))
    intro x hx h
    exact hx (mem_Iic.2 h.2.le)
  rw [← measure_congr (ae_eq_univ.2 hnull), measure_Iic_triangularMeasure hab hac hcb,
    triangularSpline_of_le hab hac hcb le_rfl, ENNReal.ofReal_one]

/-- The triangular law is a probability measure exactly when `a < b` and `a ≤ c ≤ b`. -/
@[simp]
theorem isProbabilityMeasure_triangularMeasure_iff :
    IsProbabilityMeasure (triangularMeasure a b c) ↔ a < b ∧ a ≤ c ∧ c ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ isProbabilityMeasure_triangularMeasure h.1 h.2.1 h.2.2⟩
  by_contra habc
  rw [triangularMeasure_eq_zero_of_not habc] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl

/-- The triangular density has total mass one at valid parameters. -/
@[simp]
theorem lintegral_triangularPDF_eq_one (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫⁻ x, triangularPDF a b c x = 1 := by
  have := isProbabilityMeasure_triangularMeasure hab hac hcb
  rw [← setLIntegral_univ, ← withDensity_apply _ .univ, ← triangularMeasure_eq_withDensity,
    measure_univ]

/-- The real triangular density integrates to one at valid parameters. -/
@[simp]
theorem integral_triangularPDFReal (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x, triangularPDFReal a b c x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (triangularPDFReal_nonneg a b c))
    (measurable_triangularPDFReal a b c).aestronglyMeasurable]
  simp only [← triangularPDF_eq_ofReal, lintegral_triangularPDF_eq_one hab hac hcb,
    ENNReal.toReal_one]

/-- When the mode lies between the endpoints `a < b`, the topological support of the triangular
law is the closed interval `[a, b]`. -/
theorem support_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    (triangularMeasure a b c).support = Icc a b := by
  have hsupp : Function.support (triangularPDF a b c) = Ioo a b := by
    ext x
    rw [Function.mem_support, triangularPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff,
      triangularPDFReal_pos_iff hac hcb]
  rw [triangularMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_triangularPDF a b c) isOpen_Ioo hsupp,
    closure_Ioo hab.ne]

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a triangular law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_triangularMeasure (hX : HasLaw X (triangularMeasure a b c) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_triangularPDF a b c).aemeasurable hX

/-- The density of a random variable with a triangular law is `triangularPDF`. -/
theorem pdf_eq_triangularPDF_of_hasLaw_triangularMeasure
    (hX : HasLaw X (triangularMeasure a b c) P) :
    pdf X P volume =ᵐ[volume] triangularPDF a b c :=
  pdf_eq_of_hasLaw_withDensity (measurable_triangularPDF a b c).aemeasurable hX

end RandomVariables

/-- The Radon–Nikodym derivative of a triangular law with respect to Lebesgue measure. -/
theorem rnDeriv_triangularMeasure (a b c : ℝ) :
    (triangularMeasure a b c).rnDeriv volume =ᵐ[volume] triangularPDF a b c :=
  Measure.rnDeriv_withDensity volume (measurable_triangularPDF a b c)

/-- The triangular family is jointly measurable in its endpoints and mode. -/
@[fun_prop]
theorem measurable_triangularMeasure :
    Measurable fun p : ℝ × ℝ × ℝ ↦ triangularMeasure p.1 p.2.1 p.2.2 := by
  simpa only [triangularMeasure_eq_withDensity] using
    measurable_withDensity (μ := volume) measurable_uncurry_triangularPDF

/-! ### Cumulative distribution function -/

/-- The triangular cdf is the cumulative quadratic spline. -/
private theorem cdf_triangularMeasure_eq_triangularSpline (hab : a < b) (hac : a ≤ c)
    (hcb : c ≤ b) (x : ℝ) :
    cdf (triangularMeasure a b c) x = triangularSpline a b c x := by
  have := isProbabilityMeasure_triangularMeasure hab hac hcb
  rw [cdf_eq_real, triangularMeasure_eq_withDensity, funext (triangularPDF_eq_ofReal a b c),
    measureReal_withDensity_ofReal (ae_of_all _ (triangularPDFReal_nonneg a b c))
      measurableSet_Iic (integrable_triangularPDFReal a b c).integrableOn,
    integral_Iic_triangularPDFReal hab hac hcb]

/-- The triangular cdf in closed form at every point: `0` up to the lower endpoint, the rising
quadratic `(x - a) ^ 2 / ((b - a) * (c - a))` up to the mode, the falling quadratic
`1 - (b - x) ^ 2 / ((b - a) * (b - c))` up to the upper endpoint, and `1` afterwards. -/
theorem cdf_triangularMeasure_eq (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) (x : ℝ) :
    cdf (triangularMeasure a b c) x =
      if x ≤ a then 0
      else if x ≤ c then (x - a) ^ 2 / ((b - a) * (c - a))
      else if x ≤ b then 1 - (b - x) ^ 2 / ((b - a) * (b - c))
      else 1 := by
  rw [cdf_triangularMeasure_eq_triangularSpline hab hac hcb, triangularSpline]

/-- The triangular cdf vanishes up to the lower endpoint. -/
@[simp]
theorem cdf_triangularMeasure_of_le_left (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b)
    (hx : x ≤ a) : cdf (triangularMeasure a b c) x = 0 := by
  rw [cdf_triangularMeasure_eq hab hac hcb, ite_eq_left hx]

/-- Between the lower endpoint and the mode, the triangular cdf is the rising quadratic
`(x - a) ^ 2 / ((b - a) * (c - a))`. -/
theorem cdf_triangularMeasure_of_mem_Icc_left (hab : a < b) (hcb : c ≤ b) (hx : x ∈ Icc a c) :
    cdf (triangularMeasure a b c) x = (x - a) ^ 2 / ((b - a) * (c - a)) := by
  rw [cdf_triangularMeasure_eq hab (hx.1.trans hx.2) hcb]
  rcases hx.1.eq_or_lt with rfl | hax
  · simp
  · rw [ite_eq_right hax.not_ge, ite_eq_left hx.2]

/-- Between the mode and the upper endpoint, the triangular cdf is the falling quadratic
`1 - (b - x) ^ 2 / ((b - a) * (b - c))`. -/
theorem cdf_triangularMeasure_of_mem_Icc_right (hab : a < b) (hac : a ≤ c) (hx : x ∈ Icc c b) :
    cdf (triangularMeasure a b c) x = 1 - (b - x) ^ 2 / ((b - a) * (b - c)) := by
  have hcb := hx.1.trans hx.2
  rcases hx.1.eq_or_lt with rfl | hcx
  · rw [← rising_eq_falling hab hac hcb]
    exact cdf_triangularMeasure_of_mem_Icc_left hab hcb ⟨hac, le_rfl⟩
  · rw [cdf_triangularMeasure_eq hab hac hcb, ite_eq_right (hac.trans_lt hcx).not_ge,
      ite_eq_right hcx.not_ge, ite_eq_left hx.2]

/-- From the upper endpoint on, the triangular cdf is one. -/
@[simp]
theorem cdf_triangularMeasure_of_le_right (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b)
    (hx : b ≤ x) : cdf (triangularMeasure a b c) x = 1 := by
  rw [cdf_triangularMeasure_eq_triangularSpline hab hac hcb,
    triangularSpline_of_le hab hac hcb hx]

/-- The triangular cdf is continuous. -/
theorem continuous_cdf_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    Continuous (cdf (triangularMeasure a b c)) := by
  simpa only [← funext (cdf_triangularMeasure_eq_triangularSpline hab hac hcb)] using
    continuous_triangularSpline hab hac hcb

end TauCeti.Probability
