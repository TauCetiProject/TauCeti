/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SideLength
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Divergence of Schwarz--Christoffel boundary values at infinity

For Schwarz--Christoffel data with total exponent `S = ∑ i, e i`, the boundary density is
asymptotic to `|x| ^ S` at either end of the real axis.  Consequently, when `-1 ≤ S`, the
two outer boundary edges have infinite length and their boundary values escape every bounded set.

This is the counterpart to the finite vertex-at-infinity theory of
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Basic`, which applies when
`S < -1`.  The two regimes decide whether the point at infinity of the upper half-plane is sent to
a finite vertex (`S < -1`) or to a vertex at infinity (`-1 ≤ S`, this file).

## Main results

* `TauCeti.tendsto_schwarzChristoffelDensity_div_rpow_atTop` and
  `TauCeti.tendsto_schwarzChristoffelDensity_div_rpow_atBot` identify the leading term of the
  boundary density at both ends of the real axis.
* `TauCeti.tendsto_integral_schwarzChristoffelDensity_atTop` and
  `TauCeti.tendsto_integral_schwarzChristoffelDensity_atBot` show that the two outer boundary
  edges have infinite length when the total exponent is at least `-1`.
* `TauCeti.tendsto_schwarzChristoffelBoundary_atTop_cobounded` and
  `TauCeti.tendsto_schwarzChristoffelBoundary_atBot_cobounded` show that the boundary values on
  those edges tend to the cobounded filter of `ℂ`.
* `TauCeti.isProperMap_schwarzChristoffelBoundary` -- when also every finite prevertex is
  integrable, the boundary map `ℝ → ℂ` is proper; in particular its range is closed.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Asymptotic boundary density at positive infinity.**  The Schwarz--Christoffel density is
asymptotic to `x ^ (∑ i, e i)` as `x → +∞`. -/
theorem tendsto_schwarzChristoffelDensity_div_rpow_atTop (a e : ι → ℝ) :
    Tendsto (fun x : ℝ => schwarzChristoffelDensity a e x / x ^ ∑ i, e i)
      atTop (𝓝 1) := by
  have habs (c : ℝ) : Tendsto (fun x : ℝ => |x - c| / x) atTop (𝓝 1) := by
    have hlim : Tendsto (fun x : ℝ => 1 - c / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_id.const_div_atTop c)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (max c 1)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le ((le_max_right c 1).trans hx))
    rw [abs_of_nonneg (sub_nonneg.mpr ((le_max_left c 1).trans hx))]
    field_simp
  have hprod : Tendsto (fun x : ℝ => ∏ i, (|x - a i| / x) ^ e i) atTop
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd Finset.univ fun i _ => by
      simpa only [Real.one_rpow] using (habs (a i)).rpow_const (p := e i) (Or.inl one_ne_zero)
  simp only [Finset.prod_const_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [schwarzChristoffelDensity_def]
  calc
    ∏ i, (|x - a i| / x) ^ e i =
        ∏ i, (|x - a i| ^ e i / x ^ e i) := by
          apply Finset.prod_congr rfl
          intro i _
          exact Real.div_rpow (abs_nonneg (x - a i)) hx.le (e i)
    _ = (∏ i, |x - a i| ^ e i) / ∏ i, x ^ e i := by simp
    _ = (∏ i, |x - a i| ^ e i) / x ^ ∑ i, e i := by
      rw [Real.rpow_sum_of_pos hx]

/-- **Asymptotic boundary density at negative infinity.**  The Schwarz--Christoffel density is
asymptotic to `(-x) ^ (∑ i, e i)` as `x → -∞`. -/
theorem tendsto_schwarzChristoffelDensity_div_rpow_atBot (a e : ι → ℝ) :
    Tendsto (fun x : ℝ => schwarzChristoffelDensity a e x / (-x) ^ ∑ i, e i)
      atBot (𝓝 1) :=
  ((tendsto_schwarzChristoffelDensity_div_rpow_atTop (fun i => -a i) e).comp
    tendsto_neg_atBot_atTop).congr fun x => by
      simp [schwarzChristoffelDensity_neg]

/-- In the nonintegrable exponent range, the boundary density eventually dominates `(2 * t)⁻¹`
at positive infinity. -/
private theorem eventually_inv_two_mul_le_schwarzChristoffelDensity (a e : ι → ℝ)
    (hsum : -1 ≤ ∑ i, e i) :
    ∀ᶠ t : ℝ in atTop, (2 * t)⁻¹ ≤ schwarzChristoffelDensity a e t := by
  filter_upwards [(tendsto_schwarzChristoffelDensity_div_rpow_atTop a e).eventually
    (eventually_ge_nhds (by norm_num : (2⁻¹ : ℝ) < 1)), eventually_ge_atTop 1] with t ht ht1
  have hpow : 0 < t ^ ∑ i, e i := Real.rpow_pos_of_pos (zero_lt_one.trans_le ht1) _
  calc
    (2 * t)⁻¹ = 2⁻¹ * t ^ (-1 : ℝ) := by rw [mul_inv, Real.rpow_neg_one]
    _ ≤ 2⁻¹ * t ^ ∑ i, e i :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 hsum) (by norm_num)
    _ ≤ schwarzChristoffelDensity a e t := (le_div_iff₀ hpow).mp ht

/-- **The right-hand outer edge has infinite length.**  If the total turning exponent is at least
`-1`, the integral of the boundary density from any point to the right of every prevertex with a
nonzero exponent tends to infinity at positive infinity. -/
theorem tendsto_integral_schwarzChristoffelDensity_atTop {a e : ι → ℝ} {p : ℝ}
    (hp : ∀ i, e i ≠ 0 → a i < p) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (fun x => ∫ t in p..x, schwarzChristoffelDensity a e t) atTop atTop := by
  obtain ⟨R, hR⟩ := eventually_atTop.1
    ((eventually_inv_two_mul_le_schwarzChristoffelDensity a e hsum).and
      (eventually_ge_atTop (max (p + 1) 1)))
  have hpR : p < R := (lt_add_one p).trans_le ((le_max_left _ _).trans (hR R le_rfl).2)
  have hR0 : 0 < R := zero_lt_one.trans_le ((le_max_right _ _).trans (hR R le_rfl).2)
  have hlog : Tendsto (fun x : ℝ => (∫ t in p..R, schwarzChristoffelDensity a e t) +
      2⁻¹ * Real.log (x / R)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ ((Real.tendsto_log_atTop.comp
      (tendsto_id.atTop_div_const hR0)).const_mul_atTop (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [eventually_ge_atTop R] with x hx
  have hzero : ∀ c, p ≤ c → ∑ k with a k = c, e k = 0 := fun c hc =>
    Finset.sum_eq_zero fun k hk => by_contra fun h =>
      ((hp k h).trans_le hc).ne (Finset.mem_filter.1 hk).2
  have hint : IntervalIntegrable (schwarzChristoffelDensity a e) volume p x :=
    intervalIntegrable_schwarzChristoffelDensity a e (hpR.trans_le hx)
      (fun k hk hmem => lt_asymm hmem.1 (hp k hk)) (by rw [hzero p le_rfl]; norm_num)
      (by rw [hzero x (hpR.le.trans hx)]; norm_num)
  have hRmem : R ∈ uIcc p x := mem_uIcc_of_le hpR.le hx
  have hinv : ContinuousOn (fun t : ℝ => (2 * t)⁻¹) (Icc R x) :=
    (continuousOn_const.mul continuousOn_id).inv₀ fun t ht =>
      mul_ne_zero two_ne_zero (hR0.trans_le ht.1).ne'
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (uIcc_subset_uIcc_left hRmem))
    (hint.mono_set (uIcc_subset_uIcc_right hRmem))]
  refine add_le_add le_rfl ?_
  calc
    2⁻¹ * Real.log (x / R) = ∫ t in R..x, (2 * t)⁻¹ := by
      simp_rw [mul_inv]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hR0 (hR0.trans_le hx)]
    _ ≤ ∫ t in R..x, schwarzChristoffelDensity a e t :=
      intervalIntegral.integral_mono_on hx (hinv.intervalIntegrable_of_Icc hx)
        (hint.mono_set (uIcc_subset_uIcc_right hRmem)) fun t ht => (hR t ht.1).1

/-- **The left-hand outer edge has infinite length.**  If the total turning exponent is at least
`-1`, the integral of the boundary density up to any point to the left of every prevertex with a
nonzero exponent tends to infinity at negative infinity. -/
theorem tendsto_integral_schwarzChristoffelDensity_atBot {a e : ι → ℝ} {p : ℝ}
    (hp : ∀ i, e i ≠ 0 → p < a i) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (fun x => ∫ t in x..p, schwarzChristoffelDensity a e t) atBot atTop := by
  refine ((tendsto_integral_schwarzChristoffelDensity_atTop (a := fun i => -a i) (p := -p)
    (fun i hi => neg_lt_neg (hp i hi)) hsum).comp tendsto_neg_atBot_atTop).congr fun x => ?_
  simp only [Function.comp_apply, schwarzChristoffelDensity_neg]
  simpa only [neg_neg] using intervalIntegral.integral_comp_neg
    (f := fun t => schwarzChristoffelDensity a e t) (a := -p) (b := -x)

/-- **A Schwarz--Christoffel boundary edge escapes at positive infinity.**  If the total turning
exponent is at least `-1`, the canonical boundary values on the right-hand outer edge tend to the
cobounded filter of the complex plane. -/
theorem tendsto_schwarzChristoffelBoundary_atTop_cobounded (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (schwarzChristoffelBoundary a e z₀) atTop (cobounded ℂ) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ i, a i + 1 < R :=
    (eventually_all.2 fun i => eventually_gt_atTop (a i + 1)).exists (f := atTop)
  let B := schwarzChristoffelBoundary a e z₀
  have hint := tendsto_integral_schwarzChristoffelDensity_atTop (a := a) (p := R)
    (fun i _ => by linarith [hR i]) hsum
  have hsub : ∀ᶠ x : ℝ in atTop,
      B x - B R = ((∫ t in R..x, schwarzChristoffelDensity a e t : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop R] with x hx
    have hformula := schwarzChristoffelBoundary_sub_eq a e z₀ (p := R - 1) (q := x + 1)
      (fun i _ hi => lt_asymm hi.1 (by linarith [hR i]))
      (x := x) (y := R) (by constructor <;> linarith) (by constructor <;> linarith)
    have hangle : schwarzChristoffelEdgeAngle a e (R - 1) = 0 :=
      schwarzChristoffelEdgeAngle_eq_zero_of_forall_le a e fun i => by linarith [hR i]
    simpa [B, hangle] using hformula
  have hdiff : Tendsto (fun x => B x - B R) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine hint.congr' ?_
    filter_upwards [hsub, hint.eventually_ge_atTop 0] with x hx hnonneg
    rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa [Function.comp_def] using (tendsto_add_const_cobounded (B R)).comp hdiff

/-- **A Schwarz--Christoffel boundary edge escapes at negative infinity.**  If the total turning
exponent is at least `-1`, the canonical boundary values on the left-hand outer edge tend to the
cobounded filter of the complex plane. -/
theorem tendsto_schwarzChristoffelBoundary_atBot_cobounded (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (schwarzChristoffelBoundary a e z₀) atBot (cobounded ℂ) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ i, R < a i - 1 :=
    (eventually_all.2 fun i => eventually_lt_atBot (a i - 1)).exists (f := atBot)
  let B := schwarzChristoffelBoundary a e z₀
  have hint := tendsto_integral_schwarzChristoffelDensity_atBot (a := a) (p := R)
    (fun i _ => by linarith [hR i]) hsum
  have hsub : ∀ᶠ x : ℝ in atBot,
      B R - B x = ((∫ t in x..R, schwarzChristoffelDensity a e t : ℝ) : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e (x - 1) * Complex.I) := by
    filter_upwards [eventually_lt_atBot R] with x hx
    exact schwarzChristoffelBoundary_sub_eq a e z₀ (p := x - 1) (q := R + 1)
      (fun i _ hi => lt_asymm hi.2 (by linarith [hR i]))
      (x := R) (y := x) (by constructor <;> linarith) (by constructor <;> linarith)
  have hdiff : Tendsto (fun x => B R - B x) atBot (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine hint.congr' ?_
    filter_upwards [hsub, hint.eventually_ge_atTop 0] with x hx hnonneg
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  simpa [Function.comp_def] using (tendsto_const_sub_cobounded (B R)).comp hdiff

/-- **The Schwarz--Christoffel boundary map is proper** when every finite prevertex is integrable
and the total turning exponent is at least `-1`: it is continuous on all of `ℝ` and escapes every
bounded set at both ends of the real axis. -/
theorem isProperMap_schwarzChristoffelBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hsum : -1 ≤ ∑ i, e i) :
    IsProperMap (schwarzChristoffelBoundary a e z₀) := by
  refine isProperMap_iff_tendsto_cocompact.mpr ⟨continuousOn_univ.mp ?_, ?_⟩
  · exact continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one a e z₀ fun x _ =>
      lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite x
  · rw [cocompact_eq_atBot_atTop, ← Metric.cobounded_eq_cocompact]
    exact (tendsto_schwarzChristoffelBoundary_atBot_cobounded a e z₀ hsum).sup
      (tendsto_schwarzChristoffelBoundary_atTop_cobounded a e z₀ hsum)

end TauCeti

end
