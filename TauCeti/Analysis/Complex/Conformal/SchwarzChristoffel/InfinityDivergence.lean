/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Divergence of Schwarz--Christoffel boundary values at infinity

For Schwarz--Christoffel data with total exponent `S = ∑ i, e i`, the boundary density is
asymptotic to `|x| ^ S` at either end of the real axis.  Consequently, when `-1 ≤ S`, the
two outer boundary edges have infinite length and their boundary values escape every bounded set.

This is the counterpart to the finite vertex-at-infinity theory, which applies when `S < -1`.
Together the two regimes distinguish bounded polygonal images from polygonal images having a
vertex at infinity.

## Main results

* `TauCeti.tendsto_schwarzChristoffelDensity_div_rpow_atTop` and
  `TauCeti.tendsto_schwarzChristoffelDensity_div_rpow_atBot` identify the leading term of the
  boundary density at both ends of the real axis.
* `TauCeti.tendsto_norm_schwarzChristoffelBoundary_atTop` and
  `TauCeti.tendsto_norm_schwarzChristoffelBoundary_atBot` show that the two outer boundary edges
  escape to infinity when the total exponent is at least `-1`; their
  `tendsto_schwarzChristoffelBoundary_atTop_cobounded` and
  `tendsto_schwarzChristoffelBoundary_atBot_cobounded` companions express this directly in the
  bornological filter.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Bornology Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- At the right end of the real axis, the distance to a fixed real point is asymptotic to the
absolute size of the variable. -/
private theorem tendsto_abs_sub_div_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => |x - c| / x) atTop (𝓝 1) := by
  have hlim : Tendsto (fun x : ℝ => 1 - c / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.const_div_atTop c))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max c 1)] with x hx
  have hxc : 0 ≤ x - c := sub_nonneg.mpr ((le_max_left c 1).trans hx)
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le ((le_max_right c 1).trans hx))
  rw [abs_of_nonneg hxc]
  field_simp

/-- At the left end of the real axis, the distance to a fixed real point is asymptotic to the
absolute size of the variable. -/
private theorem tendsto_abs_sub_div_neg_atBot (c : ℝ) :
    Tendsto (fun x : ℝ => |x - c| / (-x)) atBot (𝓝 1) := by
  have hlim : Tendsto (fun x : ℝ => 1 - c / x) atBot (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.const_div_atBot c))
  refine hlim.congr' ?_
  filter_upwards [eventually_le_atBot (min c (-1))] with x hx
  have hxc : x - c ≤ 0 := sub_nonpos.mpr (hx.trans (min_le_left c (-1)))
  have hx0 : x ≠ 0 := ne_of_lt (hx.trans_lt ((min_le_right c (-1)).trans_lt (by norm_num)))
  rw [abs_of_nonpos hxc]
  field_simp

/-- **Asymptotic boundary density at positive infinity.**  The Schwarz--Christoffel density is
asymptotic to `x ^ (∑ i, e i)` as `x → +∞`. -/
theorem tendsto_schwarzChristoffelDensity_div_rpow_atTop (a e : ι → ℝ) :
    Tendsto (fun x : ℝ => schwarzChristoffelDensity a e x / x ^ ∑ i, e i)
      atTop (𝓝 1) := by
  have hprod : Tendsto (fun x : ℝ => ∏ i, (|x - a i| / x) ^ e i) atTop
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd Finset.univ fun i _ => by
      simpa only [Real.one_rpow] using
        (tendsto_abs_sub_div_atTop (a i)).rpow_const (p := e i) (Or.inl one_ne_zero)
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
      atBot (𝓝 1) := by
  have hprod : Tendsto (fun x : ℝ => ∏ i, (|x - a i| / (-x)) ^ e i) atBot
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd Finset.univ fun i _ => by
      simpa only [Real.one_rpow] using
        (tendsto_abs_sub_div_neg_atBot (a i)).rpow_const (p := e i) (Or.inl one_ne_zero)
  simp only [Finset.prod_const_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with x hx
  have hxneg : 0 < -x := neg_pos.mpr hx
  rw [schwarzChristoffelDensity_def]
  calc
    ∏ i, (|x - a i| / (-x)) ^ e i =
        ∏ i, (|x - a i| ^ e i / (-x) ^ e i) := by
          apply Finset.prod_congr rfl
          intro i _
          exact Real.div_rpow (abs_nonneg (x - a i)) hxneg.le (e i)
    _ = (∏ i, |x - a i| ^ e i) / ∏ i, (-x) ^ e i := by simp
    _ = (∏ i, |x - a i| ^ e i) / (-x) ^ ∑ i, e i := by
      rw [Real.rpow_sum_of_pos hxneg]

/-- Reflecting the prevertices and the boundary parameter preserves the Schwarz--Christoffel
density. -/
private theorem schwarzChristoffelDensity_neg (a e : ι → ℝ) (x : ℝ) :
    schwarzChristoffelDensity (fun i => -a i) e x =
      schwarzChristoffelDensity a e (-x) := by
  rw [schwarzChristoffelDensity_def, schwarzChristoffelDensity_def]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  rw [show x - -a i = -( -x - a i) by ring, abs_neg]

/-- In the nonintegrable exponent range, the accumulated density on a right-hand boundary edge
tends to infinity.  The starting point can be chosen to the right of every prevertex. -/
private theorem exists_tendsto_integral_schwarzChristoffelDensity_atTop (a e : ι → ℝ)
    (hsum : -1 ≤ ∑ i, e i) :
    ∃ R > 0, (∀ i, a i < R - 1) ∧
      Tendsto (fun x => ∫ t in R..x, schwarzChristoffelDensity a e t) atTop atTop := by
  have hratio := tendsto_schwarzChristoffelDensity_div_rpow_atTop a e
  have hhalf : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) ≤ schwarzChristoffelDensity a e x / x ^ ∑ i, e i :=
    hratio.eventually (eventually_ge_nhds (by norm_num))
  obtain ⟨R₀, hR₀⟩ := (eventually_atTop.1 hhalf)
  let R : ℝ := max (max R₀ 1) (∑ i, |a i| + 2)
  have hR₀R : R₀ ≤ R := (le_max_left R₀ 1).trans (le_max_left _ _)
  have hR1 : 1 ≤ R := (le_max_right R₀ 1).trans (le_max_left _ _)
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have haR : ∀ i, a i < R - 1 := by
    intro i
    have hai : |a i| ≤ ∑ j, |a j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    have hsumR : ∑ j, |a j| + 2 ≤ R := le_max_right _ _
    linarith [le_trans (le_abs_self (a i)) hai]
  have hlower : ∀ t, R ≤ t → (2 * t)⁻¹ ≤ schwarzChristoffelDensity a e t := by
    intro t ht
    have ht1 : 1 ≤ t := hR1.trans ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hpow : 0 < t ^ ∑ i, e i := Real.rpow_pos_of_pos ht0 _
    have hratio_t := hR₀ t (hR₀R.trans ht)
    have hrpow : t⁻¹ ≤ t ^ ∑ i, e i := by
      rw [← Real.rpow_neg_one t]
      exact Real.rpow_le_rpow_of_exponent_le ht1 hsum
    calc
      (2 * t)⁻¹ = (1 / 2) * t⁻¹ := by ring
      _ ≤ (1 / 2) * t ^ ∑ i, e i := by gcongr
      _ ≤ schwarzChristoffelDensity a e t := (le_div_iff₀ hpow).mp hratio_t
  refine ⟨R, hRpos, haR, ?_⟩
  have hlogSub : Tendsto (fun x : ℝ => Real.log x - Real.log R) atTop atTop := by
    simpa [sub_eq_add_neg] using
      Real.tendsto_log_atTop.atTop_add (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => -Real.log R) atTop (𝓝 (-Real.log R)))
  have hlog : Tendsto (fun x : ℝ => (1 / 2) * (Real.log x - Real.log R)) atTop atTop :=
    hlogSub.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [eventually_ge_atTop R] with x hx
  have hfree : ∀ i, e i ≠ 0 → a i ∉ Ioo (R - 1) (x + 1) := by
    intro i _ hi
    exact (not_lt_of_ge hi.1.le (haR i)).elim
  have hcont : ContinuousOn (schwarzChristoffelDensity a e) (Icc R x) :=
    (continuousOn_schwarzChristoffelDensity a e hfree).mono fun t ht => by
      constructor <;> linarith [ht.1, ht.2]
  have hinv : ContinuousOn (fun t : ℝ => (2 * t)⁻¹) (Icc R x) := by
    exact (continuousOn_const.mul continuousOn_id).inv₀ fun t ht =>
      mul_ne_zero (by norm_num) (ne_of_gt (hRpos.trans_le ht.1))
  have hcont' : ContinuousOn (schwarzChristoffelDensity a e) (uIcc R x) := by
    rwa [uIcc_of_le hx]
  have hinv' : ContinuousOn (fun t : ℝ => (2 * t)⁻¹) (uIcc R x) := by
    rwa [uIcc_of_le hx]
  calc
    (1 / 2) * (Real.log x - Real.log R) = ∫ t in R..x, (2 * t)⁻¹ := by
      rw [show (fun t : ℝ => (2 * t)⁻¹) = fun t => (1 / 2) * t⁻¹ by
        funext t; ring, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hRpos (hRpos.trans_le hx)]
      rw [Real.log_div (hRpos.trans_le hx).ne' hRpos.ne']
    _ ≤ ∫ t in R..x, schwarzChristoffelDensity a e t :=
      intervalIntegral.integral_mono_on hx hinv'.intervalIntegrable hcont'.intervalIntegrable
        fun t ht => hlower t ht.1

/-- In the nonintegrable exponent range, the accumulated density on a left-hand boundary edge
tends to infinity.  The endpoint can be chosen to the left of every prevertex. -/
private theorem exists_tendsto_integral_schwarzChristoffelDensity_atBot (a e : ι → ℝ)
    (hsum : -1 ≤ ∑ i, e i) :
    ∃ R > 0, (∀ i, -R + 1 < a i) ∧
      Tendsto (fun x => ∫ t in x..(-R), schwarzChristoffelDensity a e t) atBot atTop := by
  obtain ⟨R, hR, haR, hint⟩ :=
    exists_tendsto_integral_schwarzChristoffelDensity_atTop (fun i => -a i) e hsum
  refine ⟨R, hR, fun i => by linarith [haR i], ?_⟩
  refine (hint.comp tendsto_neg_atBot_atTop).congr' ?_
  filter_upwards [] with x
  simp only [Function.comp_apply]
  simp_rw [schwarzChristoffelDensity_neg]
  simpa only [neg_neg] using intervalIntegral.integral_comp_neg
    (f := fun t => schwarzChristoffelDensity a e t) (a := R) (b := -x)

/-- **A Schwarz--Christoffel boundary edge escapes at positive infinity.**  If the total turning
exponent is at least `-1`, the canonical boundary values tend to infinity in norm along the
positive real direction.  Equivalently, the right-hand outer edge has infinite length. -/
theorem tendsto_norm_schwarzChristoffelBoundary_atTop (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (fun x => ‖schwarzChristoffelBoundary a e z₀ x‖) atTop atTop := by
  obtain ⟨R, _, haR, hint⟩ :=
    exists_tendsto_integral_schwarzChristoffelDensity_atTop a e hsum
  let B := schwarzChristoffelBoundary a e z₀
  have hsub : ∀ᶠ x : ℝ in atTop,
      B x - B R = ((∫ t in R..x, schwarzChristoffelDensity a e t : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop R] with x hx
    have hfree : ∀ i, e i ≠ 0 → a i ∉ Ioo (R - 1) (x + 1) := by
      intro i _ hi
      exact (not_lt_of_ge hi.1.le (haR i)).elim
    have hformula := schwarzChristoffelBoundary_sub_eq a e z₀ hfree
      (x := x) (y := R) (by constructor <;> linarith) (by constructor <;> linarith)
    have hangle : schwarzChristoffelEdgeAngle a e (R - 1) = 0 :=
      schwarzChristoffelEdgeAngle_eq_zero_of_forall_le a e fun i => (haR i).le
    simpa [B, hangle] using hformula
  have hnormSub : Tendsto (fun x => ‖B x - B R‖) atTop atTop := by
    refine hint.congr' ?_
    filter_upwards [hsub, hint.eventually_ge_atTop 0] with x hx hnonneg
    rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hlower : Tendsto (fun x => ‖B x - B R‖ - ‖B R‖) atTop atTop := by
    simpa [sub_eq_add_neg] using hnormSub.atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => -‖B R‖) atTop (𝓝 (-‖B R‖)))
  refine tendsto_atTop_mono (fun x => ?_) hlower
  linarith [norm_sub_le (B x) (B R)]

/-- In the nonintegrable exponent range, the right-hand boundary edge tends to the cobounded
filter of the complex plane. -/
theorem tendsto_schwarzChristoffelBoundary_atTop_cobounded (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (schwarzChristoffelBoundary a e z₀) atTop (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  exact tendsto_norm_schwarzChristoffelBoundary_atTop a e z₀ hsum

/-- **A Schwarz--Christoffel boundary edge escapes at negative infinity.**  If the total turning
exponent is at least `-1`, the canonical boundary values tend to infinity in norm along the
negative real direction.  Equivalently, the left-hand outer edge has infinite length. -/
theorem tendsto_norm_schwarzChristoffelBoundary_atBot (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (fun x => ‖schwarzChristoffelBoundary a e z₀ x‖) atBot atTop := by
  obtain ⟨R, _, haR, hint⟩ :=
    exists_tendsto_integral_schwarzChristoffelDensity_atBot a e hsum
  let B := schwarzChristoffelBoundary a e z₀
  have hsub : ∀ᶠ x : ℝ in atBot,
      B (-R) - B x = ((∫ t in x..(-R), schwarzChristoffelDensity a e t : ℝ) : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e (x - 1) * Complex.I) := by
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    have hfree : ∀ i, e i ≠ 0 → a i ∉ Ioo (x - 1) (-R + 1) := by
      intro i _ hi
      exact (not_lt_of_ge (haR i).le hi.2).elim
    exact schwarzChristoffelBoundary_sub_eq a e z₀ hfree
      (x := -R) (y := x) (by constructor <;> linarith) (by constructor <;> linarith)
  have hnormSub : Tendsto (fun x => ‖B (-R) - B x‖) atBot atTop := by
    refine hint.congr' ?_
    filter_upwards [hsub, hint.eventually_ge_atTop 0] with x hx hnonneg
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hlower : Tendsto (fun x => ‖B (-R) - B x‖ - ‖B (-R)‖) atBot atTop := by
    simpa [sub_eq_add_neg] using hnormSub.atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => -‖B (-R)‖) atBot (𝓝 (-‖B (-R)‖)))
  refine tendsto_atTop_mono (fun x => ?_) hlower
  linarith [norm_sub_le (B (-R)) (B x)]

/-- In the nonintegrable exponent range, the left-hand boundary edge tends to the cobounded
filter of the complex plane. -/
theorem tendsto_schwarzChristoffelBoundary_atBot_cobounded (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hsum : -1 ≤ ∑ i, e i) :
    Tendsto (schwarzChristoffelBoundary a e z₀) atBot (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  exact tendsto_norm_schwarzChristoffelBoundary_atBot a e z₀ hsum

end TauCeti

end
