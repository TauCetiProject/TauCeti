/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Strip
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Calderón's log-convexity and Poisson integral bounds for `[X₀, X₁]_θ`

The three-lines bound on an admissible strip function `F` controls `‖F θ‖_{[X₀, X₁]_θ}` only by
the boundary suprema `‖g₀‖ ^ (1 - θ) * ‖g₁‖ ^ θ`. Pulling the Herglotz–Riesz integral on the unit
disc back along `TauCeti.stripToUnitDisc` refines this maximum-principle estimate to Calderón's
fundamental log-convexity inequality (Bergh–Löfström, Lemma 4.3.2): for `0 < θ < 1` and `ε > 0`,

`‖u‖ ≤ exp (∫ μ₀(θ, t) log (max ‖g₀ t‖ ε) dt + ∫ μ₁(θ, t) log (max ‖g₁ t‖ ε) dt)`.

Applying Jensen's inequality (`ConvexOn.map_integral_le` for `Real.exp`) to the normalized
probability measures `stripPoissonMeasure₀ θ` and `stripPoissonMeasure₁ θ` and letting `ε → 0⁺`
yields `L^{p₀}`–`L^{p₁}` and mixed sup/`L^p` bounds on `[X₀, X₁]_θ`. None of the estimates require
completeness, density of the intersection, or duality.

## Main results

* `TauCeti.CompatibleCouple.IsStripFunction.exists_smul_of_differentiableOn`:
  bounded holomorphic scalar multiplier lemma for admissible strip functions.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_exp_integral_stripPoissonKernel`:
  Calderón's log-convexity bound for `[X₀, X₁]_θ`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure`:
  `(L^{p₀}, L^{p₁})` strip Poisson bound for `0 < p₀, p₁ < ∞`.
* `norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure` and
  `norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow` (in
  `TauCeti.CompatibleCouple.ComplexMethodSpace`):
  mixed `(L^∞, L^{p₁})` and `(L^{p₀}, L^∞)` strip Poisson bounds.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_integral_stripPoissonKernel`:
  the `p₀ = p₁ = 1` Calderón–Hirschman bound in terms of `stripPoissonKernel₀` and
  `stripPoissonKernel₁`.

## References

* I. I. Hirschman, *A convexity theorem for certain groups of transformations*, J. Analyse Math.
  **2** (1952), 209–218.
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §9.4.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Lemma 4.3.2.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set
open scoped ENNReal Topology ZeroAtInfty

namespace TauCeti

/-! ### Gluing strip boundary data onto the unit circle -/

/-- Inverse rational expression sending `stripToUnitDisc θ z` back to `exp (i π z)`. -/
private def unitDiscToExpStrip (θ : ℝ) (w : ℂ) : ℂ :=
  (exp (I * π * θ) - w * exp (-I * π * θ)) / (1 - w)

private theorem exp_I_pi_sub_exp_neg_I_pi_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    exp (I * π * θ) - exp (-I * π * θ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im (sub_eq_zero.1 h)
  have h₁ : (exp (I * π * θ)).im = Real.sin (π * θ) := by
    have : I * ↑π * ↑θ = ((π * θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I]
    simp [-ofReal_cos, -ofReal_sin]
  have h₂ : (exp (-I * π * θ)).im = -Real.sin (π * θ) := by
    have : -I * ↑π * ↑θ = ((-(π * θ) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I, Real.sin_neg]
    simp [-ofReal_cos, -ofReal_sin]
  have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])
  linarith

private theorem exp_I_pi_mul_sub_exp_neg_I_pi_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    exp (I * π * z) - exp (-I * π * θ) ≠ 0 := by
  have hz' := mem_verticalClosedStrip_iff.1 hz
  intro h
  have him := congrArg Complex.im (sub_eq_zero.1 h)
  have h₁ : 0 ≤ (exp (I * π * z)).im := by
    have hre : (I * π * z).re = -π * z.im := by simp [mul_assoc]
    have him' : (I * π * z).im = π * z.re := by simp [mul_assoc]
    rw [Complex.exp_im, hre, him']
    exact mul_nonneg (Real.exp_nonneg _)
      (Real.sin_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos, hz'.1], by nlinarith [pi_pos, hz'.2]⟩)
  have h₂ : (exp (-I * π * θ)).im = -Real.sin (π * θ) := by
    have : -I * ↑π * ↑θ = ((-(π * θ) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I, Real.sin_neg]
    simp [-ofReal_cos, -ofReal_sin]
  have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])
  linarith

private theorem stripToUnitDisc_ne_one {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    stripToUnitDisc θ z ≠ 1 := by
  rw [stripToUnitDisc_def, ne_eq,
    div_eq_one_iff_eq (exp_I_pi_mul_sub_exp_neg_I_pi_ne_zero hθ hz), sub_right_inj]
  exact fun h ↦ exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ (sub_eq_zero.2 h)

private theorem unitDiscToExpStrip_stripToUnitDisc {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    unitDiscToExpStrip θ (stripToUnitDisc θ z) = exp (I * π * z) := by
  have hne1 : 1 - stripToUnitDisc θ z ≠ 0 := sub_ne_zero.2 (stripToUnitDisc_ne_one hθ hz).symm
  have hden : exp (I * π * z) - exp (-(I * π * θ)) ≠ 0 := by
    simpa [neg_mul] using exp_I_pi_mul_sub_exp_neg_I_pi_ne_zero hθ hz
  rw [unitDiscToExpStrip, div_eq_iff hne1, stripToUnitDisc_def]
  simp only [neg_mul]
  field_simp [hden]
  ring

private theorem abs_re_unitDiscToExpStrip_of_mem_sphere (θ : ℝ) {w : ℂ}
    (hw : w ∈ sphere 0 1) (hw1 : w ≠ 1) :
    |(unitDiscToExpStrip θ w).re| = ‖unitDiscToExpStrip θ w‖ := by
  have hww : w * star w = 1 := by
    rw [RCLike.star_def, mul_conj, normSq_eq_norm_sq, mem_sphere_zero_iff_norm.1 hw,
      one_pow, ofReal_one]
  have h1w : 1 - w ≠ 0 := sub_ne_zero.2 hw1.symm
  have h1sw : 1 - star w ≠ 0 := fun h ↦ h1w (by simpa using congrArg star h)
  have hζ : star (exp (I * π * θ)) = exp (-I * π * θ) := by
    rw [RCLike.star_def, ← exp_conj]; congr 1; simp
  have hζ' : star (exp (-I * π * θ)) = exp (I * π * θ) := by
    rw [RCLike.star_def, ← exp_conj]; congr 1; simp
  have hself : star (unitDiscToExpStrip θ w) = unitDiscToExpStrip θ w := by
    rw [unitDiscToExpStrip, star_div₀, star_sub, star_mul, star_sub, star_one, hζ, hζ',
      div_eq_div_iff h1sw h1w]
    linear_combination (exp (I * ↑π * ↑θ) - exp (-I * ↑π * ↑θ)) * hww
  have him : (unitDiscToExpStrip θ w).im = 0 := by
    have := congrArg Complex.im hself
    simp only [RCLike.star_def, conj_im] at this
    linarith
  rw [← Complex.re_add_im (unitDiscToExpStrip θ w), him]
  simp

/-- Glues two functions `u₀, u₁ : ℝ → ℝ` equal to `c₀` near `±∞` into a single function on
`sphere 0 1` agreeing with `u₀` and `u₁` along the left and right strip boundary arcs. -/
private def glueBoundary (θ c₀ : ℝ) (u₀ u₁ : ℝ → ℝ) (w : ℂ) : ℝ :=
  let x := (unitDiscToExpStrip θ w).re
  if w = 1 ∨ x = 0 then c₀
  else if 0 < x then u₀ (-Real.log x / π)
  else u₁ (-Real.log (-x) / π)

private theorem glueBoundary_stripToUnitDisc_mul_I {θ c₀ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (u₀ u₁ : ℝ → ℝ) (t : ℝ) :
    glueBoundary θ c₀ u₀ u₁ (stripToUnitDisc θ (t * I)) = u₀ t := by
  have hz : t * I ∈ verticalClosedStrip 0 1 := by simp [mem_verticalClosedStrip_iff]
  have hw1 := stripToUnitDisc_ne_one hθ hz
  have hexp : unitDiscToExpStrip θ (stripToUnitDisc θ (t * I)) = (Real.exp (-π * t) : ℂ) := by
    rw [unitDiscToExpStrip_stripToUnitDisc hθ hz]
    have : I * ↑π * (↑t * I) = ((-π * t : ℝ) : ℂ) := by
      calc I * ↑π * (↑t * I) = ↑π * ↑t * (I * I) := by ring
        _ = ((-π * t : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
    rw [this, ofReal_exp]
  have hx : (unitDiscToExpStrip θ (stripToUnitDisc θ (t * I))).re = Real.exp (-π * t) := by
    rw [hexp, ofReal_re]
  have hpos : 0 < Real.exp (-π * t) := Real.exp_pos _
  simp only [glueBoundary, hx, hw1, hpos.ne', or_self, ↓reduceIte, hpos, Real.log_exp]
  congr 1
  field_simp [pi_pos.ne']

private theorem glueBoundary_stripToUnitDisc_one_add_mul_I {θ c₀ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (u₀ u₁ : ℝ → ℝ) (t : ℝ) :
    glueBoundary θ c₀ u₀ u₁ (stripToUnitDisc θ (1 + t * I)) = u₁ t := by
  have hz : 1 + t * I ∈ verticalClosedStrip 0 1 := by simp [mem_verticalClosedStrip_iff]
  have hw1 := stripToUnitDisc_ne_one hθ hz
  have hexp : unitDiscToExpStrip θ (stripToUnitDisc θ (1 + t * I)) = -(Real.exp (-π * t) : ℂ) := by
    rw [unitDiscToExpStrip_stripToUnitDisc hθ hz]
    have : I * ↑π * (1 + ↑t * I) = ((-π * t : ℝ) : ℂ) + ↑π * I := by
      calc I * ↑π * (1 + ↑t * I) = ↑π * ↑t * (I * I) + ↑π * I := by ring
        _ = ((-π * t : ℝ) : ℂ) + ↑π * I := by rw [I_mul_I]; push_cast; ring
    rw [this, Complex.exp_add, exp_pi_mul_I, ofReal_exp, mul_neg_one]
  have hx : (unitDiscToExpStrip θ (stripToUnitDisc θ (1 + t * I))).re = -Real.exp (-π * t) := by
    rw [hexp, neg_re, ofReal_re]
  have hneg : -Real.exp (-π * t) < 0 := neg_lt_zero.2 (Real.exp_pos _)
  simp only [glueBoundary, hx, hw1, hneg.ne, or_self, ↓reduceIte, not_lt.2 hneg.le, neg_neg,
    Real.log_exp]
  congr 1
  field_simp [pi_pos.ne']

private theorem glueBoundary_eq_const_of_abs_log {θ c₀ T : ℝ} {u₀ u₁ : ℝ → ℝ}
    (hT : ∀ t, T ≤ |t| → u₀ t = c₀ ∧ u₁ t = c₀) {w : ℂ}
    (hlog : w = 1 ∨ (unitDiscToExpStrip θ w).re = 0 ∨
      π * T ≤ |Real.log (|(unitDiscToExpStrip θ w).re|)|) :
    glueBoundary θ c₀ u₀ u₁ w = c₀ := by
  dsimp only [glueBoundary]
  rcases hlog with hw | hx | hbig
  · simp [hw]
  · simp [hx]
  · split_ifs with h0 hpos
    · rfl
    · refine (hT _ ?_).1
      rw [abs_of_pos hpos] at hbig
      rw [abs_div, abs_neg, abs_of_pos pi_pos, le_div_iff₀ pi_pos]
      linarith
    · have hneg : (unitDiscToExpStrip θ w).re < 0 :=
        lt_of_le_of_ne (not_lt.1 hpos) (not_or.1 h0).2
      refine (hT _ ?_).2
      rw [abs_of_neg hneg] at hbig
      rw [abs_div, abs_neg, abs_of_pos pi_pos, le_div_iff₀ pi_pos]
      linarith

private theorem continuousWithinAt_glueBoundary_one {θ c₀ T : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u₀ u₁ : ℝ → ℝ} (hT : ∀ t, T ≤ |t| → u₀ t = c₀ ∧ u₁ t = c₀) :
    ContinuousWithinAt (glueBoundary θ c₀ u₀ u₁) (sphere 0 1) 1 := by
  have hpos : 0 < ‖exp (I * π * θ) - (1 : ℂ) * exp (-I * π * θ)‖ := by
    simpa using norm_pos_iff.2 (exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ)
  have hfn : Continuous fun w : ℂ ↦ ‖exp (I * π * θ) - w * exp (-I * π * θ)‖ := by fun_prop
  have hnum_ev : ∀ᶠ w in 𝓝 (1 : ℂ),
      ‖exp (I * π * θ) - (1 : ℂ) * exp (-I * π * θ)‖ / 2 <
        ‖exp (I * π * θ) - w * exp (-I * π * θ)‖ :=
    (hfn.tendsto 1).eventually_const_lt (half_lt_self hpos)
  have hfd : Continuous fun w : ℂ ↦ ‖(1 : ℂ) - w‖ := by fun_prop
  have hden_ev : ∀ᶠ w in 𝓝 (1 : ℂ),
      ‖(1 : ℂ) - w‖ <
        (‖exp (I * π * θ) - (1 : ℂ) * exp (-I * π * θ)‖ / 2) / Real.exp (π * T) :=
    (hfd.tendsto 1).eventually_lt_const
      (by simp only [sub_self, norm_zero]; exact div_pos (half_pos hpos) (Real.exp_pos _))
  refine (continuousWithinAt_const (b := c₀)).congr_of_eventuallyEq ?_ (by simp [glueBoundary])
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnum_ev,
    eventually_nhdsWithin_of_eventually_nhds hden_ev] with w hw hnum hden
  refine glueBoundary_eq_const_of_abs_log hT ?_
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  · right; right
    have h1w : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hw1))
    have hgt : Real.exp (π * T) < |(unitDiscToExpStrip θ w).re| := by
      rw [abs_re_unitDiscToExpStrip_of_mem_sphere θ hw hw1, unitDiscToExpStrip, norm_div,
        lt_div_iff₀ h1w]
      have := (lt_div_iff₀ (Real.exp_pos (π * T))).1 hden
      linarith
    have hlog := Real.log_le_log (Real.exp_pos _) hgt.le
    rw [Real.log_exp] at hlog
    exact hlog.trans (le_abs_self _)

private theorem continuousOn_glueBoundary {θ c₀ : ℝ} (hθ : θ ∈ Ioo 0 1) {u₀ u₁ : ℝ → ℝ}
    (hu₀c : Continuous u₀) (hu₁c : Continuous u₁)
    (hu₀ : ∀ᶠ t in cocompact ℝ, u₀ t = c₀) (hu₁ : ∀ᶠ t in cocompact ℝ, u₁ t = c₀) :
    ContinuousOn (glueBoundary θ c₀ u₀ u₁) (sphere 0 1) := by
  obtain ⟨K, hKc, hK⟩ := Filter.mem_cocompact.1 (hu₀.and hu₁)
  obtain ⟨T₀, hT₀⟩ := hKc.isBounded.subset_closedBall 0
  set T := max T₀ 0 + 1
  have hT : ∀ t, T ≤ |t| → u₀ t = c₀ ∧ u₁ t = c₀ := fun t ht ↦
    hK fun htK ↦ by
      have hle : |t| ≤ T₀ := by simpa [Real.norm_eq_abs] using mem_closedBall_zero_iff.1 (hT₀ htK)
      linarith [le_max_left T₀ 0]
  intro w₀ _
  by_cases hw₀1 : w₀ = 1
  · exact hw₀1 ▸ continuousWithinAt_glueBoundary_one hθ hT
  have hcx : ContinuousAt (fun w ↦ (unitDiscToExpStrip θ w).re) w₀ := by
    unfold unitDiscToExpStrip
    exact Complex.continuous_re.continuousAt.comp
      ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).div
        (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 (Ne.symm hw₀1)))
  rcases lt_trichotomy ((unitDiscToExpStrip θ w₀).re) 0 with hneg | hzero | hpos
  · have hlx : ContinuousAt (fun w ↦ Real.log (-(unitDiscToExpStrip θ w).re)) w₀ :=
      (Real.continuousAt_log (neg_pos.2 hneg).ne').comp
        (f := fun w ↦ -(unitDiscToExpStrip θ w).re) hcx.neg
    have hcont : ContinuousAt (fun w ↦ u₁ (-Real.log (-(unitDiscToExpStrip θ w).re) / π)) w₀ :=
      hu₁c.continuousAt.comp (f := fun w ↦ -Real.log (-(unitDiscToExpStrip θ w).re) / π)
        (hlx.neg.div_const π)
    refine (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hw₀1, hcx.eventually_lt_const hneg] with w hw1 hlt
    simp only [glueBoundary, hw1, hlt.ne, or_self, ↓reduceIte, not_lt.2 hlt.le]
  · refine (continuousWithinAt_const (b := c₀)).congr_of_eventuallyEq ?_
      (by simp [glueBoundary, hzero])
    have habs : ContinuousAt (fun w ↦ |(unitDiscToExpStrip θ w).re|) w₀ :=
      continuous_abs.continuousAt.comp (f := fun w ↦ (unitDiscToExpStrip θ w).re) hcx
    have hev : ∀ᶠ w in 𝓝 w₀, |(unitDiscToExpStrip θ w).re| < Real.exp (-π * T) :=
      habs.eventually_lt_const (by dsimp only; rw [hzero, abs_zero]; exact Real.exp_pos _)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with w hw
    refine glueBoundary_eq_const_of_abs_log hT ?_
    by_cases hx : (unitDiscToExpStrip θ w).re = 0
    · exact Or.inr (Or.inl hx)
    · right; right
      have hlog := Real.log_le_log (abs_pos.2 hx) hw.le
      rw [Real.log_exp] at hlog
      exact (le_neg.2 (by linarith)).trans (neg_le_abs _)
  · have hlx : ContinuousAt (fun w ↦ Real.log ((unitDiscToExpStrip θ w).re)) w₀ :=
      (Real.continuousAt_log hpos.ne').comp (f := fun w ↦ (unitDiscToExpStrip θ w).re) hcx
    have hcont : ContinuousAt (fun w ↦ u₀ (-Real.log ((unitDiscToExpStrip θ w).re) / π)) w₀ :=
      hu₀c.continuousAt.comp (f := fun w ↦ -Real.log ((unitDiscToExpStrip θ w).re) / π)
        (hlx.neg.div_const π)
    refine (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hw₀1, hcx.eventually_const_lt hpos] with w hw1 hgt
    simp only [glueBoundary, hw1, hgt.ne', or_self, ↓reduceIte, hgt]

/-! ### Bounded holomorphic multipliers and Jensen inequalities -/

private theorem le_of_forall_pos_le {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = b)
    (h : ∀ ε > 0, a ≤ f ε) : a ≤ b :=
  ge_of_tendsto (hf0 ▸ (hf.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (eventually_nhdsWithin_of_forall h)

private theorem integrable_log_max_of_zeroAtInfty {X : Type*} [NormedAddCommGroup X]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (f : C₀(ℝ, X)) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t ↦ Real.log (max ‖f t‖ ε)) μ := by
  have hmax_pos (t : ℝ) : 0 < max ‖f t‖ ε := lt_max_of_lt_right hε
  refine Integrable.of_bound
    (((continuous_norm.comp f.continuous).max continuous_const).log
      fun t ↦ (hmax_pos t).ne').aestronglyMeasurable
    (|Real.log ε| + |Real.log (max ‖f‖ ε)|) (Eventually.of_forall fun t ↦ ?_)
  have h₁ := Real.log_le_log hε (le_max_right ‖f t‖ ε)
  have h₂ := Real.log_le_log (hmax_pos t)
    (max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t))
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log (max ‖f‖ ε))],
    by linarith [abs_nonneg (Real.log ε), le_abs_self (Real.log (max ‖f‖ ε))]⟩

/-- Jensen inequality on a probability space for `t ↦ log (max ‖f t‖ ε)` with `f ∈ C₀(ℝ, X)`. -/
private theorem exp_mul_integral_log_max_le {X : Type*} [NormedAddCommGroup X]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : C₀(ℝ, X)) {α p ε : ℝ}
    (hα : 0 ≤ α) (hp : 0 < p) (hε : 0 < ε) :
    Real.exp (α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ) ≤
      ((∫ t, ‖f t‖ ^ p ∂μ) + ε ^ p) ^ (α / p) := by
  set w : ℝ → ℝ := fun t ↦ p * Real.log (max ‖f t‖ ε)
  have hmax_pos (t : ℝ) : 0 < max ‖f t‖ ε := lt_max_of_lt_right hε
  have hw_int : Integrable w μ := (integrable_log_max_of_zeroAtInfty f hε).const_mul p
  have hexp_eq : Real.exp ∘ w = fun t ↦ (max ‖f t‖ ε) ^ p := by
    ext t; simp only [Function.comp_apply, w, Real.rpow_def_of_pos (hmax_pos t), mul_comm p]
  have hexp_int : Integrable (Real.exp ∘ w) μ := by
    rw [hexp_eq]
    refine Integrable.of_bound
      (((continuous_norm.comp f.continuous).max continuous_const).rpow_const
        fun _ ↦ Or.inr hp.le).aestronglyMeasurable
      ((max ‖f‖ ε) ^ p) (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hmax_pos t).le _)]
    exact Real.rpow_le_rpow (hmax_pos t).le
      (max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t)) hp.le
  have hf_int : Integrable (fun t ↦ ‖f t‖ ^ p) μ := by
    refine Integrable.of_bound
      ((continuous_norm.comp f.continuous).rpow_const fun _ ↦ Or.inr hp.le).aestronglyMeasurable
      (‖f‖ ^ p) (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (ZeroAtInftyContinuousMap.norm_coe_le_norm f t) hp.le
  have hjensen : Real.exp (∫ t, w t ∂μ) ≤ (∫ t, ‖f t‖ ^ p ∂μ) + ε ^ p := by
    have hpt (t : ℝ) : (Real.exp ∘ w) t ≤ ‖f t‖ ^ p + ε ^ p := by
      rw [hexp_eq]; dsimp only
      rcases le_total ‖f t‖ ε with hle | hle
      · rw [max_eq_right hle]; exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
      · rw [max_eq_left hle]; exact le_add_of_nonneg_right (Real.rpow_nonneg hε.le _)
    refine (convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (Eventually.of_forall fun _ ↦ mem_univ _) hw_int hexp_int).trans ?_
    refine (integral_mono hexp_int (hf_int.add (integrable_const (ε ^ p))) hpt).trans_eq ?_
    rw [Pi.add_def, integral_add hf_int (integrable_const (ε ^ p)), integral_const, probReal_univ,
      one_smul]
  have hpow := Real.rpow_le_rpow (Real.exp_nonneg _) hjensen (div_nonneg hα hp.le)
  rw [← Real.exp_mul] at hpow
  have harg : (∫ t, w t ∂μ) * (α / p) = α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ := by
    simp only [w, integral_const_mul]; field_simp [hp.ne']
  rwa [harg] at hpow

/-- Supremum bound on a probability space for `t ↦ log (max ‖f t‖ ε)` with `f ∈ C₀(ℝ, X)`. -/
private theorem exp_mul_integral_log_max_le_norm {X : Type*} [NormedAddCommGroup X]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : C₀(ℝ, X)) {α ε : ℝ}
    (hα : 0 ≤ α) (hε : 0 < ε) :
    Real.exp (α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ) ≤ (max ‖f‖ ε) ^ α := by
  have hle : ∫ t, Real.log (max ‖f t‖ ε) ∂μ ≤ Real.log (max ‖f‖ ε) := by
    refine (integral_mono (integrable_log_max_of_zeroAtInfty f hε) (integrable_const _) fun t ↦
      Real.log_le_log (lt_max_of_lt_right hε)
        (max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t))).trans_eq ?_
    rw [integral_const, probReal_univ, one_smul]
  rw [Real.rpow_def_of_pos (lt_max_of_lt_right hε), mul_comm _ α]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle hα)

/-- Multiplying an admissible strip function by a bounded function `c` differentiable on the
closed strip produces an admissible strip function with traces `(t ↦ c (t * I) • g.1 t,
t ↦ c (1 + t * I) • g.2 t)`. -/
theorem CompatibleCouple.IsStripFunction.exists_smul_of_differentiableOn
    {X₀ X₁ V : Type*} [NormedAddCommGroup X₀] [NormedSpace ℂ X₀]
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
    {C : CompatibleCouple ℂ X₀ X₁ V} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) {c : ℂ → ℂ} {K : ℝ}
    (hc : DifferentiableOn ℂ c (verticalClosedStrip 0 1))
    (hK : ∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) :
    ∃ g' : C₀(ℝ, X₀) × C₀(ℝ, X₁),
      C.IsStripFunction (fun z ↦ c z • F z) g' ∧
      (∀ t, g'.1 t = c (t * I) • g.1 t) ∧
      (∀ t, g'.2 t = c (1 + t * I) • g.2 t) := by
  refine ⟨(⟨⟨fun t ↦ c (t * I) • g.1 t,
      (hc.continuousOn.comp_continuous (by fun_prop)
        fun t ↦ by simp [mem_verticalClosedStrip_iff]).smul g.1.continuous⟩,
    squeeze_zero_norm
      (fun t ↦ (norm_smul _ _).trans_le (mul_le_mul_of_nonneg_right
        (hK _ (by simp [mem_verticalClosedStrip_iff])) (norm_nonneg _)))
      (by simpa using (tendsto_norm_zero.comp (zero_at_infty g.1)).const_mul K)⟩,
    ⟨⟨fun t ↦ c (1 + t * I) • g.2 t,
      (hc.continuousOn.comp_continuous (by fun_prop)
        fun t ↦ by simp [mem_verticalClosedStrip_iff]).smul g.2.continuous⟩,
    squeeze_zero_norm
      (fun t ↦ (norm_smul _ _).trans_le (mul_le_mul_of_nonneg_right
        (hK _ (by simp [mem_verticalClosedStrip_iff])) (norm_nonneg _)))
      (by simpa using (tendsto_norm_zero.comp (zero_at_infty g.2)).const_mul K)⟩), ?_,
    fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact hF.smul ⟨hc.mono (verticalStrip_subset_verticalClosedStrip 0 1),
    hc.continuousOn.mono (closure_verticalStrip_subset 0 1)⟩
    (fun _ hz ↦ hK _ hz) (fun _ ↦ rfl) (fun _ ↦ rfl)

namespace CompatibleCouple.ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

/-- Constructs the radial Herglotz–Riesz scalar multiplier on the vertical strip associated to
continuous boundary data `ψ` on `sphere 0 1`. -/
private theorem exists_herglotz_multiplier {θ δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hδ : 0 < δ)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (sphere 0 1)) :
    ∃ (r : ℝ) (c : ℂ → ℂ) (K : ℝ), r ∈ Ioo 0 1 ∧
      DifferentiableOn ℂ c (verticalClosedStrip 0 1) ∧
      (∀ z ∈ verticalClosedStrip 0 1, ‖c z‖ ≤ K) ∧
      c θ = 1 ∧
      (∀ ζ ∈ sphere 0 |1|, |ψ ζ - planarPoissonIntegral ψ 0 1 ((r : ℂ) * ζ)| < δ) ∧
      ∀ z ∈ verticalClosedStrip 0 1,
        ‖c z‖ = Real.exp (circleAverage ψ 0 1 -
          planarPoissonIntegral ψ 0 1 ((r : ℂ) * stripToUnitDisc θ z)) := by
  have hψ' : ContinuousOn ψ (sphere 0 |1|) := by simpa using hψ
  have hψi : CircleIntegrable ψ 0 1 := hψ'.circleIntegrable'
  have hψic : CircleIntegrable (fun ζ ↦ (ψ ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hψi ⊢
    exact Complex.ofRealCLM.integrable_comp hψi
  let H : ℂ → ℂ := fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (ψ ζ : ℂ)) 0 1
  have hH_re {w : ℂ} (hw : w ∈ ball 0 1) : (H w).re = planarPoissonIntegral ψ 0 1 w := by
    rw [planarPoissonIntegral_def, poissonKernel_eq_re_herglotzRieszKernel]
    exact re_circleAverage_herglotzRieszKernel_smul hψi
      (by simpa using (mem_ball_zero_iff.1 hw).ne)
  have hH0 : (H 0).re = circleAverage ψ 0 1 := by
    rw [hH_re (mem_ball_self zero_lt_one), planarPoissonIntegral_def]
    exact circleAverage_congr_sphere fun ζ hζ ↦ by
      simp [poissonKernel_def, show ‖ζ‖ = 1 by simpa using hζ]
  have hunif := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_planarPoissonIntegral_mul one_ne_zero hψ') δ hδ
  obtain ⟨r, hr_dist, hr_mem⟩ := (hunif.and (Ioo_mem_nhdsLT zero_lt_one)).exists
  let c : ℂ → ℂ := fun z ↦ exp (H 0 - H ((r : ℂ) * stripToUnitDisc θ z))
  have hc_ball {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      (r : ℂ) * stripToUnitDisc θ z ∈ closedBall 0 r := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_of_nonneg hr_mem.1.le]
    exact mul_le_of_le_one_right hr_mem.1.le (norm_stripToUnitDisc_le_one hθ hz)
  have hcb_sub : closedBall (0 : ℂ) r ⊆ (sphere 0 |1|)ᶜ := fun w hw ↦ by
    simp only [mem_compl_iff, mem_sphere_zero_iff_norm, abs_one]
    exact ((mem_closedBall_zero_iff.1 hw).trans_lt hr_mem.2).ne
  have hc_diff : DifferentiableOn ℂ c (verticalClosedStrip 0 1) := fun z hz ↦ by
    have hdH := (hasDerivAt_circleAverage_herglotzRieszKernel_smul hψic
      (hcb_sub (hc_ball hz))).differentiableAt
    have hdr := (differentiableAt_stripToUnitDisc hθ hz).const_mul (r : ℂ)
    exact ((differentiableAt_const _).sub (hdH.comp z hdr)).cexp.differentiableWithinAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (continuous_exp.comp_continuousOn (continuousOn_const.sub
      ((differentiableOn_circleAverage_herglotzRieszKernel_smul hψic).continuousOn.mono hcb_sub)))
  refine ⟨r, c, K, hr_mem, hc_diff, fun _ hz ↦ hK _ (hc_ball hz), by simp [c], ?_, ?_⟩
  · intro ζ hζ
    simpa [Real.dist_eq, Complex.real_smul] using hr_dist ζ hζ
  · intro z hz
    rw [Complex.norm_exp, sub_re, hH0, hH_re (closedBall_subset_ball hr_mem.2 (hc_ball hz))]

/-- Radial Herglotz–Riesz multiplier bound for an admissible function on the strip. -/
private theorem norm_le_exp_circleAverage_add {θ ε δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (hδ : 0 < δ) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (sphere 0 1))
    (hψ₀ : ∀ t, Real.log (max ‖g.1 t‖ ε) ≤ ψ (stripToUnitDisc θ (t * I)))
    (hψ₁ : ∀ t, Real.log (max ‖g.2 t‖ ε) ≤ ψ (stripToUnitDisc θ (1 + t * I))) :
    ‖u‖ ≤ Real.exp (circleAverage ψ 0 1 + δ) := by
  obtain ⟨r, c, K, _, hc_diff, hK, hcθ, hr_dist, hc_norm⟩ := exists_herglotz_multiplier hθ hδ hψ
  obtain ⟨g', hsmul, hg'₀, hg'₁⟩ := hF.exists_smul_of_differentiableOn hc_diff hK
  refine (norm_le_of_toSum_eq ⟨hθ.1.le, hθ.2.le⟩ hsmul (by simp [hcθ, hu])).trans ?_
  refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (Real.exp_nonneg _)).2 fun t ↦ ?_,
    (ZeroAtInftyContinuousMap.norm_le (Real.exp_nonneg _)).2 fun t ↦ ?_⟩
  · have hd := hr_dist _ (by simpa using stripToUnitDisc_mul_I_mem_sphere hθ t)
    rw [hg'₀, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    calc Real.exp (circleAverage ψ 0 1 -
          planarPoissonIntegral ψ 0 1 ((r : ℂ) * stripToUnitDisc θ (t * I))) * ‖g.1 t‖
      _ ≤ Real.exp (circleAverage ψ 0 1 + δ - Real.log (max ‖g.1 t‖ ε)) * max ‖g.1 t‖ ε :=
          mul_le_mul (Real.exp_le_exp.2 (by linarith [(abs_lt.1 hd).2, hψ₀ t]))
            (le_max_left _ _) (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (circleAverage ψ 0 1 + δ) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
            Real.exp_log (lt_max_of_lt_right hε),
            inv_mul_cancel_right₀ (lt_max_of_lt_right hε).ne']
  · have hd := hr_dist _ (by simpa using stripToUnitDisc_one_add_mul_I_mem_sphere hθ t)
    rw [hg'₁, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    calc Real.exp (circleAverage ψ 0 1 -
          planarPoissonIntegral ψ 0 1 ((r : ℂ) * stripToUnitDisc θ (1 + t * I))) * ‖g.2 t‖
      _ ≤ Real.exp (circleAverage ψ 0 1 + δ - Real.log (max ‖g.2 t‖ ε)) * max ‖g.2 t‖ ε :=
          mul_le_mul (Real.exp_le_exp.2 (by linarith [(abs_lt.1 hd).2, hψ₁ t]))
            (le_max_left _ _) (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (circleAverage ψ 0 1 + δ) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
            Real.exp_log (lt_max_of_lt_right hε),
            inv_mul_cancel_right₀ (lt_max_of_lt_right hε).ne']

/-- **Calderón's log-convexity inequality (Bergh–Löfström, Lemma 4.3.2).**
For `0 < θ < 1`, `ε > 0`, and any admissible strip function `F` with boundary traces `g` and
`toSum u = F θ`, the norm in `[X₀, X₁]_θ` is bounded by the exponential of the sum of the two
boundary integrals against `stripPoissonKernel₀ θ` and `stripPoissonKernel₁ θ`. -/
theorem norm_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.2 t‖ ε)) := by
  let u₀ : ℝ → ℝ := fun t ↦ Real.log (max ‖g.1 t‖ ε)
  let u₁ : ℝ → ℝ := fun t ↦ Real.log (max ‖g.2 t‖ ε)
  have hu₀_c : Continuous u₀ :=
    ((continuous_norm.comp g.1.continuous).max continuous_const).log
      fun _ ↦ (lt_max_of_lt_right hε).ne'
  have hu₁_c : Continuous u₁ :=
    ((continuous_norm.comp g.2.continuous).max continuous_const).log
      fun _ ↦ (lt_max_of_lt_right hε).ne'
  have hu₀_inf : ∀ᶠ t in cocompact ℝ, u₀ t = Real.log ε := by
    filter_upwards [(tendsto_norm_zero.comp (zero_at_infty g.1)).eventually_lt_const hε] with t ht
    change ‖g.1 t‖ < ε at ht
    simp only [u₀, max_eq_right ht.le]
  have hu₁_inf : ∀ᶠ t in cocompact ℝ, u₁ t = Real.log ε := by
    filter_upwards [(tendsto_norm_zero.comp (zero_at_infty g.2)).eventually_lt_const hε] with t ht
    change ‖g.2 t‖ < ε at ht
    simp only [u₁, max_eq_right ht.le]
  let ψ := glueBoundary θ (Real.log ε) u₀ u₁
  have hψ : ContinuousOn ψ (sphere 0 1) :=
    continuousOn_glueBoundary hθ hu₀_c hu₁_c hu₀_inf hu₁_inf
  have hψi : CircleIntegrable ψ 0 1 :=
    (by simpa using hψ : ContinuousOn ψ (sphere 0 |1|)).circleIntegrable'
  have hca : circleAverage ψ 0 1 =
      (∫ t, stripPoissonKernel₀ θ t * u₀ t) + ∫ t, stripPoissonKernel₁ θ t * u₁ t := by
    rw [circleAverage_eq_stripPoissonKernel hθ hψi]
    dsimp only [ψ]
    simp_rw [smul_eq_mul, glueBoundary_stripToUnitDisc_mul_I hθ u₀ u₁,
      glueBoundary_stripToUnitDisc_one_add_mul_I hθ u₀ u₁]
  rw [← hca]
  exact le_of_forall_pos_le (by fun_prop) (by simp) fun δ hδ ↦
    norm_le_exp_circleAverage_add hθ hε hδ hF hu hψ
      (fun t ↦ (glueBoundary_stripToUnitDisc_mul_I hθ u₀ u₁ t).ge)
      (fun t ↦ (glueBoundary_stripToUnitDisc_one_add_mul_I hθ u₀ u₁ t).ge)

/-- Calderón's log-convexity inequality applied to `mk θ g`. -/
theorem norm_mk_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.1.2 t‖ ε)) :=
  norm_le_exp_integral_stripPoissonKernel hθ hε (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

private theorem norm_le_exp_stripPoissonMeasure {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ Real.exp ((1 - θ) * ∫ t, Real.log (max ‖g.1 t‖ ε) ∂stripPoissonMeasure₀ θ) *
      Real.exp (θ * ∫ t, Real.log (max ‖g.2 t‖ ε) ∂stripPoissonMeasure₁ θ) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  refine (norm_le_exp_integral_stripPoissonKernel hθ hε hF hu).trans_eq ?_
  rw [Real.exp_add, integral_stripPoissonMeasure₀ hθ, integral_stripPoissonMeasure₁ hθ]
  simp_rw [smul_eq_mul]
  rw [mul_inv_cancel_left₀ h1θ.ne', mul_inv_cancel_left₀ hθ.1.ne']

/-- **`(L^{p₀}, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.**
For `0 < θ < 1` and `0 < p₀, p₁ < ∞`, any admissible strip function `F` with boundary traces `g`
and `toSum u = F θ` satisfies
`‖u‖ ≤ (∫ ‖g₀ t‖ ^ p₀ dP₀) ^ ((1 - θ) / p₀) * (∫ ‖g₁ t‖ ^ p₁ dP₁) ^ (θ / p₁)`,
where `P₀ = stripPoissonMeasure₀ θ` and `P₁ = stripPoissonMeasure₁ θ`. -/
theorem norm_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) := by
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  refine le_of_forall_pos_le
    (f := fun ε ↦ ((∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) + ε ^ p₀) ^ ((1 - θ) / p₀) *
      ((∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) + ε ^ p₁) ^ (θ / p₁))
    (((continuous_const.add (Real.continuous_rpow_const hp₀.le)).rpow_const
      fun _ ↦ Or.inr (div_nonneg h1θ.le hp₀.le)).mul
      ((continuous_const.add (Real.continuous_rpow_const hp₁.le)).rpow_const
        fun _ ↦ Or.inr (div_nonneg hθ.1.le hp₁.le)))
    (by simp [Real.zero_rpow hp₀.ne', Real.zero_rpow hp₁.ne']) fun ε hε ↦ ?_
  refine (norm_le_exp_stripPoissonMeasure hθ hε hF hu).trans ?_
  exact mul_le_mul (exp_mul_integral_log_max_le g.1 h1θ.le hp₀ hε)
    (exp_mul_integral_log_max_le g.2 hθ.1.le hp₁ hε) (Real.exp_nonneg _)
    (Real.rpow_nonneg (add_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg hε.le _)) _)

/-- `(L^{p₀}, L^{p₁})` strip Poisson bound applied to `mk θ g`. -/
theorem norm_mk_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (g : C.stripTraces) :
    ‖mk θ g‖ ≤ (∫ t, ‖g.1.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.1.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_rpow_integral_stripPoissonMeasure hθ hp₀ hp₁ (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

/-- **Mixed `(L^∞, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure {θ p₁ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ ‖g.1‖ ^ (1 - θ) * (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) := by
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  refine le_of_forall_pos_le
    (f := fun ε ↦ (max ‖g.1‖ ε) ^ (1 - θ) *
      ((∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) + ε ^ p₁) ^ (θ / p₁))
    (((continuous_const.max continuous_id).rpow_const fun _ ↦ Or.inr h1θ.le).mul
      ((continuous_const.add (Real.continuous_rpow_const hp₁.le)).rpow_const
        fun _ ↦ Or.inr (div_nonneg hθ.1.le hp₁.le)))
    (by simp [Real.zero_rpow hp₁.ne']) fun ε hε ↦ ?_
  refine (norm_le_exp_stripPoissonMeasure hθ hε hF hu).trans ?_
  exact mul_le_mul (exp_mul_integral_log_max_le_norm g.1 h1θ.le hε)
    (exp_mul_integral_log_max_le g.2 hθ.1.le hp₁ hε) (Real.exp_nonneg _)
    (Real.rpow_nonneg (lt_max_of_lt_right hε).le _)

/-- **Mixed `(L^{p₀}, L^∞)` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow {θ p₀ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₀ : 0 < p₀) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) * ‖g.2‖ ^ θ := by
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  refine le_of_forall_pos_le
    (f := fun ε ↦ ((∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) + ε ^ p₀) ^ ((1 - θ) / p₀) *
      (max ‖g.2‖ ε) ^ θ)
    (((continuous_const.add (Real.continuous_rpow_const hp₀.le)).rpow_const
      fun _ ↦ Or.inr (div_nonneg h1θ.le hp₀.le)).mul
      ((continuous_const.max continuous_id).rpow_const fun _ ↦ Or.inr hθ.1.le))
    (by simp [Real.zero_rpow hp₀.ne']) fun ε hε ↦ ?_
  refine (norm_le_exp_stripPoissonMeasure hθ hε hF hu).trans ?_
  exact mul_le_mul (exp_mul_integral_log_max_le g.1 h1θ.le hp₀ hε)
    (exp_mul_integral_log_max_le_norm g.2 hθ.1.le hε) (Real.exp_nonneg _)
    (Real.rpow_nonneg (add_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg hε.le _)) _)

/-- **`L¹` strip Poisson bound (Calderón–Hirschman).**
Specializing `norm_le_rpow_integral_stripPoissonMeasure` to `p₀ = p₁ = 1` bounds `‖u‖` directly
in terms of `stripPoissonKernel₀ θ` and `stripPoissonKernel₁ θ`. -/
theorem norm_le_integral_stripPoissonKernel {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ ((1 - θ)⁻¹ * ∫ t, stripPoissonKernel₀ θ t * ‖g.1 t‖) ^ (1 - θ) *
      (θ⁻¹ * ∫ t, stripPoissonKernel₁ θ t * ‖g.2 t‖) ^ θ := by
  have h := norm_le_rpow_integral_stripPoissonMeasure hθ one_pos one_pos hF hu
  simpa [div_one, Real.rpow_one, integral_stripPoissonMeasure₀ hθ,
    integral_stripPoissonMeasure₁ hθ, smul_eq_mul] using h

end CompatibleCouple.ComplexMethodSpace

end TauCeti

end
