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

Pulling the Herglotz–Riesz integral on `ball 0 1` back along `TauCeti.stripToUnitDisc` refines the
three-lines bound on `[X₀, X₁]_θ` to Calderón's log-convexity inequality (Bergh–Löfström,
Lemma 4.3.2): for `0 < θ < 1` and `ε > 0`,
`‖u‖ ≤ exp (∫ μ₀(θ, t) log (max ‖g₀ t‖ ε) dt + ∫ μ₁(θ, t) log (max ‖g₁ t‖ ε) dt)`.
Applying Jensen's inequality (`ConvexOn.map_integral_le` for `Real.exp`) to `stripPoissonMeasure₀ θ`
and `stripPoissonMeasure₁ θ` and letting `ε → 0⁺` yields `(L^{p₀}, L^{p₁})` and mixed `(L^∞, L^p)`
bounds on `[X₀, X₁]_θ` without completeness, density of the intersection, or duality.

## Main results

* `TauCeti.CompatibleCouple.IsStripFunction.exists_smul_of_differentiableOn`:
  bounded holomorphic scalar multiplier lemma for admissible strip functions.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_exp_integral_stripPoissonKernel`:
  Calderón's log-convexity bound for `[X₀, X₁]_θ`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_le_rpow_integral_stripPoissonMeasure`,
  `norm_le_norm_fst_rpow_mul_rpow_integral_stripPoissonMeasure`,
  `norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow`, and
  `norm_le_integral_stripPoissonKernel`: `(L^{p₀}, L^{p₁})`, mixed, and `L¹` strip Poisson bounds.

## References

* I. I. Hirschman, *A convexity theorem for certain groups of transformations*, J. Analyse Math.
  **2** (1952), 209–218.
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. **24**
  (1964), 113–190, §9.4.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, Lemma 4.3.2.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open Filter MeasureTheory Metric Real Set
open scoped ENNReal Topology ZeroAtInfty

namespace TauCeti

/-! ### Gluing strip boundary data onto the unit circle -/

private def unitDiscToExpStrip (θ : ℝ) (w : ℂ) : ℂ :=
  (exp (I * π * θ) - w * exp (-I * π * θ)) / (1 - w)

private theorem sub_exp_neg_I_pi_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {w : ℂ} (hw : 0 ≤ w.im) :
    w - exp (-I * π * θ) ≠ 0 := fun h ↦ by
  have him := congrArg Complex.im (sub_eq_zero.1 h)
  have hθ' : (exp (-I * π * θ)).im = -Real.sin (π * θ) := by
    have : -I * ↑π * ↑θ = ((-(π * θ) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I, Real.sin_neg]; simp [-ofReal_cos, -ofReal_sin]
  linarith [Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])]

private theorem exp_I_pi_sub_exp_neg_I_pi_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    exp (I * π * θ) - exp (-I * π * θ) ≠ 0 :=
  sub_exp_neg_I_pi_ne_zero hθ <| by
    have : I * ↑π * ↑θ = ((π * θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_ofReal_mul_I]
    simpa [-ofReal_cos, -ofReal_sin] using
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hθ.1) (by nlinarith [pi_pos, hθ.2])).le

private theorem cayley_ofReal {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (r : ℝ) :
    ((r : ℂ) - exp (I * π * θ)) / ((r : ℂ) - exp (-I * π * θ)) ≠ 1 ∧
      (unitDiscToExpStrip θ (((r : ℂ) - exp (I * π * θ)) / ((r : ℂ) - exp (-I * π * θ)))).re =
        r := by
  have hden : (r : ℂ) - exp (-I * π * θ) ≠ 0 := sub_exp_neg_I_pi_ne_zero hθ (by simp)
  have hne1 : ((r : ℂ) - exp (I * π * θ)) / ((r : ℂ) - exp (-I * π * θ)) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hden, sub_right_inj]
    exact fun h ↦ exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ (sub_eq_zero.2 h)
  refine ⟨hne1, ?_⟩
  have heq : unitDiscToExpStrip θ (((r : ℂ) - exp (I * π * θ)) / ((r : ℂ) - exp (-I * π * θ))) =
      (r : ℂ) := by
    rw [unitDiscToExpStrip]; set ζ := exp (I * π * θ); set ζ' := exp (-I * π * θ)
    rw [div_eq_iff (sub_ne_zero.2 hne1.symm)]; field_simp [hden]; ring
  rw [heq, ofReal_re]

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
  have hζ' : star (exp (-I * π * θ)) = exp (I * π * θ) := by rw [← hζ, star_involutive]
  have hself : star (unitDiscToExpStrip θ w) = unitDiscToExpStrip θ w := by
    rw [unitDiscToExpStrip, star_div₀, star_sub, star_mul, star_sub, star_one, hζ, hζ',
      div_eq_div_iff h1sw h1w]
    linear_combination (exp (I * ↑π * ↑θ) - exp (-I * ↑π * ↑θ)) * hww
  have him : (unitDiscToExpStrip θ w).im = 0 := by
    have := congrArg Complex.im hself; simp only [RCLike.star_def, conj_im] at this; linarith
  rw [← Complex.re_add_im (unitDiscToExpStrip θ w), him]; simp

private def glueBoundary (θ c₀ : ℝ) (u₀ u₁ : ℝ → ℝ) (w : ℂ) : ℝ :=
  let x := (unitDiscToExpStrip θ w).re
  if w = 1 ∨ x = 0 then c₀
  else if 0 < x then u₀ (-Real.log x / π)
  else u₁ (-Real.log (-x) / π)

private theorem glueBoundary_stripToUnitDisc_mul_I {θ c₀ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (u₀ u₁ : ℝ → ℝ) (t : ℝ) :
    glueBoundary θ c₀ u₀ u₁ (stripToUnitDisc θ (t * I)) = u₀ t := by
  have harg : exp (I * ↑π * (↑t * I)) = (Real.exp (-π * t) : ℂ) := by
    have : I * ↑π * (↑t * I) = ((-π * t : ℝ) : ℂ) := by
      push_cast; linear_combination (π * t : ℂ) * I_mul_I
    rw [this, ofReal_exp]
  obtain ⟨hne1, hx⟩ := cayley_ofReal hθ (Real.exp (-π * t))
  have hpos : 0 < Real.exp (-π * t) := Real.exp_pos _
  rw [stripToUnitDisc_def, harg]
  simp only [glueBoundary, hx, hne1, hpos.ne', or_self, ↓reduceIte, hpos, Real.log_exp]
  congr 1; field_simp [pi_pos.ne']

private theorem glueBoundary_stripToUnitDisc_one_add_mul_I {θ c₀ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (u₀ u₁ : ℝ → ℝ) (t : ℝ) :
    glueBoundary θ c₀ u₀ u₁ (stripToUnitDisc θ (1 + t * I)) = u₁ t := by
  have harg : exp (I * ↑π * (1 + ↑t * I)) = ((-Real.exp (-π * t) : ℝ) : ℂ) := by
    have : I * ↑π * (1 + ↑t * I) = ((-π * t : ℝ) : ℂ) + ↑π * I := by
      push_cast; linear_combination (π * t : ℂ) * I_mul_I
    rw [this, Complex.exp_add, exp_pi_mul_I, ofReal_neg, ofReal_exp, mul_neg_one]
  obtain ⟨hne1, hx⟩ := cayley_ofReal hθ (-Real.exp (-π * t))
  have hneg : -Real.exp (-π * t) < 0 := neg_lt_zero.2 (Real.exp_pos _)
  rw [stripToUnitDisc_def, harg]
  simp only [glueBoundary, hx, hne1, hneg.ne, or_self, ↓reduceIte, not_lt.2 hneg.le, neg_neg,
    Real.log_exp]
  congr 1; field_simp [pi_pos.ne']

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
    · rw [abs_of_pos hpos] at hbig
      exact (hT _ (by rw [abs_div, abs_neg, abs_of_pos pi_pos, le_div_iff₀ pi_pos]; linarith)).1
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 hpos) (not_or.1 h0).2)] at hbig
      exact (hT _ (by rw [abs_div, abs_neg, abs_of_pos pi_pos, le_div_iff₀ pi_pos]; linarith)).2

private theorem continuousWithinAt_glueBoundary_one {θ c₀ T : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u₀ u₁ : ℝ → ℝ} (hT : ∀ t, T ≤ |t| → u₀ t = c₀ ∧ u₁ t = c₀) :
    ContinuousWithinAt (glueBoundary θ c₀ u₀ u₁) (sphere 0 1) 1 := by
  have hpos : 0 < ‖exp (I * π * θ) - (1 : ℂ) * exp (-I * π * θ)‖ := by
    simpa using norm_pos_iff.2 (exp_I_pi_sub_exp_neg_I_pi_ne_zero hθ)
  have hfn : Continuous fun w : ℂ ↦ ‖exp (I * π * θ) - w * exp (-I * π * θ)‖ := by fun_prop
  have hfd : Continuous fun w : ℂ ↦ ‖(1 : ℂ) - w‖ := by fun_prop
  have hnum_ev := (hfn.tendsto 1).eventually_const_lt (half_lt_self hpos)
  have hden_ev := (hfd.tendsto 1).eventually_lt_const
    (by simp only [sub_self, norm_zero]; exact div_pos (half_pos hpos) (Real.exp_pos (π * T)))
  refine (continuousWithinAt_const (b := c₀)).congr_of_eventuallyEq ?_ (by simp [glueBoundary])
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnum_ev,
    eventually_nhdsWithin_of_eventually_nhds hden_ev] with w hw hnum hden
  refine glueBoundary_eq_const_of_abs_log hT ?_
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  have hgt : Real.exp (π * T) < |(unitDiscToExpStrip θ w).re| := by
    rw [abs_re_unitDiscToExpStrip_of_mem_sphere θ hw hw1, unitDiscToExpStrip, norm_div,
      lt_div_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hw1)))]
    linarith [(lt_div_iff₀ (Real.exp_pos (π * T))).1 hden]
  exact Or.inr <| Or.inr <|
    (Real.log_exp (π * T) ▸ Real.log_le_log (Real.exp_pos _) hgt.le).trans (le_abs_self _)

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
  · have hlx := (Real.continuousAt_log (neg_pos.2 hneg).ne').comp
      (f := fun w ↦ -(unitDiscToExpStrip θ w).re) hcx.neg
    refine ((hu₁c.continuousAt.comp (f := fun w ↦ -Real.log (-(unitDiscToExpStrip θ w).re) / π)
      (hlx.neg.div_const π)).congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hw₀1, hcx.eventually_lt_const hneg] with w hw1 hlt
    simp [glueBoundary, hw1, hlt.ne, not_lt.2 hlt.le]
  · refine (continuousWithinAt_const (b := c₀)).congr_of_eventuallyEq ?_
      (by simp [glueBoundary, hzero])
    have hev : ∀ᶠ w in 𝓝 w₀, |(unitDiscToExpStrip θ w).re| < Real.exp (-π * T) :=
      (continuous_abs.continuousAt.comp hcx).eventually_lt_const (by simp [hzero, Real.exp_pos])
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with w hw
    refine glueBoundary_eq_const_of_abs_log hT ?_
    by_cases hx : (unitDiscToExpStrip θ w).re = 0
    · exact Or.inr (Or.inl hx)
    have hlog := Real.log_exp (-π * T) ▸ Real.log_le_log (abs_pos.2 hx) hw.le
    exact Or.inr <| Or.inr <| (le_neg.2 (by linarith)).trans (neg_le_abs _)
  · have hlx := (Real.continuousAt_log hpos.ne').comp
      (f := fun w ↦ (unitDiscToExpStrip θ w).re) hcx
    refine ((hu₀c.continuousAt.comp (f := fun w ↦ -Real.log ((unitDiscToExpStrip θ w).re) / π)
      (hlx.neg.div_const π)).congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [eventually_ne_nhds hw₀1, hcx.eventually_const_lt hpos] with w hw1 hgt
    simp [glueBoundary, hw1, hgt.ne', hgt]

/-! ### Bounded holomorphic multipliers and Jensen inequalities -/

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
  have hbnd {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (h0 : ∀ t, 0 ≤ g t) (hM : ∀ t, g t ≤ M) :
      Integrable (fun t ↦ g t ^ p) μ :=
    Integrable.of_bound (hg.rpow_const fun _ ↦ Or.inr hp.le).aestronglyMeasurable (M ^ p)
      (Eventually.of_forall fun t ↦ (Real.norm_of_nonneg (Real.rpow_nonneg (h0 t) _)).trans_le
        (Real.rpow_le_rpow (h0 t) (hM t) hp.le))
  have hexp_int : Integrable (Real.exp ∘ w) μ := hexp_eq ▸ hbnd
    ((continuous_norm.comp f.continuous).max continuous_const) (fun t ↦ (hmax_pos t).le)
    fun t ↦ max_le_max_right ε (ZeroAtInftyContinuousMap.norm_coe_le_norm f t)
  have hf_int : Integrable (fun t ↦ ‖f t‖ ^ p) μ := hbnd (continuous_norm.comp f.continuous)
    (fun _ ↦ norm_nonneg _) (ZeroAtInftyContinuousMap.norm_coe_le_norm f)
  have hjensen : Real.exp (∫ t, w t ∂μ) ≤ (∫ t, ‖f t‖ ^ p ∂μ) + ε ^ p := by
    have hpt (t : ℝ) : (Real.exp ∘ w) t ≤ ‖f t‖ ^ p + ε ^ p := by
      rw [hexp_eq]; dsimp only
      rcases le_total ‖f t‖ ε with hle | hle
      · rw [max_eq_right hle]; exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
      · rw [max_eq_left hle]; exact le_add_of_nonneg_right (Real.rpow_nonneg hε.le _)
    refine (convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (Eventually.of_forall fun _ ↦ mem_univ _) hw_int hexp_int).trans <|
      (integral_mono hexp_int (hf_int.add (integrable_const (ε ^ p))) hpt).trans_eq ?_
    rw [Pi.add_def, integral_add hf_int (integrable_const (ε ^ p)), integral_const, probReal_univ,
      one_smul]
  have hpow := Real.rpow_le_rpow (Real.exp_nonneg _) hjensen (div_nonneg hα hp.le)
  rw [← Real.exp_mul] at hpow
  have harg : (∫ t, w t ∂μ) * (α / p) = α * ∫ t, Real.log (max ‖f t‖ ε) ∂μ := by
    simp only [w, integral_const_mul]; field_simp [hp.ne']
  rwa [harg] at hpow

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

private def smulBoundaryTrace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : C₀(ℝ, X)) {φ : ℝ → ℂ} (hφ : Continuous φ) {K : ℝ} (hK : ∀ t, ‖φ t‖ ≤ K) : C₀(ℝ, X) :=
  ⟨⟨fun t ↦ φ t • f t, hφ.smul f.continuous⟩,
    squeeze_zero_norm
      (fun t ↦ (norm_smul _ _).trans_le (mul_le_mul_of_nonneg_right (hK t) (norm_nonneg _)))
      (by simpa using (tendsto_norm_zero.comp (zero_at_infty f)).const_mul K)⟩

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
    ∃ g' : C₀(ℝ, X₀) × C₀(ℝ, X₁), C.IsStripFunction (fun z ↦ c z • F z) g' ∧
      (∀ t, g'.1 t = c (t * I) • g.1 t) ∧ ∀ t, g'.2 t = c (1 + t * I) • g.2 t :=
  have hc0 : Continuous fun t : ℝ ↦ c (t * I) :=
    hc.continuousOn.comp_continuous (by fun_prop) fun _ ↦ by simp [mem_verticalClosedStrip_iff]
  have hc1 : Continuous fun t : ℝ ↦ c (1 + t * I) :=
    hc.continuousOn.comp_continuous (by fun_prop) fun _ ↦ by simp [mem_verticalClosedStrip_iff]
  ⟨(smulBoundaryTrace g.1 hc0 fun _ ↦ hK _ (by simp [mem_verticalClosedStrip_iff]),
    smulBoundaryTrace g.2 hc1 fun _ ↦ hK _ (by simp [mem_verticalClosedStrip_iff])),
    hF.smul ⟨hc.mono (verticalStrip_subset_verticalClosedStrip 0 1),
      hc.continuousOn.mono (closure_verticalStrip_subset 0 1)⟩
      (fun _ hz ↦ hK _ hz) (fun _ ↦ rfl) (fun _ ↦ rfl), fun _ ↦ rfl, fun _ ↦ rfl⟩

namespace CompatibleCouple.ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

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
    exact re_circleAverage_herglotzRieszKernel_smul hψi (by simpa using (mem_ball_zero_iff.1 hw).ne)
  have hH0 : (H 0).re = circleAverage ψ 0 1 := by
    rw [hH_re (mem_ball_self zero_lt_one), planarPoissonIntegral_def]
    exact circleAverage_congr_sphere fun ζ hζ ↦ by
      have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
      simp [poissonKernel_def, hζ1]
  obtain ⟨r, hr_dist, hr_mem⟩ := ((Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_planarPoissonIntegral_mul one_ne_zero hψ') δ hδ).and
    (Ioo_mem_nhdsLT zero_lt_one)).exists
  let c : ℂ → ℂ := fun z ↦ exp (H 0 - H ((r : ℂ) * stripToUnitDisc θ z))
  have hc_ball {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
      (r : ℂ) * stripToUnitDisc θ z ∈ closedBall 0 r := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_of_nonneg hr_mem.1.le]
    exact mul_le_of_le_one_right hr_mem.1.le (norm_stripToUnitDisc_le_one hθ hz)
  have hcb_sub : closedBall (0 : ℂ) r ⊆ (sphere 0 |1|)ᶜ := fun w hw ↦ by
    simp only [mem_compl_iff, mem_sphere_zero_iff_norm, abs_one]
    exact ((mem_closedBall_zero_iff.1 hw).trans_lt hr_mem.2).ne
  have hc_diff : DifferentiableOn ℂ c (verticalClosedStrip 0 1) := fun z hz ↦
    ((differentiableAt_const _).sub
      ((hasDerivAt_circleAverage_herglotzRieszKernel_smul hψic
        (hcb_sub (hc_ball hz))).differentiableAt.comp z
        ((differentiableAt_stripToUnitDisc hθ hz).const_mul (r : ℂ)))).cexp.differentiableWithinAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (continuous_exp.comp_continuousOn (continuousOn_const.sub
      ((differentiableOn_circleAverage_herglotzRieszKernel_smul hψic).continuousOn.mono hcb_sub)))
  refine ⟨r, c, K, hr_mem, hc_diff, fun _ hz ↦ hK _ (hc_ball hz), by simp [c],
    fun ζ hζ ↦ by simpa [Real.dist_eq, Complex.real_smul] using hr_dist ζ hζ, fun z hz ↦ ?_⟩
  rw [Complex.norm_exp, sub_re, hH0, hH_re (closedBall_subset_ball hr_mem.2 (hc_ball hz))]

private theorem norm_le_exp_circleAverage_add {θ ε δ : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (hδ : 0 < δ) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (sphere 0 1))
    (hψ₀ : ∀ t, Real.log (max ‖g.1 t‖ ε) ≤ ψ (stripToUnitDisc θ (t * I)))
    (hψ₁ : ∀ t, Real.log (max ‖g.2 t‖ ε) ≤ ψ (stripToUnitDisc θ (1 + t * I))) :
    ‖u‖ ≤ Real.exp (circleAverage ψ 0 1 + δ) := by
  obtain ⟨r, c, K, _, hc_diff, hK, hcθ, hr_dist, hc_norm⟩ := exists_herglotz_multiplier hθ hδ hψ
  obtain ⟨g', hsmul, hg'₀, hg'₁⟩ := hF.exists_smul_of_differentiableOn hc_diff hK
  have hpt {x a p : ℝ} (hx : 0 ≤ x) (hd : |a - p| < δ) (hlog : Real.log (max x ε) ≤ a) :
      Real.exp (circleAverage ψ 0 1 - p) * x ≤ Real.exp (circleAverage ψ 0 1 + δ) :=
    (mul_le_mul (b := Real.exp (circleAverage ψ 0 1 + δ - Real.log (max x ε)))
      (Real.exp_le_exp.2 (by linarith [(abs_lt.1 hd).2])) (le_max_left x ε) hx
      (Real.exp_nonneg _)).trans_eq <| by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log (lt_max_of_lt_right hε),
          inv_mul_cancel_right₀ (lt_max_of_lt_right hε).ne']
  refine (norm_le_of_toSum_eq ⟨hθ.1.le, hθ.2.le⟩ hsmul (by simp [hcθ, hu])).trans <|
    norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (Real.exp_nonneg _)).2 fun t ↦ ?_,
      (ZeroAtInftyContinuousMap.norm_le (Real.exp_nonneg _)).2 fun t ↦ ?_⟩
  · rw [hg'₀, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    exact hpt (norm_nonneg _) (hr_dist _ (by simpa using stripToUnitDisc_mul_I_mem_sphere hθ t))
      (hψ₀ t)
  · rw [hg'₁, norm_smul, hc_norm _ (by simp [mem_verticalClosedStrip_iff])]
    exact hpt (norm_nonneg _)
      (hr_dist _ (by simpa using stripToUnitDisc_one_add_mul_I_mem_sphere hθ t)) (hψ₁ t)

private theorem continuous_and_eventually_log_max {X : Type*} [NormedAddCommGroup X]
    (f : C₀(ℝ, X)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t ↦ Real.log (max ‖f t‖ ε)) ∧
      ∀ᶠ t in cocompact ℝ, Real.log (max ‖f t‖ ε) = Real.log ε :=
  ⟨((continuous_norm.comp f.continuous).max continuous_const).log
    fun _ ↦ (lt_max_of_lt_right hε).ne',
    ((tendsto_norm_zero.comp (zero_at_infty f)).eventually_lt_const hε).mono fun _ ht ↦ by
      simp only [Function.comp_apply] at ht; rw [max_eq_right ht.le]⟩

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
  let ψ := glueBoundary θ (Real.log ε) u₀ u₁
  have hl₀ := continuous_and_eventually_log_max g.1 hε
  have hl₁ := continuous_and_eventually_log_max g.2 hε
  have hψ : ContinuousOn ψ (sphere 0 1) :=
    continuousOn_glueBoundary hθ hl₀.1 hl₁.1 hl₀.2 hl₁.2
  have hψi : CircleIntegrable ψ 0 1 :=
    (by simpa using hψ : ContinuousOn ψ (sphere 0 |1|)).circleIntegrable'
  have hca : circleAverage ψ 0 1 =
      (∫ t, stripPoissonKernel₀ θ t * u₀ t) + ∫ t, stripPoissonKernel₁ θ t * u₁ t := by
    rw [circleAverage_eq_stripPoissonKernel hθ hψi]
    simp_rw [ψ, smul_eq_mul, glueBoundary_stripToUnitDisc_mul_I hθ u₀ u₁,
      glueBoundary_stripToUnitDisc_one_add_mul_I hθ u₀ u₁]
  rw [← hca]
  have hcont : Continuous (fun δ : ℝ ↦ Real.exp (circleAverage ψ 0 1 + δ)) := by fun_prop
  refine ge_of_tendsto
    (by simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (eventually_nhdsWithin_of_forall fun δ hδ ↦
      norm_le_exp_circleAverage_add hθ hε hδ hF hu hψ
        (fun t ↦ (glueBoundary_stripToUnitDisc_mul_I hθ u₀ u₁ t).ge)
        (fun t ↦ (glueBoundary_stripToUnitDisc_one_add_mul_I hθ u₀ u₁ t).ge))

/-- Calderón's log-convexity inequality applied to `mk θ g`. -/
theorem norm_mk_le_exp_integral_stripPoissonKernel {θ ε : ℝ} (hθ : θ ∈ Ioo 0 1) (hε : 0 < ε)
    (g : C.stripTraces) :
    ‖mk θ g‖ ≤ Real.exp ((∫ t, stripPoissonKernel₀ θ t * Real.log (max ‖g.1.1 t‖ ε)) +
      ∫ t, stripPoissonKernel₁ θ t * Real.log (max ‖g.1.2 t‖ ε)) :=
  norm_le_exp_integral_stripPoissonKernel hθ hε (C.isStripFunction_stripFunction g)
    (by simp [stripEval_apply])

private theorem norm_le_of_stripPoissonMeasure {θ b₀ b₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) {φ₀ φ₁ : ℝ → ℝ}
    (ht₀ : Tendsto φ₀ (𝓝[>] 0) (𝓝 b₀)) (ht₁ : Tendsto φ₁ (𝓝[>] 0) (𝓝 b₁))
    (h₀ : [IsProbabilityMeasure (stripPoissonMeasure₀ θ)] → ∀ ε > 0,
      Real.exp ((1 - θ) * ∫ t, Real.log (max ‖g.1 t‖ ε) ∂stripPoissonMeasure₀ θ) ≤ φ₀ ε)
    (h₁ : [IsProbabilityMeasure (stripPoissonMeasure₁ θ)] → ∀ ε > 0,
      Real.exp (θ * ∫ t, Real.log (max ‖g.2 t‖ ε) ∂stripPoissonMeasure₁ θ) ≤ φ₁ ε) :
    ‖u‖ ≤ b₀ * b₁ :=
  have := isProbabilityMeasure_stripPoissonMeasure₀ hθ
  have := isProbabilityMeasure_stripPoissonMeasure₁ hθ
  ge_of_tendsto (ht₀.mul ht₁) <| eventually_nhdsWithin_of_forall fun ε hε ↦ by
    refine ((norm_le_exp_integral_stripPoissonKernel hθ hε hF hu).trans_eq ?_).trans
      (mul_le_mul (h₀ ε hε) (h₁ ε hε) (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (h₀ ε hε)))
    rw [Real.exp_add, integral_stripPoissonMeasure₀ hθ, integral_stripPoissonMeasure₁ hθ]
    simp_rw [smul_eq_mul]
    rw [mul_inv_cancel_left₀ (sub_pos.2 hθ.2).ne', mul_inv_cancel_left₀ hθ.1.ne']

private theorem tendsto_add_rpow_nhdsGT (a : ℝ) {p α : ℝ} (hp : 0 < p) (hα : 0 ≤ α) :
    Tendsto (fun ε : ℝ ↦ (a + ε ^ p) ^ (α / p)) (𝓝[>] 0) (𝓝 (a ^ (α / p))) := by
  have hc : Continuous fun ε : ℝ ↦ (a + ε ^ p) ^ (α / p) :=
    (continuous_const.add (Real.continuous_rpow_const hp.le)).rpow_const
      fun _ ↦ Or.inr (div_nonneg hα hp.le)
  simpa [Real.zero_rpow hp.ne'] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))

private theorem tendsto_max_rpow_nhdsGT {a α : ℝ} (ha : 0 ≤ a) (hα : 0 ≤ α) :
    Tendsto (fun ε : ℝ ↦ (max a ε) ^ α) (𝓝[>] 0) (𝓝 (a ^ α)) := by
  have hc : Continuous fun ε : ℝ ↦ (max a ε) ^ α :=
    (continuous_const.max continuous_id).rpow_const fun _ ↦ Or.inr hα
  simpa [max_eq_left ha] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))

/-- **`(L^{p₀}, L^{p₁})` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure {θ p₀ p₁ : ℝ} (hθ : θ ∈ Ioo 0 1)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) *
      (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_of_stripPoissonMeasure hθ hF hu
    (tendsto_add_rpow_nhdsGT _ hp₀ (sub_nonneg.2 hθ.2.le)) (tendsto_add_rpow_nhdsGT _ hp₁ hθ.1.le)
    (fun _ ↦ exp_mul_integral_log_max_le g.1 (sub_nonneg.2 hθ.2.le) hp₀)
    (fun _ ↦ exp_mul_integral_log_max_le g.2 hθ.1.le hp₁)

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
    ‖u‖ ≤ ‖g.1‖ ^ (1 - θ) * (∫ t, ‖g.2 t‖ ^ p₁ ∂stripPoissonMeasure₁ θ) ^ (θ / p₁) :=
  norm_le_of_stripPoissonMeasure hθ hF hu
    (tendsto_max_rpow_nhdsGT (norm_nonneg g.1) (sub_nonneg.2 hθ.2.le))
    (tendsto_add_rpow_nhdsGT _ hp₁ hθ.1.le)
    (fun _ ↦ exp_mul_integral_log_max_le_norm g.1 (sub_nonneg.2 hθ.2.le))
    (fun _ ↦ exp_mul_integral_log_max_le g.2 hθ.1.le hp₁)

/-- **Mixed `(L^{p₀}, L^∞)` strip Poisson bound for `[X₀, X₁]_θ`.** -/
theorem norm_le_rpow_integral_stripPoissonMeasure_mul_norm_snd_rpow {θ p₀ : ℝ}
    (hθ : θ ∈ Ioo 0 1) (hp₀ : 0 < p₀) {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ (∫ t, ‖g.1 t‖ ^ p₀ ∂stripPoissonMeasure₀ θ) ^ ((1 - θ) / p₀) * ‖g.2‖ ^ θ :=
  norm_le_of_stripPoissonMeasure hθ hF hu
    (tendsto_add_rpow_nhdsGT _ hp₀ (sub_nonneg.2 hθ.2.le))
    (tendsto_max_rpow_nhdsGT (norm_nonneg g.2) hθ.1.le)
    (fun _ ↦ exp_mul_integral_log_max_le g.1 (sub_nonneg.2 hθ.2.le) hp₀)
    (fun _ ↦ exp_mul_integral_log_max_le_norm g.2 hθ.1.le)

/-- **`L¹` strip Poisson bound (Calderón–Hirschman).** -/
theorem norm_le_integral_stripPoissonKernel {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {u : C.ComplexMethodSpace θ} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : C.IsStripFunction F g) (hu : toSum u = F θ) :
    ‖u‖ ≤ ((1 - θ)⁻¹ * ∫ t, stripPoissonKernel₀ θ t * ‖g.1 t‖) ^ (1 - θ) *
      (θ⁻¹ * ∫ t, stripPoissonKernel₁ θ t * ‖g.2 t‖) ^ θ := by
  simpa [div_one, Real.rpow_one, integral_stripPoissonMeasure₀ hθ,
    integral_stripPoissonMeasure₁ hθ, smul_eq_mul] using
    norm_le_rpow_integral_stripPoissonMeasure hθ one_pos one_pos hF hu

end CompatibleCouple.ComplexMethodSpace

end TauCeti

end
