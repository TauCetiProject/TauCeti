/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The one-dimensional energy estimate for traces

A `C¹` function with values in a real normed space has both endpoint norms controlled
by its value and derivative energies on a finite interval, with an explicit width-dependent
constant. No compact support is needed for this finite-interval estimate.

For `1 ≤ r`, a compactly supported `C¹` curve in a real normed space has the `r`-th power
of the norm of its value at the endpoint of a half-line bounded by the integral of
`(r - 1) ‖g‖ʳ + ‖g'‖ʳ` on that half-line (`ContDiff.norm_rpow_le_integral_Ioi`); for `r = 2` this
is the `H¹` energy. Integrating this estimate over the transverse variables supplies the
flat-boundary `W^{1,p}` trace inequality. The energy density `(r - 1) ‖u‖ʳ + ‖Du‖ʳ` of a
compactly supported `C¹` function between normed spaces is continuous for `0 ≤ r` and has
compact support for every `r` (`ContDiff.continuous_rpow_energy`,
`HasCompactSupport.rpow_energy`).

Both estimates reduce to real-valued curves: composing with a continuous linear functional of
norm at most `1` that norms the endpoint value (Hahn–Banach) does not increase the energy.

The estimate follows the fundamental-theorem-of-calculus proof of the trace theorem in
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

namespace TauCeti

open MeasureTheory Set

/-- An affine weight `(t - m) / ℓ` of absolute value at most `1` on `[a, b]` controls the weighted
squares of `φ ∘ g` at `a` and `b` by the energy of `g` on `[a, b]`, for a curve `g` that is `C¹`
near `[a, b]` and a functional `φ` of norm at most `1`. -/
private theorem weighted_sq_sub_weighted_sq_le_integral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ → F} {a b m ℓ : ℝ} (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g t)
    (hab : a ≤ b) (hm : ∀ t ∈ Icc a b, |t - m| ≤ ℓ) (φ : StrongDual ℝ F) (hφ : ‖φ‖ ≤ 1) :
    (b - m) / ℓ * φ (g b) ^ 2 - (a - m) / ℓ * φ (g a) ^ 2 ≤
      ∫ t in a..b, (ℓ⁻¹ + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
  -- `ℓ ≥ 0` by `hm`; for `ℓ = 0` the left side is `0` (division by zero).
  rcases ((abs_nonneg _).trans (hm a (left_mem_Icc.2 hab))).eq_or_lt with rfl | hℓ
  · simp only [div_zero, zero_mul, sub_self]
    exact intervalIntegral.integral_nonneg hab fun t _ ↦ by positivity
  have hgc : ContinuousOn g (Icc a b) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv g) (Icc a b) :=
    fun t ht ↦ ((hg t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun t ↦ (t - m) / ℓ * φ (g t) ^ 2)
      (ℓ⁻¹ * φ (g t) ^ 2 + (t - m) / ℓ * (2 * φ (g t) * φ (deriv g t))) t := by
    have hφg : HasDerivAt (fun t ↦ φ (g t)) (φ (deriv g t)) t :=
      φ.hasFDerivAt.comp_hasDerivAt t ((hg t ht).differentiableAt one_ne_zero).hasDerivAt
    convert (((hasDerivAt_id' t).sub_const m).div_const ℓ).fun_mul (hφg.fun_pow 2) using 1
    ring
  have hint : IntervalIntegrable
      (fun t ↦ ℓ⁻¹ * φ (g t) ^ 2 + (t - m) / ℓ * (2 * φ (g t) * φ (deriv g t))) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      ((continuousOn_const.mul ((φ.continuous.comp_continuousOn hgc).pow 2)).add
        ((continuous_id.sub continuous_const).div_const ℓ |>.continuousOn.mul
          (continuousOn_const.mul (φ.continuous.comp_continuousOn hgc) |>.mul
            (φ.continuous.comp_continuousOn hdc))))
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hd t ((uIcc_of_le hab) ▸ ht)) hint]
  refine intervalIntegral.integral_mono_on hab hint
    (((continuousOn_const.mul (hgc.norm.pow 2)).add (hdc.norm.pow 2)).intervalIntegrable_of_Icc
      hab) fun t ht ↦ ?_
  -- Bound `φ ∘ g`, its derivative and the weight, then use `2 x y ≤ x ^ 2 + y ^ 2`.
  have hle (v : F) : |φ v| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs, one_mul] using φ.le_of_opNorm_le hφ v
  have hq : |(t - m) / ℓ| ≤ 1 := by
    rw [abs_div, abs_of_pos hℓ, div_le_one hℓ]
    exact hm t ht
  have hx := sq_le_sq' (abs_le.1 (hle (g t))).1 (abs_le.1 (hle (g t))).2
  have hy := sq_le_sq' (abs_le.1 (hle (deriv g t))).1 (abs_le.1 (hle (deriv g t))).2
  have hxy : (t - m) / ℓ * (2 * φ (g t) * φ (deriv g t)) ≤
      2 * (|φ (g t)| * |φ (deriv g t)|) :=
    (le_abs_self _).trans <| by
      rw [abs_mul, abs_mul, abs_mul, abs_two, mul_assoc]
      exact mul_le_of_le_one_left (by positivity) hq
  nlinarith [sq_nonneg (|φ (g t)| - |φ (deriv g t)|), sq_abs (φ (g t)),
    sq_abs (φ (deriv g t)), mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hℓ.le)]

/-- Both endpoint norms of a curve that is `C¹` near a closed interval are controlled by
its energy on that interval.
The coefficient of the value energy depends on the interval width; no compact support or
integrability outside the interval is required. -/
theorem norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} {a b : ℝ} (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g t)
    (hab : a < b) :
    ‖g a‖ ^ 2 + ‖g b‖ ^ 2 ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
  -- Split at the midpoint `m = (a + b) / 2`. On each half, project onto a functional norming the
  -- outer endpoint value and use the weight `(t - m) / ℓ` with `ℓ = (b - a) / 2`, which vanishes
  -- at `m`.
  obtain ⟨φ, hφ, hφa⟩ := exists_dual_vector'' ℝ (g a)
  obtain ⟨ψ, hψ, hψb⟩ := exists_dual_vector'' ℝ (g b)
  have hl := weighted_sq_sub_weighted_sq_le_integral (b := (a + b) / 2) (m := (a + b) / 2)
    (ℓ := (b - a) / 2)
    (fun t ht ↦ hg t ⟨ht.1, ht.2.trans (by linarith)⟩) (by linarith)
    (fun t ht ↦ abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩) φ hφ
  have hr := weighted_sq_sub_weighted_sq_le_integral (a := (a + b) / 2) (m := (a + b) / 2)
    (ℓ := (b - a) / 2)
    (fun t ht ↦ hg t ⟨(by linarith : a ≤ (a + b) / 2).trans ht.1, ht.2⟩) (by linarith)
    (fun t ht ↦ abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩) ψ hψ
  have hc : ((b - a) / 2)⁻¹ = 2 / (b - a) := inv_div _ _
  have hla : (a - (a + b) / 2) / ((b - a) / 2) = -1 := by
    field_simp [(sub_pos.2 hab).ne']; ring
  have hrb : (b - (a + b) / 2) / ((b - a) / 2) = 1 := by
    field_simp [(sub_pos.2 hab).ne']; ring
  simp only [sub_self, zero_div, zero_mul, hc, hla, hrb, hφa, hψb, RCLike.ofReal_real_eq_id,
    id_eq] at hl hr
  have hgc : ContinuousOn g (Icc a b) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv g) (Icc a b) :=
    fun t ht ↦ ((hg t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hE : ContinuousOn (fun t ↦ (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2) (Icc a b) :=
    (continuousOn_const.mul (hgc.norm.pow 2)).add (hdc.norm.pow 2)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (a + b) / 2)
    ((hE.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith))
    ((hE.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith))]
  linarith

section Energy

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- For `0 ≤ r`, the density `(r - 1) ‖u‖ʳ + ‖Du‖ʳ` of a `C¹` function is continuous. For
`1 ≤ r` this is the `Lʳ` energy density. -/
theorem _root_.ContDiff.continuous_rpow_energy {u : F → G} (hu : ContDiff ℝ 1 u) {r : ℝ}
    (hr : 0 ≤ r) : Continuous fun x ↦ (r - 1) * ‖u x‖ ^ r + ‖fderiv ℝ u x‖ ^ r :=
  (continuous_const.mul (hu.continuous.norm.rpow_const fun _ ↦ Or.inr hr)).add
    ((hu.continuous_fderiv one_ne_zero).norm.rpow_const fun _ ↦ Or.inr hr)

/-- The density `(r - 1) ‖u‖ʳ + ‖Du‖ʳ` of a compactly supported function has compact support,
for every exponent `r`. For `r = 0` it vanishes identically. -/
theorem _root_.HasCompactSupport.rpow_energy {u : F → G} (hsupp : HasCompactSupport u) (r : ℝ) :
    HasCompactSupport fun x ↦ (r - 1) * ‖u x‖ ^ r + ‖fderiv ℝ u x‖ ^ r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp only [Real.rpow_zero, zero_sub, mul_one, neg_add_cancel]
    exact HasCompactSupport.zero
  exact (hsupp.norm.rpow_const hr0).mul_left.add ((hsupp.fderiv ℝ).norm.rpow_const hr0)

/-- For `0 ≤ r`, the energy density of a compactly supported `C¹` curve is integrable. -/
private theorem _root_.ContDiff.integrable_rpow_energy {g : ℝ → G} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun t ↦ (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r) volume := by
  simpa only [← norm_deriv_eq_norm_fderiv] using
    (hg.continuous_rpow_energy hr).integrable_of_hasCompactSupport (hs.rpow_energy r)

end Energy

/-- The scalar case of `ContDiff.norm_rpow_le_integral_Ioi`. -/
private theorem _root_.ContDiff.norm_rpow_le_integral_Ioi_of_real {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖g a‖ ^ r ≤ ∫ t in Ioi a, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by
  rcases hr.eq_or_lt with rfl | hr1
  · -- For `r = 1`, this is Mathlib's endpoint bound on `Iic` for the reflected curve.
    simp only [Real.rpow_one, sub_self, zero_mul, zero_add]
    have h := (hs.comp_homeomorph (Homeomorph.neg ℝ)).eNorm_le_lintegral_Ici_deriv
      (hg.comp contDiff_neg) (-a)
    have hint : Integrable (fun t ↦ deriv g (-t)) volume :=
      ((hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hs.deriv).comp_neg
    simp only [Function.comp_def, neg_neg, deriv_comp_neg, eNorm_neg] at h
    rw [← ofReal_norm, ← ofReal_integral_norm_eq_lintegral_eNorm hint.integrableOn,
      integral_comp_neg_Iic (f := fun t ↦ ‖deriv g t‖), neg_neg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ norm_nonneg _)).1 h
  · -- For `r > 1`, integrate the derivative of the compactly supported `C¹` function `‖g‖ʳ`
    -- over `Ioi a`; it is bounded by `r ‖g‖ʳ⁻¹ ‖g'‖` and then by Young's inequality.
    have hv : ContDiff ℝ 1 (fun t ↦ ‖g t‖ ^ r) := hg.norm_rpow hr1
    have hvs : HasCompactSupport (fun t ↦ ‖g t‖ ^ r) :=
      hs.norm.rpow_const (zero_lt_one.trans hr1).ne'
    have hi := hvs.integral_Ioi_deriv_eq hv a
    have hdv : Integrable (fun t ↦ deriv (fun t ↦ ‖g t‖ ^ r) t) volume :=
      (hv.continuous_deriv le_rfl).integrable_of_hasCompactSupport hvs.deriv
    have hyoung : ∀ t, |deriv (fun t ↦ ‖g t‖ ^ r) t| ≤ (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by
      intro t
      have hd := norm_fderiv_norm_rpow_le (hg.differentiable one_ne_zero) (x := t) hr1
      rw [← norm_deriv_eq_norm_fderiv, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] at hd
      refine hd.trans ?_
      -- Young's inequality with the conjugate exponents `r / (r - 1)` and `r`.
      have hw := Real.young_inequality_of_nonneg (Real.rpow_nonneg (norm_nonneg (g t)) (r - 1))
        (norm_nonneg (deriv g t)) (Real.HolderConjugate.conjExponent hr1).symm
      rw [← Real.rpow_mul (norm_nonneg _), Real.conjExponent,
        mul_div_cancel₀ _ (sub_ne_zero.2 hr1.ne')] at hw
      calc r * ‖g t‖ ^ (r - 1) * ‖deriv g t‖ = r * (‖g t‖ ^ (r - 1) * ‖deriv g t‖) := by ring
        _ ≤ r * (‖g t‖ ^ r / (r / (r - 1)) + ‖deriv g t‖ ^ r / r) := by gcongr
        _ = (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by field_simp
    calc ‖g a‖ ^ r = ∫ t in Ioi a, -deriv (fun t ↦ ‖g t‖ ^ r) t := by
          rw [integral_neg, hi, neg_neg]
      _ ≤ ∫ t in Ioi a, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r :=
          integral_mono hdv.neg.integrableOn
            (hg.integrable_rpow_energy hs (zero_le_one.trans hr)).integrableOn
            fun t ↦ (neg_le_abs _).trans (hyoung t)

section Curve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The one-dimensional `Lᵖ` trace estimate.** For `1 ≤ r`, the `r`-th power of the norm of the
value at the endpoint of a half-line of a compactly supported `C¹` curve in a real normed space
is controlled by `(r - 1) ‖g‖ʳ + ‖g'‖ʳ` on that half-line. For `r = 2` the right side is
the `H¹` energy. -/
theorem _root_.ContDiff.norm_rpow_le_integral_Ioi {g : ℝ → E} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖g a‖ ^ r ≤ ∫ t in Ioi a, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r := by
  -- Apply the scalar case to `φ ∘ g` for a functional `φ` of norm at most `1` norming `g a`.
  obtain ⟨φ, hφ, hφa⟩ := exists_dual_vector'' ℝ (g a)
  have hle (v : E) : ‖φ v‖ ≤ ‖v‖ := (φ.le_of_opNorm_le hφ v).trans_eq (one_mul _)
  have hφg : ContDiff ℝ 1 (φ ∘ g) := φ.contDiff.comp hg
  have hφs : HasCompactSupport (φ ∘ g) := hs.comp_left φ.map_zero
  have hd (t : ℝ) : deriv (φ ∘ g) t = φ (deriv g t) :=
    (φ.hasFDerivAt.comp_hasDerivAt t ((hg.differentiable one_ne_zero t).hasDerivAt)).deriv
  have hr1 : 0 ≤ r := zero_le_one.trans hr
  calc ‖g a‖ ^ r = ‖(φ ∘ g) a‖ ^ r := by
        rw [Function.comp_apply, hφa, RCLike.ofReal_real_eq_id, id_eq, norm_norm]
    _ ≤ ∫ t in Ioi a, (r - 1) * ‖(φ ∘ g) t‖ ^ r + ‖deriv (φ ∘ g) t‖ ^ r :=
        hφg.norm_rpow_le_integral_Ioi_of_real hφs a hr
    _ ≤ ∫ t in Ioi a, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r :=
        setIntegral_mono (hφg.integrable_rpow_energy hφs hr1).integrableOn
          (hg.integrable_rpow_energy hs hr1).integrableOn fun t ↦ by
            have := sub_nonneg.2 hr
            simp only [Function.comp_apply, hd]
            gcongr <;> exact hle _

/-- For `1 ≤ r`, the `r`-th power of the norm of a point value of a compactly supported `C¹`
curve in a real normed space is controlled by `(r - 1) ‖g‖ʳ + ‖g'‖ʳ` on the whole line. -/
theorem _root_.ContDiff.norm_rpow_le_integral {g : ℝ → E} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ‖g a‖ ^ r ≤ ∫ t, (r - 1) * ‖g t‖ ^ r + ‖deriv g t‖ ^ r :=
  (hg.norm_rpow_le_integral_Ioi hs a hr).trans
    (setIntegral_le_integral (hg.integrable_rpow_energy hs (zero_le_one.trans hr))
      (.of_forall fun t ↦ by have := sub_nonneg.2 hr; positivity))

end Curve

end TauCeti
