/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Uniform `L^k` bounds for affine complex logarithms

For the affine family `t ↦ Complex.log (1 - t * z)` as `z : ℂ` varies over a bounded set
`‖z‖ ≤ R`, translating `|log |t - Re(z⁻¹)||` yields a uniform `L^k` bound on every bounded
interval `(a, b]`, even though the logarithmic singularity `t = z⁻¹` moves through `(a, b]`.

## Main declarations

* `TauCeti.setLIntegral_abs_log_abs_sub_pow_le`: bounds `∫⁻ t in (a, b], |log |t - s|| ^ k` for
  `s ∈ [c, d]` by `∫⁻ u in [a - d, b - c], |log ‖u‖| ^ k`.
* `TauCeti.setLIntegral_norm_clog_one_sub_mul_pow_le`: uniform `L^k` bound for `Log (1 - t * z)` on
  `(a, b]` when `0 < r ≤ ‖z‖ ≤ R`.
* `TauCeti.exists_setLIntegral_norm_clog_one_sub_mul_pow_le`: uniform finite `L^k` bound for
  `Log (1 - t * z)` on `(a, b]` over any bounded ball `‖z‖ ≤ R`.
-/

public section

namespace TauCeti

open MeasureTheory

open scoped ENNReal in
private lemma one_le_affineLogBound {T r R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    1 ≤ Real.log (1 + T * R) + |Real.log r| + Real.log (1 + R) + Real.pi := by
  linarith [Real.two_le_pi,
    Real.log_nonneg (by linarith [mul_nonneg hT hR] : (1 : ℝ) ≤ 1 + T * R),
    abs_nonneg (Real.log r), Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + R)]

/-- Translating by `s ∈ [c, d]` bounds the Lebesgue integral of `|log |t - s|| ^ k` over `(a, b]`
by the integral of `|log ‖u‖| ^ k` over `[a - d, b - c]`. -/
theorem setLIntegral_abs_log_abs_sub_pow_le (k : ℕ) {a b c d s : ℝ} (hs : s ∈ Set.Icc c d) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (|Real.log (|t - s|)| ^ k) ≤
      ∫⁻ u in Set.Icc (a - d) (b - c), ENNReal.ofReal (|Real.log ‖u‖| ^ k) := by
  have hsub : Set.Ioc a b ⊆ (fun t : ℝ ↦ -s + (1 : ℝ) • t) ⁻¹' Set.Icc (a - d) (b - c) := by
    intro t ht
    rw [Set.mem_preimage, smul_eq_mul, one_mul, neg_add_eq_sub]
    exact ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
  refine (lintegral_mono_set hsub).trans_eq ?_
  simpa [neg_add_eq_sub, Real.norm_eq_abs] using
    Measure.setLIntegral_comp_add_smul volume
      (fun u : ℝ ↦ ENNReal.ofReal (|Real.log ‖u‖| ^ k)) (-s) one_ne_zero
      (Set.Icc (a - d) (b - c))

/-- On `(a, b]`, when `0 < r ≤ ‖z‖ ≤ R`, shifting by `Re(z⁻¹) ∈ [-r⁻¹, r⁻¹]` bounds the `L^k`
integral of `t ↦ Complex.log (1 - t * z)` uniformly in `z`. -/
theorem setLIntegral_norm_clog_one_sub_mul_pow_le (k : ℕ) (a b : ℝ) {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hzr : r ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ k) ≤
      ENNReal.ofReal
        ((2 : ℝ) ^ (k - 1) *
          (Real.log (1 + max |a| |b| * R) + |Real.log r| + Real.log (1 + R) + Real.pi) ^ k) *
          volume (Set.Ioc a b) +
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) *
          ∫⁻ u in Set.Icc (a - r⁻¹) (b + r⁻¹), ENNReal.ofReal (|Real.log ‖u‖| ^ k) := by
  have hz_pos : 0 < ‖z‖ := hr.trans_le hzr
  have hR : 0 ≤ R := hz_pos.le.trans hzR
  set T : ℝ := max |a| |b|
  have hT : 0 ≤ T := le_max_of_le_left (abs_nonneg a)
  set M : ℝ := Real.log (1 + T * R) + |Real.log r| + Real.log (1 + R) + Real.pi
  have hM0 : 0 ≤ M := zero_le_one.trans (one_le_affineLogBound hT hR)
  have hs : (z⁻¹).re ∈ Set.Icc (-r⁻¹) r⁻¹ := by
    rw [Set.mem_Icc, ← abs_le]
    exact (Complex.abs_re_le_norm z⁻¹).trans ((norm_inv z).trans_le (inv_anti₀ hr hzr))
  have hlogz : |Real.log ‖z‖| ≤ |Real.log r| + Real.log (1 + R) := by
    have hlow := Real.log_le_log hr hzr
    have hhigh := Real.log_le_log hz_pos (by linarith : ‖z‖ ≤ 1 + R)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log r), abs_nonneg (Real.log r),
      Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + R)]
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc a b),
      ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ k) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * M ^ k) +
          ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) *
            ENNReal.ofReal (|Real.log (|t - (z⁻¹).re|)| ^ k) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume (z⁻¹).re)] with t ht hts
    have htT : |t| ≤ T := abs_le_max_abs_abs ht.1.le ht.2
    have hlogt : Real.log (1 + |t| * ‖z‖) ≤ Real.log (1 + T * R) :=
      Real.log_le_log (by positivity) (by linarith [mul_le_mul htT hzR hz_pos.le hT])
    have hbound : ‖Complex.log (1 - t * z)‖ ≤ M + |Real.log (|t - (z⁻¹).re|)| :=
      (Complex.norm_log_one_sub_ofReal_mul_le z hts).trans (by linarith)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal <| (pow_le_pow_left₀ (norm_nonneg _) hbound k).trans <| by
      simpa [mul_add] using add_pow_le hM0 (abs_nonneg _) k
  refine (lintegral_mono_ae hae).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul _ (by fun_prop)]
  gcongr _ + _ * ?_
  have hsub := setLIntegral_abs_log_abs_sub_pow_le k (a := a) (b := b) hs
  rwa [sub_neg_eq_add] at hsub

open scoped ENNReal in
/-- Over any bounded ball `‖z‖ ≤ R`, every natural power `‖Complex.log (1 - t * z)‖ ^ k` has a
uniform finite Lebesgue integral on `(a, b]` independent of `z`. -/
theorem exists_setLIntegral_norm_clog_one_sub_mul_pow_le (k : ℕ) (a b R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z : ℂ, ‖z‖ ≤ R →
      ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖Complex.log (1 - t * z)‖ ^ k) ≤ C := by
  set T : ℝ := max |a| |b|
  have hT : 0 ≤ T := le_max_of_le_left (abs_nonneg a)
  set R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  set r : ℝ := (2 * (T + 1))⁻¹ with hr_def
  have hr : 0 < r := by positivity
  set M : ℝ := Real.log (1 + T * R') + |Real.log r| + Real.log (1 + R') + Real.pi
  have hM : 1 ≤ M := one_le_affineLogBound hT hR'
  set I : ℝ≥0∞ := ∫⁻ u in Set.Icc (a - r⁻¹) (b + r⁻¹), ENNReal.ofReal (|Real.log ‖u‖| ^ k)
  have hI : I < ∞ := lt_of_le_of_lt
    (lintegral_mono fun u ↦ le_of_eq <| by
      rw [← ofReal_norm, norm_pow, Real.norm_eq_abs (Real.log _)])
    ((locallyIntegrable_log_norm_pow (E := ℝ) (μ := volume) k).integrableOn_isCompact
      isCompact_Icc).hasFiniteIntegral
  have hvol : volume (Set.Ioc a b) < ∞ := by simp [Real.volume_Ioc]
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * M ^ k) * volume (Set.Ioc a b) +
      ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) * I,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne⟩, fun z hz ↦ ?_⟩
  rcases le_or_gt ‖z‖ r with hsmall | hlarge
  · refine (setLIntegral_mono' measurableSet_Ioc
        (g := fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * M ^ k)) fun t ht ↦ ?_).trans ?_
    · have htT : |t| ≤ T := abs_le_max_abs_abs ht.1.le ht.2
      have htz : ‖-((t : ℂ) * z)‖ ≤ 1 / 2 := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine (mul_le_mul htT hsmall (norm_nonneg z) hT).trans ?_
        rw [hr_def, ← one_div, mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      have hlog : ‖Complex.log (1 - t * z)‖ ≤ M := by
        have h := Complex.norm_log_one_add_half_le_self (z := -((t : ℂ) * z)) htz
        rw [← sub_eq_add_neg] at h
        linarith [norm_nonneg (-((t : ℂ) * z))]
      exact ENNReal.ofReal_le_ofReal <| (pow_le_pow_left₀ (norm_nonneg _) hlog k).trans <|
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact le_self_add
  · exact setLIntegral_norm_clog_one_sub_mul_pow_le k a b hr hlarge.le
      (hz.trans (le_max_left R 0))

end TauCeti
