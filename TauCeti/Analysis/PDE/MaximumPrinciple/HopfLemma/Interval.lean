/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Hopf's boundary-point lemma for weak supersolutions on an interval

Let `L u = -(a u' + b u)' + c u' + d u` be a second-order operator in divergence form on an
interval `(l, r)`, with measurable coefficients satisfying `λ ≤ a ≤ Λ` for some `λ > 0` and
`|b| ≤ β`, and with `c ∈ L²(l, r)` and `d ∈ L¹(l, r)`. A function `u ∈ H¹(l, r)` is a weak
supersolution, `L u ≥ 0`, when

`0 ≤ ∫ ((a u' + b u) φ' + (c u' + d u) φ)`

for every nonnegative test function `φ` on `(l, r)`; for `L u = -u''` this says that `u` is
concave. This file proves **Hopf's boundary-point lemma** for such `u`: if `u` vanishes at `l` and
is positive on `(l, r)`, then `u` leaves `l` at a positive linear rate, `ε t ≤ u (l + t)` for some
`ε > 0` and all small `t > 0`. In particular a right derivative of `u` at `l`, if it exists, is
positive. The right endpoint is the left endpoint of the reflected problem.

In one dimension the coefficients need no continuity: bounded measurable `a` and `b` suffice. In
dimension two and higher the lemma fails for bounded measurable coefficients in divergence form,
and a Hölder modulus of `a` and `b` is needed. No sign condition on the lower-order coefficients is
needed either, because the boundary value is zero. The class `c ∈ L²` is the one for which `c u'`
is integrable for every `u ∈ H¹`.

## The argument

The weak inequality says that the flux `F = a u' + b u` satisfies `F' ≤ G = c u' + d u` in the
sense of distributions. Since `c u' = k (F - b u)` with `k = c / a ∈ L²`, the integrating factor
`w = exp (-∫ k)` turns this into `(w F)' ≤ w e u` with `e = d - k b ∈ L¹`, a bound that no longer
involves `u'`. As `w` is only absolutely continuous, this is proved by testing against the smooth
weights `exp (-∫ κ) φ` for smooth `κ` approximating `k` in `L²`, and passing to the limit by
dominated convergence and Hölder's inequality. By the monotone du Bois-Reymond lemma
`MeasureTheory.LocallyIntegrableOn.exists_monotoneOn_of_integral_deriv_mul_nonpos`, the function
`ψ = w F - ∫ w e u` is antitone on a subset of `(l, r)` of full measure.

If `ψ` is positive somewhere, it is bounded below near `l` by a positive constant `m`; as
`∫ w e u` and `b u` are small near `l`, this gives `a u' ≥ m / (4 exp ‖k‖₁)` and hence `u' ≥ ε`
there. Otherwise `ψ ≤ 0`, which bounds `u'` near `l` by a multiple `C M` of the maximum `M` of `u`
on `[l, l + δ]`. Integrating, `M ≤ δ C M`, so `M = 0` once `δ C < 1`, contradicting `u > 0`.

## Main declarations

* `TauCeti.PDE.exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg`: **Hopf's boundary-point
  lemma** for weak supersolutions on an interval, the inward difference quotients
  `u (l + t) / t` are bounded below by a positive constant.
* `TauCeti.PDE.pos_of_hasDerivWithinAt_of_integral_mul_deriv_add_mul_nonneg`: its derivative
  form.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 3.4 (the classical boundary-point lemma) and Section 8.1 (weak solutions in divergence
  form).
* Rosales, *Generalizing Hopf's boundary point lemma*, arXiv:1806.07003 (the boundary-point lemma
  for weak supersolutions in divergence form in dimension at least two).
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff ENNReal

namespace TauCeti

namespace PDE

variable {l r : ℝ}

/-- For a smooth `κ`, the weight `exp (-∫ κ)` times a nonnegative test function is again one, and
testing a distributional inequality `0 ≤ ∫ F φ' + G φ` against it moves the derivative of the
weight onto `F`. -/
private theorem integral_exp_mul_nonneg_of_contDiff {F G κ φ : ℝ → ℝ}
    (hH : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, F x * deriv φ x + G x * φ x)
    (hκ : ContDiff ℝ ∞ κ) (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo l r)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, Real.exp (-∫ t in l..x, κ t) *
      (F x * deriv φ x + G x * φ x - κ x * (F x * φ x)) := by
  set P : ℝ → ℝ := fun x ↦ ∫ t in l..x, κ t
  have hPd (x : ℝ) : HasDerivAt P (κ x) x :=
    integral_hasDerivAt_right (hκ.continuous.intervalIntegrable _ _)
      (hκ.continuous.stronglyMeasurableAtFilter _ _) hκ.continuous.continuousAt
  have hP : ContDiff ℝ ∞ P := contDiff_infty_iff_deriv.mpr
    ⟨fun x ↦ (hPd x).differentiableAt, by
      rw [show deriv P = κ from funext fun x ↦ (hPd x).deriv]; exact hκ⟩
  have hW : ContDiff ℝ ∞ fun x ↦ Real.exp (-P x) := Real.contDiff_exp.comp hP.neg
  have hderiv (x : ℝ) : deriv (fun x ↦ Real.exp (-P x) * φ x) x =
      Real.exp (-P x) * deriv φ x - κ x * (Real.exp (-P x) * φ x) := by
    have h1 : HasDerivAt (fun x ↦ Real.exp (-P x) * φ x)
        (Real.exp (-P x) * -κ x * φ x + Real.exp (-P x) * deriv φ x) x :=
      ((hPd x).neg.exp).mul (hφ.differentiable (by simp) x).hasDerivAt
    rw [h1.deriv]
    ring
  have h := hH (fun x ↦ Real.exp (-P x) * φ x) (hW.mul hφ)
    (tsupport_mul_subset_right.trans hφs) fun x ↦ mul_nonneg (Real.exp_pos _).le (hφ0 x)
  simp_rw [hderiv] at h
  refine h.trans_eq (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
  simp only [P]
  ring

/-- Hölder's inequality for a primitive on `[l, r]`: `|∫ t in l..x, f t|` is bounded by the
`L²` norm of `f` times that of the indicator of `(l, r]`. -/
private theorem abs_intervalIntegral_le_mul_eLpNorm {x : ℝ} (hlx : l ≤ x) (hxr : x ≤ r)
    {f : ℝ → ℝ} (hf : MemLp f 2) :
    |∫ t in l..x, f t| ≤
      (eLpNorm ((Ioc l r).indicator fun _ ↦ (1 : ℝ)) 2).toReal * (eLpNorm f 2).toReal := by
  have hind : MemLp ((Ioc l r).indicator fun _ ↦ (1 : ℝ)) 2 :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet 1 (Or.inr measure_Ioc_lt_top.ne)
  have heq : ∫ t in l..x, f t = ∫ t, (Ioc l x).indicator (fun _ ↦ (1 : ℝ)) t * f t := by
    rw [integral_of_le hlx, ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1 with t
    by_cases ht : t ∈ Ioc l x <;> simp [ht]
  have hmono : eLpNorm ((Ioc l x).indicator fun _ ↦ (1 : ℝ)) 2 ≤
      eLpNorm ((Ioc l r).indicator fun _ ↦ (1 : ℝ)) 2 :=
    eLpNorm_mono (aestronglyMeasurable_const.indicator measurableSet_Ioc) fun t ↦ by
      by_cases ht : t ∈ Ioc l x
      · simp [ht, show t ∈ Ioc l r from ⟨ht.1, ht.2.trans hxr⟩]
      · simp [ht]
  have h := (enorm_integral_mul_le (p := 2) (q := 2) (μ := volume)
    (u := (Ioc l x).indicator fun _ ↦ (1 : ℝ)) (v := f)).trans
      (mul_le_mul_of_nonneg_right hmono zero_le)
  rw [← heq, Real.enorm_eq_ofReal_abs] at h
  rw [← ENNReal.toReal_mul, ← ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.mul_ne_top hind.eLpNorm_ne_top hf.eLpNorm_ne_top)]
  exact h

/-- Let `κ n → kt` in `L²` with `‖κ n - kt‖₂ ≤ 1 / (n + 1)`. Then the weights
`exp (-∫ t in l..x, κ n t)` are bounded on `(l, r)` uniformly in `n`, and converge there to
`exp (-∫ t in l..x, kt t)`. -/
private theorem exists_bound_and_tendsto_exp_neg_primitive {kt : ℝ → ℝ} {κ : ℕ → ℝ → ℝ}
    (hkt2 : MemLp kt 2) (hkt1 : Integrable kt) (hκ : ∀ n, Continuous (κ n))
    (hκ2 : ∀ n, MemLp (κ n) 2)
    (hκk : ∀ n : ℕ, eLpNorm (kt - κ n) 2 ≤ ENNReal.ofReal (1 / (n + 1))) :
    ∃ C, 0 ≤ C ∧ (∀ n, ∀ x ∈ Ioo l r, Real.exp (-∫ t in l..x, κ n t) ≤ C) ∧
      ∀ x ∈ Ioo l r, Tendsto (fun n ↦ Real.exp (-∫ t in l..x, κ n t)) atTop
        (𝓝 (Real.exp (-∫ t in l..x, kt t))) := by
  set E₁ := (eLpNorm ((Ioc l r).indicator fun _ ↦ (1 : ℝ)) 2).toReal
  have hE₁ : 0 ≤ E₁ := ENNReal.toReal_nonneg
  set K₀ := ∫ x, |kt x|
  -- `|∫ (κ n - kt)| ≤ E₁ / (n + 1)` by Hölder's inequality, and `|∫ kt| ≤ K₀`.
  have hsub (n : ℕ) (x : ℝ) (hx : x ∈ Ioo l r) :
      |(∫ t in l..x, κ n t) - ∫ t in l..x, kt t| ≤ E₁ * (1 / (n + 1)) := by
    have h := abs_intervalIntegral_le_mul_eLpNorm hx.1.le hx.2.le ((hκ2 n).sub hkt2)
    simp only [Pi.sub_apply] at h
    rw [intervalIntegral.integral_sub ((hκ n).intervalIntegrable _ _)
      hkt1.intervalIntegrable] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hE₁)
    rw [eLpNorm_sub_comm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hκk n)
  have hle (x : ℝ) (hx : x ∈ Ioo l r) : |∫ t in l..x, kt t| ≤ K₀ :=
    (abs_integral_le_integral_abs hx.1.le).trans <| by
      rw [integral_of_le hx.1.le]
      exact setIntegral_le_integral hkt1.abs (Eventually.of_forall fun _ ↦ abs_nonneg _)
  refine ⟨Real.exp (K₀ + E₁), (Real.exp_pos _).le, fun n x hx ↦ Real.exp_le_exp.2 ?_,
    fun x hx ↦ ?_⟩
  · have h3 : E₁ * (1 / (n + 1)) ≤ E₁ :=
      mul_le_of_le_one_right hE₁ (by rw [div_le_one (by positivity)]; linarith)
    linarith [neg_le_abs ((∫ t in l..x, κ n t) - ∫ t in l..x, kt t),
      neg_le_abs (∫ t in l..x, kt t), hsub n x hx, hle x hx]
  · have h : Tendsto (fun n ↦ ∫ t in l..x, κ n t) atTop (𝓝 (∫ t in l..x, kt t)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n ↦ norm_nonneg _)
        (fun n ↦ (Real.norm_eq_abs _).trans_le (hsub n x hx)) ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul E₁
    exact (Real.continuous_exp.tendsto _).comp h.neg

/-- Passing to the limit in the weights. Let `κ n → kt` in `L²` with `‖κ n - kt‖₂ ≤ 1 / (n + 1)`,
and let `Φ ∈ L¹` and `B ∈ L²` vanish off `(l, r)`. If the pairings of `Φ - (κ n - kt) B` with the
weights `exp (-∫ κ n)` are nonnegative, so is the pairing of `Φ` with `exp (-∫ kt)`: the first
terms converge by dominated convergence, and the error terms tend to zero by Hölder's
inequality. -/
private theorem integral_exp_mul_nonneg_of_approx {kt Φ B : ℝ → ℝ} {κ : ℕ → ℝ → ℝ}
    (hkt2 : MemLp kt 2) (hkt1 : Integrable kt) (hκ : ∀ n, Continuous (κ n))
    (hκ2 : ∀ n, MemLp (κ n) 2)
    (hκk : ∀ n : ℕ, eLpNorm (kt - κ n) 2 ≤ ENNReal.ofReal (1 / (n + 1)))
    (hΦ : Integrable Φ) (hΦ_out : ∀ x ∉ Ioo l r, Φ x = 0) (hB : MemLp B 2)
    (hB_out : ∀ x ∉ Ioo l r, B x = 0)
    (hJ : ∀ n, 0 ≤ ∫ x, Real.exp (-∫ t in l..x, κ n t) * (Φ x - (κ n - kt) x * B x)) :
    0 ≤ ∫ x, Real.exp (-∫ t in l..x, kt t) * Φ x := by
  obtain ⟨C, hC0, hC, hlim⟩ :=
    exists_bound_and_tendsto_exp_neg_primitive (l := l) (r := r) hkt2 hkt1 hκ hκ2 hκk
  set Pn : ℕ → ℝ → ℝ := fun n x ↦ ∫ t in l..x, κ n t with hPn_def
  have hw_meas (n : ℕ) : AEStronglyMeasurable fun x ↦ Real.exp (-Pn n x) :=
    (Real.continuous_exp.comp
      (continuous_primitive (fun a b ↦ (hκ n).intervalIntegrable a b) l).neg).aestronglyMeasurable
  -- A pointwise domination of the weighted integrands.
  have hdom (n : ℕ) {f : ℝ → ℝ} (hf : ∀ x ∉ Ioo l r, f x = 0) (x : ℝ) :
      ‖Real.exp (-Pn n x) * f x‖ ≤ C * ‖f x‖ := by
    by_cases hx : x ∈ Ioo l r
    · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (hC n x hx) (norm_nonneg _)
    · simp [hf x hx]
  have hT1 : Tendsto (fun n ↦ ∫ x, Real.exp (-Pn n x) * Φ x) atTop
      (𝓝 (∫ x, Real.exp (-∫ t in l..x, kt t) * Φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ C * ‖Φ x‖)
      (fun n ↦ (hw_meas n).mul hΦ.aestronglyMeasurable) (hΦ.norm.const_mul _)
      (fun n ↦ Eventually.of_forall (hdom n hΦ_out)) (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ Ioo l r
    · exact (hlim x hx).mul_const _
    · simp [hΦ_out x hx]
  -- The error term `∫ w (κ n - kt) B` tends to zero by Hölder's inequality.
  have hD (n : ℕ) : Integrable fun x ↦ (κ n - kt) x * B x :=
    ((hκ2 n).sub hkt2).integrable_mul hB
  have hD_out (n : ℕ) (x : ℝ) (hx : x ∉ Ioo l r) : (κ n - kt) x * B x = 0 := by
    simp [hB_out x hx]
  have hT2 : Tendsto (fun n ↦ ∫ x, Real.exp (-Pn n x) * ((κ n - kt) x * B x)) atTop (𝓝 0) := by
    set CB := C * (eLpNorm B 2).toReal
    have hbound (n : ℕ) :
        ‖∫ x, Real.exp (-Pn n x) * ((κ n - kt) x * B x)‖ ≤ 1 / (n + 1) * CB := by
      have hwB : eLpNorm (fun x ↦ Real.exp (-Pn n x) * B x) 2 ≤ ENNReal.ofReal C * eLpNorm B 2 :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hw_meas n).mul hB.aestronglyMeasurable)
          (Eventually.of_forall (hdom n hB_out)) 2
      have heq : ∫ x, Real.exp (-Pn n x) * ((κ n - kt) x * B x) =
          ∫ x, (κ n - kt) x * (Real.exp (-Pn n x) * B x) :=
        integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
      have h : ‖∫ x, Real.exp (-Pn n x) * ((κ n - kt) x * B x)‖ₑ ≤
          ENNReal.ofReal (1 / (n + 1) * CB) := by
        rw [heq]
        refine (enorm_integral_mul_le (p := 2) (q := 2)).trans ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC0,
          ENNReal.ofReal_toReal hB.eLpNorm_ne_top, eLpNorm_sub_comm]
        gcongr
        exact hκk n
      rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const CB
  -- For each `n`, split the nonnegative pairing into the two terms.
  have hJn (n : ℕ) : 0 ≤ (∫ x, Real.exp (-Pn n x) * Φ x) -
      ∫ x, Real.exp (-Pn n x) * ((κ n - kt) x * B x) := by
    have hI₁ : Integrable fun x ↦ Real.exp (-Pn n x) * Φ x :=
      (hΦ.norm.const_mul _).mono' ((hw_meas n).mul hΦ.aestronglyMeasurable)
        (Eventually.of_forall (hdom n hΦ_out))
    have hI₂ : Integrable fun x ↦ Real.exp (-Pn n x) * ((κ n - kt) x * B x) :=
      ((hD n).norm.const_mul _).mono' ((hw_meas n).mul (hD n).aestronglyMeasurable)
        (Eventually.of_forall (hdom n (hD_out n)))
    rw [← integral_sub hI₁ hI₂]
    refine (hJ n).trans_eq (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
    simp only [Pn]
    ring
  simpa using ge_of_tendsto' (hT1.sub hT2) hJn

/-- **Weighting a first-order distributional inequality.** If `0 ≤ ∫ F φ' + G φ` for every
nonnegative test function `φ` on `(l, r)`, with `F, k ∈ L²(l, r)` and `G ∈ L¹(l, r)`, then the same
holds after multiplication by the integrating factor `w x = exp (-∫ t in l..x, k t)`:
`0 ≤ ∫ w (F φ' + G φ - k F φ)`. In distributional terms, `F' ≤ G` gives `(w F)' ≤ w (G - k F)`.
The weight is only absolutely continuous, so it is approximated by smooth weights. -/
private theorem integral_exp_mul_nonneg {F G k φ : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (Ioo l r))) (hG : IntegrableOn G (Ioo l r))
    (hk : MemLp k 2 (volume.restrict (Ioo l r)))
    (hH : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, F x * deriv φ x + G x * φ x)
    (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo l r) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, Real.exp (-∫ t in l..x, k t) *
      (F x * deriv φ x + G x * φ x - k x * (F x * φ x)) := by
  -- `φ` and `φ'` are bounded and vanish off `(l, r)`.
  have hφcs : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) (hφs.trans Ioo_subset_Icc_self)
  obtain ⟨C₀, hC₀⟩ := hφ.continuous.bounded_above_of_compact_support hφcs
  obtain ⟨C₁, hC₁⟩ := (hφ.continuous_deriv (by simp)).bounded_above_of_compact_support hφcs.deriv
  have hφ_out (x : ℝ) (hx : x ∉ Ioo l r) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h)
  have hφ'_out (x : ℝ) (hx : x ∉ Ioo l r) : deriv φ x = 0 :=
    Function.notMem_support.1 fun h ↦ hx (hφs (support_deriv_subset h))
  -- `k` extended by zero off `(l, r)`.
  set kt := (Ioo l r).indicator k with hkt_def
  have hkt2 : MemLp kt 2 :=
    (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).2 hk
  have hkt1 : Integrable kt :=
    (integrable_indicator_iff measurableSet_Ioo).2 (hk.integrable one_le_two)
  -- The pairings `A = F φ' + G φ` and `B = F φ`, which vanish off `(l, r)`.
  set A : ℝ → ℝ := fun x ↦ F x * deriv φ x + G x * φ x with hA_def
  set B : ℝ → ℝ := fun x ↦ F x * φ x with hB_def
  have hA_out (x : ℝ) (hx : x ∉ Ioo l r) : A x = 0 := by simp [A, hφ_out x hx, hφ'_out x hx]
  have hB_out (x : ℝ) (hx : x ∉ Ioo l r) : B x = 0 := by simp [B, hφ_out x hx]
  -- A function in `Lᵖ(l, r)` vanishing off `(l, r)` lies in `Lᵖ(ℝ)`.
  have hext {f : ℝ → ℝ} {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict (Ioo l r)))
      (h0 : ∀ x ∉ Ioo l r, f x = 0) : MemLp f p := by
    rw [← indicator_eq_self.2 fun x hx ↦ by_contra fun h ↦ hx (h0 x h)]
    exact (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).2 hf
  have hA : Integrable A := by
    refine (memLp_one_iff_integrable.1 (hext ?_ hA_out))
    refine memLp_one_iff_integrable.2 (Integrable.add ?_ ?_)
    · exact (hF.integrable one_le_two).mul_bdd
        (hφ.continuous_deriv (by simp)).aestronglyMeasurable (Eventually.of_forall hC₁)
    · exact hG.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hC₀)
  have hB : MemLp B 2 := by
    refine hext (MemLp.of_le (hF.const_mul C₀)
      (hF.aestronglyMeasurable.mul hφ.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)) hB_out
    rw [norm_mul, norm_mul, Real.norm_eq_abs C₀, mul_comm (|C₀|)]
    exact mul_le_mul_of_nonneg_left ((hC₀ x).trans (le_abs_self C₀)) (norm_nonneg _)
  set Φ : ℝ → ℝ := fun x ↦ A x - kt x * B x with hΦ_def
  have hΦ : Integrable Φ := hA.sub (hkt2.integrable_mul hB)
  have hΦ_out (x : ℝ) (hx : x ∉ Ioo l r) : Φ x = 0 := by simp [Φ, hA_out x hx, hB_out x hx]
  -- The target only sees `kt`.
  set P : ℝ → ℝ := fun x ↦ ∫ t in l..x, kt t with hP_def
  have htarget : ∫ x, Real.exp (-∫ t in l..x, k t) *
      (F x * deriv φ x + G x * φ x - k x * (F x * φ x)) = ∫ x, Real.exp (-P x) * Φ x := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ Ioo l r
    · have hprim : ∫ t in l..x, k t = P x := by
        refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
        rw [uIoc_of_le hx.1.le] at ht
        rw [hkt_def, indicator_of_mem (show t ∈ Ioo l r from ⟨ht.1, ht.2.trans_lt hx.2⟩)]
      simp only [hprim, Φ, A, B, hkt_def, indicator_of_mem hx]
    · simp [hΦ_out x hx, hφ_out x hx, hφ'_out x hx]
  rw [htarget]
  -- Smooth compactly supported `κ n` with `‖κ n - kt‖₂ ≤ 1 / (n + 1)`.
  choose κ hκc hκ hκk using fun n : ℕ ↦
    hkt2.exist_eLpNorm_sub_le (by simp) one_le_two (Nat.one_div_pos_of_nat (n := n))
  refine integral_exp_mul_nonneg_of_approx hkt2 hkt1 (fun n ↦ (hκ n).continuous)
    (fun n ↦ (hκ n).continuous.memLp_of_hasCompactSupport (hκc n)) hκk hΦ hΦ_out hB hB_out
    fun n ↦ (integral_exp_mul_nonneg_of_contDiff hH (hκ n) hφ hφs hφ0).trans_eq
      (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
  simp only [Φ, A, B, Pi.sub_apply]
  ring

/-- **The weighted flux is almost everywhere antitone.** If `0 ≤ ∫ F φ' + G φ` for every
nonnegative test function `φ` on `(l, r)`, with `F, k ∈ L²(l, r)` and `G ∈ L¹(l, r)`, then with the
integrating factor `w x = exp (-∫ t in l..x, k t)` the function
`w F - ∫ t in l..x, w (G - k F)` is antitone on a subset of `(l, r)` of full measure. The
integrand `w (G - k F)`, extended by zero, is integrable. -/
private theorem integrable_and_exists_antitoneOn {F G k : ℝ → ℝ} (hlr : l < r)
    (hF : MemLp F 2 (volume.restrict (Ioo l r))) (hG : IntegrableOn G (Ioo l r))
    (hk : MemLp k 2 (volume.restrict (Ioo l r)))
    (hH : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, F x * deriv φ x + G x * φ x) :
    Integrable ((Ioo l r).indicator fun t ↦ Real.exp (-∫ τ in l..t, k τ) * (G t - k t * F t)) ∧
    ∃ s ⊆ Ioo l r, volume (Ioo l r \ s) = 0 ∧
      AntitoneOn (fun x ↦ Real.exp (-∫ t in l..x, k t) * F x - ∫ t in l..x,
        (Ioo l r).indicator (fun t ↦ Real.exp (-∫ τ in l..t, k τ) * (G t - k t * F t)) t) s := by
  set W : ℝ → ℝ := fun x ↦ Real.exp (-∫ t in l..x, k t) with hW_def
  have hk1 : IntegrableOn k (Ioo l r) := hk.integrable one_le_two
  have hW_cont : ContinuousOn W (Icc l r) := by
    have h := continuousOn_primitive_interval (μ := volume) (a := l) (b := r) (f := k)
      (by rwa [uIcc_of_le hlr.le, integrableOn_Icc_iff_integrableOn_Ioo])
    rw [uIcc_of_le hlr.le] at h
    exact Real.continuous_exp.comp_continuousOn h.neg
  have hW_meas : AEStronglyMeasurable W (volume.restrict (Ioo l r)) :=
    (hW_cont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hW_le : ∀ᵐ x ∂volume.restrict (Ioo l r), ‖W x‖ ≤ Real.exp (∫ x in Ioo l r, |k x|) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.2
        ((neg_le_abs _).trans ((abs_integral_le_integral_abs hx.1.le).trans ?_))
      rw [integral_of_le hx.1.le]
      exact setIntegral_mono_set hk1.abs (ae_of_all _ fun _ ↦ abs_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioo_right hx.2))
  have hWF : IntegrableOn (fun x ↦ W x * F x) (Ioo l r) :=
    (hF.integrable one_le_two).bdd_mul hW_meas hW_le
  set q := (Ioo l r).indicator fun t ↦ W t * (G t - k t * F t) with hq_def
  have hq : Integrable q := (integrable_indicator_iff measurableSet_Ioo).2
    ((hG.sub (hk.integrable_mul hF)).bdd_mul hW_meas hW_le)
  set Q : ℝ → ℝ := fun x ↦ ∫ t in l..x, q t with hQ_def
  have hQ : Continuous Q := continuous_primitive (fun _ _ ↦ hq.intervalIntegrable) l
  -- It suffices that `-(w F - Q)` has a nonnegative distributional derivative.
  suffices hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      ∫ x, deriv φ x * -(W x * F x - Q x) ≤ 0 by
    obtain ⟨s, hs, hs0, hmono⟩ :=
      ((hWF.sub (hQ.integrableOn_Icc.mono_set Ioo_subset_Icc_self)).neg.locallyIntegrableOn
        ).exists_monotoneOn_of_integral_deriv_mul_nonpos hweak
    exact ⟨hq, s, hs, hs0, fun x hx y hy hxy ↦ neg_le_neg_iff.1 (hmono hx hy hxy)⟩
  intro φ hφ hφs hφ0
  have hφcs : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) (hφs.trans Ioo_subset_Icc_self)
  obtain ⟨C₀, hC₀⟩ := hφ.continuous.bounded_above_of_compact_support hφcs
  obtain ⟨C₁, hC₁⟩ := (hφ.continuous_deriv (by simp)).bounded_above_of_compact_support hφcs.deriv
  have hφ_out (x : ℝ) (hx : x ∉ Ioo l r) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h)
  have hφ'_out (x : ℝ) (hx : x ∉ Ioo l r) : deriv φ x = 0 :=
    Function.notMem_support.1 fun h ↦ hx (hφs (support_deriv_subset h))
  have hsupp {f : ℝ → ℝ} (hf : ∀ x ∉ Ioo l r, f x = 0) : Function.support f ⊆ Ioo l r :=
    fun x hx ↦ by_contra fun h ↦ hx (hf x h)
  -- Integration by parts against the primitive `Q`.
  have hIBP : ∫ x, deriv φ x * Q x = -∫ x, φ x * q x := by
    have h := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hlr.le
      (hφ.of_le (by simp)) hq.intervalIntegrable
    simp only [smul_eq_mul, hφ_out r (by simp), zero_mul, zero_sub] at h
    rwa [intervalIntegral.integral_eq_integral_of_support_subset
        ((hsupp fun x hx ↦ by simp [hφ'_out x hx]).trans Ioo_subset_Ioc_self),
      intervalIntegral.integral_eq_integral_of_support_subset
        ((hsupp fun x hx ↦ by simp [hφ_out x hx]).trans Ioo_subset_Ioc_self)] at h
  have hint₁ : Integrable fun x ↦ deriv φ x * (W x * F x) := by
    rw [← integrableOn_iff_integrable_of_support_subset (hsupp fun x hx ↦ by simp [hφ'_out x hx])]
    exact hWF.bdd_mul (hφ.continuous_deriv (by simp)).aestronglyMeasurable
      (Eventually.of_forall hC₁)
  have hint₂ : Integrable fun x ↦ deriv φ x * Q x :=
    ((hφ.continuous_deriv (by simp)).mul hQ).integrable_of_hasCompactSupport hφcs.deriv.mul_right
  have hint₃ : Integrable fun x ↦ φ x * q x :=
    hq.bdd_mul hφ.continuous.aestronglyMeasurable (Eventually.of_forall hC₀)
  calc ∫ x, deriv φ x * -(W x * F x - Q x)
      = -((∫ x, deriv φ x * (W x * F x)) + ∫ x, φ x * q x) := by
        rw [show (fun x ↦ deriv φ x * -(W x * F x - Q x)) =
            fun x ↦ deriv φ x * Q x - deriv φ x * (W x * F x) from funext fun x ↦ by ring,
          integral_sub hint₂ hint₁, hIBP]
        ring
    _ = -∫ x, W x * (F x * deriv φ x + G x * φ x - k x * (F x * φ x)) := by
        rw [← integral_add hint₁ hint₃]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ Ioo l r
        · simp only [hq_def, indicator_of_mem hx]
          ring
        · simp [hφ_out x hx, hφ'_out x hx]
    _ ≤ 0 := neg_nonpos.2 (integral_exp_mul_nonneg hF hG hk hH hφ hφs hφ0)

/-- Integrating an almost everywhere upper bound `v ≤ B` on `(l, l + δ)` from `l`. -/
private theorem intervalIntegral_le_mul_of_ae_le {v : ℝ → ℝ} {B δ y : ℝ} (hv : Integrable v)
    (hy : y ∈ Icc l (l + δ)) (h : ∀ᵐ x, x ∈ Ioo l (l + δ) → v x ≤ B) :
    ∫ x in l..y, v x ≤ (y - l) * B := by
  have h' := intervalIntegral.integral_mono_ae_restrict hy.1 hv.intervalIntegrable
    (intervalIntegrable_const (c := B)) ?_
  · rwa [intervalIntegral.integral_const, smul_eq_mul] at h'
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h, compl_mem_ae_iff.2 (measure_singleton l),
    compl_mem_ae_iff.2 (measure_singleton (l + δ))] with x hx hxl hxr hxI
  exact hx ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxl), lt_of_le_of_ne (hxI.2.trans hy.2) hxr⟩

/-- Integrating an almost everywhere lower bound `B ≤ v` on `(l, l + δ)` from `l`. -/
private theorem mul_le_intervalIntegral_of_ae_le {v : ℝ → ℝ} {B δ y : ℝ} (hv : Integrable v)
    (hy : y ∈ Icc l (l + δ)) (h : ∀ᵐ x, x ∈ Ioo l (l + δ) → B ≤ v x) :
    (y - l) * B ≤ ∫ x in l..y, v x := by
  have h' := intervalIntegral_le_mul_of_ae_le hv.neg hy (h.mono fun x hx hxI ↦ neg_le_neg (hx hxI))
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at h'
  linarith

/-- The case of a positive weighted flux. Let `F = a v + b U` on `(l, r)` and `w F = ψ + Q` with
a weight `0 < w ≤ ρ` on `(l, r)`, where `ψ` is antitone on a subset `s` of `(l, r)` of full measure
and `Q` and `U` tend to `0` at `l`. If `ψ` is positive at a point of `s`, then `v` is bounded below
by a positive constant almost everywhere near `l`. -/
private theorem exists_pos_ae_le_of_pos {lam Λ β ρ x₁ : ℝ} {a b v U F W ψ Q : ℝ → ℝ}
    {s : Set ℝ} (hlam : 0 < lam) (hlam_le : ∀ y ∈ Ioo l r, lam ≤ a y)
    (hle_Λ : ∀ y ∈ Ioo l r, a y ≤ Λ) (hbβ : ∀ y ∈ Ioo l r, |b y| ≤ β)
    (hF : ∀ y ∈ Ioo l r, F y = a y * v y + b y * U y) (hWF : ∀ y, W y * F y = ψ y + Q y)
    (hW_pos : ∀ y, 0 < W y) (hW_le : ∀ y ∈ Ioo l r, W y ≤ ρ) (hs : s ⊆ Ioo l r)
    (hs_ae : ∀ᵐ y, y ∈ Ioo l r → y ∈ s) (hanti : AntitoneOn ψ s) (hQ : Tendsto Q (𝓝 l) (𝓝 0))
    (hU : Tendsto U (𝓝 l) (𝓝 0)) (hx₁ : x₁ ∈ s) (hm : 0 < ψ x₁) :
    ∃ ε > 0, ∃ δ > 0, ∀ᵐ y, y ∈ Ioo l (l + δ) → ε ≤ v y := by
  have hx₁I := hs hx₁
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hbβ _ hx₁I)
  have hρ : 0 < ρ := (hW_pos x₁).trans_le (hW_le x₁ hx₁I)
  have hΛ : 0 < Λ := hlam.trans_le ((hlam_le _ hx₁I).trans (hle_Λ _ hx₁I))
  set m := ψ x₁
  set m₁ := m / (2 * ρ)
  have hm₁ : 0 < m₁ := by positivity
  obtain ⟨δ₁, hδ₁, hQδ⟩ :=
    Metric.eventually_nhds_iff.1 (Metric.tendsto_nhds.1 hQ (m / 2) (by positivity))
  obtain ⟨δ₂, hδ₂, hUδ⟩ :=
    Metric.eventually_nhds_iff.1 (Metric.tendsto_nhds.1 hU (m₁ / (2 * (β + 1))) (by positivity))
  set δ := min (min δ₁ δ₂) (x₁ - l)
  refine ⟨m₁ / (2 * Λ), by positivity, δ, lt_min (lt_min hδ₁ hδ₂) (sub_pos.2 hx₁I.1), ?_⟩
  filter_upwards [hs_ae] with y hys hy
  have hδx₁ : δ ≤ x₁ - l := min_le_right _ _
  have hyI : y ∈ Ioo l r := ⟨hy.1, by linarith [hy.2, hx₁I.2]⟩
  have hdist : dist y l < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hy.1])]
    linarith [hy.2]
  have hψy : m ≤ ψ y := hanti (hys hyI) hx₁ (by linarith [hy.2])
  have hQy : |Q y| < m / 2 := by
    simpa [Real.dist_eq] using hQδ (hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hUy : |U y| < m₁ / (2 * (β + 1)) := by
    simpa [Real.dist_eq] using hUδ (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  -- `F ≥ m₁`, since `w F = ψ + Q ≥ m / 2` and `w ≤ ρ`.
  have hFy : m₁ ≤ F y := by
    have h1 : m / 2 ≤ W y * F y := by rw [hWF]; linarith [neg_abs_le (Q y)]
    have hF0 : 0 ≤ F y := nonneg_of_mul_nonneg_right (by linarith) (hW_pos y)
    have h2 : m / 2 ≤ ρ * F y := h1.trans (mul_le_mul_of_nonneg_right (hW_le y hyI) hF0)
    rw [div_le_iff₀' (by positivity)]
    linarith
  -- `|b U| ≤ m₁ / 2`, so `a v = F - b U ≥ m₁ / 2`.
  have hbU : |b y * U y| ≤ m₁ / 2 := by
    rw [abs_mul]
    calc |b y| * |U y| ≤ (β + 1) * (m₁ / (2 * (β + 1))) :=
          mul_le_mul (by linarith [hbβ y hyI]) hUy.le (abs_nonneg _) (by linarith)
      _ = m₁ / 2 := by field_simp
  have hav : m₁ / 2 ≤ a y * v y := by linarith [hF y hyI, le_abs_self (b y * U y)]
  have hv0 : 0 ≤ v y := nonneg_of_mul_nonneg_right (by linarith) (hlam.trans_le (hlam_le y hyI))
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hle_Λ y hyI]

/-- The case of a nonpositive weighted flux. Let `F = a v + b U` on `(l, r)` and `w F = ψ + Q` with
a positive weight satisfying `w⁻¹ ≤ ρ` on `(l, r)`, where `ψ ≤ 0` on a subset `s` of `(l, r)` of
full measure. If `|Q| ≤ E` and `0 ≤ U ≤ M` on `(l, l + δ)`, then `v ≤ (ρ E + β M) / λ` almost
everywhere there. -/
private theorem ae_le_of_nonpos {lam β ρ E M δ : ℝ} {a b v U F W ψ Q : ℝ → ℝ} {s : Set ℝ}
    (hlam : 0 < lam) (hlam_le : ∀ y ∈ Ioo l r, lam ≤ a y) (hbβ : ∀ y ∈ Ioo l r, |b y| ≤ β)
    (hF : ∀ y ∈ Ioo l r, F y = a y * v y + b y * U y) (hWF : ∀ y, W y * F y = ψ y + Q y)
    (hW_pos : ∀ y, 0 < W y) (hW_inv : ∀ y ∈ Ioo l r, (W y)⁻¹ ≤ ρ)
    (hs_ae : ∀ᵐ y, y ∈ Ioo l r → y ∈ s) (hψ : ∀ y ∈ s, ψ y ≤ 0) (hδr : l + δ ≤ r)
    (hU : ∀ y ∈ Ioo l (l + δ), 0 ≤ U y ∧ U y ≤ M) (hQ : ∀ y ∈ Ioo l (l + δ), |Q y| ≤ E) :
    ∀ᵐ y, y ∈ Ioo l (l + δ) → v y ≤ (ρ * E + β * M) / lam := by
  filter_upwards [hs_ae] with y hys hy
  have hyI : y ∈ Ioo l r := ⟨hy.1, hy.2.trans_le hδr⟩
  have hE : 0 ≤ E := (abs_nonneg _).trans (hQ y hy)
  have hρ : 0 ≤ ρ := (inv_pos.2 (hW_pos y)).le.trans (hW_inv y hyI)
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hbβ y hyI)
  have hM : 0 ≤ M := (hU y hy).1.trans (hU y hy).2
  -- `F ≤ ρ E`, since `w F = ψ + Q ≤ E` and `w⁻¹ ≤ ρ`.
  have hFy : F y ≤ ρ * E := by
    have h1 : W y * F y ≤ E := by
      rw [hWF]
      linarith [hψ y (hys hyI), le_abs_self (Q y), hQ y hy]
    calc F y = (W y)⁻¹ * (W y * F y) := by field_simp [(hW_pos y).ne']
      _ ≤ ρ * E := by
        rcases le_or_gt (W y * F y) 0 with h0 | h0
        · exact (mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 (hW_pos y)).le h0).trans
            (mul_nonneg hρ hE)
        · exact mul_le_mul (hW_inv y hyI) h1 h0.le hρ
  -- `-b U ≤ β M`, so `a v = F - b U ≤ ρ E + β M`.
  have hbU : -(b y * U y) ≤ β * M := by
    have h := neg_abs_le (b y * U y)
    rw [abs_mul, abs_of_nonneg (hU y hy).1] at h
    linarith [mul_le_mul (hbβ y hyI) (hU y hy).2 (hU y hy).1 hβ]
  have hav : a y * v y ≤ ρ * E + β * M := by linarith [hF y hyI]
  rw [le_div_iff₀ hlam]
  rcases le_or_gt (v y) 0 with h0 | h0
  · exact (mul_nonpos_of_nonpos_of_nonneg h0 hlam.le).trans
      (add_nonneg (mul_nonneg hρ hE) (mul_nonneg hβ hM))
  · rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right (hlam_le y hyI) h0.le).trans hav

/-- The case of a nonpositive weighted flux leads to a contradiction. Let `F = a v + b U` on
`(l, r)` and `w F = ψ + Q` with a positive weight satisfying `w⁻¹ ≤ ρ` on `(l, r)`, where `ψ ≤ 0` on
a subset `s` of `(l, r)` of full measure, `U` and `Q` are the primitives from `l` of `v` and `q`,
and `|q| ≤ ρ |e| |U|` on `(l, r)` with `e ∈ L¹(l, r)`. Then `U` is not positive on `(l, r)`: with
`M` the maximum of `U` on `[l, l + δ]`, `v ≤ C M` near `l`, so `M ≤ δ C M ≤ M / 2` and `M = 0`. -/
private theorem false_of_nonpos {lam β ρ : ℝ} {a b v U F W ψ Q q e : ℝ → ℝ} {s : Set ℝ}
    (hlr : l < r) (hlam : 0 < lam) (hlam_le : ∀ y ∈ Ioo l r, lam ≤ a y)
    (hbβ : ∀ y ∈ Ioo l r, |b y| ≤ β) (hF : ∀ y ∈ Ioo l r, F y = a y * v y + b y * U y)
    (hWF : ∀ y, W y * F y = ψ y + Q y) (hW_pos : ∀ y, 0 < W y)
    (hW_inv : ∀ y ∈ Ioo l r, (W y)⁻¹ ≤ ρ) (hs_ae : ∀ᵐ y, y ∈ Ioo l r → y ∈ s)
    (hψ : ∀ y ∈ s, ψ y ≤ 0) (hv : Integrable v) (hU_cont : Continuous U)
    (hU : ∀ y, U y = ∫ t in l..y, v t) (hpos : ∀ y ∈ Ioo l r, 0 < U y)
    (hQ : ∀ y, Q y = ∫ t in l..y, q t) (he : IntegrableOn e (Ioo l r))
    (hq : ∀ y ∈ Ioo l r, |q y| ≤ ρ * (|e y| * |U y|)) : False := by
  have hmid : (l + r) / 2 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have hρ : 0 ≤ ρ := (inv_pos.2 (hW_pos _)).le.trans (hW_inv _ hmid)
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hbβ _ hmid)
  have hU_l : U l = 0 := by rw [hU, intervalIntegral.integral_same]
  set E := ∫ x, |(Ioo l r).indicator e x|
  set C := (ρ * (ρ * E) + β) / lam
  have hE : 0 ≤ E := integral_nonneg fun _ ↦ abs_nonneg _
  have hC : 0 ≤ C := by positivity
  set δ := min ((r - l) / 2) (1 / (2 * (C + 1)))
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδr : l + δ < r := by linarith [min_le_left ((r - l) / 2) (1 / (2 * (C + 1)))]
  have hδC : δ * C ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * (C + 1)) := min_le_right _ _
    calc δ * C ≤ 1 / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right h1 hC
      _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) two_pos]
        linarith
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith))
    hU_cont.continuousOn (s := Icc l (l + δ))
  set M := U xM
  have hU_nonneg (y : ℝ) (hy : y ∈ Icc l (l + δ)) : 0 ≤ U y := by
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, hU_l]
    · exact (hpos y ⟨h, by linarith [hy.2]⟩).le
  have hUM (y : ℝ) (hy : y ∈ Icc l (l + δ)) : U y ≤ M := hmax hy
  have hM : 0 ≤ M := hU_nonneg xM hxM
  -- `|Q y| ≤ ρ E M` on `(l, l + δ]`, from `|q| ≤ ρ |e| |U|`.
  have hQ_le (y : ℝ) (hy : y ∈ Ioc l (l + δ)) : |Q y| ≤ ρ * (E * M) := by
    have hEi : Integrable fun x ↦ |(Ioo l r).indicator e x| :=
      ((integrable_indicator_iff measurableSet_Ioo).2 he).abs
    have h := intervalIntegral.norm_integral_le_of_norm_le (f := q)
      (g := fun x ↦ ρ * (|(Ioo l r).indicator e x| * M)) hy.1.le
      (Eventually.of_forall fun x hx ↦ ?_) ((hEi.mul_const M).const_mul ρ).intervalIntegrable
    · rw [hQ, ← Real.norm_eq_abs]
      refine h.trans ?_
      rw [intervalIntegral.integral_of_le hy.1.le, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_mul_const]
      gcongr
      exact setIntegral_le_integral hEi (Eventually.of_forall fun _ ↦ abs_nonneg _)
    · have hxI : x ∈ Ioo l r := ⟨hx.1, by linarith [hx.2, hy.2]⟩
      have hxδ : x ∈ Icc l (l + δ) := ⟨hx.1.le, hx.2.trans hy.2⟩
      rw [Real.norm_eq_abs, indicator_of_mem hxI]
      refine (hq x hxI).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hρ)
      rw [abs_of_nonneg (hU_nonneg x hxδ)]
      exact hUM x hxδ
  -- `v ≤ C M` almost everywhere on `(l, l + δ)`.
  have hv_le := ae_le_of_nonpos hlam hlam_le hbβ hF hWF hW_pos hW_inv hs_ae hψ hδr.le
    (fun y hy ↦ ⟨hU_nonneg y ⟨hy.1.le, hy.2.le⟩, hUM y ⟨hy.1.le, hy.2.le⟩⟩)
    fun y hy ↦ hQ_le y ⟨hy.1, hy.2.le⟩
  have hCM : (ρ * (ρ * (E * M)) + β * M) / lam = C * M := by
    simp only [C]
    field_simp
  rw [hCM] at hv_le
  -- Integrating, `M = U xM ≤ δ C M ≤ M / 2`, so `M = 0`, contradicting `U > 0`.
  have h := intervalIntegral_le_mul_of_ae_le hv hxM hv_le
  rw [← hU] at h
  have h' : (xM - l) * (C * M) ≤ δ * C * M := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [hxM.2]) (by positivity)
  have hM0 : M ≤ 0 := by nlinarith
  have hy : l + δ / 2 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  linarith [hUM (l + δ / 2) ⟨by linarith, by linarith⟩, hpos _ hy]

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval.** Let
`L u = -(a u' + b u)' + c u' + d u` on `(l, r)`, with `a` measurable and `λ ≤ a ≤ Λ` for some
`λ > 0`, `b` measurable with `|b| ≤ β`, `c ∈ L²(l, r)` and `d ∈ L¹(l, r)`. Let `u` be the primitive
`u x = ∫ t in l..x, u' t` of some `u' ∈ L²(l, r)`, so that `u ∈ H¹(l, r)` with `u (l⁺) = 0`, and
let `u` be a weak supersolution, `L u ≥ 0`:

`0 ≤ ∫ ((a u' + b u) φ' + (c u' + d u) φ)` for every nonnegative test function `φ` on `(l, r)`.

If `u > 0` on `(l, r)`, then `u` leaves the boundary point `l` at a positive linear rate: there are
`ε, δ > 0` with `ε t ≤ u (l + t)` for `0 < t < δ`.

No continuity is needed of the coefficients and no sign condition on the lower-order terms, since
`u` vanishes at `l`. In dimension two and higher the lemma fails for merely bounded measurable
coefficients in divergence form. -/
theorem exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg {lam Λ β : ℝ}
    {a b c d u u' : ℝ → ℝ} (hlr : l < r) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo l r)))
    (hlam_le : ∀ x ∈ Ioo l r, lam ≤ a x) (hle_Λ : ∀ x ∈ Ioo l r, a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo l r))) (hbβ : ∀ x ∈ Ioo l r, |b x| ≤ β)
    (hc : MemLp c 2 (volume.restrict (Ioo l r))) (hd : IntegrableOn d (Ioo l r))
    (hu' : MemLp u' 2 (volume.restrict (Ioo l r)))
    (hu : ∀ x ∈ Ioo l r, u x = ∫ t in l..x, u' t)
    (hsuper : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, (a x * u' x + b x * u x) * deriv φ x + (c x * u' x + d x * u x) * φ x)
    (hpos : ∀ x ∈ Ioo l r, 0 < u x) :
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ε * t ≤ u (l + t) := by
  have hI : MeasurableSet (Ioo l r) := measurableSet_Ioo
  have hae {p : ℝ → Prop} (h : ∀ x ∈ Ioo l r, p x) : ∀ᵐ x ∂volume.restrict (Ioo l r), p x :=
    ae_restrict_of_forall_mem hI h
  have hmid : (l + r) / 2 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have hΛ : 0 < Λ := hlam.trans_le ((hlam_le _ hmid).trans (hle_Λ _ hmid))
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hbβ _ hmid)
  have ha_pos (x : ℝ) (hx : x ∈ Ioo l r) : 0 < a x := hlam.trans_le (hlam_le x hx)
  have hφ_out {φ : ℝ → ℝ} (hφs : tsupport φ ⊆ Ioo l r) (x : ℝ) (hx : x ∉ Ioo l r) :
      φ x = 0 ∧ deriv φ x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h),
      Function.notMem_support.1 fun h ↦ hx (hφs (support_deriv_subset h))⟩
  /- The primitive `U` of the zero extension `v` of `u'`, which is continuous on `ℝ`, vanishes at
  `l` and agrees with `u` on `(l, r)`. -/
  set v := (Ioo l r).indicator u' with hv_def
  have hv : Integrable v := (integrable_indicator_iff hI).2 (hu'.integrable one_le_two)
  set U : ℝ → ℝ := fun x ↦ ∫ t in l..x, v t with hU_def
  have hU_cont : Continuous U := continuous_primitive (fun _ _ ↦ hv.intervalIntegrable) l
  have hU_l : U l = 0 := intervalIntegral.integral_same
  have hUu (x : ℝ) (hx : x ∈ Ioo l r) : U x = u x := by
    rw [hu x hx]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le hx.1.le] at ht
    rw [hv_def, indicator_of_mem (show t ∈ Ioo l r from ⟨ht.1, ht.2.trans_lt hx.2⟩)]
  have hU_le (x : ℝ) (hx : x ∈ Ioo l r) : ‖U x‖ ≤ ∫ x, |v x| := by
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs hx.1.le).trans ?_
    rw [integral_of_le hx.1.le]
    exact setIntegral_le_integral hv.abs (Eventually.of_forall fun _ ↦ abs_nonneg _)
  /- The flux `F = a u' + b u`, the source `G = c u' + d u` and the drift ratio `k = c / a`. -/
  set F : ℝ → ℝ := fun x ↦ a x * u' x + b x * U x with hF_def
  set G : ℝ → ℝ := fun x ↦ c x * u' x + d x * U x with hG_def
  set k : ℝ → ℝ := fun x ↦ c x / a x with hk_def
  have hF : MemLp F 2 (volume.restrict (Ioo l r)) := by
    refine MemLp.add (MemLp.of_le (hu'.const_mul Λ) (ha.mul hu'.aestronglyMeasurable)
      (hae fun x hx ↦ ?_)) (MemLp.of_bound (hb.mul hU_cont.aestronglyMeasurable) (β * ∫ x, |v x|)
        (hae fun x hx ↦ ?_))
    · rw [norm_mul, norm_mul, Real.norm_of_nonneg hΛ.le, Real.norm_of_nonneg (ha_pos x hx).le]
      exact mul_le_mul_of_nonneg_right (hle_Λ x hx) (norm_nonneg _)
    · rw [norm_mul, Real.norm_eq_abs (b x)]
      exact mul_le_mul (hbβ x hx) (hU_le x hx) (norm_nonneg _) hβ
  have hG : IntegrableOn G (Ioo l r) :=
    (hc.integrable_mul hu').add (hd.mul_bdd hU_cont.aestronglyMeasurable (hae hU_le))
  have hk : MemLp k 2 (volume.restrict (Ioo l r)) := by
    refine MemLp.of_le (hc.const_mul lam⁻¹)
      (hc.aestronglyMeasurable.aemeasurable.div ha.aemeasurable).aestronglyMeasurable
      (hae fun x hx ↦ ?_)
    rw [norm_div, norm_mul, Real.norm_of_nonneg (ha_pos x hx).le,
      Real.norm_of_nonneg (inv_pos.2 hlam).le, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (ha_pos x hx) hlam).2 (hlam_le x hx))
      (norm_nonneg _)
  have hH : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, F x * deriv φ x + G x * φ x := fun φ hφ hφs hφ0 ↦
    (hsuper φ hφ hφs hφ0).trans_eq (integral_congr_ae (Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ Ioo l r
      · simp only [F, G, hUu x hx]
      · simp [(hφ_out hφs x hx).1, (hφ_out hφs x hx).2]))
  /- The weighted flux `ψ = w F - Q` with `w = exp (-∫ k)` and `Q = ∫ w (G - k F)` is antitone on
  a subset `s` of `(l, r)` of full measure. -/
  obtain ⟨hq, s, hs, hs0, hanti⟩ := integrable_and_exists_antitoneOn hlr hF hG hk hH
  have hs_ae : ∀ᵐ x, x ∈ Ioo l r → x ∈ s := by
    rw [ae_iff]
    exact measure_mono_null (t := Ioo l r \ s) (fun x hx ↦ not_imp.1 hx) hs0
  set W : ℝ → ℝ := fun x ↦ Real.exp (-∫ t in l..x, k t) with hW_def
  set q := (Ioo l r).indicator fun t ↦ W t * (G t - k t * F t) with hq_def
  set Q : ℝ → ℝ := fun x ↦ ∫ t in l..x, q t with hQ_def
  -- Bounds on the weight on `(l, r)`.
  set K := ∫ x in Ioo l r, |k x|
  have hK (x : ℝ) (hx : x ∈ Ioo l r) : |∫ t in l..x, k t| ≤ K := by
    refine (abs_integral_le_integral_abs hx.1.le).trans ?_
    rw [integral_of_le hx.1.le]
    exact setIntegral_mono_set (hk.integrable one_le_two).abs
      (ae_of_all _ fun _ ↦ abs_nonneg _) (Eventually.of_forall (Ioc_subset_Ioo_right hx.2))
  have hW_le (x : ℝ) (hx : x ∈ Ioo l r) : W x ≤ Real.exp K :=
    Real.exp_le_exp.2 ((neg_le_abs _).trans (hK x hx))
  have hW_inv (x : ℝ) (hx : x ∈ Ioo l r) : (W x)⁻¹ ≤ Real.exp K := by
    rw [hW_def, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hK x hx))
  /- On `(l, r)`, `G - k F = e U` with `e = d - k b ∈ L¹(l, r)`, so `|q| ≤ exp K |e| |U|`. -/
  set e : ℝ → ℝ := fun x ↦ d x - k x * b x with he_def
  have he : IntegrableOn e (Ioo l r) :=
    hd.sub ((hk.integrable one_le_two).mul_bdd hb (hae fun x hx ↦ (hbβ x hx).trans_eq' rfl))
  have hq_le (x : ℝ) (hx : x ∈ Ioo l r) : |q x| ≤ Real.exp K * (|e x| * |U x|) := by
    have hGkF : G x - k x * F x = e x * U x := by
      simp only [F, G, k, e]
      field_simp [(ha_pos x hx).ne']
      ring
    rw [hq_def, indicator_of_mem hx, hGkF, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hW_le x hx) (by positivity)
  have hQ_cont : Continuous Q := continuous_primitive (fun _ _ ↦ hq.intervalIntegrable) l
  have hQ_l : Q l = 0 := intervalIntegral.integral_same
  set ψ : ℝ → ℝ := fun x ↦ W x * F x - Q x with hψ_def
  have hWF (y : ℝ) : W y * F y = ψ y + Q y := by simp only [ψ]; ring
  have hFv (y : ℝ) (hy : y ∈ Ioo l r) : F y = a y * v y + b y * U y := by
    simp only [F, hv_def, indicator_of_mem hy]
  by_cases hA : ∃ x₁ ∈ s, 0 < ψ x₁
  · -- If `ψ` is positive somewhere on `s`, then `u' ≥ ε > 0` near `l`; integrate.
    obtain ⟨x₁, hx₁s, hm⟩ := hA
    obtain ⟨ε, hε, δ, hδ, hv_ge⟩ := exists_pos_ae_le_of_pos hlam hlam_le hle_Λ hbβ hFv hWF
      (fun y ↦ Real.exp_pos _) hW_le hs hs_ae hanti (hQ_l ▸ hQ_cont.tendsto l)
      (hU_l ▸ hU_cont.tendsto l) hx₁s hm
    refine ⟨ε, hε, min δ (r - l), lt_min hδ (sub_pos.2 hlr), fun t ht ↦ ?_⟩
    have htI : l + t ∈ Ioo l r :=
      ⟨by linarith [ht.1], by linarith [ht.2, min_le_right δ (r - l)]⟩
    have h := mul_le_intervalIntegral_of_ae_le (y := l + t) hv
      ⟨by linarith [ht.1], by linarith [ht.2, min_le_left δ (r - l)]⟩ hv_ge
    rw [add_sub_cancel_left] at h
    rw [← hUu _ htI, mul_comm]
    exact h
  · -- Otherwise `ψ ≤ 0` on `s`, which forces `u = 0` near `l`.
    simp only [not_exists, not_and, not_lt] at hA
    exact (false_of_nonpos hlr hlam hlam_le hbβ hFv hWF (fun y ↦ Real.exp_pos _) hW_inv hs_ae hA
      hv hU_cont (fun _ ↦ rfl) (fun y hy ↦ hUu y hy ▸ hpos y hy) (fun _ ↦ rfl) he hq_le).elim

/-- **Hopf's boundary-point lemma on an interval, derivative form.** Under the hypotheses of
`exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg`, if `u l = 0` and `u` has a right
derivative `D` at `l`, then `D > 0`. -/
theorem pos_of_hasDerivWithinAt_of_integral_mul_deriv_add_mul_nonneg {lam Λ β : ℝ}
    {a b c d u u' : ℝ → ℝ} (hlr : l < r) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo l r)))
    (hlam_le : ∀ x ∈ Ioo l r, lam ≤ a x) (hle_Λ : ∀ x ∈ Ioo l r, a x ≤ Λ)
    (hb : AEStronglyMeasurable b (volume.restrict (Ioo l r))) (hbβ : ∀ x ∈ Ioo l r, |b x| ≤ β)
    (hc : MemLp c 2 (volume.restrict (Ioo l r))) (hd : IntegrableOn d (Ioo l r))
    (hu' : MemLp u' 2 (volume.restrict (Ioo l r)))
    (hu : ∀ x ∈ Ioo l r, u x = ∫ t in l..x, u' t)
    (hsuper : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ Ioo l r → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, (a x * u' x + b x * u x) * deriv φ x + (c x * u' x + d x * u x) * φ x)
    (hpos : ∀ x ∈ Ioo l r, 0 < u x) (hul : u l = 0) {D : ℝ}
    (hD : HasDerivWithinAt u D (Ici l) l) :
    0 < D := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_pos_mul_le_of_integral_mul_deriv_add_mul_nonneg hlr hlam ha
    hlam_le hle_Λ hb hbβ hc hd hu' hu hsuper hpos
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl l)).mp hD.Ioi_of_Ici
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  filter_upwards [Ioo_mem_nhdsGT (show l < l + δ by linarith)] with x hx
  rw [slope_def_field, hul, sub_zero, le_div_iff₀ (sub_pos.2 hx.1)]
  simpa using h (x - l) ⟨sub_pos.2 hx.1, by linarith [hx.2]⟩

end PDE

end TauCeti
