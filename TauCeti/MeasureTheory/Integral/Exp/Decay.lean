/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.SpecialFunctions.Exp.Overlap
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Exponential integrals on the real line and radial exponentials

This file records integrability and evaluation of exponential integrands: on a half-line or the
whole real line, natural powers multiplied by an exponentially decaying factor, the exact rate at
which a bare exponential is integrable on a right half-line, and integrability and the integral
of the two-sided exponential; and, on a finite-dimensional real normed space, integrability of the
radial exponential `exp (-a ‖x‖)` for every additive Haar measure, by integrating in polar
coordinates, and the resulting `Lᵖ` membership of continuous functions decaying at that rate.
The radial exponential then bounds the overlap of two functions that decay exponentially about two
points: it decays exponentially in the distance between the points.

Mathlib supplies the *sufficient* direction of the right-half-line integrability criterion,
`integrableOn_exp_mul_Ioi`, for a negative rate.  `integrableOn_exp_mul_Ioi_iff` adds the converse,
which is what lets a caller describe an exponential-moment domain as an exact set rather than an
inclusion.

## Main results

* `TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi`: integrability on `(0, ∞)`.
* `TauCeti.integrableOn_rpow_mul_exp_mul_sub_mul_rpow`: integrability of
  `t ^ q * exp (a * t - b * t ^ p)` on `(0, ∞)` when `1 < p`, `-1 < q`, and `0 < b`.
* `TauCeti.integral_pow_mul_exp_neg_mul_Ioi`: evaluation in terms of a factorial.
* `TauCeti.lintegral_ofReal_exp_neg_mul_mul_lintegral`: an iterated exponential integral is a
  Stieltjes-kernel integral.
* `TauCeti.integrableOn_exp_mul_Ioi_iff`: `exp (a * ·)` is integrable on `(c, ∞)` exactly when
  `a < 0`.
* `TauCeti.integrableOn_exp_mul_Iic_iff`: `exp (a * ·)` is integrable on `(-∞, c]` exactly when
  `0 < a`.
* `TauCeti.not_integrableOn_rpow_mul_exp_mul_Ioi`,
  `TauCeti.integrableOn_rpow_mul_exp_mul_Ioi_iff`,
  `TauCeti.integrableOn_rpow_mul_exp_neg_mul_Ioi_of_pos`: `x ↦ x ^ s * exp (a * x)` is not
  integrable on `(c, ∞)` for any `c : ℝ` when `0 < a`, and for `0 < c` is integrable on `(c, ∞)`
  precisely when `a < 0`, or `a = 0` and `s < -1`.
* `TauCeti.integrable_exp_neg_mul_abs`: `exp (-(a * |·|))` is integrable when `0 < a`.
* `TauCeti.memLp_exp_neg_mul_abs`: it lies in every `Lᵖ`.
* `TauCeti.integral_exp_neg_mul_abs`: its integral is `2 / a`.
* `TauCeti.lintegral_ofReal_mul_exp_neg_mul_abs`: the same evaluation as a lower Lebesgue integral
  of `c * exp (-(a * |·|))`.
* `TauCeti.integrable_exp_mul_I_mul_exp_neg_mul_abs`: the same times the oscillation
  `exp (b * x * I)`.
* `TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs`: `(1 + |·|) ^ K * exp (-(a * |·|))`
  is integrable for every `K : ℝ` when `0 < a`.
* `TauCeti.integrable_exp_neg_mul_norm`: `exp (-(a * ‖·‖))` is integrable on a finite-dimensional
  space when `0 < a`.
* `TauCeti.memLp_exp_neg_mul_norm`: it lies in every `Lᵖ`.
* `Continuous.memLp_of_isBigO_exp_neg_mul_norm`: so does every continuous function which is
  `O(exp (-(a * ‖·‖)))` at infinity.
* `TauCeti.integral_norm_mul_norm_le_mul_exp_neg_mul_norm`: two functions decaying
  exponentially at rates `c₁` and `c₂` about points at distance `‖a‖` overlap, after integration,
  by `O(exp (-(c' ‖a‖)))` for every `0 ≤ c'` with `c' < c₁` and `c' ≤ c₂`, with an explicit
  constant depending only on the two decay constants.
  `TauCeti.exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt` restates the bound for
  nonnegative functions decaying at every rate below a threshold. The pointwise overlap bounds
  are in `TauCeti.Analysis.SpecialFunctions.Exp.Overlap`.
* `TauCeti.integral_mul_le_mul_exp_of_forall_le_norm_sub`: the same for functions decaying in the
  distance to two finite multisets of centres at distance at least `δ` from each other: their
  overlap integral is `O(exp (-(c δ)))`, with a constant depending only on the decay constants and
  the number of centres. It integrates the radial exponentials about finitely many centres,
  `TauCeti.integrable_sum_map_exp_neg_mul_norm_sub` and
  `TauCeti.integral_sum_map_exp_neg_mul_norm_sub`.
* `TauCeti.integrable_norm_mul_norm_comp_add`, `TauCeti.integrable_mul_comp_add`: the overlap of
  an exponentially decaying function with a translate of a bounded one is integrable, and
  `TauCeti.integrable_mul_comp_add_of_forall_lt` restates this for nonnegative functions decaying
  at every rate below a threshold.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- Natural powers times an exponentially decaying factor are integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(b * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) one_pos hb
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

/-- For `1 < p`, `-1 < q`, and `0 < b`, a linear drift `a * t` in the exponent is dominated by
`-b * t ^ p`, so `t ^ q * exp (a * t - b * t ^ p)` is integrable on `(0, ∞)`. -/
theorem integrableOn_rpow_mul_exp_mul_sub_mul_rpow {p q b : ℝ} (hp : 1 < p) (hq : -1 < q)
    (hb : 0 < b) (a : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ q * Real.exp (a * t - b * t ^ p)) (Set.Ioi 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  set M : ℝ := max 1 ((2 * |a| / b) ^ (p - 1)⁻¹)
  have hmajor : IntegrableOn
      (fun t : ℝ => Real.exp (|a| * M) * (t ^ q * Real.exp (-(b / 2) * t ^ p))) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hq hp0 (half_pos hb)).const_mul _
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  have hexp : a * t - b * t ^ p ≤ |a| * M - b / 2 * t ^ p := by
    have hat : a * t ≤ |a| * t := mul_le_mul_of_nonneg_right (le_abs_self a) ht.le
    rcases le_total t M with htM | hMt
    · have h1 : |a| * t ≤ |a| * M := mul_le_mul_of_nonneg_left htM (abs_nonneg a)
      have h2 : 0 ≤ b / 2 * t ^ p := by positivity
      linarith
    · have h2ab : 2 * |a| / b ≤ t ^ (p - 1) := by
        rcases eq_or_lt_of_le (abs_nonneg a) with ha0 | ha0
        · rw [← ha0, mul_zero, zero_div]; positivity
        · have hbase : 0 < 2 * |a| / b := by positivity
          calc 2 * |a| / b
              = ((2 * |a| / b) ^ (p - 1)⁻¹) ^ (p - 1) := by
                  rw [← Real.rpow_mul hbase.le, inv_mul_cancel₀ hp1.ne', Real.rpow_one]
            _ ≤ M ^ (p - 1) := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp1.le
            _ ≤ t ^ (p - 1) := Real.rpow_le_rpow (by positivity) hMt hp1.le
      have hbt : 2 * |a| ≤ t ^ (p - 1) * b := (div_le_iff₀ hb).mp h2ab
      have hbtp : 2 * (|a| * t) ≤ b * t ^ p := by
        calc 2 * (|a| * t) = (2 * |a|) * t := by ring
          _ ≤ (t ^ (p - 1) * b) * t := mul_le_mul_of_nonneg_right hbt ht.le
          _ = b * (t ^ (p - 1) * t ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
          _ = b * t ^ p := by rw [← Real.rpow_add ht, sub_add_cancel]
      have hM0 : 0 ≤ |a| * M := mul_nonneg (abs_nonneg a) (zero_le_one.trans (le_max_left _ _))
      linarith
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht q) (Real.exp_pos _)),
    mul_left_comm, ← Real.exp_add]
  gcongr
  linarith

/-- The integral of a natural power times an exponentially decaying factor on `(0, ∞)`. -/
theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) = n.factorial / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Real.Gamma_nat_eq_factorial] at h
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast] at h
  have h' : ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) =
      (1 / a) ^ (n + 1) * n.factorial := by
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp
    rw [Real.rpow_natCast t n]
  rw [h', one_div, div_eq_mul_inv, inv_pow]
  ring

/-- **The Stieltjes kernel is an iterated exponential integral.** Swapping the two integrations
turns the outer Laplace integral of the inner one into the Stieltjes integral of `ν`. -/
theorem lintegral_ofReal_exp_neg_mul_mul_lintegral (ν : Measure ℝ≥0) [SFinite ν] {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s))) *
        ∫⁻ x : ℝ≥0, ENNReal.ofReal (Real.exp (-(s * (x : ℝ)))) ∂ν
      = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
  have hmeas : AEMeasurable (Function.uncurry fun (s : ℝ) (x : ℝ≥0) =>
      ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s))))
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    refine Measurable.aemeasurable ?_
    simp only [Function.uncurry_def]
    fun_prop
  calc
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * s))) *
          ∫⁻ x : ℝ≥0, ENNReal.ofReal (Real.exp (-(s * (x : ℝ)))) ∂ν
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x : ℝ≥0,
            ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s))) ∂ν := by
          refine lintegral_congr fun s => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
    _ = ∫⁻ x : ℝ≥0, (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-((t + (x : ℝ)) * s)))) ∂ν := lintegral_lintegral_swap hmeas
    _ = ∫⁻ x : ℝ≥0, ENNReal.ofReal (t + (x : ℝ))⁻¹ ∂ν := by
          refine lintegral_congr fun x => ?_
          have htx : 0 < t + (x : ℝ) := add_pos_of_pos_of_nonneg ht x.coe_nonneg
          have hint : IntegrableOn
              (fun s : ℝ => Real.exp (-((t + (x : ℝ)) * s))) (Ioi 0) := by
            simpa only [pow_zero, one_mul] using
              integrableOn_pow_mul_exp_neg_mul_Ioi 0 htx
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (.of_forall fun s => (Real.exp_pos _).le)]
          simpa using congrArg ENNReal.ofReal
            (integral_pow_mul_exp_neg_mul_Ioi 0 htx)

/-- The radial exponential `exp (-(a * ‖x‖))` is integrable for every additive Haar measure on a
finite-dimensional real normed space, when `0 < a`. -/
theorem integrable_exp_neg_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E ↦ Real.exp (-(a * ‖x‖))) μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : CompactSpace E := Finite.compactSpace
    exact (integrable_const (1 : ℝ)).congr (.of_forall fun x ↦ by simp [Subsingleton.elim x 0])
  · refine (integrable_fun_norm_addHaar μ (f := fun t ↦ Real.exp (-(a * t)))).mpr ?_
    simpa only [smul_eq_mul] using integrableOn_pow_mul_exp_neg_mul_Ioi _ ha

/-- The radial exponential `exp (-a ‖x‖)` lies in every `Lᵖ` for every additive Haar measure on a
finite-dimensional real normed space, when `0 < a`: its `p`-th power is the radial exponential
with rate `p a`. -/
theorem memLp_exp_neg_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : ℝ} (ha : 0 < a) (p : ℝ≥0∞) :
    MemLp (fun x : E ↦ Real.exp (-(a * ‖x‖))) p μ := by
  have hm : AEStronglyMeasurable (fun x : E ↦ Real.exp (-(a * ‖x‖))) μ :=
    (by fun_prop : Continuous fun x : E ↦ Real.exp (-(a * ‖x‖))).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm
  rcases eq_or_ne p ∞ with rfl | hptop
  · refine memLp_top_of_bound hm 1 (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    positivity
  · rw [← integrable_norm_rpow_iff hm hp0 hptop]
    refine (integrable_exp_neg_mul_norm μ (mul_pos (ENNReal.toReal_pos hp0 hptop) ha)).congr
      (.of_forall fun x ↦ ?_)
    dsimp only
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
    ring_nf

/-- A continuous function which is `O(exp (-a ‖x‖))` at infinity, for some `0 < a`, lies in every
`Lᵖ` for every additive Haar measure on a finite-dimensional real normed space. -/
theorem _root_.Continuous.memLp_of_isBigO_exp_neg_mul_norm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] {f : E → F}
    (hf : Continuous f) {a : ℝ} (ha : 0 < a)
    (hdec : f =O[Filter.cocompact E] fun x ↦ Real.exp (-(a * ‖x‖))) (p : ℝ≥0∞) :
    MemLp f p μ := by
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨K, hK⟩ := exists_forall_le_mul_exp_of_eventually_le hf.norm
    (hC.mono fun x hx ↦ by rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hx)
  refine ((memLp_exp_neg_mul_norm μ ha p).const_mul K).of_le hf.aestronglyMeasurable
    (.of_forall fun x ↦ (hK x).trans ?_)
  rw [Real.norm_eq_abs]
  exact le_abs_self _

section Overlap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  [SeminormedAddCommGroup F] [SeminormedAddCommGroup G] {K L c : ℝ}

/-- **Overlap of exponentially decaying functions, integrated.** If `‖f z‖ ≤ K exp (-(c₁ ‖z‖))`
and `‖g z‖ ≤ L exp (-(c₂ ‖z‖))` on a finite-dimensional space, then for every rate `0 ≤ c'` with
`c' < c₁` and `c' ≤ c₂` the overlap integral `∫ ‖f z‖ ‖g (z + a)‖` of `f` with the translate
`g (· + a)` is at most `K L (∫ exp (-((c₁ - c') ‖z‖))) exp (-(c' ‖a‖))`, for every additive Haar
measure. The constant depends on `f` and `g` only through `K` and `L`. -/
theorem integral_norm_mul_norm_le_mul_exp_neg_mul_norm {f : E → F} {g : E → G} {c₁ c₂ c' : ℝ}
    (hc'₀ : 0 ≤ c') (hc'₁ : c' < c₁) (hc'₂ : c' ≤ c₂)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c₁ * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c₂ * ‖z‖))) (a : E) :
    ∫ z, ‖f z‖ * ‖g (z + a)‖ ∂μ ≤
      K * L * (∫ z, Real.exp (-((c₁ - c') * ‖z‖)) ∂μ) * Real.exp (-(c' * ‖a‖)) := by
  have hint := integrable_exp_neg_mul_norm μ (sub_pos.2 hc'₁)
  calc ∫ z, ‖f z‖ * ‖g (z + a)‖ ∂μ
      ≤ ∫ z, K * L * Real.exp (-(c' * ‖a‖)) * Real.exp (-((c₁ - c') * ‖z‖)) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun z ↦ by positivity) (hint.const_mul _)
          (.of_forall fun z ↦ norm_mul_norm_le_mul_exp_mul_exp hc'₀ hc'₂ hf hg z a)
    _ = K * L * Real.exp (-(c' * ‖a‖)) * ∫ z, Real.exp (-((c₁ - c') * ‖z‖)) ∂μ :=
        integral_const_mul _ _
    _ = _ := by ring

/-- **Integrability of the overlap of an exponentially decaying function with a bounded one.**
If `f` and `g` are almost everywhere strongly measurable with `‖f z‖ ≤ K exp (-(c ‖z‖))` for some
`0 < c` on a finite-dimensional space and `‖g z‖ ≤ L`, then the overlap `‖f z‖ ‖g (z + a)‖` of
`f` with the translate `g (· + a)` is integrable for every additive Haar measure. -/
theorem integrable_norm_mul_norm_comp_add {f : E → F} {g : E → G} (hc : 0 < c)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖))) (hg : ∀ z, ‖g z‖ ≤ L) (a : E) :
    Integrable (fun z ↦ ‖f z‖ * ‖g (z + a)‖) μ := by
  refine ((integrable_exp_neg_mul_norm μ hc).const_mul (K * L)).mono'
    (hfm.norm.mul (hgm.comp_quasiMeasurePreserving
      (measurePreserving_add_right μ a).quasiMeasurePreserving).norm)
    (.of_forall fun z ↦ ?_)
  have hK : 0 ≤ K * Real.exp (-(c * ‖z‖)) := (norm_nonneg _).trans (hf z)
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖f z‖ * ‖g (z + a)‖ ≤ K * Real.exp (-(c * ‖z‖)) * L :=
        mul_le_mul (hf z) (hg _) (norm_nonneg _) hK
    _ = K * L * Real.exp (-(c * ‖z‖)) := by ring

/-- **Integrability of the product of an exponentially decaying function with a bounded one.**
In a normed ring, if `f` and `g` are almost everywhere strongly measurable with
`‖f z‖ ≤ K exp (-(c ‖z‖))` for some `0 < c` on a finite-dimensional space and `‖g z‖ ≤ L`, then
the product `f z * g (z + a)` of `f` with the translate `g (· + a)` is integrable for every
additive Haar measure. -/
theorem integrable_mul_comp_add {R : Type*} [NonUnitalNormedRing R] {f g : E → R} (hc : 0 < c)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖))) (hg : ∀ z, ‖g z‖ ≤ L) (a : E) :
    Integrable (fun z ↦ f z * g (z + a)) μ :=
  (integrable_norm_mul_norm_comp_add μ hc hfm hgm hf hg a).mono'
    (hfm.mul (hgm.comp_quasiMeasurePreserving
      (measurePreserving_add_right μ a).quasiMeasurePreserving))
    (.of_forall fun _ ↦ norm_mul_le _ _)

/-- **Overlap of nonnegative functions decaying at every rate below `r`, integrated.** If
`0 ≤ f`, `0 ≤ g` and both are at most `K exp (-(c ‖z‖))` for every rate `c < r`, with `K`
depending on `c`, then `∫ f z g (z + a) ≤ K exp (-(c ‖a‖))` for every rate `c < r`, on a
finite-dimensional space with an additive Haar measure. -/
theorem exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt {f g : E → ℝ} {r : ℝ}
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ c < r, ∃ K, ∀ z, f z ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ c < r, ∃ K, ∀ z, g z ≤ K * Real.exp (-(c * ‖z‖))) (hr : 0 < r) (hc : c < r) :
    ∃ K, ∀ a, ∫ z, f z * g (z + a) ∂μ ≤ K * Real.exp (-(c * ‖a‖)) := by
  -- Spend a rate strictly between `max c 0` and `r` on the decay of `f` and `g`.
  obtain ⟨c₁, hc₁, hc₁r⟩ := exists_between (max_lt hc hr)
  obtain ⟨Kf, hKf⟩ := hf c₁ hc₁r
  obtain ⟨Kg, hKg⟩ := hg c₁ hc₁r
  refine ⟨Kf * Kg * ∫ z, Real.exp (-((c₁ - max c 0) * ‖z‖)) ∂μ, fun a ↦ ?_⟩
  have h := integral_norm_mul_norm_le_mul_exp_neg_mul_norm μ (le_max_right c 0) hc₁ hc₁.le
    (f := f) (g := g) (fun w ↦ (Real.norm_of_nonneg (hf₀ w)).trans_le (hKf w))
    (fun w ↦ (Real.norm_of_nonneg (hg₀ w)).trans_le (hKg w)) a
  simp only [Real.norm_of_nonneg (hf₀ _), Real.norm_of_nonneg (hg₀ _)] at h
  have hKfg : 0 ≤ Kf * Kg * ∫ z, Real.exp (-((c₁ - max c 0) * ‖z‖)) ∂μ :=
    nonneg_of_mul_nonneg_left ((integral_nonneg fun z ↦ mul_nonneg (hf₀ z) (hg₀ _)).trans h)
      (Real.exp_pos _)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hKfg)
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg a)))

/-- **Integrability of the overlap of nonnegative functions decaying at every rate below `r`.**
If `f` and `g` are nonnegative and almost everywhere strongly measurable, and both are at most
`K exp (-(c ‖z‖))` for every rate `c < r`, with `K` depending on `c`, then for `0 < r` the overlap
`f z g (z + a)` is integrable on a finite-dimensional space with an additive Haar measure. -/
theorem integrable_mul_comp_add_of_forall_lt {f g : E → ℝ} {r : ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ c < r, ∃ K, ∀ z, f z ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ c < r, ∃ K, ∀ z, g z ≤ K * Real.exp (-(c * ‖z‖))) (hr : 0 < r) (a : E) :
    Integrable (fun z ↦ f z * g (z + a)) μ := by
  obtain ⟨Kf, hKf⟩ := hf (r / 2) (half_lt_self hr)
  obtain ⟨Kg, hKg⟩ := hg 0 hr
  exact integrable_mul_comp_add μ (half_pos hr) hfm hgm
    (fun z ↦ (Real.norm_of_nonneg (hf₀ z)).trans_le (hKf z))
    (fun z ↦ (Real.norm_of_nonneg (hg₀ z)).trans_le (by simpa using hKg z)) a

/-- **Radial exponentials about finitely many centres are integrable.** For `0 < a` and a finite
multiset `S` of centres, `z ↦ ∑_{x ∈ S} exp (-(a ‖z - x‖))` is integrable on a finite-dimensional
space for every additive Haar measure. -/
theorem integrable_sum_map_exp_neg_mul_norm_sub {a : ℝ} (ha : 0 < a) (S : Multiset E) :
    Integrable (fun z ↦ (S.map fun x ↦ Real.exp (-(a * ‖z - x‖))).sum) μ := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact ((integrable_exp_neg_mul_norm μ ha).comp_sub_right x).add ih

/-- **The integral of radial exponentials about finitely many centres.** For `0 < a` and a finite
multiset `S` of centres, `∫ ∑_{x ∈ S} exp (-(a ‖z - x‖)) = card S ∫ exp (-(a ‖z‖))` on a
finite-dimensional space, for every additive Haar measure. -/
theorem integral_sum_map_exp_neg_mul_norm_sub {a : ℝ} (ha : 0 < a) (S : Multiset E) :
    ∫ z, (S.map fun x ↦ Real.exp (-(a * ‖z - x‖))).sum ∂μ =
      Multiset.card S * ∫ z, Real.exp (-(a * ‖z‖)) ∂μ := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [integral_add ((integrable_exp_neg_mul_norm μ ha).comp_sub_right x)
      (integrable_sum_map_exp_neg_mul_norm_sub μ ha S), ih,
      integral_sub_right_eq_self (fun z ↦ Real.exp (-(a * ‖z‖)))]
    push_cast
    ring

/-- **Overlap of functions decaying away from separated finite sets of centres, integrated.**
Let `0 ≤ c < b`. Suppose that `0 ≤ f z ≤ K exp (-(b ρ))` whenever every point of the multiset
`S` is at distance at least `ρ` from `z`, that `0 ≤ g z ≤ L exp (-(b ρ))` whenever every point of
`T` is, and that every point of `S` is at distance at least `δ` from every point of `T`. Then on a
finite-dimensional space, for every additive Haar measure,

`∫ f z g z ≤ K L (card S ∫ exp (-((b - c) ‖z‖))) exp (-(c δ))`.

The constant depends on `f`, `g`, `S` and `T` only through `K`, `L` and the number of points
of `S`. -/
theorem integral_mul_le_mul_exp_of_forall_le_norm_sub {f g : E → ℝ} {S T : Multiset E}
    {b δ : ℝ} (hc : 0 ≤ c) (hcb : c < b) (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ z ρ, (∀ a ∈ S, ρ ≤ ‖z - a‖) → f z ≤ K * Real.exp (-(b * ρ)))
    (hg : ∀ z ρ, (∀ a ∈ T, ρ ≤ ‖z - a‖) → g z ≤ L * Real.exp (-(b * ρ)))
    (hST : ∀ a ∈ S, ∀ a' ∈ T, δ ≤ ‖a - a'‖) :
    ∫ z, f z * g z ∂μ ≤
      K * L * (Multiset.card S * ∫ z, Real.exp (-((b - c) * ‖z‖)) ∂μ) *
        Real.exp (-(c * δ)) := by
  have hint := integrable_sum_map_exp_neg_mul_norm_sub μ (sub_pos.2 hcb) S
  calc ∫ z, f z * g z ∂μ
      ≤ ∫ z, K * L * Real.exp (-(c * δ)) *
          (S.map fun a ↦ Real.exp (-((b - c) * ‖z - a‖))).sum ∂μ :=
        integral_mono_of_nonneg (.of_forall fun z ↦ mul_nonneg (hf₀ z) (hg₀ z))
          (hint.const_mul _)
          (.of_forall (mul_le_mul_exp_mul_sum_exp_of_forall_le_norm_sub hc hcb hf₀ hg₀ hf hg hST))
    _ = _ := by
      rw [integral_const_mul, integral_sum_map_exp_neg_mul_norm_sub μ (sub_pos.2 hcb)]
      ring

end Overlap

/-- The two-sided exponential is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  simpa only [neg_mul] using MeasureTheory.integrable_comp_abs
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)

/-- The two-sided exponential lies in every `Lᵖ` space of the line when `0 < a`. -/
theorem memLp_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (p : ℝ≥0∞) :
    MemLp (fun x : ℝ ↦ Real.exp (-(a * |x|))) p := by
  have hm : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (-(a * |x|))) :=
    (by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-(a * |x|))).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm
  rcases eq_or_ne p ∞ with rfl | hptop
  · refine memLp_top_of_bound hm 1 (.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    positivity
  -- The `p`-th power of the two-sided exponential is the two-sided exponential of rate `p a`.
  refine (integrable_norm_rpow_iff hm hp0 hptop).1 ((integrable_exp_neg_mul_abs
    (mul_pos (ENNReal.toReal_pos hp0 hptop) ha)).congr (.of_forall fun x ↦ ?_))
  simp only [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_mul]
  congr 1
  ring

/-- The two-sided exponential `exp (-(a * |x|))` has integral `2 / a` when `0 < a`. -/
theorem integral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * |x|)) = 2 / a := by
  rw [integral_comp_abs (f := fun x ↦ Real.exp (-(a * x)))]
  simp only [← neg_mul]
  rw [integral_exp_mul_Ioi (neg_neg_of_pos ha), mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

/-- The lower Lebesgue integral of a constant multiple of the two-sided exponential:
`∫⁻ x, ofReal (c * exp (-(a * |x|))) = ofReal (2 * c / a)` when `0 < a`. For `c ≤ 0` both sides
vanish. -/
theorem lintegral_ofReal_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (c * Real.exp (-(a * |x|))) = ENNReal.ofReal (2 * c / a) := by
  rcases le_total 0 c with hc | hc
  · rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_abs ha).const_mul c)
      (.of_forall fun _ ↦ by positivity), integral_const_mul, integral_exp_neg_mul_abs ha]
    ring_nf
  · have hc' : 2 * c / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
    simp only [ENNReal.ofReal_of_nonpos hc',
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc (Real.exp_pos _).le),
      lintegral_zero]

/-- The two-sided exponential times a unimodular oscillation `exp (b * x * I)` is integrable on
the line. -/
theorem integrable_exp_mul_I_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)) :=
  ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
    (.of_forall fun x ↦ by simp [Complex.norm_exp])

/-- Any real power of `1 + |x|` times a two-sided decaying exponential `exp (-(a * |x|))` is
integrable on the line when `0 < a`. -/
theorem integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (K : ℝ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ (1 + |x|) ^ K * Real.exp (-(a * |x|))) := by
  set M : ℝ := max K 0
  have hM : 0 ≤ M := le_max_right K 0
  set c : ℝ := a / (2 * (M + 1))
  have hc : 0 < c := by positivity
  refine ((integrable_exp_neg_mul_abs (half_pos ha)).const_mul ((max 1 c⁻¹) ^ M)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact ((continuous_const.add continuous_abs).rpow_const fun x ↦
      Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg x)).ne').mul (by fun_prop)
  · refine .of_forall fun x ↦ ?_
    have h1x : 1 ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
    have hlin : 1 + |x| ≤ max 1 c⁻¹ * Real.exp (c * |x|) := by
      calc 1 + |x| = 1 * 1 + c⁻¹ * (c * |x|) := by
              rw [inv_mul_cancel_left₀ hc.ne', one_mul]
        _ ≤ max 1 c⁻¹ * 1 + max 1 c⁻¹ * (c * |x|) :=
              add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le_one)
                (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        _ = max 1 c⁻¹ * (c * |x| + 1) := by ring
        _ ≤ max 1 c⁻¹ * Real.exp (c * |x|) :=
              mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
    have hrpow : (1 + |x|) ^ K ≤ (max 1 c⁻¹) ^ M * Real.exp (a / 2 * |x|) := by
      calc (1 + |x|) ^ K ≤ (1 + |x|) ^ M :=
              Real.rpow_le_rpow_of_exponent_le h1x (le_max_left K 0)
        _ ≤ (max 1 c⁻¹ * Real.exp (c * |x|)) ^ M :=
              Real.rpow_le_rpow (by positivity) hlin hM
        _ = (max 1 c⁻¹) ^ M * (Real.exp (c * |x|)) ^ M :=
              Real.mul_rpow (by positivity) (Real.exp_pos _).le
        _ = (max 1 c⁻¹) ^ M * Real.exp (c * |x| * M) := by
              rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        _ ≤ (max 1 c⁻¹) ^ M * Real.exp (a / 2 * |x|) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
              have hMc : c * (M + 1) = a / 2 := by
                dsimp [c]
                field_simp
              nlinarith [abs_nonneg x]
    rw [Real.norm_of_nonneg (by positivity)]
    calc (1 + |x|) ^ K * Real.exp (-(a * |x|))
        ≤ (max 1 c⁻¹) ^ M * Real.exp (a / 2 * |x|) * Real.exp (-(a * |x|)) :=
            mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
      _ = (max 1 c⁻¹) ^ M * Real.exp (-(a / 2 * |x|)) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring

/-- At a nonnegative rate the integrand is bounded below by a positive constant on `(c, ∞)`, a set
of infinite measure, so it is not integrable there. -/
private theorem not_integrableOn_exp_mul_Ioi {a c : ℝ} (ha : 0 ≤ a) :
    ¬ IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) := by
  intro h
  have hsub : Set.Ioi c ⊆ {x : ℝ | Real.exp (a * c) ≤ Real.exp (a * x)} := by
    intro x hx
    exact Real.exp_le_exp.2 (by nlinarith [le_of_lt (Set.mem_Ioi.mp hx)])
  have h1 : (volume.restrict (Set.Ioi c)) (Set.Ioi c) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (h.measure_ge_lt_top (Real.exp_pos (a * c)))
  rw [Measure.restrict_apply_self, Real.volume_Ioi] at h1
  exact absurd h1 (by simp)

/-- **The exact integrability rate.**  `fun x => exp (a * x)` is integrable on `(c, ∞)` precisely
when the rate is negative.  Mathlib's `integrableOn_exp_mul_Ioi` is the `←` direction. -/
@[simp]
theorem integrableOn_exp_mul_Ioi_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) ↔ a < 0 := by
  refine ⟨fun h => ?_, fun ha => integrableOn_exp_mul_Ioi ha c⟩
  by_contra hne
  exact not_integrableOn_exp_mul_Ioi (not_lt.mp hne) h

/-- **The exact integrability rate on a left half-line.** `fun x => exp (a * x)` is integrable
on `(-∞, c]` precisely when the rate is positive. -/
@[simp]
theorem integrableOn_exp_mul_Iic_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Iic c) ↔ 0 < a := by
  rw [integrableOn_Iic_iff_integrableOn_Iio,
    ← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_neg, mul_neg, neg_mul,
    neg_lt_zero] using (integrableOn_exp_mul_Ioi_iff (a := -a) (c := -c))

/-- At a positive rate `0 < a`, `exp (a * x)` dominates `x ^ (-s)` for large `x`, so
`x ↦ x ^ s * exp (a * x)` is not integrable on `(c, ∞)` for any `c : ℝ`. -/
theorem not_integrableOn_rpow_mul_exp_mul_Ioi {a s c : ℝ} (ha : 0 < a) :
    ¬ IntegrableOn (fun x : ℝ => x ^ s * Real.exp (a * x)) (Set.Ioi c) := by
  refine MeasureTheory.not_integrableOn_Ioi_of_eventually_le_norm one_pos c ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    (tendsto_exp_mul_div_rpow_atTop (-s) a ha).eventually_ge_atTop 1] with x hx hge
  rw [Real.rpow_neg hx.le, div_inv_eq_mul, mul_comm] at hge
  exact hge.trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)

/-- On a right half-line `(c, ∞)` bounded away from zero (`0 < c`), a real power times an
exponential `x ↦ x ^ s * exp (a * x)` is integrable precisely when either `a < 0`, or `a = 0` and
`s < -1`. -/
@[simp]
theorem integrableOn_rpow_mul_exp_mul_Ioi_iff {a s c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.exp (a * x)) (Set.Ioi c) ↔
      a < 0 ∨ (a = 0 ∧ s < -1) := by
  refine ⟨fun hint => ?_, fun h => ?_⟩
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · exact Or.inl ha
    · refine Or.inr ⟨rfl, (integrableOn_Ioi_rpow_iff hc).mp ?_⟩
      simpa using hint
    · exact absurd hint (not_integrableOn_rpow_mul_exp_mul_Ioi ha)
  · -- For `a < 0`, dominate `(x / c) ^ s ≤ (x / c) ^ max s 0` across `c < x`.
    rcases h with ha | ⟨rfl, hs⟩
    · set s' := max s 0
      have hs' : -1 < s' := lt_of_lt_of_le (by norm_num) (le_max_right s 0)
      have hbase : IntegrableOn (fun x : ℝ => x ^ s' * Real.exp (a * x)) (Set.Ioi c) := by
        refine ((integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs' one_pos
          (neg_pos.mpr ha)).mono_set (Set.Ioi_subset_Ioi hc.le)).congr_fun (fun x _ => ?_)
          measurableSet_Ioi
        simp
      refine Integrable.mono' (hbase.const_mul (c ^ s * (c ^ s')⁻¹))
        (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hc.trans hx
      have hdiv : (x / c) ^ s ≤ (x / c) ^ s' :=
        Real.rpow_le_rpow_of_exponent_le ((one_le_div hc).mpr hx.le) (le_max_left s 0)
      rw [Real.div_rpow hx0.le hc.le, Real.div_rpow hx0.le hc.le,
        div_le_iff₀ (Real.rpow_pos_of_pos hc s), div_eq_mul_inv] at hdiv
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc x ^ s * Real.exp (a * x)
          ≤ (x ^ s' * (c ^ s')⁻¹ * c ^ s) * Real.exp (a * x) :=
            mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)
        _ = c ^ s * (c ^ s')⁻¹ * (x ^ s' * Real.exp (a * x)) := by ring
    · simpa using integrableOn_Ioi_rpow_of_lt hs hc

/-- Sufficient condition for integrability of `x ↦ x ^ s * exp (-a * x)` on `(c, ∞)` (`0 < c`):
either positive decay rate `0 < a`, or nonnegative rate `0 ≤ a` with integrable power `s < -1`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi_of_pos {a s c : ℝ} (hc : 0 < c)
    (h : 0 < a ∨ (0 ≤ a ∧ s < -1)) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-a * x)) (Set.Ioi c) := by
  rw [integrableOn_rpow_mul_exp_mul_Ioi_iff hc]
  rcases h with ha | ⟨ha, hs⟩
  · exact Or.inl (neg_lt_zero.mpr ha)
  · rcases ha.eq_or_lt with rfl | ha'
    · exact Or.inr ⟨neg_zero, hs⟩
    · exact Or.inl (neg_lt_zero.mpr ha')

end TauCeti
