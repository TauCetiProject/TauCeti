/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Exponential integrals on the real line and radial exponentials

This file records integrability and evaluation of exponential integrands: on a half-line or the
whole real line, natural powers multiplied by an exponentially decaying factor, the exact rate at
which a bare exponential is integrable on a right half-line, and integrability and the integral
of the two-sided exponential; and, on a finite-dimensional real normed space, integrability of the
radial exponential `exp (-a ‖x‖)` for every additive Haar measure, by integrating in polar
coordinates. The radial exponential then bounds the overlap of two functions that decay
exponentially about two points: it decays exponentially in the distance between the points.

Mathlib supplies the *sufficient* direction of the right-half-line integrability criterion,
`integrableOn_exp_mul_Ioi`, for a negative rate.  `integrableOn_exp_mul_Ioi_iff` adds the converse,
which is what lets a caller describe an exponential-moment domain as an exact set rather than an
inclusion.

## Main results

* `TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi`: integrability on `(0, ∞)`.
* `TauCeti.integral_pow_mul_exp_neg_mul_Ioi`: evaluation in terms of a factorial.
* `TauCeti.lintegral_ofReal_exp_neg_mul_mul_lintegral`: an iterated exponential integral is a
  Stieltjes-kernel integral.
* `TauCeti.integrableOn_exp_mul_Ioi_iff`: `exp (a * ·)` is integrable on `(c, ∞)` exactly when
  `a < 0`.
* `TauCeti.integrableOn_exp_mul_Iic_iff`: `exp (a * ·)` is integrable on `(-∞, c]` exactly when
  `0 < a`.
* `TauCeti.integrable_exp_neg_mul_abs`: `exp (-(a * |·|))` is integrable when `0 < a`.
* `TauCeti.integral_exp_neg_mul_abs`: its integral is `2 / a`.
* `TauCeti.lintegral_ofReal_mul_exp_neg_mul_abs`: the same evaluation as a lower Lebesgue integral
  of `c * exp (-(a * |·|))`.
* `TauCeti.integrable_exp_mul_I_mul_exp_neg_mul_abs`: the same times the oscillation
  `exp (b * x * I)`.
* `TauCeti.integrable_exp_neg_mul_norm`: `exp (-(a * ‖·‖))` is integrable on a finite-dimensional
  space when `0 < a`.
* `TauCeti.norm_mul_norm_le_mul_exp_neg_mul_norm` and
  `TauCeti.exists_integral_norm_mul_norm_le_mul_exp_neg_mul_norm`: two functions decaying
  exponentially at rate `c` about points at distance `‖a‖` overlap, pointwise and after
  integration, by `O(exp (-(c' ‖a‖)))`, with `c' = c` pointwise and every `c' < c` for the
  integral. `TauCeti.exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt` and
  `TauCeti.exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt` restate this for
  nonnegative functions decaying at every rate below a threshold.
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

section Overlap

variable {E F G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup G] {f : E → F} {g : E → G} {K L c : ℝ}

/-- The overlap of two functions decaying at rate `c` about `0` and about `-a`, with part
`b ≤ c` of the rate spent on the separation `‖a‖` and the rest kept as decay in `z`. -/
private theorem norm_mul_norm_le_mul_exp_mul_exp {b : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c * ‖z‖))) (z a : E) :
    ‖f z‖ * ‖g (z + a)‖ ≤ K * L * Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖)) := by
  have hK : 0 ≤ K * Real.exp (-(c * ‖z‖)) := (norm_nonneg _).trans (hf z)
  -- `‖a‖ ≤ ‖z‖ + ‖z + a‖`, so the two decay factors together beat `exp (-(b ‖a‖))`.
  have ha : ‖a‖ ≤ ‖z‖ + ‖z + a‖ := by
    simpa [add_comm ‖z‖] using norm_sub_le (z + a) z
  have hexp : Real.exp (-(c * ‖z‖)) * Real.exp (-(c * ‖z + a‖)) ≤
      Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [norm_nonneg (z + a), mul_le_mul_of_nonneg_left ha hb]
  have hKL : 0 ≤ K * L := by
    have hK' : 0 ≤ K := nonneg_of_mul_nonneg_left hK (Real.exp_pos _)
    have hL' : 0 ≤ L :=
      nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hg z)) (Real.exp_pos _)
    positivity
  calc ‖f z‖ * ‖g (z + a)‖
      ≤ K * Real.exp (-(c * ‖z‖)) * (L * Real.exp (-(c * ‖z + a‖))) :=
        mul_le_mul (hf z) (hg _) (norm_nonneg _) hK
    _ = K * L * (Real.exp (-(c * ‖z‖)) * Real.exp (-(c * ‖z + a‖))) := by ring
    _ ≤ K * L * (Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖))) :=
        mul_le_mul_of_nonneg_left hexp hKL
    _ = _ := by ring

/-- **Overlap of exponentially decaying functions, pointwise.** If `‖f z‖ ≤ K exp (-(c ‖z‖))`
and `‖g z‖ ≤ L exp (-(c ‖z‖))` with `0 ≤ c`, then the product of `f` and of the translate
`g (· + a)`, which decays about `-a`, is at most `K L exp (-(c ‖a‖))` everywhere. -/
theorem norm_mul_norm_le_mul_exp_neg_mul_norm (hc : 0 ≤ c)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c * ‖z‖))) (z a : E) :
    ‖f z‖ * ‖g (z + a)‖ ≤ K * L * Real.exp (-(c * ‖a‖)) := by
  simpa using norm_mul_norm_le_mul_exp_mul_exp hc le_rfl hf hg z a

/-- **Overlap of exponentially decaying functions, integrated.** If `‖f z‖ ≤ K exp (-(c ‖z‖))`
and `‖g z‖ ≤ L exp (-(c ‖z‖))` on a finite-dimensional space with `0 < c`, then for every rate
`c' < c` the overlap integral `∫ ‖f z‖ ‖g (z + a)‖` of `f` with the translate `g (· + a)` is at
most `C exp (-(c' ‖a‖))`, for every additive Haar measure and with `C` independent of `a`. -/
theorem exists_integral_norm_mul_norm_le_mul_exp_neg_mul_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} {g : E → G} {c' : ℝ} (hc : 0 < c)
    (hc' : c' < c) (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c * ‖z‖))) :
    ∃ C, ∀ a, ∫ z, ‖f z‖ * ‖g (z + a)‖ ∂μ ≤ C * Real.exp (-(c' * ‖a‖)) := by
  set b := max c' 0
  have hδ : 0 < c - b := sub_pos.2 (max_lt hc' hc)
  refine ⟨K * L * ∫ z, Real.exp (-((c - b) * ‖z‖)) ∂μ, fun a ↦ ?_⟩
  have hint := integrable_exp_neg_mul_norm μ hδ
  calc ∫ z, ‖f z‖ * ‖g (z + a)‖ ∂μ
      ≤ ∫ z, K * L * Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖)) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun z ↦ by positivity) (hint.const_mul _)
          (.of_forall fun z ↦ norm_mul_norm_le_mul_exp_mul_exp (le_max_right _ _)
            (max_le hc'.le hc.le) hf hg z a)
    _ = K * L * Real.exp (-(b * ‖a‖)) * ∫ z, Real.exp (-((c - b) * ‖z‖)) ∂μ :=
        integral_const_mul _ _
    _ ≤ K * L * Real.exp (-(c' * ‖a‖)) * ∫ z, Real.exp (-((c - b) * ‖z‖)) ∂μ := by
        have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf 0))
          (Real.exp_pos _)
        have hL : 0 ≤ L := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hg 0))
          (Real.exp_pos _)
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (integral_nonneg fun z ↦ (Real.exp_pos _).le)
        exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (norm_nonneg a)))
    _ = _ := by ring

/-- **Overlap of nonnegative functions decaying at every rate below `r`, pointwise.** If
`0 ≤ f`, `0 ≤ g` and both are at most `K exp (-(c ‖z‖))` for every rate `c < r`, with `K`
depending on `c`, then `f z g (z + a) ≤ K exp (-(c ‖a‖))` for every rate `c < r`. -/
theorem exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt {f g : E → ℝ} {r : ℝ}
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ c < r, ∃ K, ∀ z, f z ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ c < r, ∃ K, ∀ z, g z ≤ K * Real.exp (-(c * ‖z‖))) (hr : 0 < r) (hc : c < r) :
    ∃ K, ∀ z a, f z * g (z + a) ≤ K * Real.exp (-(c * ‖a‖)) := by
  obtain ⟨Kf, hKf⟩ := hf (max c 0) (max_lt hc hr)
  obtain ⟨Kg, hKg⟩ := hg (max c 0) (max_lt hc hr)
  refine ⟨Kf * Kg, fun z a ↦ ?_⟩
  have h := norm_mul_norm_le_mul_exp_neg_mul_norm (le_max_right c 0) (f := f) (g := g)
    (fun w ↦ (Real.norm_of_nonneg (hf₀ w)).trans_le (hKf w))
    (fun w ↦ (Real.norm_of_nonneg (hg₀ w)).trans_le (hKg w)) z a
  rw [Real.norm_of_nonneg (hf₀ z), Real.norm_of_nonneg (hg₀ _)] at h
  have hKfg : 0 ≤ Kf * Kg :=
    nonneg_of_mul_nonneg_left ((mul_nonneg (hf₀ z) (hg₀ (z + a))).trans h) (Real.exp_pos _)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hKfg)
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg a)))

/-- **Overlap of nonnegative functions decaying at every rate below `r`, integrated.** If
`0 ≤ f`, `0 ≤ g` and both are at most `K exp (-(c ‖z‖))` for every rate `c < r`, with `K`
depending on `c`, then `∫ f z g (z + a) ≤ K exp (-(c ‖a‖))` for every rate `c < r`, on a
finite-dimensional space with an additive Haar measure. -/
theorem exists_integral_mul_le_mul_exp_neg_mul_norm_of_forall_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {f g : E → ℝ} {r : ℝ}
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ c < r, ∃ K, ∀ z, f z ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ c < r, ∃ K, ∀ z, g z ≤ K * Real.exp (-(c * ‖z‖))) (hr : 0 < r) (hc : c < r) :
    ∃ K, ∀ a, ∫ z, f z * g (z + a) ∂μ ≤ K * Real.exp (-(c * ‖a‖)) := by
  -- Spend a rate strictly between `max c 0` and `r` on the decay of `f` and `g`.
  obtain ⟨c₁, hc₁, hc₁r⟩ := exists_between (max_lt hc hr)
  obtain ⟨Kf, hKf⟩ := hf c₁ hc₁r
  obtain ⟨Kg, hKg⟩ := hg c₁ hc₁r
  obtain ⟨K, hK⟩ := exists_integral_norm_mul_norm_le_mul_exp_neg_mul_norm μ
    ((le_max_right c 0).trans_lt hc₁) ((le_max_left c 0).trans_lt hc₁) (f := f) (g := g)
    (fun w ↦ (Real.norm_of_nonneg (hf₀ w)).trans_le (hKf w))
    (fun w ↦ (Real.norm_of_nonneg (hg₀ w)).trans_le (hKg w))
  refine ⟨K, fun a ↦ (le_of_eq (integral_congr_ae (.of_forall fun z ↦ ?_))).trans (hK a)⟩
  simp only [Real.norm_of_nonneg (hf₀ z), Real.norm_of_nonneg (hg₀ (z + a))]

end Overlap

/-- The two-sided exponential is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  simpa only [neg_mul] using MeasureTheory.integrable_comp_abs
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)

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

end TauCeti
