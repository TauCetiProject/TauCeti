/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Completeness of the Fourier sine system on an interval

On an interval `[a, b]` the functions `x ↦ sin (k π (x - a) / (b - a))`, `k = 1, 2, …`, are the
eigenfunctions of `-d²/dx²` with zero boundary values at both ends. This file proves that they
form a **complete** system in `L²(a, b)`: a square integrable function orthogonal to all of them
vanishes almost everywhere (`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`).

The proof reduces to Mathlib's completeness of the exponentials on a circle. Extend `g` oddly
about `a` to `[2a - b, b]`. On this interval of length `2(b - a)`, the `n`-th Fourier coefficient
of the odd extension is a nonzero multiple of `∫ g(x) sin (n π (x - a) / (b - a)) dx`, so all of
them vanish, and Parseval's identity (`hasSum_sq_fourierCoeffOn`) forces the extension, hence `g`,
to vanish almost everywhere. The first step is recorded separately: a square integrable function
on `(a, b]` whose Fourier coefficients on `[a, b]` all vanish is zero almost everywhere
(`TauCeti.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero`).

## Main results

* `TauCeti.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero`: uniqueness of Fourier coefficients of
  square integrable functions on an interval.
* `TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`: completeness of the sine system
  `sin (k π (x - a) / (b - a))`, `k ≥ 1`, in `L²(a, b)`.

## References

* G. B. Folland, *Fourier Analysis and its Applications*, Section 2.4 (odd extensions and
  Fourier sine series) and Section 3.4 (completeness of the trigonometric system).
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

/-- **A square integrable function with vanishing Fourier coefficients is zero.** If `f` is square
integrable on `(a, b]` and every Fourier coefficient of `f` on `[a, b]` vanishes, then `f = 0`
almost everywhere on `(a, b]`. This is Parseval's identity `hasSum_sq_fourierCoeffOn`. -/
theorem ae_eq_zero_of_forall_fourierCoeffOn_eq_zero (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b))) (h : ∀ n : ℤ, fourierCoeffOn hab f n = 0) :
    f =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hsum := hasSum_sq_fourierCoeffOn hab hf
  simp only [h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsum
  have h0 := hasSum_zero.unique hsum
  rw [eq_comm, smul_eq_mul, mul_eq_zero, integral_of_le hab.le] at h0
  have hint : ∫ x in Ioc a b, ‖f x‖ ^ 2 = 0 :=
    h0.resolve_left (inv_ne_zero (sub_pos.2 hab).ne')
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun x => by positivity)
    (hf.integrable_norm_pow' (p := 2))).1 hint] with x hx
  simpa using hx

/-! ### Completeness of the sine system -/

/-- The difference of a Fourier monomial on `[2a - b, b]` at `y` and at its reflection `2a - y`
about `a` is a multiple of `sin (n π (y - a) / (b - a))`. -/
private theorem fourier_sub_fourier_reflect (hab : a < b) (n : ℤ) (y : ℝ) :
    fourier (-n) (y : AddCircle (b - (2 * a - b))) -
        fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b))) =
      -2 * I * exp (-(π * I * n * a / (b - a))) * (Real.sin (n * π * (y - a) / (b - a)) : ℂ) := by
  have hba : (b : ℂ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.ne')
  set C : ℂ := -(π * I * n * a / (b - a))
  set Y : ℂ := ((n * π * (y - a) / (b - a) : ℝ) : ℂ)
  have hrhs : -2 * I * exp C * ((exp (-Y * I) - exp (Y * I)) * I / 2) =
      exp (C + -Y * I) - exp (C + Y * I) := by
    rw [exp_add, exp_add]
    linear_combination (-(exp C * exp (-Y * I) - exp C * exp (Y * I))) * I_sq
  rw [fourier_coe_apply, fourier_coe_apply, ofReal_sin, sin, hrhs]
  congr 2 <;>
  · simp only [C, Y]
    push_cast
    rw [show (b : ℂ) - (2 * a - b) = 2 * (b - a) by ring]
    field_simp
    ring

/-- Orthogonality to the sines `sin (k π (x - a) / (b - a))` for `k ≥ 1` extends to every integer
frequency, since `sin` is odd. -/
private theorem integral_mul_sin_intCast_eq_zero {g : ℝ → ℝ}
    (h : ∀ k : ℕ, 0 < k → ∫ x in a..b, g x * Real.sin (k * π * (x - a) / (b - a)) = 0)
    (n : ℤ) : ∫ x in a..b, g x * Real.sin (n * π * (x - a) / (b - a)) = 0 := by
  rcases n with k | k
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simpa using h k hk
  · have hk := h (k + 1) k.succ_pos
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_mul, neg_div, Real.sin_neg,
      mul_neg, intervalIntegral.integral_neg, neg_eq_zero]
    simpa using hk

open Classical in
/-- The odd extension of `g` about `a`: equal to `g` to the right of `a` and to
`x ↦ -g (2a - x)` at and to the left of `a`. -/
private noncomputable def oddExtension (a : ℝ) (g : ℝ → ℝ) : ℝ → ℂ :=
  (Ioi a).piecewise (fun x => (g x : ℂ)) fun x => -(g (2 * a - x) : ℂ)

private theorem oddExtension_of_lt {g : ℝ → ℝ} {x : ℝ} (hx : a < x) :
    oddExtension a g x = g x := by
  rw [oddExtension, Set.piecewise_eq_of_mem _ _ _ (by simpa using hx)]

private theorem oddExtension_of_le {g : ℝ → ℝ} {x : ℝ} (hx : x ≤ a) :
    oddExtension a g x = -(g (2 * a - x) : ℂ) := by
  rw [oddExtension, Set.piecewise_eq_of_notMem _ _ _ (by simpa using hx)]

/-- The odd extension of a function square integrable on `(a, b]` is square integrable on
`(2a - b, b]`. -/
private theorem memLp_oddExtension (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    MemLp (oddExtension a g) 2 (volume.restrict (Ioc (2 * a - b) b)) := by
  classical
  have hset1 : Ioi a ∩ Ioc (2 * a - b) b = Ioc a b := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, by linarith [hx.1], hx.2⟩⟩
  have hset2 : (Ioi a)ᶜ ∩ Ioc (2 * a - b) b = Ioc (2 * a - b) a := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Ioi, not_lt, mem_Ioc]
    exact ⟨fun hx => ⟨hx.2.1, hx.1⟩, fun hx => ⟨hx.2, hx.1, by linarith [hx.2]⟩⟩
  refine MemLp.piecewise measurableSet_Ioi.nullMeasurableSet ?_ ?_
  · rw [Measure.restrict_restrict measurableSet_Ioi, hset1]
    exact hg.ofReal
  · rw [Measure.restrict_restrict measurableSet_Ioi.compl, hset2]
    -- The reflection `x ↦ 2a - x` carries `(2a - b, a]` onto `[a, b)`, preserving measure.
    have hmp : MeasurePreserving (fun x => 2 * a - x) (volume.restrict (Ioc (2 * a - b) a))
        (volume.restrict (Ico a b)) := by
      have := ((volume : Measure ℝ).measurePreserving_sub_left (2 * a)).restrict_preimage
        (measurableSet_Ico (a := a) (b := b))
      rwa [preimage_const_sub_Ico, show 2 * a - a = a by ring] at this
    have hg' : MemLp g 2 (volume.restrict (Ico a b)) := by
      rwa [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact (hg'.ofReal.comp_measurePreserving hmp).neg

/-- Integrating a continuous `F` against the odd extension of `g` over `[2a - b, b]` folds the
left half onto `[a, b]` by the substitution `x = 2a - y`. -/
private theorem integral_mul_oddExtension (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) {F : ℝ → ℂ} (hFc : Continuous F) :
    ∫ x in (2 * a - b)..b, F x * oddExtension a g x =
      ∫ y in a..b, (F y - F (2 * a - y)) * (g y : ℂ) := by
  have hgi : IntervalIntegrable (fun x => (g x : ℂ)) volume a b := by
    have : IsFiniteMeasure (volume.restrict (Ioc a b)) := isFiniteMeasure_restrict.2 (by simp)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (hg.ofReal.integrable one_le_two)
  have hgi' : IntervalIntegrable (fun x => (g (2 * a - x) : ℂ)) volume (2 * a - b) a := by
    simpa [show 2 * a - a = a by ring] using (hgi.comp_sub_left (2 * a)).symm
  -- On `[2a - b, a]` substitute `x = 2a - y`; on `(a, b]` the extension is `g` itself.
  have hleft : ∫ x in (2 * a - b)..a, F x * oddExtension a g x =
      ∫ y in a..b, F (2 * a - y) * -(g y : ℂ) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun x => F x * -(g (2 * a - x) : ℂ)) (a := a) (b := b) (2 * a)
    simp only [sub_sub_cancel, show 2 * a - a = a by ring] at hsub
    rw [hsub]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [oddExtension_of_le hx.2]
  have hright : ∫ x in a..b, F x * oddExtension a g x = ∫ y in a..b, F y * (g y : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hab.le] at hx
    rw [oddExtension_of_lt hx.1]
  have hint1 : IntervalIntegrable (fun y => F y * (g y : ℂ)) volume a b :=
    hgi.continuousOn_mul hFc.continuousOn
  have hint2 : IntervalIntegrable (fun y => F (2 * a - y) * -(g y : ℂ)) volume a b :=
    hgi.neg.continuousOn_mul (hFc.comp (continuous_const.sub continuous_id)).continuousOn
  have hintL : IntervalIntegrable (fun x => F x * oddExtension a g x) volume (2 * a - b) a := by
    refine (hgi'.neg.continuousOn_mul hFc.continuousOn).congr_ae ?_
    rw [uIoc_of_le (by linarith)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Pi.neg_apply, oddExtension_of_le hx.2]
  have hintR : IntervalIntegrable (fun x => F x * oddExtension a g x) volume a b := by
    refine hint1.congr_ae ?_
    rw [uIoc_of_le hab.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [oddExtension_of_lt hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hintL hintR, hleft, hright,
    ← intervalIntegral.integral_add hint2 hint1]
  congr 1 with y
  ring

/-- The Fourier coefficients on `[2a - b, b]` of the odd extension of `g` about `a` are multiples
of the integrals of `g` against `sin (n π (x - a) / (b - a))` over `[a, b]`; under orthogonality
to all of these they vanish. -/
private theorem fourierCoeffOn_oddExtension_eq_zero (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (hZ : ∀ n : ℤ, ∫ x in a..b, g x * Real.sin (n * π * (x - a) / (b - a)) = 0) (n : ℤ) :
    fourierCoeffOn (by linarith : 2 * a - b < b) (oddExtension a g) n = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul]
  rw [integral_mul_oddExtension hab hg
    (F := fun x : ℝ => fourier (-n) (x : AddCircle (b - (2 * a - b))))
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _))]
  have hpt : ∀ y : ℝ, (fourier (-n) (y : AddCircle (b - (2 * a - b))) -
      fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b)))) * (g y : ℂ) =
        -2 * I * exp (-(π * I * n * a / (b - a))) *
          ((g y * Real.sin (n * π * (y - a) / (b - a)) : ℝ) : ℂ) := fun y => by
    rw [fourier_sub_fourier_reflect hab n y, ofReal_mul]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hZ n]
  simp

/-- **Completeness of the Fourier sine system.** A function `g` square integrable on `(a, b]` with

`∫ x in a..b, g x * sin (k π (x - a) / (b - a)) = 0` for every `k ≥ 1`

vanishes almost everywhere on `(a, b]`. These sines are the Dirichlet eigenfunctions of
`-d²/dx²` on `(a, b)`, so this is the completeness half of the Fourier sine expansion. -/
theorem ae_eq_zero_of_forall_integral_mul_sin_eq_zero (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (h : ∀ k : ℕ, 0 < k → ∫ x in a..b, g x * Real.sin (k * π * (x - a) / (b - a)) = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hzero := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_left (by linarith : 2 * a - b ≤ a))
    (ae_eq_zero_of_forall_fourierCoeffOn_eq_zero _ (memLp_oddExtension hab hg)
      (fourierCoeffOn_oddExtension_eq_zero hab hg (integral_mul_sin_intCast_eq_zero h)))
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioc] with x hx hxm
  rw [Pi.zero_apply, oddExtension_of_lt hxm.1] at hx
  exact_mod_cast hx

end TauCeti
