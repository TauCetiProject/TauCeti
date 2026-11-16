/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.FourierCoeffOn

/-!
# Complex shifts and global Fourier series of entire periodic functions

Let `f : ℂ → E` be an entire function with values in a complex normed space `E` and real period `T`.
Shifting the argument of `f` by any complex vector `z` leaves its period integral unchanged
(`Differentiable.intervalIntegral_comp_add_eq`): real shifts are absorbed by real periodicity, while
vertical shifts apply Cauchy's rectangle theorem with vertical sides cancelling by periodicity. No
completeness assumption on `E` or sign assumption on `T` is needed for the period integral.

Applying this invariance to the integrand `w ↦ e^{-2πinw/(b-a)} • f w` shows that translating `f` by
`z ∈ ℂ` multiplies its `n`-th Fourier coefficient on `[a, b]` by `e^{2πinz/(b-a)}`
(`Differentiable.fourierCoeffOn_comp_add`). When `E` is complete, two entire `(b - a)`-periodic
functions with the same Fourier coefficients on `[a, b]` agree throughout `ℂ`
(`Differentiable.eq_of_forall_fourierCoeffOn_eq`).

For scalar entire periodic functions `f : ℂ → ℂ`, smoothness on `ℝ / (b - a)ℤ` makes the Fourier
coefficients summable, and evaluating the Fourier series of the translated function `w ↦ f (w + z)`
at `0` expands `f z` as the convergent bilateral series
`∑_{n ∈ ℤ} c_n e^{2πinz/(b-a)}` at every complex point `z`
(`Differentiable.hasSum_fourierCoeffOn_mul_cexp`).

## Main results

* `Differentiable.intervalIntegral_comp_add_eq`: for entire `T`-periodic `f : ℂ → E`,
  `∫ x in a..a + T, f (x + z) = ∫ x in b..b + T, f (x + w)`.
* `Differentiable.fourierCoeffOn_comp_add`: complex translation multiplies the `n`-th Fourier
  coefficient on `[a, b]` of an entire `(b - a)`-periodic function by `e^{2πinz/(b-a)}`.
* `Differentiable.fourierCoeffOn_zero_comp_add`: specialization to `[0, T]` with `0 < T`.
* `Differentiable.eq_of_forall_fourierCoeffOn_eq` and
  `Differentiable.eq_of_forall_fourierCoeffOn_zero_eq`: Fourier coefficients on `[a, b]` (or
  `[0, T]`) determine an entire periodic function `ℂ → E` (`[CompleteSpace E]`) on all of `ℂ`.
* `Differentiable.hasSum_fourierCoeffOn_mul_cexp`,
  `Differentiable.summable_fourierCoeffOn_mul_cexp`, and
  `Differentiable.tsum_fourierCoeffOn_mul_cexp` (together with `[0, T]` specializations): global
  complex Fourier expansion of an entire `(b - a)`-periodic function `f : ℂ → ℂ`.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Princeton Lectures in Analysis II, Princeton
  University Press, 2003, Chapter 4.
-/

public section

open Complex MeasureTheory
open scoped Real

namespace Differentiable

section VectorValued

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Shifting the argument of an entire `T`-periodic function `f : ℂ → E` by a purely imaginary
offset `y * I` does not change its integral over `[0, T]`, by Cauchy's theorem on the rectangle
with opposite corners `0` and `T + y * I`. -/
private theorem intervalIntegral_zero_add_mul_I_eq {f : ℂ → E} (hf : Differentiable ℂ f)
    {T : ℝ} (hper : Function.Periodic f T) (y : ℝ) :
    ∫ x : ℝ in (0 : ℝ)..T, f (x + y * I) = ∫ x : ℝ in (0 : ℝ)..T, f x := by
  have hrect : (∫ x : ℝ in (0 : ℝ)..T, f x) - (∫ x : ℝ in (0 : ℝ)..T, f (x + y * I)) +
      I • (∫ t : ℝ in (0 : ℝ)..y, f (T + t * I)) - I • ∫ t : ℝ in (0 : ℝ)..y, f (t * I) = 0 := by
    simpa using
      integral_boundary_rect_eq_zero_of_differentiableOn f 0 (T + y * I) hf.differentiableOn
  have hside : ∫ t : ℝ in (0 : ℝ)..y, f (T + t * I) = ∫ t : ℝ in (0 : ℝ)..y, f (t * I) :=
    intervalIntegral.integral_congr fun t _ ↦ by rw [add_comm, hper]
  rw [hside, add_sub_cancel_right, sub_eq_zero] at hrect
  exact hrect.symm

/-- **Complex shift invariance of period integrals.** For an entire function `f : ℂ → E` of real
period `T`, the integral of `x ↦ f (x + z)` over `[a, a + T]` is independent of both the real
basepoint `a` and the complex shift `z`. -/
theorem intervalIntegral_comp_add_eq {f : ℂ → E} (hf : Differentiable ℂ f)
    {T : ℝ} (hper : Function.Periodic f T) (a b : ℝ) (z w : ℂ) :
    ∫ x : ℝ in a..a + T, f (x + z) = ∫ x : ℝ in b..b + T, f (x + w) := by
  have h0 (c : ℝ) (u : ℂ) : ∫ x : ℝ in c..c + T, f (x + u) = ∫ x : ℝ in (0 : ℝ)..T, f x := by
    have hper_u (v : ℂ) : Function.Periodic (fun x : ℝ ↦ f (x + v)) T := fun x ↦ by
      push_cast
      rw [add_right_comm]
      exact hper (x + v)
    have h1 := (hper_u u).intervalIntegral_add_eq c 0
    rw [zero_add] at h1
    have h2 : ∫ x : ℝ in (0 : ℝ)..T, f (x + u) =
        ∫ x : ℝ in (0 : ℝ)..T, f ((x + u.re : ℝ) + u.im * I) :=
      intervalIntegral.integral_congr fun x _ ↦ congrArg f <| by
        conv_lhs => rw [← re_add_im u]
        push_cast
        ring
    rw [h1, h2, intervalIntegral.integral_comp_add_right fun x : ℝ ↦ f (x + u.im * I), zero_add,
      add_comm T u.re]
    have h3 := (hper_u (u.im * I)).intervalIntegral_add_eq u.re 0
    rw [zero_add] at h3
    exact h3.trans (hf.intervalIntegral_zero_add_mul_I_eq hper u.im)
  exact (h0 a z).trans (h0 b w).symm

/-- Shifting an entire `T`-periodic function `f : ℂ → E` by `z ∈ ℂ` leaves its integral over
`[a, a + T]` unchanged. -/
theorem intervalIntegral_comp_add_eq_self {f : ℂ → E} (hf : Differentiable ℂ f)
    {T : ℝ} (hper : Function.Periodic f T) (a : ℝ) (z : ℂ) :
    ∫ x : ℝ in a..a + T, f (x + z) = ∫ x : ℝ in a..a + T, f x := by
  simpa using hf.intervalIntegral_comp_add_eq hper a a z 0

/-- **Complex translation of Fourier coefficients.** Translating an entire `(b - a)`-periodic
function `f : ℂ → E` by `z ∈ ℂ` multiplies its `n`-th Fourier coefficient on `[a, b]` by
`e^{2πinz/(b - a)}`. -/
theorem fourierCoeffOn_comp_add {f : ℂ → E} (hf : Differentiable ℂ f)
    {a b : ℝ} (hab : a < b) (hper : Function.Periodic f ((b - a : ℝ) : ℂ)) (z : ℂ) (n : ℤ) :
    fourierCoeffOn hab (fun x : ℝ ↦ f (x + z)) n =
      cexp (2 * π * I * n * z / (b - a)) • fourierCoeffOn hab (fun x : ℝ ↦ f x) n := by
  set T : ℝ := b - a
  have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 (sub_pos.2 hab).ne'
  let g : ℂ → E := fun w ↦ cexp (2 * π * I * (-n : ℤ) * w / T) • f w
  have hg : Differentiable ℂ g :=
    (differentiable_exp.comp ((differentiable_id.const_mul _).div_const _)).smul hf
  have hperg : Function.Periodic g T := fun w ↦ by
    simp only [g, TauCeti.periodic_cexp_two_pi_mul_I_mul_div (-n) w, hper w]
  have hint (u : ℂ) : ∫ x : ℝ in a..b, fourier (-n) (x : AddCircle T) • f (x + u) =
      cexp (2 * π * I * n * u / T) • ∫ x : ℝ in a..a + T, g (x + u) := by
    rw [show b = a + T by simp [T], ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    rw [fourier_coe_apply, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, hint z,
    hg.intervalIntegral_comp_add_eq_self hperg a z]
  have hint0 := hint 0
  simp only [add_zero, mul_zero, zero_div, Complex.exp_zero, one_smul] at hint0
  rw [← hint0, smul_comm]
  simp [T, ofReal_sub]

/-- Specialization of `Differentiable.fourierCoeffOn_comp_add` to the period interval `[0, T]`
with `0 < T`. -/
theorem fourierCoeffOn_zero_comp_add {f : ℂ → E} (hf : Differentiable ℂ f)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T) (z : ℂ) (n : ℤ) :
    fourierCoeffOn hT (fun x : ℝ ↦ f (x + z)) n =
      cexp (2 * π * I * n * z / T) • fourierCoeffOn hT (fun x : ℝ ↦ f x) n := by
  simpa [sub_zero] using hf.fourierCoeffOn_comp_add hT (by simpa [sub_zero] using hper) z n

/-- **Uniqueness of Fourier coefficients for entire periodic functions.** Two entire
`(b - a)`-periodic functions `f, g : ℂ → E` into a complete complex normed space whose Fourier
coefficients on `[a, b]` agree are equal throughout `ℂ`. -/
theorem eq_of_forall_fourierCoeffOn_eq [CompleteSpace E] {f g : ℂ → E}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {a b : ℝ} (hab : a < b)
    (hperf : Function.Periodic f ((b - a : ℝ) : ℂ))
    (hperg : Function.Periodic g ((b - a : ℝ) : ℂ))
    (h : ∀ n : ℤ, fourierCoeffOn hab (fun x : ℝ ↦ f x) n =
      fourierCoeffOn hab (fun x : ℝ ↦ g x) n) :
    f = g := by
  have hIcc := TauCeti.eqOn_Icc_of_fourierCoeffOn_eq hab
    (hf.continuous.comp continuous_ofReal).continuousOn
    (hg.continuous.comp continuous_ofReal).continuousOn h
  have hperR_f : Function.Periodic (fun x : ℝ ↦ f x) (b - a) := fun x ↦ by
    simpa [ofReal_sub] using hperf x
  have hperR_g : Function.Periodic (fun x : ℝ ↦ g x) (b - a) := fun x ↦ by
    simpa [ofReal_sub] using hperg x
  have hT : 0 < b - a := sub_pos.2 hab
  refine hf.eq_of_ofReal_eq hg fun x ↦ ?_
  -- Reduce any real `x` into `[a, b]` by subtracting a multiple of `b - a`.
  let k : ℤ := ⌊(x - a) / (b - a)⌋
  have hx_mem : x - k * (b - a) ∈ Set.Icc a b := by
    constructor
    · have hle : (k : ℝ) * (b - a) ≤ x - a :=
        (le_div_iff₀ hT).1 (Int.floor_le ((x - a) / (b - a)))
      linarith
    · have hlt : x - a < ((k : ℝ) + 1) * (b - a) :=
        (div_lt_iff₀ hT).1 (Int.lt_floor_add_one ((x - a) / (b - a)))
      linarith
  have hfx : f (x - k * (b - a) : ℝ) = f x := hperR_f.sub_int_mul_eq k
  have hgx : g (x - k * (b - a) : ℝ) = g x := hperR_g.sub_int_mul_eq k
  rw [← hfx, ← hgx]
  exact hIcc hx_mem

/-- An entire `(b - a)`-periodic function `f : ℂ → E` into a complete complex normed space whose
Fourier coefficients on `[a, b]` all vanish is identically zero on `ℂ`. -/
theorem eq_zero_of_forall_fourierCoeffOn_eq_zero [CompleteSpace E] {f : ℂ → E}
    (hf : Differentiable ℂ f) {a b : ℝ} (hab : a < b)
    (hper : Function.Periodic f ((b - a : ℝ) : ℂ))
    (h : ∀ n : ℤ, fourierCoeffOn hab (fun x : ℝ ↦ f x) n = 0) :
    f = 0 :=
  hf.eq_of_forall_fourierCoeffOn_eq (differentiable_const 0) hab hper (fun _ ↦ rfl) fun n ↦ by
    simp [h n, fourierCoeffOn_eq_integral]

/-- Specialization of `Differentiable.eq_of_forall_fourierCoeffOn_eq` to `[0, T]` with `0 < T`. -/
theorem eq_of_forall_fourierCoeffOn_zero_eq [CompleteSpace E] {f g : ℂ → E}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {T : ℝ} (hT : 0 < T)
    (hperf : Function.Periodic f T) (hperg : Function.Periodic g T)
    (h : ∀ n : ℤ, fourierCoeffOn hT (fun x : ℝ ↦ f x) n =
      fourierCoeffOn hT (fun x : ℝ ↦ g x) n) :
    f = g :=
  hf.eq_of_forall_fourierCoeffOn_eq hg hT (by simpa [sub_zero] using hperf)
    (by simpa [sub_zero] using hperg) h

/-- Specialization of `Differentiable.eq_zero_of_forall_fourierCoeffOn_eq_zero` to `[0, T]` with
`0 < T`. -/
theorem eq_zero_of_forall_fourierCoeffOn_zero_eq_zero [CompleteSpace E] {f : ℂ → E}
    (hf : Differentiable ℂ f) {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T)
    (h : ∀ n : ℤ, fourierCoeffOn hT (fun x : ℝ ↦ f x) n = 0) :
    f = 0 :=
  hf.eq_zero_of_forall_fourierCoeffOn_eq_zero hT (by simpa [sub_zero] using hper) h

end VectorValued

section ScalarValued

/-- **Global complex Fourier series of an entire periodic function.** If `f : ℂ → ℂ` is entire and
periodic of real period `b - a > 0`, then at every complex point `z` the bilateral series
`∑_{n ∈ ℤ} c_n e^{2πinz/(b - a)}`, where `c_n = fourierCoeffOn hab (fun x : ℝ ↦ f x) n`, converges
to `f z`. -/
theorem hasSum_fourierCoeffOn_mul_cexp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b : ℝ} (hab : a < b) (hper : Function.Periodic f ((b - a : ℝ) : ℂ)) (z : ℂ) :
    HasSum (fun n : ℤ ↦
      fourierCoeffOn hab (fun x : ℝ ↦ f x) n * cexp (2 * π * I * n * z / (b - a))) (f z) := by
  set T : ℝ := b - a
  have hT : 0 < T := sub_pos.2 hab
  have : Fact (0 < T) := ⟨hT⟩
  let g : ℂ → ℂ := fun w ↦ f (w + z)
  have hg : Differentiable ℂ g := hf.comp (differentiable_id.add_const z)
  have hperR : Function.Periodic (fun x : ℝ ↦ g x) T := fun x ↦ by
    dsimp only [g]
    push_cast
    rw [add_right_comm]
    exact hper (x + z)
  let G : C(AddCircle T, ℂ) :=
    ⟨hperR.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
      (hg.continuous.comp continuous_ofReal)⟩
  have hG_smooth : ContDiff ℝ 2 fun x : ℝ ↦ G x := by
    have hfun : (fun x : ℝ ↦ G x) = fun x : ℝ ↦ g x := funext hperR.lift_coe
    rw [hfun]
    exact ((hg.contDiff (n := 2)).restrict_scalars ℝ).comp ofRealCLM.contDiff
  have hsumm : Summable (fourierCoeff (G : AddCircle T → ℂ)) :=
    TauCeti.summable_fourierCoeff_of_contDiff hG_smooth
  have hsum0 := has_pointwise_sum_fourier_series_of_summable (f := G) hsumm ((0 : ℝ) : AddCircle T)
  have hG0 : G ((0 : ℝ) : AddCircle T) = f z := by
    simpa [G, g] using hperR.lift_coe 0
  have hcoeff (n : ℤ) :
      fourierCoeffOn hab (fun x : ℝ ↦ f x) n * cexp (2 * π * I * n * z / (b - a)) =
      fourierCoeff (G : AddCircle T → ℂ) n • fourier n ((0 : ℝ) : AddCircle T) := by
    have hf0 : fourier n ((0 : ℝ) : AddCircle T) = 1 := by simp
    have hFG : fourierCoeff (G : AddCircle T → ℂ) n =
        fourierCoeffOn hab (fun x : ℝ ↦ f (x + z)) n := by
      rw [fourierCoeff_eq_intervalIntegral _ n a, fourierCoeffOn_eq_integral,
        show a + T = b by simp [T]]
      rfl
    rw [hf0, smul_eq_mul, mul_one, hFG, hf.fourierCoeffOn_comp_add hab hper z n,
      smul_eq_mul, mul_comm]
  rw [← hG0]
  exact hsum0.congr_fun hcoeff

/-- The complex Fourier series `n ↦ fourierCoeffOn hab (fun x : ℝ ↦ f x) n * e^{2πinz/(b - a)}`
of an entire `(b - a)`-periodic function `f : ℂ → ℂ` is summable at every `z ∈ ℂ`. -/
theorem summable_fourierCoeffOn_mul_cexp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b : ℝ} (hab : a < b) (hper : Function.Periodic f ((b - a : ℝ) : ℂ)) (z : ℂ) :
    Summable fun n : ℤ ↦
      fourierCoeffOn hab (fun x : ℝ ↦ f x) n * cexp (2 * π * I * n * z / (b - a)) :=
  (hf.hasSum_fourierCoeffOn_mul_cexp hab hper z).summable

/-- Sum identity `∑' n, fourierCoeffOn hab (fun x : ℝ ↦ f x) n * e^{2πinz/(b - a)} = f z` for an
entire `(b - a)`-periodic function `f : ℂ → ℂ`. -/
theorem tsum_fourierCoeffOn_mul_cexp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b : ℝ} (hab : a < b) (hper : Function.Periodic f ((b - a : ℝ) : ℂ)) (z : ℂ) :
    (∑' n : ℤ, fourierCoeffOn hab (fun x : ℝ ↦ f x) n *
      cexp (2 * π * I * n * z / (b - a))) = f z :=
  (hf.hasSum_fourierCoeffOn_mul_cexp hab hper z).tsum_eq

/-- Specialization of `Differentiable.hasSum_fourierCoeffOn_mul_cexp` to the period interval
`[0, T]` with `0 < T`. -/
theorem hasSum_fourierCoeffOn_zero_mul_cexp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T) (z : ℂ) :
    HasSum (fun n : ℤ ↦
      fourierCoeffOn hT (fun x : ℝ ↦ f x) n * cexp (2 * π * I * n * z / T)) (f z) := by
  simpa [sub_zero] using hf.hasSum_fourierCoeffOn_mul_cexp hT (by simpa [sub_zero] using hper) z

/-- Specialization of `Differentiable.summable_fourierCoeffOn_mul_cexp` to `[0, T]` with
`0 < T`. -/
theorem summable_fourierCoeffOn_zero_mul_cexp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T) (z : ℂ) :
    Summable fun n : ℤ ↦
      fourierCoeffOn hT (fun x : ℝ ↦ f x) n * cexp (2 * π * I * n * z / T) :=
  (hf.hasSum_fourierCoeffOn_zero_mul_cexp hT hper z).summable

/-- Specialization of `Differentiable.tsum_fourierCoeffOn_mul_cexp` to `[0, T]` with `0 < T`. -/
theorem tsum_fourierCoeffOn_zero_mul_cexp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T) (z : ℂ) :
    (∑' n : ℤ, fourierCoeffOn hT (fun x : ℝ ↦ f x) n * cexp (2 * π * I * n * z / T)) = f z :=
  (hf.hasSum_fourierCoeffOn_zero_mul_cexp hT hper z).tsum_eq

end ScalarValued

end Differentiable
