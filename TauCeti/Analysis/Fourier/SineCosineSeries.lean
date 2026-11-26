/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Fourier.Uniqueness

/-!
# Completeness of the Fourier sine, cosine and quarter-wave sine systems on an interval, and of
sine products on a box

On an interval `[a, b]` with `a < b`, the functions `x ↦ sin (k π (x - a) / (b - a))`,
`k = 1, 2, …`, are the eigenfunctions of `-d²/dx²` with zero boundary values at both ends. This
file proves that they form a **complete** system: an integrable function on `(a, b]` orthogonal to
all of them vanishes almost everywhere (`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`).
This covers in particular every function in `L²(a, b)`. The theorem does not assume `a < b`: when
`b ≤ a` the interval `(a, b]` is empty, so the restricted measure is zero and the conclusion holds
trivially.

For `a < b`, the proof reduces to the uniqueness of Fourier coefficients of integrable functions
on an interval (`MeasureTheory.IntegrableOn.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero`). Extend
`g` oddly about `a` to `[2a - b, b]`. On this interval of length `2(b - a)`, the `n`-th Fourier
coefficient of the odd extension is a multiple of `∫ g(x) sin (n π (x - a) / (b - a)) dx`, so all
of them vanish, and uniqueness forces the extension, hence `g`, to vanish almost everywhere.

The cosines `cos (k π (x - a) / (b - a))`, `k = 0, 1, 2, …`, the eigenfunctions of `-d²/dx²` with
zero Neumann data at both ends, are complete in the same sense
(`TauCeti.ae_eq_zero_of_forall_integral_mul_cos_eq_zero`), by the same argument with the even
extension of `g` about `a` in place of the odd one. The constant `k = 0` belongs to the system:
without it the constant function `1` would be orthogonal to every other cosine.

The quarter-wave sines `sin ((2k + 1) π (x - a) / (2 (b - a)))`, `k ≥ 0`, vanish at `a` and have
zero derivative at `b`; they are complete too
(`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero`). Reflected evenly about
`b`, a function orthogonal to them is orthogonal to every sine of the doubled interval
`(a, 2b - a)`.

The same holds on a box `∏ᵢ (aᵢ, bᵢ) ⊆ ℝ^ι` for the products of sines
`∏ᵢ sin (kᵢ π (xᵢ - aᵢ) / (bᵢ - aᵢ))`, `kᵢ ≥ 1`, the separated Dirichlet eigenfunctions of `-Δ`
on the box (`TauCeti.ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero`). The proof is by
induction on the dimension. Split off the first coordinate, `x = (t, y)`. For each `k`, the
coefficient `y ↦ ∫ g (t, y) sin (k π (t - a₀) / (b₀ - a₀)) dt` is orthogonal to every sine product
in `y`, so it vanishes for almost every `y` by induction; for those `y` the slice `g (·, y)` is
orthogonal to every sine, so it vanishes by the one-dimensional theorem, and Fubini concludes.

## Main results

* `TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`: completeness of the sine system
  `sin (k π (x - a) / (b - a))`, `k ≥ 1`, among the integrable functions on `(a, b]`.
* `TauCeti.ae_eq_zero_of_forall_integral_mul_cos_eq_zero`: completeness of the cosine system
  `cos (k π (x - a) / (b - a))`, `k ≥ 0`, among the integrable functions on `(a, b]`.
* `TauCeti.ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero`: completeness of the
  quarter-wave sines `sin ((2k + 1) π (x - a) / (2 (b - a)))`, `k ≥ 0`, the eigenfunctions with a
  Dirichlet condition at `a` and a Neumann condition at `b`.
* `TauCeti.ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero`: completeness of the products of
  sines among the integrable functions on a box.

## References

* G. B. Folland, *Fourier Analysis and its Applications*, Section 2.4 (odd and even extensions,
  Fourier sine and cosine series) and Section 3.4 (completeness of the trigonometric system).
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

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

/-- The extension of `g` about `a` with sign `ε`: equal to `g` to the right of `a` and to
`x ↦ ε g (2a - x)` at and to the left of `a`. It is the odd extension for `ε = -1` and the even
extension for `ε = 1`. -/
private noncomputable def reflectExtension (ε : ℂ) (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℂ :=
  if a < x then (g x : ℂ) else ε * (g (2 * a - x) : ℂ)

private theorem reflectExtension_of_lt {ε : ℂ} {g : ℝ → ℝ} {x : ℝ} (hx : a < x) :
    reflectExtension ε a g x = g x := by
  simp [reflectExtension, hx]

private theorem reflectExtension_of_le {ε : ℂ} {g : ℝ → ℝ} {x : ℝ} (hx : x ≤ a) :
    reflectExtension ε a g x = ε * (g (2 * a - x) : ℂ) := by
  simp [reflectExtension, hx.not_gt]

/-- The extension of a function integrable on `[a, b]` is integrable on the reflected interval
`[2a - b, a]`. -/
private theorem intervalIntegrable_reflectExtension_left (ε : ℂ) (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b) :
    IntervalIntegrable (reflectExtension ε a g) volume (2 * a - b) a := by
  have hg' : IntervalIntegrable (fun x => (g (2 * a - x) : ℂ)) volume (2 * a - b) a := by
    simpa [show 2 * a - a = a by ring] using (hg.comp_sub_left (2 * a)).symm
  refine (hg'.const_mul ε).congr_ae ?_
  rw [uIoc_of_le (by linarith)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [reflectExtension_of_le hx.2]

/-- The extension of a function integrable on `[a, b]` is integrable on `[a, b]`. -/
private theorem intervalIntegrable_reflectExtension_right (ε : ℂ) (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b) :
    IntervalIntegrable (reflectExtension ε a g) volume a b := by
  refine hg.congr_ae ?_
  rw [uIoc_of_le hab]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [reflectExtension_of_lt hx.1]

/-- Integrating a continuous `F` against the extension of `g` over `[2a - b, b]` folds the left
half onto `[a, b]` by the substitution `x = 2a - y`. -/
private theorem integral_mul_reflectExtension (ε : ℂ) (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b) {F : ℝ → ℂ} (hFc : Continuous F) :
    ∫ x in (2 * a - b)..b, F x * reflectExtension ε a g x =
      ∫ y in a..b, (F y + ε * F (2 * a - y)) * (g y : ℂ) := by
  -- On `[2a - b, a]` substitute `x = 2a - y`; on `(a, b]` the extension is `g` itself.
  have hleft : ∫ x in (2 * a - b)..a, F x * reflectExtension ε a g x =
      ∫ y in a..b, F (2 * a - y) * (ε * (g y : ℂ)) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun x => F x * (ε * (g (2 * a - x) : ℂ))) (a := a) (b := b) (2 * a)
    simp only [sub_sub_cancel, show 2 * a - a = a by ring] at hsub
    rw [hsub]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [reflectExtension_of_le hx.2]
  have hright : ∫ x in a..b, F x * reflectExtension ε a g x =
      ∫ y in a..b, F y * (g y : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hab] at hx
    rw [reflectExtension_of_lt hx.1]
  have hint1 : IntervalIntegrable (fun y => F y * (g y : ℂ)) volume a b :=
    hg.continuousOn_mul hFc.continuousOn
  have hint2 : IntervalIntegrable (fun y => F (2 * a - y) * (ε * (g y : ℂ))) volume a b :=
    (hg.const_mul ε).continuousOn_mul (hFc.comp (continuous_const.sub continuous_id)).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_reflectExtension_left ε hab hg).continuousOn_mul hFc.continuousOn)
      ((intervalIntegrable_reflectExtension_right ε hab hg).continuousOn_mul hFc.continuousOn),
    hleft, hright, ← intervalIntegral.integral_add hint2 hint1]
  congr 1 with y
  ring

/-- Let `t n`, `n ∈ ℤ`, be functions such that the Fourier monomial of frequency `-n` on
`[2a - b, b]`, plus `ε` times its reflection about `a`, is a multiple of `t n`. Then the `n`-th
Fourier coefficient on `[2a - b, b]` of the extension of `g` with sign `ε` is a multiple of
`∫ x in a..b, g x * t n x`, so if `g` is orthogonal to every `t n` then all these coefficients
vanish, and uniqueness of Fourier coefficients forces `g` to vanish almost everywhere on
`(a, b]`. -/
private theorem ae_eq_zero_of_forall_integral_mul_eq_zero_of_reflect (ε : ℂ) (hab : a < b)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc a b)) (t : ℤ → ℝ → ℝ) (c : ℤ → ℂ)
    (ht : ∀ n (y : ℝ), fourier (-n) (y : AddCircle (b - (2 * a - b))) +
        ε * fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b))) = c n * (t n y : ℂ))
    (hZ : ∀ n, ∫ x in a..b, g x * t n x = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hgi : IntervalIntegrable (fun x => (g x : ℂ)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hg.ofReal
  have hcoeff (n : ℤ) :
      fourierCoeffOn (by linarith : 2 * a - b < b) (reflectExtension ε a g) n = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [smul_eq_mul]
    rw [integral_mul_reflectExtension ε hab.le hgi
      (F := fun x : ℝ => fourier (-n) (x : AddCircle (b - (2 * a - b))))
      ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _))]
    have hpt : ∀ y : ℝ, (fourier (-n) (y : AddCircle (b - (2 * a - b))) +
        ε * fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b)))) * (g y : ℂ) =
          c n * ((g y * t n y : ℝ) : ℂ) := fun y => by
      rw [ht n y, ofReal_mul]
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hZ n]
    simp
  have hzero := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_left (by linarith : 2 * a - b ≤ a))
    (IntegrableOn.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero _
      ((intervalIntegrable_reflectExtension_left ε hab.le hgi).trans
        (intervalIntegrable_reflectExtension_right ε hab.le hgi)).1 hcoeff)
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioc] with x hx hxm
  rw [Pi.zero_apply, reflectExtension_of_lt hxm.1] at hx
  exact_mod_cast hx

/-- **Completeness of the Fourier sine system.** A function `g` integrable on `(a, b]` with

`∫ x in a..b, g x * sin (k π (x - a) / (b - a)) = 0` for every `k ≥ 1`

vanishes almost everywhere on `(a, b]`. For `a < b` these sines are the Dirichlet eigenfunctions
of `-d²/dx²` on `(a, b)`, so this is the completeness half of the Fourier sine expansion. For
`b ≤ a` the interval `(a, b]` is empty, the restricted measure is zero, and the conclusion holds
trivially. -/
theorem ae_eq_zero_of_forall_integral_mul_sin_eq_zero {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc a b))
    (h : ∀ k : ℕ, 0 < k → ∫ x in a..b, g x * Real.sin (k * π * (x - a) / (b - a)) = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  by_cases hab : a < b
  · exact ae_eq_zero_of_forall_integral_mul_eq_zero_of_reflect (-1) hab hg
      (fun n y => Real.sin (n * π * (y - a) / (b - a)))
      (fun n => -2 * I * exp (-(π * I * n * a / (b - a))))
      (fun n y => by rw [neg_one_mul, ← sub_eq_add_neg, fourier_sub_fourier_reflect hab n y])
      (integral_mul_sin_intCast_eq_zero h)
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab), Filter.EventuallyEq]

/-- The sum of a Fourier monomial on `[2a - b, b]` at `y` and at its reflection `2a - y` about `a`
is a multiple of `cos (n π (y - a) / (b - a))`. -/
private theorem fourier_add_fourier_reflect (hab : a < b) (n : ℤ) (y : ℝ) :
    fourier (-n) (y : AddCircle (b - (2 * a - b))) +
        fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b))) =
      2 * exp (-(π * I * n * a / (b - a))) * (Real.cos (n * π * (y - a) / (b - a)) : ℂ) := by
  have hba : (b : ℂ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.ne')
  set C : ℂ := -(π * I * n * a / (b - a))
  set Y : ℂ := ((n * π * (y - a) / (b - a) : ℝ) : ℂ)
  have hrhs : 2 * exp C * ((exp (Y * I) + exp (-Y * I)) / 2) =
      exp (C + -Y * I) + exp (C + Y * I) := by
    rw [exp_add, exp_add]
    ring
  rw [fourier_coe_apply, fourier_coe_apply, ofReal_cos, cos, hrhs]
  congr 2 <;>
  · simp only [C, Y]
    push_cast
    rw [show (b : ℂ) - (2 * a - b) = 2 * (b - a) by ring]
    field_simp
    ring

/-- Orthogonality to the cosines `cos (k π (x - a) / (b - a))` for `k ≥ 0` extends to every integer
frequency, since `cos` is even. -/
private theorem integral_mul_cos_intCast_eq_zero {g : ℝ → ℝ}
    (h : ∀ k : ℕ, ∫ x in a..b, g x * Real.cos (k * π * (x - a) / (b - a)) = 0)
    (n : ℤ) : ∫ x in a..b, g x * Real.cos (n * π * (x - a) / (b - a)) = 0 := by
  rcases n with k | k
  · simpa using h k
  · have hk := h (k + 1)
    simp only [Int.cast_negSucc, neg_mul, neg_div, Real.cos_neg]
    simpa using hk

/-- **Completeness of the Fourier cosine system.** A function `g` integrable on `(a, b]` with

`∫ x in a..b, g x * cos (k π (x - a) / (b - a)) = 0` for every `k ≥ 0`

vanishes almost everywhere on `(a, b]`. For `a < b` these cosines are the Neumann eigenfunctions
of `-d²/dx²` on `(a, b)`, so this is the completeness half of the Fourier cosine expansion. For
`b ≤ a` the interval `(a, b]` is empty, the restricted measure is zero, and the conclusion holds
trivially. -/
theorem ae_eq_zero_of_forall_integral_mul_cos_eq_zero {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc a b))
    (h : ∀ k : ℕ, ∫ x in a..b, g x * Real.cos (k * π * (x - a) / (b - a)) = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  by_cases hab : a < b
  · exact ae_eq_zero_of_forall_integral_mul_eq_zero_of_reflect 1 hab hg
      (fun n y => Real.cos (n * π * (y - a) / (b - a)))
      (fun n => 2 * exp (-(π * I * n * a / (b - a))))
      (fun n y => by rw [one_mul, fourier_add_fourier_reflect hab n y])
      (integral_mul_cos_intCast_eq_zero h)
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab), Filter.EventuallyEq]

/-- The even reflection about `b` of a function integrable on `[a, b]` is integrable on
`[a, b]` and on `[b, 2b - a]`. -/
private theorem intervalIntegrable_reflect_right (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun x => if x ≤ b then g x else g (2 * b - x)) volume a b ∧
      IntervalIntegrable (fun x => if x ≤ b then g x else g (2 * b - x)) volume b (2 * b - a) := by
  refine ⟨hg.congr_ae ?_, ?_⟩
  · rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp [hx.2]
  · have h' : IntervalIntegrable (fun x => g (2 * b - x)) volume b (2 * b - a) := by
      simpa [show 2 * b - b = b by ring] using (hg.comp_sub_left (2 * b)).symm
    refine h'.congr_ae ?_
    rw [uIoc_of_le (by linarith)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp [not_le.2 hx.1]

/-- Against the `j`-th sine of `(a, 2b - a)`, the even reflection of `g` about `b` integrates to
`1 - (-1)^j` times the integral of `g` against the same sine over `(a, b)`: the reflected sine
is `-(-1)^j` times the sine. -/
private theorem integral_reflect_right_mul_sin (hab : a < b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) (j : ℕ) :
    ∫ x in a..(2 * b - a), (if x ≤ b then g x else g (2 * b - x)) *
        Real.sin (j * π * (x - a) / (2 * b - a - a)) =
      (1 - (-1) ^ j) * ∫ x in a..b, g x * Real.sin (j * π * (x - a) / (2 * b - a - a)) := by
  set s : ℝ → ℝ := fun x => Real.sin (j * π * (x - a) / (2 * b - a - a))
  have hs : Continuous s := by fun_prop
  have hd : 2 * b - a - a ≠ 0 := by linarith
  have hrefl (y : ℝ) : s (2 * b - y) = -(-1) ^ j * s y := by
    simp only [s]
    rw [show j * π * (2 * b - y - a) / (2 * b - a - a) =
        j * π - j * π * (y - a) / (2 * b - a - a) by field_simp; ring,
      Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  obtain ⟨hGl, hGr⟩ := intervalIntegrable_reflect_right hab.le hg
  have hleft : ∫ x in a..b, (if x ≤ b then g x else g (2 * b - x)) * s x =
      ∫ x in a..b, g x * s x :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le hab.le] at hx
      simp [hx.2]
  -- On `(b, 2b - a]` substitute `x = 2b - y`.
  have hright : ∫ x in b..(2 * b - a), (if x ≤ b then g x else g (2 * b - x)) * s x =
      -(-1) ^ j * ∫ x in a..b, g x * s x := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun y => g y * s (2 * b - y)) (a := b) (b := 2 * b - a) (2 * b)
    simp only [sub_sub_cancel, show 2 * b - (2 * b - a) = a by ring,
      show 2 * b - b = b by ring] at hsub
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)).trans
      (hsub.trans (intervalIntegral.integral_congr fun y _ => ?_))
    · rw [uIoc_of_le (by linarith)] at hx
      simp [not_le.2 hx.1]
    · simp only [hrefl]
      ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hGl.mul_continuousOn hs.continuousOn)
    (hGr.mul_continuousOn hs.continuousOn), hleft, hright]
  ring

/-- **Completeness of the quarter-wave sine system.** A function `g` integrable on `(a, b]` with

`∫ x in a..b, g x * sin ((2k + 1) π (x - a) / (2 (b - a))) = 0` for every `k ≥ 0`

vanishes almost everywhere on `(a, b]`. For `a < b` these sines are the eigenfunctions of
`-d²/dx²` on `(a, b)` with a Dirichlet condition at `a` and a Neumann condition at `b`. The proof
reflects `g` evenly about `b` to `(a, 2b - a]`: the reflected sines of even frequency cancel, those
of odd frequency double, so the reflection is orthogonal to the whole sine system of `(a, 2b - a)`
and vanishes by `TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`. -/
theorem ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc a b))
    (h : ∀ k : ℕ,
      ∫ x in a..b, g x * Real.sin ((2 * k + 1) * π * (x - a) / (2 * (b - a))) = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  by_cases hab : a < b
  swap
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab), Filter.EventuallyEq]
  have hgi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hg
  obtain ⟨hGl, hGr⟩ := intervalIntegrable_reflect_right hab.le hgi
  -- The even reflection of `g` about `b` is orthogonal to every sine of `(a, 2b - a)`.
  have hzero := ae_eq_zero_of_forall_integral_mul_sin_eq_zero (hGl.trans hGr).1 fun j _ => by
    rw [integral_reflect_right_mul_sin hab hgi j]
    rcases Nat.even_or_odd j with hj | ⟨k, rfl⟩
    · rw [hj.neg_one_pow, sub_self, zero_mul]
    · have hk := h k
      rw [show (fun x => g x * Real.sin ((2 * k + 1) * π * (x - a) / (2 * (b - a)))) =
          fun x => g x * Real.sin (((2 * k + 1 : ℕ) : ℝ) * π * (x - a) / (2 * b - a - a)) by
        funext x
        push_cast
        ring_nf] at hk
      rw [hk, mul_zero]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right (by linarith))
    hzero, ae_restrict_mem measurableSet_Ioc] with x hx hxm
  simpa [hxm.2] using hx

/-- Completeness of the sine system in the first variable of a product, with a parameter `y`:
the case of `TauCeti.ae_eq_zero_prod_of_forall_integral_mul_eq_zero` for the sines of `(a, b)`. -/
private theorem ae_eq_zero_prod_of_forall_integral_mul_sin_eq_zero {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SFinite ν] {G : ℝ × β → ℝ}
    (hG : Integrable G ((volume.restrict (Ioo a b)).prod ν))
    (h : ∀ k : ℕ, 0 < k → (fun y => ∫ t, G (t, y) * Real.sin (k * π * (t - a) / (b - a))
      ∂volume.restrict (Ioo a b)) =ᵐ[ν] 0) :
    G =ᵐ[(volume.restrict (Ioo a b)).prod ν] 0 := by
  refine ae_eq_zero_prod_of_forall_integral_mul_eq_zero
    (s := fun (k : {k : ℕ // 0 < k}) t => Real.sin (k * π * (t - a) / (b - a)))
    (fun g hg hgs => ?_) hG fun k => h k k.property
  rcases le_or_gt a b with hab | hab
  · have hIoc : volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
      Measure.restrict_congr_set Ioo_ae_eq_Ioc
    have := ae_eq_zero_of_forall_integral_mul_sin_eq_zero (g := g)
      (by simpa [IntegrableOn, hIoc] using hg) fun k hk => by
        rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
        exact hgs ⟨k, hk⟩
    simpa [hIoc] using this
  · simp [Ioo_eq_empty_of_le hab.le, Filter.EventuallyEq]

/-- The sine system on a box, in the coordinates `Fin n → ℝ` and with the product of the
restricted measures, by induction on the dimension. -/
private theorem ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero_fin :
    ∀ (n : ℕ) (a b : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ),
      Integrable g (Measure.pi fun i => volume.restrict (Ioo (a i) (b i))) →
      (∀ k : Fin n → ℕ, (∀ i, 0 < k i) →
        ∫ x, g x * ∏ i, Real.sin (k i * π * (x i - a i) / (b i - a i))
          ∂Measure.pi (fun i => volume.restrict (Ioo (a i) (b i))) = 0) →
      g =ᵐ[Measure.pi fun i => volume.restrict (Ioo (a i) (b i))] 0
  | 0, a, b, g, _, h => by
    -- On `Fin 0 → ℝ` the product measure is the Dirac mass at the only point.
    have h0 := h Fin.elim0 fun i => i.elim0
    rw [Measure.pi_of_empty _ (Fin.elim0 : Fin 0 → ℝ), integral_dirac] at h0
    have hg : g = 0 := funext fun x => by
      rw [Subsingleton.elim x Fin.elim0]
      simpa using h0
    exact hg ▸ Filter.EventuallyEq.rfl
  | n + 1, a, b, g, hg, h => by
    set μ : Fin (n + 1) → Measure ℝ := fun i => volume.restrict (Ioo (a i) (b i))
    set ν : Measure (Fin n → ℝ) :=
      Measure.pi fun j => volume.restrict (Ioo (a j.succ) (b j.succ))
    -- Split off the first coordinate: `x = (x 0, tail)`.
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod ν) := by
      have h := measurePreserving_piFinSuccAbove μ 0
      simp only [Fin.succAbove_zero] at h
      exact h
    have he (t : ℝ) (y : Fin n → ℝ) : e.symm (t, y) = Fin.cons t y := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    set G : ℝ × (Fin n → ℝ) → ℝ := g ∘ e.symm
    have hG : Integrable G ((μ 0).prod ν) :=
      (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.2 hg
    set s : ℕ → ℝ → ℝ := fun k t => Real.sin (k * π * (t - a 0) / (b 0 - a 0))
    have hGs (k : ℕ) : Integrable (fun z : ℝ × (Fin n → ℝ) => G z * s k z.1) ((μ 0).prod ν) :=
      hG.mul_bdd (by fun_prop) (ae_of_all _ fun z => by simpa using Real.abs_sin_le_one _)
    -- The coefficients of `G` in the first variable are orthogonal to every sine product in the
    -- remaining ones, so they vanish by induction.
    have hH (k : ℕ) (hk : 0 < k) : (fun y => ∫ t, G (t, y) * s k t ∂μ 0) =ᵐ[ν] 0 := by
      refine ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero_fin n (fun j => a j.succ)
        (fun j => b j.succ) _ (hGs k).integral_prod_right fun k' hk' => ?_
      have hfull := h (Fin.cons k k') (Fin.cases hk hk')
      rw [← (hmp.symm e).integral_comp'] at hfull
      set P : (Fin n → ℝ) → ℝ :=
        fun y => ∏ j, Real.sin (k' j * π * (y j - a j.succ) / (b j.succ - a j.succ))
      have hP : Continuous P := by fun_prop
      have hint : Integrable (fun z : ℝ × (Fin n → ℝ) => G z * s k z.1 * P z.2) ((μ 0).prod ν) :=
        (hGs k).mul_bdd (hP.comp continuous_snd).aestronglyMeasurable (ae_of_all _ fun z => by
          rw [norm_prod]
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
            fun _ _ => by simpa using Real.abs_sin_le_one _)
      simp_rw [← MeasureTheory.integral_mul_const]
      rw [← integral_prod_symm _ hint]
      refine Eq.trans ?_ hfull
      congr 1 with ⟨t, y⟩
      simp only [G, s, P, Function.comp_apply, he, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
      ring
    have hG0 : G =ᵐ[(μ 0).prod ν] 0 :=
      ae_eq_zero_prod_of_forall_integral_mul_sin_eq_zero hG hH
    have hGe : G ∘ e = g := funext fun x => by simp [G]
    rw [← hGe]
    exact hmp.quasiMeasurePreserving.ae_eq_comp hG0

/-- **Completeness of the sine system on a box.** Let `g` be integrable on the open box
`∏ᵢ (aᵢ, bᵢ) ⊆ ℝ^ι` and orthogonal to every product of sines

`x ↦ ∏ᵢ sin (kᵢ π (xᵢ - aᵢ) / (bᵢ - aᵢ))`, `kᵢ ≥ 1`.

Then `g` vanishes almost everywhere on the box. The products of the one-dimensional Dirichlet
modes are the separated Dirichlet eigenfunctions of `-Δ` on the box, so this is the completeness
half of their expansion. No relation between `aᵢ` and `bᵢ` is assumed: an empty factor makes the
box empty. -/
theorem ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero {ι : Type*} [Fintype ι]
    {a b : ι → ℝ} {g : (ι → ℝ) → ℝ} (hg : IntegrableOn g (univ.pi fun i => Ioo (a i) (b i)))
    (h : ∀ k : ι → ℕ, (∀ i, 0 < k i) →
      ∫ x in univ.pi fun i => Ioo (a i) (b i),
        g x * ∏ i, Real.sin (k i * π * (x i - a i) / (b i - a i)) = 0) :
    g =ᵐ[volume.restrict (univ.pi fun i => Ioo (a i) (b i))] 0 := by
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi] at hg
  simp only [volume_pi, Measure.restrict_pi_pi] at h ⊢
  -- Relabel the coordinates by `Fin n`.
  let f := (Fintype.equivFin ι).symm
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) f
  have hmp : MeasurePreserving e
      (Measure.pi fun i' => volume.restrict (Ioo (a (f i')) (b (f i'))))
      (Measure.pi fun i => volume.restrict (Ioo (a i) (b i))) :=
    measurePreserving_piCongrLeft (fun i => volume.restrict (Ioo (a i) (b i))) f
  have happ (x : Fin (Fintype.card ι) → ℝ) (i' : Fin (Fintype.card ι)) : e x (f i') = x i' :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) f x i'
  have hfin := ae_eq_zero_of_forall_setIntegral_mul_prod_sin_eq_zero_fin _ (a ∘ f) (b ∘ f) (g ∘ e)
    (hmp.integrable_comp_emb e.measurableEmbedding |>.2 hg) fun k hk => by
      have := h (k ∘ f.symm) fun i => hk _
      rw [← hmp.integral_comp'] at this
      refine Eq.trans ?_ this
      congr 1 with x
      simp only [Function.comp_apply]
      congr 1
      rw [← f.prod_comp]
      simp [happ]
  have hge : (g ∘ e) ∘ e.symm = g := funext fun x => by simp
  rw [← hge]
  exact (hmp.symm e).quasiMeasurePreserving.ae_eq_comp hfin

end TauCeti
