/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.ClosedDisc
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Lobachevsky
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Conj

/-!
# The Bloch–Wigner dilogarithm

The Bloch–Wigner function is `D(z) = Im Li₂(z) + arg (1 - z) log |z|`, built from the principal
dilogarithm `TauCeti.Polylog.polylog 2` and Mathlib's principal argument. Classically, unlike
`Li₂` it is single-valued: it is continuous on the Riemann sphere and satisfies the five-term
relation exactly, which makes it the regulator of weight two, and for `Im z > 0` it is the volume
of the hyperbolic ideal tetrahedron with vertices `∞, 0, 1, z`. None of these facts is proved
here; this file supplies the function and the values that pin down its normalisation.

This file defines `TauCeti.Polylog.blochWigner` and proves its elementary values. The formula
needs no case distinction at `0` and `1`: there `Li₂(0) = 0`, `Li₂(1) = π² / 6` is real and
`log |1| = 0`, so `D(0) = D(1) = 0`. Its correction term is the weight-one polylogarithm,
`D(z) = Im (Li₂(z) - Li₁(z) log |z|)`, which is the Bernoulli form of the single-valued
dilogarithm. On the unit circle the correction vanishes, so `D` is continuous there, equal to
`Im Li₂`, with Fourier series `D(e^{it}) = ∑_{k ≥ 1} sin (k t) / k²`; it is the imaginary part of
Mathlib's exponential zeta function `expZeta a 2` at `e^{2πia}`, and twice Lobachevsky's function
at `e^{2iθ}`. At `i` the series is Catalan's constant `∑_{m ≥ 0} (-1)^m / (2m + 1)²`, which is
positive. Off the cut `(1, ∞)` the function is odd under conjugation, `D(conj z) = -D(z)`, so
`D(-i) = -D(i)`.

## Main results

* `TauCeti.Polylog.blochWigner`: the Bloch–Wigner dilogarithm.
* `TauCeti.Polylog.blochWigner_zero`, `TauCeti.Polylog.blochWigner_one`: `D(0) = D(1) = 0`.
* `TauCeti.Polylog.blochWigner_eq_im_polylog_two_sub_polylog_one_mul_log`:
  `D(z) = Im (Li₂(z) - Li₁(z) log |z|)`.
* `TauCeti.Polylog.continuousOn_blochWigner_sphere`: continuity on the unit circle.
* `TauCeti.Polylog.hasSum_blochWigner_exp_mul_I`: the Fourier series on the unit circle.
* `TauCeti.Polylog.blochWigner_exp_two_pi_mul_I`: `D(e^{2πia}) = Im expZeta a 2`.
* `TauCeti.Polylog.blochWigner_exp_two_mul_I`: `D(e^{2iθ}) = 2 Λ(θ)`.
* `TauCeti.Polylog.hasSum_blochWigner_I`, `TauCeti.Polylog.blochWigner_I_pos`: `D(i)` is
  Catalan's constant, hence positive.
* `TauCeti.Polylog.blochWigner_conj`, `TauCeti.Polylog.blochWigner_conj_of_re_le_one`:
  `D(conj z) = -D(z)` off the cut `(1, ∞)`, in particular on `re z ≤ 1`.

## References

* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and
  Geometry II (2007), Part I, §3, pp. 10–11.
* Alexander B. Goncharov, *Geometry of configurations, polylogarithms, and motivic cohomology*,
  Advances in Mathematics 114 (1995), §1.0, (1.2), p. 201.
-/

public section

open Filter Finset Real
open scoped ComplexConjugate Topology

namespace TauCeti.Polylog

/-- The **Bloch–Wigner dilogarithm** `D(z) = Im Li₂(z) + arg (1 - z) log |z|`, with Mathlib's
principal argument. Its values at `0` and `1` are `0` (`blochWigner_zero`, `blochWigner_one`). -/
noncomputable def blochWigner (z : ℂ) : ℝ :=
  (polylog 2 z).im + Complex.arg (1 - z) * Real.log ‖z‖

theorem blochWigner_def (z : ℂ) :
    blochWigner z = (polylog 2 z).im + Complex.arg (1 - z) * Real.log ‖z‖ := (rfl)

@[simp] theorem blochWigner_zero : blochWigner 0 = 0 := by
  simp [blochWigner_def]

@[simp] theorem blochWigner_one : blochWigner 1 = 0 := by
  simp [blochWigner_def, polylog_two_one, ← Complex.ofReal_pow]

/-- The correction term of the Bloch–Wigner function is the weight-one polylogarithm:
`D(z) = Im (Li₂(z) - Li₁(z) log |z|)`, the single-valued Bernoulli combination in weight two. -/
theorem blochWigner_eq_im_polylog_two_sub_polylog_one_mul_log (z : ℂ) :
    blochWigner z = (polylog 2 z - polylog 1 z * Real.log ‖z‖).im := by
  simp [blochWigner_def, Complex.log_im]

/-- On the unit circle the Bloch–Wigner function is the imaginary part of the dilogarithm. -/
theorem blochWigner_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : blochWigner z = (polylog 2 z).im := by
  simp [blochWigner_def, hz]

/-- The Bloch–Wigner function is continuous on the unit circle. -/
theorem continuousOn_blochWigner_sphere : ContinuousOn blochWigner (Metric.sphere 0 1) :=
  (Complex.continuous_im.comp_continuousOn ((continuousOn_polylog_closedBall le_rfl).mono
    Metric.sphere_subset_closedBall)).congr fun _ hz ↦
      blochWigner_of_norm_eq_one (mem_sphere_zero_iff_norm.mp hz)

/-- **The Bloch–Wigner function and Lobachevsky's function**: `D(e^{2iθ}) = 2 Λ(θ)`. -/
theorem blochWigner_exp_two_mul_I (θ : ℝ) :
    blochWigner (Complex.exp (2 * θ * Complex.I)) = 2 * lobachevsky θ := by
  rw [blochWigner_of_norm_eq_one (by simp [Complex.norm_exp]), lobachevsky_eq_im_polylog_two]
  ring

/-- **Fourier series of the Bloch–Wigner function** on the unit circle:
`D(e^{it}) = ∑_{k ≥ 1} sin (k t) / k²`. -/
theorem hasSum_blochWigner_exp_mul_I (t : ℝ) :
    HasSum (fun k : ℕ ↦ sin ((k + 1) * t) / (k + 1) ^ 2)
      (blochWigner (Complex.exp (t * Complex.I))) := by
  have h := (hasSum_lobachevsky (t / 2)).mul_left 2
  rw [← blochWigner_exp_two_mul_I, show (2 : ℂ) * ((t / 2 : ℝ) : ℂ) = t by push_cast; ring] at h
  refine h.congr_fun fun k ↦ ?_
  rw [show 2 * ((k : ℝ) + 1) * (t / 2) = (k + 1) * t by ring]
  field_simp

/-- **The Bloch–Wigner function and exponential zeta**: `D(e^{2πia}) = Im expZeta a 2`. -/
theorem blochWigner_exp_two_pi_mul_I (a : ℝ) :
    blochWigner (Complex.exp (2 * π * Complex.I * a)) = (HurwitzZeta.expZeta a 2).im := by
  have h := polylog_exp_eq_expZeta (n := 2) le_rfl a
  rw [Int.cast_ofNat] at h
  rw [blochWigner_of_norm_eq_one (by simp [Complex.norm_exp]), h]

/-- **The Bloch–Wigner function at `i` is Catalan's constant**:
`D(i) = ∑_{m ≥ 0} (-1)^m / (2m + 1)²`. -/
theorem hasSum_blochWigner_I :
    HasSum (fun m : ℕ ↦ (-1) ^ m / (2 * m + 1 : ℝ) ^ 2) (blochWigner Complex.I) := by
  have h := hasSum_blochWigner_exp_mul_I (π / 2)
  rw [show ((π / 2 : ℝ) : ℂ) * Complex.I = π / 2 * Complex.I by push_cast; ring,
    Complex.exp_pi_div_two_mul_I] at h
  -- Only the odd frequencies `k + 1 = 2m + 1` contribute, with `sin ((2m + 1) π / 2) = (-1)^m`.
  rw [← (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff fun k hk ↦ ?_] at h
  · refine h.congr_fun fun m ↦ ?_
    simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (2 * (m : ℝ) + 1) * (π / 2) = π / 2 + m * π by ring, sin_add_nat_mul_pi,
      sin_pi_div_two, mul_one]
  · obtain ⟨m, rfl⟩ : Odd k := Nat.not_even_iff_odd.mp fun ⟨m, hm⟩ ↦ hk ⟨m, by dsimp only; omega⟩
    rw [show ((2 * m + 1 : ℕ) + 1 : ℝ) * (π / 2) = (m + 1 : ℕ) * π by push_cast; ring,
      sin_nat_mul_pi, zero_div]

/-- The Bloch–Wigner function is positive at `i`. -/
theorem blochWigner_I_pos : 0 < blochWigner Complex.I := by
  set f : ℕ → ℝ := fun m ↦ 1 / (2 * m + 1) ^ 2
  have hfa : Antitone f := fun a b hab ↦ by
    simp only [f]
    gcongr
  have hl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 (blochWigner Complex.I)) :=
    hasSum_blochWigner_I.tendsto_sum_nat.congr fun n ↦
      sum_congr rfl fun i _ ↦ by simp only [f]; ring
  -- The partial sum `1 - 1 / 9` of the alternating series is a lower bound.
  have h := hfa.alternating_series_le_tendsto hl 1
  norm_num [sum_range_succ, f] at h
  linarith

/-- The Bloch–Wigner function is odd under complex conjugation, away from the cut `(1, ∞)` where
the principal dilogarithm does not commute with conjugation. -/
theorem blochWigner_conj {z : ℂ} (hz : (1 - z).arg ≠ π) :
    blochWigner (conj z) = -blochWigner z := by
  rw [blochWigner_def, blochWigner_def, polylog_conj 2 hz, show 1 - conj z = conj (1 - z) by simp,
    Complex.arg_conj]
  simp only [hz, ↓reduceIte, Complex.conj_im, Complex.norm_conj]
  ring

/-- The Bloch–Wigner function is odd under complex conjugation on the closed half-plane
`re z ≤ 1`, in particular on the closed unit disc. -/
theorem blochWigner_conj_of_re_le_one {z : ℂ} (hz : z.re ≤ 1) :
    blochWigner (conj z) = -blochWigner z :=
  blochWigner_conj (Complex.arg_lt_pi_iff.2 (.inl (by simpa using hz))).ne

/-- The Bloch–Wigner function takes opposite values at `-i` and `i`. -/
theorem blochWigner_neg_I : blochWigner (-Complex.I) = -blochWigner Complex.I := by
  simpa using blochWigner_conj_of_re_le_one (z := Complex.I) (by simp)

end TauCeti.Polylog
