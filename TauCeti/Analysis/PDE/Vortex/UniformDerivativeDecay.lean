/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
public import TauCeti.Analysis.PDE.Vortex.ModulusBound
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.PDE.Regularity.PlanarGradientEstimate
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Uniform decay of the derivatives of plane vortices away from their zeros

Let `x` be a smooth plane vortex with the degree-`m` end framing and zero divisor `D`, and write
`α` for its section, so that `|α|² = 4 (p² + q²)` in the coordinates `x = (b₁, b₂, p, q)`. The
modulus defect decays exponentially in the distance to the zeros with a constant depending only on
`m` and the rate: for `0 ≤ c < 1 / 2`, `1 - |α(z)|² ≤ K exp (-c ρ)` whenever every zero is at
distance at least `ρ` from `z`
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub`). This file proves the
same uniform decay for the first derivatives: the gradient of `log |α|²` and of `|α|²`, the
covariant derivative `d_a α`, and the energy density. In each case the constants depend only on
`m` and the rate, not on the vortex or on the position of its zeros, so the estimates hold over
the whole noncompact space of divisors of degree `m`, for instance for clusters of zeros moving
apart. For a single vortex and decay in `|z|` instead, these are
`TauCeti.Vortex.exists_eventually_norm_fderiv_log_normSq_le_mul_exp`,
`TauCeti.Vortex.exists_norm_fderiv_normSq_le_mul_exp`,
`TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp` and
`TauCeti.Vortex.exists_energyDensity_le_mul_exp`.

The estimates hold at distance at least a fixed `R` from the zeros, with `R` depending only on `m`
and the rate. Some threshold is needed for `log |α|²`, which tends to `-∞` at a zero.

The argument is local. At distance at least `L = √(2 m (16 m + 1))` from the zeros, `|α|² > 1 / 2`
(`TauCeti.Vortex.one_sub_lt_normSq_of_forall_le_norm_sub`). Let `z` be at distance `ρ ≥ L + 3`
from the zeros. On the closed disc of radius `3` about `z`, the function `ℓ = log |α|²` is then
smooth (`TauCeti.Vortex.contDiffAt_log_normSq_of_equation_eq_zero`) and solves
`Δ ℓ = (|α|² - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`). There
`|ℓ| ≤ 2 (1 - |α|²)` (`Real.abs_log_le_two_mul_one_sub`), and every point is at distance at least
`ρ - 3` from the zeros, so both `ℓ` and `Δ ℓ` are at most a constant times `exp (-c (ρ - 3))`.
The interior gradient estimate for Poisson's equation
(`TauCeti.norm_fderiv_le_of_abs_le_of_abs_laplacian_le`) then bounds `∇ ℓ (z)` by
`101 K exp (-c (ρ - 3))`. Since `∇ |α|² = |α|² ∇ ℓ` and `|α|² ≤ 1`, the same bound holds for the
gradient of `|α|²`, and where `|α|² ≥ 1 / 2` it controls the covariant derivative
(`TauCeti.Vortex.norm_covariantDerivative_one_le_norm_fderiv_normSq`).

## Main results

All in the namespace `TauCeti.Vortex`, for a degree `m` and a rate `0 ≤ c < 1 / 2`, with constants
`K` and `R` depending only on `m` and `c`, at every point at distance at least `ρ ≥ R` from every
zero:

* `exists_norm_fderiv_log_normSq_le_mul_exp_of_forall_le_norm_sub`:
  `|∇ log |α|²| ≤ K exp (-c ρ)`.
* `exists_norm_fderiv_normSq_le_mul_exp_of_forall_le_norm_sub`: `|∇ |α|²| ≤ K exp (-c ρ)`.
* `exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub`:
  `|d_a α (v)| ≤ K |v| exp (-c ρ)`.
* `exists_energyDensity_le_mul_exp_of_forall_le_norm_sub`: the energy density
  `|F_a|² + |d_a α|² + (1 - |α|²)²` is at most `K exp (-c ρ)`, here for every rate `0 ≤ c < 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology InnerProductSpace Laplacian
open scoped ContDiff

/-- At distance at least `√(2 m (16 m + 1))` from every zero, `|α|² > 1 / 2`: the case `δ = 1 / 2`
of `TauCeti.Vortex.one_sub_lt_normSq_of_forall_le_norm_sub`. -/
private theorem half_lt_normSq_of_forall_le_norm_sub {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {z : ℂ}
    (hz : ∀ a ∈ D, Real.sqrt (m * (16 * m + 1) / (1 / 2)) ≤ ‖z - a‖) :
    1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
  have := one_sub_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD (lt_add_one _)
    (by norm_num : (0 : ℝ) < 1 / 2) hz
  linarith

/-- **Uniform exponential decay of the gradient of `log |α|²` away from the zeros.** For every
degree `m` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that every smooth plane
vortex with the degree-`m` end framing and zero divisor `D` satisfies
`|∇ log |α|²| ≤ K exp (-c ρ)` at every point whose distance to every zero is at least `ρ ≥ R`. -/
theorem exists_norm_fderiv_log_normSq_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ‖fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
          K * Real.exp (-(c * ρ)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
  set L : ℝ := Real.sqrt (m * (16 * m + 1) / (1 / 2))
  refine ⟨101 * K * Real.exp (c * 3), L + 3, by positivity,
    fun x D hx hsol hframe hD z ρ hR hρ ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hp : ContDiff ℝ 2 fun w ↦ x w 2 := (hxi 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ x w 3 := (hxi 3).of_le (by simp)
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) with hs
  set E : ℝ := K * Real.exp (-(c * (ρ - 3)))
  -- Every point of the closed disc of radius `3` about `z` is at distance at least `ρ - 3` from
  -- the zeros, so `|α|² > 1 / 2` there and the defect is at most `E`.
  have hfar (w : ℂ) (hw : w ∈ closedBall z 3) (a : ℂ) (ha : a ∈ D) : ρ - 3 ≤ ‖w - a‖ := by
    have hwz : ‖w - z‖ ≤ 3 := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
    have := norm_sub_le_norm_sub_add_norm_sub z w a
    rw [norm_sub_rev z w] at this
    linarith [hρ a ha]
  have hhalf (w : ℂ) (hw : w ∈ closedBall z 3) : 1 / 2 < s w :=
    half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      (show L ≤ ‖w - a‖ by linarith [hfar w hw a ha])
  have hs₁ (w : ℂ) : s w ≤ 1 :=
    normSq_le_one_of_tendsto hp hq hsol
      (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) w
  have hdef (w : ℂ) (hw : w ∈ closedBall z 3) : 1 - s w ≤ E :=
    hK x D hx hsol hframe hD w (ρ - 3) (hfar w hw)
  have hα (w : ℂ) (hw : w ∈ closedBall z 3) : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0 := fun h ↦ by
    have := hhalf w hw
    simp only [hs, h, mul_zero] at this
    norm_num at this
  -- The interior gradient estimate for `ℓ = log |α|²` on the disc of radius `3`.
  have h := norm_fderiv_le_of_abs_le_of_abs_laplacian_le (u := fun w ↦ Real.log (s w)) (x := z)
    (ρ := 1) (ε := 2 * E) (K := E / 4)
    (fun w hw ↦ (contDiffAt_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt
      (hα w (by simpa using hw)) (Eventually.of_forall hsol)).of_le (by simp)) one_pos
    (fun w hw ↦ by
      have hw' : w ∈ closedBall z 3 := ball_subset_closedBall (ball_subset_ball (by norm_num) hw)
      exact (Real.abs_log_le_two_mul_one_sub (hhalf w hw').le (hs₁ w)).trans
        (by linarith [hdef w hw']))
    (fun w hw ↦ by
      have hw' : w ∈ closedBall z 3 := ball_subset_closedBall (by simpa using hw)
      rw [laplacian_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt (hα w hw')
        (Eventually.of_forall hsol), abs_div, abs_of_nonpos (by linarith [hs₁ w])]
      norm_num
      linarith [hdef w hw'])
  calc ‖fderiv ℝ (fun w ↦ Real.log (s w)) z‖ ≤ 8 * (2 * E) / 1 + 340 * (E / 4) * 1 := h
    _ = 101 * K * Real.exp (c * 3) * Real.exp (-(c * ρ)) := by
      simp only [E, exp_neg_mul_sub]
      ring

/-- **Uniform exponential decay of the gradient of `|α|²` away from the zeros.** For every degree
`m` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that every smooth plane vortex
with the degree-`m` end framing and zero divisor `D` satisfies `|∇ |α|²| ≤ K exp (-c ρ)` at every
point whose distance to every zero is at least `ρ ≥ R`. -/
theorem exists_norm_fderiv_normSq_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ ≤ K * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK₀, hK⟩ := exists_norm_fderiv_log_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
  set L : ℝ := Real.sqrt (m * (16 * m + 1) / (1 / 2))
  refine ⟨K, max R L, hK₀, fun x D hx hsol hframe hD z ρ hR hρ ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hp : ContDiff ℝ 2 fun w ↦ x w 2 := (hxi 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ x w 3 := (hxi 3).of_le (by simp)
  have hpos : 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      (le_max_right R L).trans (hR.trans (hρ a ha))
  have hs₁ := normSq_le_one_of_tendsto hp hq hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) z
  -- Where `0 < |α|² ≤ 1`, `|∇ |α|²| ≤ |∇ log |α|²|`.
  exact (norm_fderiv_le_norm_fderiv_log (((contDiff_normSq hp hq).differentiable (by norm_num)) z)
    (by linarith) hs₁).trans (hK x D hx hsol hframe hD z ρ ((le_max_left R L).trans hR) hρ)

/-- **Uniform exponential decay of the covariant derivative of plane vortices away from the
zeros.** For every degree `m` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that
every smooth plane vortex with the degree-`m` end framing and zero divisor `D` satisfies
`|d_a α (v)| ≤ K |v| exp (-c ρ)` at every point whose distance to every zero is at least `ρ ≥ R`. -/
theorem exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        ∀ v, ‖covariantDerivative x z v‖ ≤ K * ‖v‖ * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK₀, hK⟩ := exists_norm_fderiv_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀ hc
  set L : ℝ := Real.sqrt (m * (16 * m + 1) / (1 / 2))
  refine ⟨K, max R L, hK₀, fun x D hx hsol hframe hD z ρ hR hρ v ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hp : DifferentiableAt ℝ (fun w ↦ x w 2) z := ((hxi 2).differentiable (by simp)) z
  have hq : DifferentiableAt ℝ (fun w ↦ x w 3) z := ((hxi 3).differentiable (by simp)) z
  have hhalf : 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    (half_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD fun a ha ↦
      (le_max_right R L).trans (hR.trans (hρ a ha))).le
  -- `d_a α` is complex linear, and `|d_a α (1)|` is bounded by the gradient of `|α|²`.
  rw [norm_covariantDerivative_eq_mul_of_equation_eq_zero hp hq (by simp [hsol z])
    (by simp [hsol z]) v, mul_comm K, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((norm_covariantDerivative_one_le_norm_fderiv_normSq hp hq
    (by simp [hsol z]) (by simp [hsol z]) hhalf).trans
    (hK x D hx hsol hframe hD z ρ ((le_max_left R L).trans hR) hρ)) (norm_nonneg v)

/-- **Uniform exponential decay of the energy density of plane vortices away from the zeros.** For
every degree `m` and rate `0 ≤ c < 1` there are constants `K ≥ 0` and `R` such that every smooth
plane vortex with the degree-`m` end framing and zero divisor `D` has energy density
`|F_a|² + |d_a α|² + (1 - |α|²)²` at most `K exp (-c ρ)` at every point whose distance to every zero
is at least `ρ ≥ R`. -/
theorem exists_energyDensity_le_mul_exp_of_forall_le_norm_sub (m : ℕ) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : c < 1) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
        energyDensity x z ≤ K * Real.exp (-(c * ρ)) := by
  have hc₀' : 0 ≤ c / 2 := by positivity
  have hc' : c / 2 < 1 / 2 := by linarith
  obtain ⟨K₁, -, hK₁⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m hc₀' hc'
  obtain ⟨K₂, R, -, hK₂⟩ :=
    exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub m hc₀' hc'
  refine ⟨65 / 64 * K₁ ^ 2 + 2 * K₂ ^ 2, R, by positivity,
    fun x D hx hsol hframe hD z ρ hR hρ ↦ ?_⟩
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hs₁ := normSq_le_one_of_tendsto ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) z
  -- The modulus defect is at most `K₁ exp (-(c / 2) ρ)`, and `|d_a α (1)| ≤ K₂ exp (-(c / 2) ρ)`.
  refine (energyDensity_le_of_equation_eq_zero (((hxi 2).differentiable (by simp)) z)
    (((hxi 3).differentiable (by simp)) z) (hsol z) (by linarith)
    (hK₁ x D hx hsol hframe hD z ρ hρ)
    (by simpa using hK₂ x D hx hsol hframe hD z ρ hR hρ 1)).trans_eq ?_
  rw [mul_pow, mul_pow, exp_neg_half_mul_sq]
  ring

end TauCeti.Vortex
