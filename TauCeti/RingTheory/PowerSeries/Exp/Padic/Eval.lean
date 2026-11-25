/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.Exp.Eval
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Evaluation of p-adic exponential polynomials and their Hasse derivatives

On a closed disc strictly inside the p-adic exponential discs of all the frequencies, each
rescaled exponential series is restricted. This gives the termwise summability needed to apply the
evaluation identities of `TauCeti.RingTheory.PowerSeries.Exp.Eval`.
-/

public section

open PowerSeries Finset
open scoped Nat

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [Algebra ℚ K]
  [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {ι : Type*} {s : Finset ι} {a x : ι → K} {c : ℝ}

/-- On a closed disc strictly inside the exponential discs, each rescaled exponential series of
an exponential polynomial converges. -/
private theorem summable_coeff_rescale_exp_smul_pow
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {y : K} (hy : ‖y‖ ≤ c) :
    ∀ i ∈ s, Summable fun n ↦ coeff n (rescale (x i) (exp K)) • y ^ n := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  exact fun i hi ↦
    (isRestricted_rescale_exp ((norm_nonneg y).trans hy) (hxc i hi)).summable_smul_pow hy

/-- On a closed disc strictly inside the exponential discs, the Hasse derivatives of
`∑ᵢ aᵢ exp(xᵢX)` evaluate to `∑ᵢ aᵢ (xᵢ ^ k / k!) exp(y xᵢ)`. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (k : ℕ) {y : K} (hy : ‖y‖ ≤ c) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp K))).evalAt y =
      ∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (y * x i) := by
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp_of_summable
    (summable_coeff_rescale_exp_smul_pow hxc hy) k]
  -- the rational scalar `(k!)⁻¹` acts on `K` as division by `k!`
  simp only [Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]

/-- At any point `y` of a closed disc strictly inside the exponential discs, a fixed Hasse
derivative of an exponential polynomial evaluates to zero if and only if the corresponding
ordinary derivative sum is zero at that same point `y`. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero_iff
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (k : ℕ) {y : K} (hy : ‖y‖ ≤ c) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp K))).evalAt y = 0 ↔
      ∑ i ∈ s, a i * x i ^ k * NormedSpace.exp (y * x i) = 0 :=
  evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero_iff_of_summable
    (summable_coeff_rescale_exp_smul_pow hxc hy) k

end TauCeti
