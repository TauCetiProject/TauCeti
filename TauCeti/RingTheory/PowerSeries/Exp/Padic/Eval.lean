/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.Exp.HasseDeriv
public import TauCeti.RingTheory.PowerSeries.Exp.Eval
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Algebra

/-!
# Evaluation of exponential polynomials and their divided derivatives

The evaluation identity only needs convergence of each exponential series. Restrictedness
supplies this convergence on closed discs strictly inside the p-adic exponential discs.
-/

public section

open PowerSeries Finset
open scoped Nat

namespace TauCeti

/-- If each exponential series converges at `y * x i`, evaluating the Hasse derivative of an
exponential polynomial gives the corresponding divided derivative of its analytic value. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp_of_summable
    {R : Type*} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    {ι : Type*} {s : Finset ι} {a x : ι → R} {y : R}
    (hs : ∀ i ∈ s, Summable (fun n : ℕ ↦ (n ! : ℚ)⁻¹ • (y * x i) ^ n)) (k : ℕ) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp R))).evalAt y =
      ∑ i ∈ s, a i * ((k ! : ℚ)⁻¹ • x i ^ k) * NormedSpace.exp (y * x i) := by
  have hD : hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp R)) =
      ∑ i ∈ s, (a i * ((k ! : ℚ)⁻¹ • x i ^ k)) • rescale (x i) (exp R) := by
    rw [map_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hasseDeriv_rescale, hasseDeriv_exp, rescale_smul, ← smul_eq_C_mul]
    rw [smul_comm (x i ^ k) ((k ! : ℚ)⁻¹),
      ← smul_assoc ((k ! : ℚ)⁻¹) (x i ^ k) (rescale (x i) (exp R)), smul_smul]
  have hterm (i) (hi : i ∈ s) :
      HasSum (fun n ↦ coeff n ((a i * ((k ! : ℚ)⁻¹ • x i ^ k)) •
        rescale (x i) (exp R)) • y ^ n)
        (a i * ((k ! : ℚ)⁻¹ • x i ^ k) * NormedSpace.exp (y * x i)) := by
    rw [NormedSpace.exp_eq_tsum_rat]
    convert (hs i hi).hasSum.mul_left (a i * ((k ! : ℚ)⁻¹ • x i ^ k)) using 1
    ext n
    simp only [coeff_smul, coeff_rescale, coeff_exp]
    simp [Algebra.smul_def, mul_pow, mul_comm, mul_left_comm, mul_assoc]
  rw [hD, evalAt_def]
  have hsum := hasSum_sum hterm
  simpa only [map_sum, Finset.sum_smul] using hsum.tsum_eq

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [Algebra ℚ K]
  [NormedAlgebra ℚ_[p] K] [CompleteSpace K] {ι : Type*} {s : Finset ι} {a x : ι → K} {c : ℝ}

/-- On a closed disc strictly inside the exponential discs, the Hasse derivatives of
`∑ᵢ aᵢ exp(xᵢX)` evaluate to `∑ᵢ aᵢ (xᵢ ^ k / k!) exp(y xᵢ)`. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (k : ℕ) {y : K} (hy : ‖y‖ ≤ c) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp K))).evalAt y =
      ∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (y * x i) := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hs (i) (hi : i ∈ s) :=
    (isRestricted_rescale_exp ((norm_nonneg y).trans hy) (hxc i hi)).summable_smul_pow hy
  simpa [coeff_rescale, coeff_exp, Algebra.smul_def, mul_pow, mul_comm, mul_left_comm,
    mul_assoc, div_eq_mul_inv] using
    evalAt_hasseDeriv_sum_smul_rescale_exp_of_summable (a := a)
      (fun i hi ↦ by simpa [coeff_rescale, coeff_exp, Algebra.smul_def, mul_pow,
        mul_comm, mul_left_comm, mul_assoc] using hs i hi) k

/-- A fixed Hasse derivative of an exponential polynomial vanishes exactly when the
corresponding ordinary derivative sum vanishes; the factorial is nonzero in characteristic zero. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero_iff
    (hxc : ∀ i ∈ s, ‖x i‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (k : ℕ) {y : K} (hy : ‖y‖ ≤ c) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp K))).evalAt y = 0 ↔
      ∑ i ∈ s, a i * x i ^ k * NormedSpace.exp (y * x i) = 0 := by
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp hxc k hy]
  have h : ∑ i ∈ s, a i * (x i ^ k / k !) * NormedSpace.exp (y * x i) =
      (∑ i ∈ s, a i * x i ^ k * NormedSpace.exp (y * x i)) / k ! := by
    rw [sum_div]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [h, div_eq_zero_iff]
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hne : (k ! : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [hne, or_false]

end TauCeti
