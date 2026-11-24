/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Exp.HasseDeriv
import TauCeti.RingTheory.PowerSeries.Rescale
import Mathlib.Tactic.Module
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Evaluation of the formal exponential

Evaluating the formal exponential at a point gives the same `tsum` as `NormedSpace.exp`, even
when the evaluation terms are not summable and both sides are the junk value `0`.

For an exponential polynomial `∑ᵢ aᵢ exp(xᵢX)` whose exponential series converge at `y`, the
Hasse derivative `D⁽ᵏ⁾` evaluates at `y` to the weighted exponential sum
`∑ᵢ aᵢ (xᵢ ^ k / k!) exp(y xᵢ)`; it vanishes exactly when `∑ᵢ aᵢ xᵢ ^ k exp(y xᵢ)` does.
-/

public section

open Finset
open scoped Nat

namespace PowerSeries

/-- The formal exponential evaluates to `NormedSpace.exp`: both are the sum `∑ bⁿ / n!`. Neither
side assumes convergence, so the identity also holds for the junk value of a divergent sum. -/
@[simp]
theorem evalAt_exp {R A : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalRing A] (b : A) :
    (exp R).evalAt b = NormedSpace.exp b := by
  let : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ R)
  let : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' (Algebra.compHom_algebraMap_eq _ _)
  rw [evalAt_def, NormedSpace.exp_eq_tsum_rat]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_exp, algebraMap_smul, one_div]

variable {R : Type*} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
  [T2Space R] {ι : Type*} {s : Finset ι} {a x : ι → R} {y : R}

/-- If each rescaled exponential series `exp(xᵢX)` converges at `y`, the `k`th Hasse derivative
of the exponential polynomial `∑ᵢ aᵢ exp(xᵢX)` evaluates at `y` to the weighted exponential sum
`∑ᵢ aᵢ (xᵢ ^ k / k!) exp(y xᵢ)`. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp_of_summable
    (hs : ∀ i ∈ s, Summable fun n ↦ coeff n (rescale (x i) (exp R)) • y ^ n) (k : ℕ) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp R))).evalAt y =
      ∑ i ∈ s, a i * ((k ! : ℚ)⁻¹ • x i ^ k) * NormedSpace.exp (y * x i) := by
  -- the chain rule `D⁽ᵏ⁾ exp(xX) = (xᵏ / k!) exp(xX)`
  have hD : hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp R)) =
      ∑ i ∈ s, (a i * ((k ! : ℚ)⁻¹ • x i ^ k)) • rescale (x i) (exp R) := by
    simp only [map_sum, map_smul, hasseDeriv_rescale, hasseDeriv_exp, rescale_smul]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← smul_eq_C_mul]
    match_scalars
    rw [Algebra.smul_def]
    ring
  rw [hD, evalAt_sum_of_summable s fun i hi ↦
    (hasSum_evalAt_smul_of_summable (hs i hi) _).summable]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [evalAt_smul_of_summable (hs i hi), evalAt_rescale, evalAt_exp, smul_eq_mul,
    smul_eq_mul, mul_comm (x i)]

/-- If each rescaled exponential series `exp(xᵢX)` converges at `y`, the `k`th Hasse derivative
of `∑ᵢ aᵢ exp(xᵢX)` vanishes at `y` exactly when `∑ᵢ aᵢ xᵢ ^ k exp(y xᵢ)` does. -/
theorem evalAt_hasseDeriv_sum_smul_rescale_exp_eq_zero_iff_of_summable
    (hs : ∀ i ∈ s, Summable fun n ↦ coeff n (rescale (x i) (exp R)) • y ^ n) (k : ℕ) :
    (hasseDeriv k (∑ i ∈ s, a i • rescale (x i) (exp R))).evalAt y = 0 ↔
      ∑ i ∈ s, a i * x i ^ k * NormedSpace.exp (y * x i) = 0 := by
  have h : ∑ i ∈ s, a i * ((k ! : ℚ)⁻¹ • x i ^ k) * NormedSpace.exp (y * x i) =
      (k ! : ℚ)⁻¹ • ∑ i ∈ s, a i * x i ^ k * NormedSpace.exp (y * x i) := by
    simp only [smul_sum, mul_smul_comm, smul_mul_assoc]
  rw [evalAt_hasseDeriv_sum_smul_rescale_exp_of_summable hs, h,
    (Ne.isUnit (by positivity : (k ! : ℚ)⁻¹ ≠ 0)).smul_eq_zero]

end PowerSeries
