/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Series
public import TauCeti.Topology.Algebra.InfiniteSum.IntegralCoefficients

/-!
# Evaluating divisor-sum series

The integral divisor-sum series converges at a parameter of norm less than one in a complete
non-archimedean normed ring. Its value is the sum of its evaluated coefficients.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [NormedRing K] [NormOneClass K] [CompleteSpace K] [IsUltrametricDist K]

/-- The divisor-sum series `s_k(q) = ∑ σ_k(n) q^n` converges for `‖q‖ < 1`. -/
theorem summable_divisorSumSeries (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (((σ k n : ℕ) : ℤ) : K) * q ^ n) :=
  summable_intCast_mul_pow (fun n : ℕ ↦ ((σ k n : ℕ) : ℤ)) hq

/-- Evaluation of the integral divisor-sum series in a complete non-archimedean normed ring. Its
convergence for `‖q‖ < 1` is `summable_divisorSumSeries`. -/
noncomputable def divisorSumAt (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, (((σ k n : ℕ) : ℤ) : K) * q ^ n

omit [NormOneClass K] [CompleteSpace K] [IsUltrametricDist K] in
/-- The value of a divisor-sum series is its defining sum. -/
theorem divisorSumAt_def (k : ℕ) (q : K) :
    divisorSumAt k q = ∑' n : ℕ, (((σ k n : ℕ) : ℤ) : K) * q ^ n := by
  simp only [divisorSumAt]

end TauCeti

end
