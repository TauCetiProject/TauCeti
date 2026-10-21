/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Transforms
public import TauCeti.Probability.Moments.Pi

/-!
# Natural moments of hypoexponential laws

The `n`th raw moment of a sum of independent exponentials is `n!` times the complete homogeneous
sum of degree `n` in the reciprocal rates. The sum is indexed by
`Finset.piAntidiag Finset.univ n`, a finite set of exponent vectors whose entries sum to `n`.
Repeated rates are allowed, and the empty family gives moment one at order zero and zero at
positive orders.

The calculation combines `TauCeti.integral_pow_sum_pi` with the exponential moment formula
`TauCeti.Probability.integral_pow_expMeasure`. The factorials in the coordinate moments cancel
the denominator of Mathlib's multinomial coefficient.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ}

/-- Every natural raw moment of a hypoexponential law is a finite sum of reciprocal-rate
monomials, multiplied by the factorial of its order. This includes repeated rates and the empty
family. Integrability is supplied by `integrable_pow_hypoexponentialMeasure`. -/
@[simp]
theorem integral_pow_hypoexponentialMeasure (hr : ∀ i, 0 < r i) (n : ℕ) :
    ∫ x, x ^ n ∂hypoexponentialMeasure r =
      (n.factorial : ℝ) * ∑ k ∈ Finset.piAntidiag Finset.univ n, ∏ i, (r i)⁻¹ ^ k i := by
  classical
  let _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  rw [hypoexponentialMeasure_eq_map hr, integral_map (by fun_prop) (by fun_prop)]
  rw [integral_pow_sum_pi (fun (_ : ι) (x : ℝ) ↦ x) n
    (fun i m _ ↦ integrable_pow_expMeasure (hr i) m)]
  simp_rw [integral_pow_expMeasure (hr _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hsum : ∑ i, k i = n := (Finset.mem_piAntidiag.mp hk).1
  have hfactorial :
      (∏ i, (k i).factorial : ℝ) * Nat.multinomial Finset.univ k = n.factorial := by
    exact_mod_cast (Nat.multinomial_spec Finset.univ k).trans (congrArg Nat.factorial hsum)
  simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, ← inv_pow]
  rw [← mul_assoc, mul_comm (Nat.multinomial Finset.univ k : ℝ), hfactorial]

end TauCeti.Probability
