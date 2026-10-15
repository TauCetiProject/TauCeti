/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# Neumann series for the resolvent of a partial operator

Near a resolvent point `lambda`, the resolvent of a partial operator has the operator-norm
convergent expansion

`R(mu) = ∑' n, (lambda - mu)^n • R(lambda)^(n+1)`.

The sufficient convergence condition is `‖mu - lambda‖ * ‖R(lambda)‖ < 1`. The sign follows
the convention that `R(lambda)` inverts `lambda • I - A`. The geometric truncation bound
controls approximation of the resolvent by finite polynomials in `R(lambda)`.

No symmetry, density of the domain, or Hilbert-space structure is required: the results hold
for partial linear operators on Banach spaces over nontrivially normed fields. The expansion
uses Mathlib's `hasSum_geom_series_inverse` and the existing ring-inverse resolvent formula.

## References

* K. J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section IV.1.
-/

public section

namespace LinearPMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]
variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}

/-- The local Neumann series converges in operator norm to the resolvent at `mu`. -/
theorem hasSum_resolvent (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) :
    HasSum (fun n : ℕ ↦ (lambda - mu) ^ n • A.resolvent lambda ^ (n + 1))
      (A.resolvent mu) := by
  have hnorm : ‖(lambda - mu) • A.resolvent lambda‖ < 1 := by
    simpa only [norm_smul, norm_sub_rev] using hmu
  rw [TauCeti.LinearPMap.resolvent_eq_mul_inverse_one_sub h hmu]
  simpa only [smul_pow, mul_smul_comm, ← pow_succ'] using
    (hasSum_geom_series_inverse ((lambda - mu) • A.resolvent lambda) hnorm).mul_left
      (A.resolvent lambda)

/-- The resolvent equals its local Neumann series whenever the change of parameter is small
against the norm of the original resolvent. -/
theorem resolvent_eq_tsum (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) :
    A.resolvent mu = ∑' n : ℕ, (lambda - mu) ^ n • A.resolvent lambda ^ (n + 1) :=
  (hasSum_resolvent h hmu).tsum_eq.symm

/-- Truncating the local resolvent series after `N` terms has the geometric error bound
`‖R(lambda)‖ q^N / (1-q)`, where `q = ‖mu-lambda‖ ‖R(lambda)‖ < 1`. This includes the empty
truncation `N = 0` and the unchanged-parameter case `mu = lambda`. -/
theorem norm_resolvent_sub_sum_le (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) (N : ℕ) :
    ‖A.resolvent mu -
      ∑ n ∈ Finset.range N, (lambda - mu) ^ n • A.resolvent lambda ^ (n + 1)‖ ≤
      ‖A.resolvent lambda‖ * (‖mu - lambda‖ * ‖A.resolvent lambda‖) ^ N /
        (1 - ‖mu - lambda‖ * ‖A.resolvent lambda‖) := by
  rw [norm_sub_rev]
  refine norm_sub_le_of_geometric_bound_of_hasSum
    (C := ‖A.resolvent lambda‖) (r := ‖mu - lambda‖ * ‖A.resolvent lambda‖)
    (f := fun n : ℕ ↦ (lambda - mu) ^ n • A.resolvent lambda ^ (n + 1)) hmu (fun n ↦ ?_)
    (hasSum_resolvent h hmu) N
  calc
    ‖(lambda - mu) ^ n • A.resolvent lambda ^ (n + 1)‖ =
        ‖mu - lambda‖ ^ n * ‖A.resolvent lambda ^ (n + 1)‖ := by
      rw [norm_smul, norm_pow, norm_sub_rev]
    _ ≤ ‖mu - lambda‖ ^ n * ‖A.resolvent lambda‖ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (norm_pow_le' _ (Nat.succ_pos n)) (by positivity)
    _ = ‖A.resolvent lambda‖ * (‖mu - lambda‖ * ‖A.resolvent lambda‖) ^ n := by
      rw [mul_pow, pow_succ]
      ring

end LinearPMap
