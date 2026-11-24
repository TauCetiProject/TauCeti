/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Difference equations for coefficient Frobenius on power series

A twisted polynomial in positive coefficient Frobenius acts surjectively on power series over
an algebraically closed field if at least one of its operator coefficients has nonzero constant
term. Normalizing Laurent-series operator coefficients by a common power of `X` produces
a power-series equation with this nonzero reduction. Each successive coefficient is obtained
by solving a nonconstant residue polynomial.

## References

* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004),
  Proposition 3.17, for the reduction to a polynomial over the residue field.
-/

public section

open scoped PowerSeries
open Finset Function Polynomial

namespace TauCeti.PowerSeries

variable {p : ℕ} {k : Type*} [Field k] [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- A twisted polynomial in positive coefficient Frobenius with nonzero reduction modulo
`X` takes every value on power series over an algebraically closed field. -/
theorem exists_sum_mul_map_iterateFrobenius_eq (s : Finset ℕ) (a : ℕ → k⟦X⟧)
    {f : ℕ} (hf : 0 < f) (ha : ∃ i ∈ s, PowerSeries.constantCoeff (a i) ≠ 0) (b : k⟦X⟧) :
    ∃ x : k⟦X⟧, ∑ i ∈ s, a i * PowerSeries.map (iterateFrobenius k p (f * i)) x = b := by
  classical
  let q := p ^ f
  have hq : 1 < q := one_lt_pow₀ (Fact.out : p.Prime).one_lt hf.ne'
  -- The constant coefficients give the same nonconstant polynomial at every lifting step.
  let lead (x : k) := ∑ i ∈ s, PowerSeries.constantCoeff (a i) * x ^ (q ^ i)
  have hlead : Surjective lead := by
    let P : k[X] := ∑ i ∈ s, monomial (q ^ i) (PowerSeries.constantCoeff (a i))
    obtain ⟨i, hi, hai⟩ := ha
    have he (j : ℕ) : q ^ j = q ^ i ↔ j = i := (Nat.pow_right_injective hq).eq_iff
    have hcoeff : P.coeff (q ^ i) = PowerSeries.constantCoeff (a i) := by
      simp only [P, finsetSum_coeff, coeff_monomial_apply, he]
      simp [hi]
    have hdegree : P.natDegree ≠ 0 := by
      intro h
      have hlt : P.natDegree < q ^ i := h.symm ▸ pow_pos (by omega) _
      exact hai (hcoeff.symm.trans (coeff_eq_zero_of_natDegree_lt hlt))
    simpa only [lead, P, eval_finsetSum, eval_monomial] using IsAlgClosed.eval_surjective hdegree
  let lower (n : ℕ) (c : ℕ → k) : k :=
    ∑ i ∈ s, ∑ j ∈ range n, PowerSeries.coeff (n - j) (a i) * c j ^ (q ^ i)
  let solve (n : ℕ) (c : ℕ → k) := surjInv hlead (PowerSeries.coeff n b - lower n c)
  let step (n : ℕ) (prev : ∀ j < n, k) : k :=
    solve n (fun j => if h : j < n then prev j h else 0)
  let c : ℕ → k := fun n => Nat.strongRecOn n step
  have hc_step (n : ℕ) : c n = solve n (fun j => if j < n then c j else 0) := by
    simpa only [c, step, dite_eq_ite] using Nat.strongRecOn_eq step n
  have hc (n : ℕ) : ∑ i ∈ s, PowerSeries.constantCoeff (a i) * c n ^ (q ^ i) =
      PowerSeries.coeff n b - lower n c := by
    rw [hc_step]
    have h : lower n (fun j => if j < n then c j else 0) = lower n c := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
      simp [mem_range.mp hj]
    simpa only [solve, h] using
      rightInverse_surjInv hlead (PowerSeries.coeff n b - lower n c)
  refine ⟨PowerSeries.mk c, PowerSeries.ext fun n => ?_⟩
  have hmul (i : ℕ) :
      PowerSeries.coeff n (a i * PowerSeries.map (iterateFrobenius k p (f * i))
          (PowerSeries.mk c)) =
        (∑ j ∈ range n, PowerSeries.coeff (n - j) (a i) * c j ^ (q ^ i)) +
          PowerSeries.constantCoeff (a i) * c n ^ (q ^ i) := by
    rw [mul_comm, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, iterateFrobenius_def, q, pow_mul, mul_comm]
  simp only [map_sum, hmul, sum_add_distrib, hc, lower]
  abel

end TauCeti.PowerSeries
