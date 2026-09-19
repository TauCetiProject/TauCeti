/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Regrouping a double series by the product of the indices

A sum over pairs of positive integers `(c, m)` can be regrouped according to the product
`n = c m`: the `n`-th group is the finite sum over `Nat.divisorsAntidiagonal n`. This is how a
double series `∑_{c, m ≥ 1} a(c) b(m) q^{c m}`, such as the `q`-expansion of an Eisenstein
series, becomes a power series `∑_n (∑_{c m = n} a(c) b(m)) q^n`.

Mathlib's `tsum_prod_pow_eq_tsum_sigma` proves one instance of this regrouping, for the terms
`m^k r^{c m}`; this file states the regrouping for an arbitrary summable family, through the
same equivalence `sigmaAntidiagonalEquivProd`.

## Main results

* `HasSum.sum_divisorsAntidiagonal`: regrouping a convergent double series by the product of
  the indices.
-/

public section

variable {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α] [RegularSpace α]

/-- **Regrouping a double series by the product of the indices.** If the family
`(c, m) ↦ f c m` over pairs of positive integers sums to `a`, then so does the series over
`n ≥ 1` of the finite sums `∑_{c m = n} f c m`. -/
theorem HasSum.sum_divisorsAntidiagonal {f : ℕ → ℕ → α} {a : α}
    (hf : HasSum (fun p : ℕ+ × ℕ+ ↦ f p.1 p.2) a) :
    HasSum (fun n : ℕ+ ↦ ∑ x ∈ (n : ℕ).divisorsAntidiagonal, f x.1 x.2) a := by
  refine (sigmaAntidiagonalEquivProd.hasSum_iff.mpr hf).sigma fun n ↦ ?_
  have h := hasSum_fintype fun x : (n : ℕ).divisorsAntidiagonal ↦ f x.1.1 x.1.2
  rw [Finset.univ_eq_attach, Finset.sum_attach _ fun x : ℕ × ℕ ↦ f x.1 x.2] at h
  simpa [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors] using h
