/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integrality as an explicit monic relation of positive degree

`IsIntegral S x` says a monic polynomial over `S` kills `x`. For arguments that adjust the
coefficients one at a time it is more convenient to have the relation written out, and written
so that its degree is visibly positive:

```text
x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0.
```

Writing the degree as `n + 1` rather than carrying a separate `0 < p.natDegree` hypothesis is
what lets a caller perturb the constant coefficient without disturbing the leading one, which is
the shape Huber's approximation arguments need.

## Main results

* `TauCeti.isIntegral_iff_exists_pow_add_sum_smul_eq_zero`: over any commutative ring `S`, an
  element of an `S`-algebra is integral iff it satisfies such a relation with coefficients in `S`.
* `TauCeti.isIntegral_iff_exists_pow_add_sum_mul_eq_zero`: the same for a subring `S` of a
  commutative ring, with the coefficients taken in the ambient ring and asserted to lie in `S`
  only where the relation uses them.
-/

public section

namespace TauCeti

open Polynomial

/-- An element `x` of an `S`-algebra is integral over `S` iff it satisfies a monic relation
`x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0` of positive degree `n + 1` with
coefficients `c i` in `S`. -/
theorem isIntegral_iff_exists_pow_add_sum_smul_eq_zero {S A : Type*} [CommRing S] [Ring A]
    [Algebra S A] {x : A} :
    IsIntegral S x ↔
      ∃ (n : ℕ) (c : ℕ → S), x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0 := by
  refine ⟨fun ⟨p, hmonic, heval⟩ ↦ ?_, fun ⟨n, c, h⟩ ↦ ?_⟩
  · -- multiplying the relation by `x` shifts the coefficients up by one, which makes the degree
    -- positive even when `p` is constant
    refine ⟨p.natDegree, fun i ↦ Nat.casesOn i 0 p.coeff, ?_⟩
    have h0 : (∑ i ∈ Finset.range p.natDegree, p.coeff i • x ^ i) + x ^ p.natDegree = 0 := by
      rw [← heval, eval₂_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree]
      simp [Algebra.smul_def]
    rw [Finset.sum_range_succ', add_comm]
    simpa [add_mul, Finset.sum_mul, smul_mul_assoc, ← pow_succ] using congrArg (· * x) h0
  · -- the witness sums over `Fin (n + 1)`, the shape `degree_sum_fin_lt` bounds directly
    exact ⟨X ^ (n + 1) + ∑ i : Fin (n + 1), C (c i) * X ^ (i : ℕ),
      monic_X_pow_add (degree_sum_fin_lt _), by
        simpa [eval₂_finsetSum, C_mul_X_pow_eq_monomial, Finset.sum_range, Algebra.smul_def]
          using h⟩

/-- An element `x` of a commutative ring is integral over a subring `S` iff it satisfies a monic
relation `x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0` of positive degree `n + 1`
whose coefficients `c i` lie in `S` for `i < n + 1`. Membership is asserted only on the range
the relation sums over, so neither direction makes or needs a promise about the tail. -/
theorem isIntegral_iff_exists_pow_add_sum_mul_eq_zero {R : Type*} [CommRing R] {S : Subring R}
    {x : R} :
    IsIntegral S x ↔ ∃ (n : ℕ) (c : ℕ → R), (∀ i < n + 1, c i ∈ S) ∧
      x ^ (n + 1) + ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 := by
  rw [isIntegral_iff_exists_pow_add_sum_smul_eq_zero]
  refine ⟨fun ⟨n, c, h⟩ ↦ ⟨n, (c ·), fun i _ ↦ (c i).2, by simpa [Subring.smul_def] using h⟩,
    fun ⟨n, c, hcS, h⟩ ↦ ⟨n, fun i ↦ if hi : i < n + 1 then ⟨c i, hcS i hi⟩ else 0, ?_⟩⟩
  refine .trans (congrArg _ (Finset.sum_congr rfl fun i hi ↦ ?_)) h
  simp [Subring.smul_def, Finset.mem_range.mp hi]

end TauCeti
