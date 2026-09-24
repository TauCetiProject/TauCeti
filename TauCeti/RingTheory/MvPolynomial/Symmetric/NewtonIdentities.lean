/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Data.Multiset.Fintype

/-!
# Newton's identities for a multiset

Mathlib states Newton's identities, `MvPolynomial.mul_esymm_eq_sum`, for the elementary symmetric
and power-sum polynomials in a finite type of variables. This file evaluates them at the elements
of a multiset, which is the form in which they apply to the roots of a polynomial: the elementary
symmetric functions `Multiset.esymm` of a multiset are recovered recursively from its power sums
`(s.map (· ^ j)).sum`, in any commutative ring in which the relevant integers can be inverted.

## Main results

* `Multiset.mul_esymm_eq_sum`: **Newton's identities** for the elements of a multiset.
-/

public section

open Finset

namespace TauCeti

/-- **Newton's identities** for a multiset: `k` times the `k`-th elementary symmetric function of
the elements of `s` is an explicit combination of the lower elementary symmetric functions and
the power sums `(s.map (· ^ j)).sum`. This is `MvPolynomial.mul_esymm_eq_sum` evaluated at the
elements of `s`. -/
theorem _root_.Multiset.mul_esymm_eq_sum {R : Type*} [CommRing R] (s : Multiset R) (k : ℕ) :
    k * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval fun x : s.ToType => (x : R))
    (MvPolynomial.mul_esymm_eq_sum s.ToType R k)
  have hpsum (j : ℕ) : MvPolynomial.aeval (fun x : s.ToType => (x : R))
      (MvPolynomial.psum s.ToType R j) = (s.map (· ^ j)).sum := by
    rw [← Multiset.map_univ_comp_coe, Finset.sum_map_val]
    simp [MvPolynomial.psum]
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, hpsum] at h
  exact h

end TauCeti
