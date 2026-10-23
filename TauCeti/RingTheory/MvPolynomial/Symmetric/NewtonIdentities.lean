/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import TauCeti.Algebra.Algebra.NatCast
import Mathlib.Data.Multiset.Fintype

/-!
# Newton's identities for a multiset

Mathlib states Newton's identities, `MvPolynomial.mul_esymm_eq_sum`, for the elementary symmetric
and power-sum polynomials in a finite type of variables. This file evaluates them at the elements
of a multiset, which is the form in which they apply to the roots of a polynomial: the elementary
symmetric functions `Multiset.esymm` of a multiset are recovered recursively from its power sums
`(s.map (· ^ j)).sum`, in any commutative ring in which the relevant integers can be inverted.

Consequently, if `(card s)!` is invertible in the scalars, any subalgebra containing the first
`card s` power sums of `s` contains every elementary symmetric function and every power sum of `s`.
This is how a statement about boundedly many power sums of the translates of an element under a
finite group, as in Noether's bound on the degrees of generating invariants, controls all of them.

## Main results

* `Multiset.mul_esymm_eq_sum`: **Newton's identities** for the elements of a multiset.
* `Multiset.esymm_mem_of_sum_map_pow_mem`: the elementary symmetric functions of `s` lie in every
  subalgebra containing its first `card s` power sums.
* `Multiset.sum_map_pow_mem_of_sum_map_pow_mem`: so do all the power sums of `s`.
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

section Subalgebra

variable {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {T : Subalgebra K S}

/-- If `(card s)!` is invertible in `K`, then the elementary symmetric functions of a multiset `s`
lie in every `K`-subalgebra containing its power sums `(s.map (· ^ j)).sum` for
`1 ≤ j ≤ card s`. -/
theorem _root_.Multiset.esymm_mem_of_sum_map_pow_mem (s : Multiset S)
    (hs : IsUnit ((Multiset.card s).factorial : K))
    (hT : ∀ j, 0 < j → j ≤ Multiset.card s → (s.map (· ^ j)).sum ∈ T) (k : ℕ) :
    s.esymm k ∈ T := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases lt_or_ge (Multiset.card s) k with hk | hk
  · rw [Multiset.esymm_of_card_lt hk]
    exact zero_mem T
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  -- Newton's identity expresses `k * e_k` through lower `e_i` and the power sums `p_j`, `j ≤ k`.
  have hu : IsUnit (k : K) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_factorial hk0 hk)) hs
  rw [← T.natCast_mul_mem_iff hu, Multiset.mul_esymm_eq_sum]
  refine mul_mem (pow_mem (neg_mem (one_mem T)) _) (sum_mem fun a ha ↦ ?_)
  rw [mem_filter, mem_antidiagonal] at ha
  exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem T)) _) (ih _ ha.2))
    (hT _ (by omega) (by omega))

/-- If `(card s)!` is invertible in `K`, then every power sum `(s.map (· ^ k)).sum` of a multiset
`s` lies in every `K`-subalgebra containing those for `1 ≤ k ≤ card s`. -/
theorem _root_.Multiset.sum_map_pow_mem_of_sum_map_pow_mem (s : Multiset S)
    (hs : IsUnit ((Multiset.card s).factorial : K))
    (hT : ∀ j, 0 < j → j ≤ Multiset.card s → (s.map (· ^ j)).sum ∈ T) (k : ℕ) :
    (s.map (· ^ k)).sum ∈ T := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases le_or_gt k (Multiset.card s) with hk | hk
  · exact hT k hk0 hk
  -- Beyond `card s` we have `e_k = 0`, so Newton's identity at `k` writes `p_k` through the
  -- products `e_i * p_j` with `0 < i` and `j < k`.
  have h := s.mul_esymm_eq_sum k
  rw [Multiset.esymm_of_card_lt hk, mul_zero, eq_comm, neg_one_pow_mul_eq_zero_iff,
    ← add_sum_erase _ _ (by simp [hk0] : ((0, k) : ℕ × ℕ) ∈ {a ∈ antidiagonal k | a.1 < k})]
    at h
  simp only [pow_zero, Multiset.esymm_zero, one_mul] at h
  rw [eq_neg_of_add_eq_zero_left h]
  refine neg_mem (sum_mem fun a ha ↦ ?_)
  simp only [mem_erase, mem_filter, mem_antidiagonal, ne_eq, Prod.ext_iff, not_and] at ha
  exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem T)) _)
    (s.esymm_mem_of_sum_map_pow_mem hs hT _)) (ih _ (by omega))

end Subalgebra

end TauCeti
