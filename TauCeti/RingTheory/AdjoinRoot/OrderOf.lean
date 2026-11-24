/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Multiplicative orders of adjoined roots of cyclotomic-type relators

For a monic polynomial `g` over a nontrivial commutative ring `R`, no positive power `root g ^ m`
with `m < g.natDegree` lies in the image of `R` (`AdjoinRoot.root_pow_ne_of`). Specializing to
`1 + X + ⋯ + X ^ n` and `X ^ n + 1` gives exact multiplicative orders `n + 1` and `2 * n` whenever
`(2 : R) ≠ 0`.

## Main results

* `AdjoinRoot.root_pow_ne_of`: `root g ^ m ≠ of g c` for `0 < m < g.natDegree` and monic `g`.
* `AdjoinRoot.orderOf_root_geom_sum`: `orderOf (root (∑ k ∈ range (n + 1), X ^ k)) = n + 1` when
  `(2 : R) ≠ 0`.
* `AdjoinRoot.orderOf_root_X_pow_add_one`: `orderOf (root (X ^ n + 1)) = 2 * n` when `0 < n` and
  `(2 : R) ≠ 0`.
-/

public section

open Finset Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- In `AdjoinRoot g` for a monic polynomial `g` over a nontrivial commutative ring, no positive
power `root g ^ m` with `m < g.natDegree` lies in the image of the base ring `R`. -/
theorem root_pow_ne_of [Nontrivial R] {g : R[X]} (hg : g.Monic) {m : ℕ} (hm0 : 0 < m)
    (hmg : m < g.natDegree) (c : R) : root g ^ m ≠ of g c := by
  rw [← mk_X, ← map_pow, ← mk_C]
  intro h
  have hdegX : (X ^ m : R[X]).degree < g.degree := by
    rw [degree_X_pow, degree_eq_natDegree hg.ne_zero]; exact Nat.cast_lt.2 hmg
  have hdegC : (C c).degree < g.degree :=
    degree_C_le.trans_lt
      (by rw [degree_eq_natDegree hg.ne_zero]; exact Nat.cast_pos.2 (hm0.trans hmg))
  have hEq := congrArg (fun p : R[X] ↦ p.coeff m) ((mk_eq_mk_iff_of_degree_lt hg hdegX hdegC).1 h)
  rw [coeff_X_pow_self, coeff_C_of_ne_zero hm0.ne'] at hEq
  exact one_ne_zero hEq

/-- **The adjoined root of `1 + X + ⋯ + X ^ n` has multiplicative order `n + 1`** whenever
`(2 : R) ≠ 0`. -/
theorem orderOf_root_geom_sum (n : ℕ) (h2 : (2 : R) ≠ 0) :
    orderOf (root (∑ k ∈ range (n + 1), (X : R[X]) ^ k)) = n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdjoinRoot (∑ k ∈ range 1, (X : R[X]) ^ k)) :=
      subsingleton_of_zero_eq_one <| by
        rw [← mk_self (f := ∑ k ∈ range 1, (X : R[X]) ^ k), sum_range_one, pow_zero, map_one]
    rw [Subsingleton.elim (root (∑ k ∈ range 1, (X : R[X]) ^ k)) 1, orderOf_one]
  have : Nontrivial R := nontrivial_of_ne 2 0 h2
  set g : R[X] := ∑ k ∈ range (n + 1), X ^ k
  have hg : g.Monic := monic_geom_sum_X (Nat.succ_ne_zero n)
  have hdeg : g.natDegree = n := natDegree_geom_sum_X_succ n
  have h0deg : 0 < g.degree := by rw [degree_eq_natDegree hg.ne_zero, hdeg]; exact Nat.cast_pos.2 hn
  have hpow : root g ^ (n + 1) = 1 := sub_eq_zero.1 <| by
    rw [← map_one (mk g), ← mk_X, ← map_pow, ← map_sub, ← geom_sum_mul, map_mul, mk_self, zero_mul]
  refine (orderOf_eq_iff (by omega)).2 ⟨hpow, fun m hmlt hm0 hm1 ↦ ?_⟩
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hmlt) with hmn | rfl
  · exact root_pow_ne_of hg hm0 (hdeg ▸ hmn) 1 (by rwa [map_one])
  · have hr1 : root g = 1 := by simpa [pow_succ', hm1] using hpow
    rcases eq_or_ne m 1 with rfl | hm_ne
    · have h20 : of g 2 = of g 0 := by
        rw [map_ofNat, map_zero]
        simpa [g, sum_range_succ, hr1, one_add_one_eq_two] using (mk_self (f := g))
      exact h2 (of.injective_of_monic_of_degree_pos hg h0deg h20)
    · exact root_pow_ne_of hg Nat.one_pos (by omega) 1 (by simpa [map_one] using hr1)

/-- **The adjoined root of `X ^ n + 1` has multiplicative order `2 * n`** whenever `0 < n` and
`(2 : R) ≠ 0`. -/
theorem orderOf_root_X_pow_add_one {n : ℕ} (hn : 0 < n) (h2 : (2 : R) ≠ 0) :
    orderOf (root (X ^ n + 1 : R[X])) = 2 * n := by
  have : Nontrivial R := nontrivial_of_ne 2 0 h2
  set g : R[X] := X ^ n + 1
  have hg : g.Monic := by simpa [g] using monic_X_pow_add_C (1 : R) hn.ne'
  have hdeg : g.natDegree = n := by simp [g]
  have h0deg : 0 < g.degree := by rw [degree_eq_natDegree hg.ne_zero, hdeg]; exact Nat.cast_pos.2 hn
  have hneg : root g ^ n = -1 := eq_neg_of_add_eq_zero_left <| by
    rw [← map_one (mk g), ← mk_X, ← map_pow, ← map_add, mk_self]
  have hpow : root g ^ (2 * n) = 1 := by rw [two_mul, pow_add, hneg, neg_one_mul, neg_neg]
  refine (orderOf_eq_iff (by omega)).2 ⟨hpow, fun m hmlt hm0 hm1 ↦ ?_⟩
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · exact root_pow_ne_of hg hm0 (hdeg ▸ hmn) 1 (by rwa [map_one])
  · rw [hneg] at hm1
    have h20 : of g 2 = of g 0 := by
      rw [map_ofNat, map_zero, ← one_add_one_eq_two]; exact neg_eq_iff_add_eq_zero.1 hm1
    exact h2 (of.injective_of_monic_of_degree_pos hg h0deg h20)
  · rw [← Nat.add_sub_of_le hnm.le, pow_add, hneg, neg_one_mul, neg_eq_iff_eq_neg] at hm1
    exact root_pow_ne_of hg (m := m - n) (by omega) (by omega) (-1) (by rwa [map_neg, map_one])

end AdjoinRoot

end
