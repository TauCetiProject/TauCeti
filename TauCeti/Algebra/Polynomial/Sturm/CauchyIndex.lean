/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.Sign
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Defs
public import Mathlib.Algebra.BigOperators.Finprod

/-! # The Cauchy index of a quotient of polynomials

`Polynomial.cauchyJump p q a` is the jump of the rational function `q / p` at `a`. It is zero
unless `a` is a pole of `q / p` of odd order. At such a pole it is `+1` for a jump from `-∞` to
`+∞` and `-1` for a jump from `+∞` to `-∞`. The sign of `q / p` immediately to the right of `a`
is the right-hand sign of `p * q`, so the jump is defined algebraically from root multiplicities
and `Polynomial.signRight`. It needs no topology and makes sense over any ordered field.

`Polynomial.cauchyIndex p q s` sums these jumps over a set `s`. Only roots of `p` contribute, so
the sum is finite. As for `Polynomial.tarskiQuery p q`, the first argument supplies the
denominator, and hence the roots. With this convention the index of `p' / p` counts distinct
roots, and the index of `p' * q / p` on the whole line is the Tarski query `TaQ(q, p)`.

The index depends only on the rational function `q / p`: cancelling a common factor does not
change it, and neither does reducing `q` modulo `p`. Over a real closed field, if `a < b` and
neither `a` nor `b` is a root of `p * q`, the indices of `q / p` and `p / q` on `(a, b)` sum to
half the change of sign of `p * q` from `a` to `b`. With the reduction modulo `p` this gives the
Euclidean recurrence for the index, under the same endpoint hypotheses.

## Main declarations

* `Polynomial.cauchyJump`: the jump of `q / p` at a point.
* `Polynomial.cauchyIndex`: the sum of the jumps of `q / p` over a set.
* `Polynomial.cauchyIndex_mul_right`: cancellation of a common factor.
* `Polynomial.cauchyIndex_mod`: reduction of the numerator modulo the denominator.
* `Polynomial.cauchyIndex_derivative`: the index of `p' / p` counts distinct roots.
* `Polynomial.cauchyIndex_derivative_mul_univ`: the whole-line index of `p' * q / p` is
  `tarskiQuery p q`.
* `Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ioo`: the inversion formula on an interval
  `(a, b)` with `a < b` whose endpoints are not roots of `p * q`.
* `Polynomial.two_mul_cauchyIndex_Ioo`: the Euclidean recurrence, under the same hypotheses.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index and its properties).
-/

public section

namespace Polynomial

open SignType Set

section Definitions

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The jump of `q / p` at `a`. It is the right-hand sign of `p * q` at `a` when `a` is a pole
of `q / p` of odd order, and zero otherwise. -/
noncomputable def cauchyJump (p q : R[X]) (a : R) : ℤ :=
  if q.rootMultiplicity a < p.rootMultiplicity a ∧
      Odd (p.rootMultiplicity a - q.rootMultiplicity a) then
    ((p * q).signRight a : ℤ)
  else 0

theorem cauchyJump_def (p q : R[X]) (a : R) :
    cauchyJump p q a =
      if q.rootMultiplicity a < p.rootMultiplicity a ∧
          Odd (p.rootMultiplicity a - q.rootMultiplicity a) then
        ((p * q).signRight a : ℤ)
      else 0 := (rfl)

/-- The jump vanishes where `q / p` has no pole. -/
theorem cauchyJump_of_rootMultiplicity_le {p q : R[X]} {a : R}
    (h : p.rootMultiplicity a ≤ q.rootMultiplicity a) : cauchyJump p q a = 0 := by
  simp only [cauchyJump_def, ite_eq_right_iff]
  exact fun h' => absurd h'.1 (not_lt.mpr h)

/-- The jump vanishes away from the roots of `p`. -/
theorem cauchyJump_of_eval_ne_zero {p : R[X]} (q : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    cauchyJump p q a = 0 :=
  cauchyJump_of_rootMultiplicity_le (by simp [rootMultiplicity_eq_zero ha])

@[simp]
theorem cauchyJump_zero_left (q : R[X]) (a : R) : cauchyJump 0 q a = 0 :=
  cauchyJump_of_rootMultiplicity_le (by simp)

@[simp]
theorem cauchyJump_zero_right (p : R[X]) (a : R) : cauchyJump p 0 a = 0 := by
  simp [cauchyJump_def]

/-- The Cauchy index of `q / p` on `s`: the sum of the jumps of `q / p` at the points of `s`. -/
noncomputable def cauchyIndex (p q : R[X]) (s : Set R) : ℤ :=
  ∑ᶠ x ∈ s, cauchyJump p q x

theorem cauchyIndex_def (p q : R[X]) (s : Set R) :
    cauchyIndex p q s = ∑ᶠ x ∈ s, cauchyJump p q x := (rfl)

@[simp]
theorem cauchyIndex_empty (p q : R[X]) : cauchyIndex p q ∅ = 0 := by
  simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_singleton (p q : R[X]) (a : R) : cauchyIndex p q {a} = cauchyJump p q a := by
  simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_zero_left (q : R[X]) (s : Set R) : cauchyIndex 0 q s = 0 := by
  simp [cauchyIndex_def]

@[simp]
theorem cauchyIndex_zero_right (p : R[X]) (s : Set R) : cauchyIndex p 0 s = 0 := by
  simp [cauchyIndex_def]

end Definitions

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Only roots of `p` carry a jump of `q / p`. -/
theorem support_cauchyJump_subset (p q : R[X]) :
    Function.support (cauchyJump p q) ⊆ p.roots.toFinset := by
  intro x hx
  by_cases hp : p = 0
  · simp [hp] at hx
  by_contra hr
  exact hx (cauchyJump_of_eval_ne_zero q (by simpa [mem_roots hp] using hr))

/-- Only finitely many points carry a jump of `q / p`. -/
theorem finite_support_cauchyJump (p q : R[X]) : (Function.support (cauchyJump p q)).Finite :=
  p.roots.toFinset.finite_toSet.subset (support_cauchyJump_subset p q)

/-- The Cauchy index as a finite sum over the distinct roots of `p` in `s`. -/
theorem cauchyIndex_eq_sum (p q : R[X]) (s : Set R) [DecidablePred (· ∈ s)] :
    cauchyIndex p q s = ∑ x ∈ p.roots.toFinset with x ∈ s, cauchyJump p q x := by
  rw [cauchyIndex_def]
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext x
  simp only [mem_inter_iff, Finset.coe_filter, mem_ofPred_eq]
  exact ⟨fun h => ⟨⟨support_cauchyJump_subset p q h.2, h.1⟩, h.2⟩,
    fun h => ⟨h.1.2, h.2⟩⟩

/-- The Cauchy index is additive over disjoint sets. -/
theorem cauchyIndex_union (p q : R[X]) {s t : Set R} (h : Disjoint s t) :
    cauchyIndex p q (s ∪ t) = cauchyIndex p q s + cauchyIndex p q t :=
  finsum_mem_union' h ((finite_support_cauchyJump p q).inter_of_right s)
    ((finite_support_cauchyJump p q).inter_of_right t)

/-- Splitting an open interval at an interior point adds the jump at that point. -/
theorem cauchyIndex_Ioo_eq_add {p q : R[X]} {a b c : R} (hab : a < b) (hbc : b < c) :
    cauchyIndex p q (Ioo a c) =
      cauchyIndex p q (Ioo a b) + cauchyJump p q b + cauchyIndex p q (Ioo b c) := by
  rw [← Ioc_union_Ioo_eq_Ioo hab.le hbc,
    cauchyIndex_union _ _ (disjoint_left.mpr fun _ hx hx' => hx'.1.not_ge hx.2),
    ← Ioo_insert_right hab, insert_eq, union_comm,
    cauchyIndex_union _ _ (disjoint_singleton_right.mpr (by simp)), cauchyIndex_singleton]

/-- Cancelling a common nonzero factor of `p` and `q` does not change the jumps of `q / p`. -/
theorem cauchyJump_mul_right (p q : R[X]) {r : R[X]} (hr : r ≠ 0) (a : R) :
    cauchyJump (p * r) (q * r) a = cauchyJump p q a := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  have hs : p.signRight a * r.signRight a * (q.signRight a * r.signRight a) =
      p.signRight a * q.signRight a := by
    have h0 : r.signRight a ≠ 0 := by simpa using hr
    generalize p.signRight a = s at *
    generalize q.signRight a = t at *
    generalize r.signRight a = u at *
    cases s <;> cases t <;> cases u <;> simp_all
  simp only [cauchyJump_def, rootMultiplicity_mul (mul_ne_zero hp hr),
    rootMultiplicity_mul (mul_ne_zero hq hr), Nat.add_sub_add_right, Nat.add_lt_add_iff_right,
    signRight_mul, hs]

/-- Cancelling a common nonzero factor of `p` and `q` does not change the index of `q / p`. -/
theorem cauchyIndex_mul_right (p q : R[X]) {r : R[X]} (hr : r ≠ 0) (s : Set R) :
    cauchyIndex (p * r) (q * r) s = cauchyIndex p q s := by
  simp only [cauchyIndex_def, cauchyJump_mul_right p q hr]

/-- Adding a multiple of `p` to `q` does not change the jumps of `q / p`. -/
theorem cauchyJump_add_mul (p q r : R[X]) (a : R) :
    cauchyJump p (q + p * r) a = cauchyJump p q a := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hq : q = 0
  · rw [hq, zero_add, cauchyJump_zero_right]
    exact cauchyJump_of_rootMultiplicity_le
      (by rw [rootMultiplicity_mul (mul_ne_zero hp hr)]; omega)
  rcases lt_or_ge (q.rootMultiplicity a) (p.rootMultiplicity a) with h | h
  · -- At a pole of `q / p`, the term `p * r` vanishes to higher order than `q`.
    have hd : (X - C a) ^ (q.rootMultiplicity a + 1) ∣ p * r :=
      (pow_dvd_pow _ h).trans ((pow_rootMultiplicity_dvd p a).mul_right r)
    rw [cauchyJump_def, cauchyJump_def, rootMultiplicity_add_eq_left_of_dvd hq hd, signRight_mul,
      signRight_mul, signRight_add_eq_left_of_dvd hq hd]
  · -- Away from poles of `q / p`, there is no pole of `(q + p * r) / p` either.
    rw [cauchyJump_of_rootMultiplicity_le h]
    by_cases hs : q + p * r = 0
    · simp [hs]
    refine cauchyJump_of_rootMultiplicity_le ((le_min h ?_).trans (rootMultiplicity_add a hs))
    rw [rootMultiplicity_mul (mul_ne_zero hp hr)]
    omega

/-- Adding a multiple of `p` to `q` does not change the index of `q / p`. -/
theorem cauchyIndex_add_mul (p q r : R[X]) (s : Set R) :
    cauchyIndex p (q + p * r) s = cauchyIndex p q s := by
  simp only [cauchyIndex_def, cauchyJump_add_mul]

/-- The jumps of `q / p` and of `p / q` at a point add up to half the jump of the one-sided
signs of `p * q` there. -/
theorem two_mul_cauchyJump_add_cauchyJump (p q : R[X]) (a : R) :
    2 * (cauchyJump p q a + cauchyJump q p a) =
      ((p * q).signRight a : ℤ) - (p * q).signLeft a := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  have hl : ((p * q).signLeft a : ℤ) =
      (-1) ^ (p.rootMultiplicity a + q.rootMultiplicity a) * (p * q).signRight a := by
    rw [signLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq)]
    simp
  rw [hl, cauchyJump_def, cauchyJump_def, mul_comm q p]
  generalize ((p * q).signRight a : ℤ) = s
  generalize p.rootMultiplicity a = m
  generalize q.rootMultiplicity a = n
  -- Only the side with the larger multiplicity can jump, and only at an odd difference,
  -- which has the parity of the multiplicity `m + n` of `p * q`.
  have key (hpar : Prop) [Decidable hpar] (h : hpar ↔ Odd (m + n)) :
      2 * (if hpar then s else 0) = s - (-1) ^ (m + n) * s := by
    rcases Nat.even_or_odd (m + n) with he | ho
    · simp [h, he.neg_one_pow, Nat.not_odd_iff_even.mpr he]
    · simp [h, ho.neg_one_pow, ho]
      ring
  rcases lt_trichotomy n m with h | rfl | h
  · simpa [h, not_lt_of_gt h] using key _ ((Nat.odd_sub h.le).trans Nat.odd_add.symm)
  · simp [← two_mul, pow_mul]
  · simpa [h, not_lt_of_gt h] using key _ ((Nat.odd_sub h.le).trans Nat.odd_add'.symm)

/-- At a root of a nonzero `p`, the jump of `p' * q / p` is the sign of `q`. -/
theorem cauchyJump_derivative_mul {p : R[X]} (hp : p ≠ 0) (q : R[X]) {a : R}
    (ha : p.eval a = 0) : cauchyJump p (derivative p * q) a = sign (q.eval a) := by
  have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
  have hd : derivative p ≠ 0 := by
    rw [Ne, derivative_eq_zero]
    intro h
    rw [eq_C_of_natDegree_eq_zero h, eval_C] at ha
    exact hp (by rw [eq_C_of_natDegree_eq_zero h, ha, C_0])
  by_cases hq : q.eval a = 0
  · rw [hq, sign_zero, SignType.coe_zero]
    by_cases hq0 : q = 0
    · simp [hq0]
    refine cauchyJump_of_rootMultiplicity_le ?_
    rw [rootMultiplicity_mul (mul_ne_zero hd hq0), derivative_rootMultiplicity_of_root ha]
    have := (rootMultiplicity_pos hq0).mpr hq
    omega
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  have hsd : (derivative p).signRight a = p.signRight a := by
    rw [signRight_def, signRight_def, derivative_rootMultiplicity_of_root ha,
      ← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
  have hsp : p.signRight a * p.signRight a = 1 := by
    have h0 : p.signRight a ≠ 0 := by simpa using hp
    generalize p.signRight a = u at *
    cases u <;> simp_all
  -- `a` is a simple pole of `p' * q / p`.
  have hpole : p.rootMultiplicity a - 1 < p.rootMultiplicity a ∧
      Odd (p.rootMultiplicity a - (p.rootMultiplicity a - 1)) :=
    ⟨Nat.sub_lt hm one_pos, by rw [Nat.sub_sub_self hm]; exact odd_one⟩
  rw [cauchyJump_def, rootMultiplicity_mul (mul_ne_zero hd hq0),
    derivative_rootMultiplicity_of_root ha, rootMultiplicity_eq_zero hq, add_zero]
  simp only [hpole, and_self, ite_true]
  rw [← mul_assoc, signRight_mul, signRight_mul, hsd, hsp, one_mul,
    signRight_eq_sign_eval q hq]

/-- The index of `p' * q / p` on `s` is the sum of the signs of `q` at the distinct roots of
`p` in `s`. -/
theorem cauchyIndex_derivative_mul (p q : R[X]) (s : Set R) [DecidablePred (· ∈ s)] :
    cauchyIndex p (derivative p * q) s =
      ∑ x ∈ p.roots.toFinset with x ∈ s, (sign (q.eval x) : ℤ) := by
  by_cases hp : p = 0
  · simp [hp]
  rw [cauchyIndex_eq_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx : p.eval x = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1)
  exact cauchyJump_derivative_mul hp q hx

/-- The whole-line index of `p' * q / p` is the Tarski query of `q` at the roots of `p`. -/
theorem cauchyIndex_derivative_mul_univ (p q : R[X]) :
    cauchyIndex p (derivative p * q) univ = tarskiQuery p q := by
  classical
  rw [cauchyIndex_derivative_mul, tarskiQuery_eq_sum]
  simp

/-- The index of `p' / p` on `s` is the number of distinct roots of `p` in `s`. -/
theorem cauchyIndex_derivative (p : R[X]) (s : Set R) [DecidablePred (· ∈ s)] :
    cauchyIndex p (derivative p) s = (p.roots.toFinset.filter (· ∈ s)).card := by
  simpa using cauchyIndex_derivative_mul p 1 s

end OrderedRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Reducing `q` modulo `p` does not change the jumps of `q / p`. -/
theorem cauchyJump_mod (p q : R[X]) (a : R) : cauchyJump p (q % p) a = cauchyJump p q a := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, sub_eq_add_neg, ← mul_neg, cauchyJump_add_mul]

/-- Reducing `q` modulo `p` does not change the index of `q / p`. -/
theorem cauchyIndex_mod (p q : R[X]) (s : Set R) : cauchyIndex p (q % p) s = cauchyIndex p q s := by
  simp only [cauchyIndex_def, cauchyJump_mod]

variable [IsRealClosed R]

/-- **The inversion formula.** On an interval whose endpoints are not roots of `p * q`, the
indices of `q / p` and `p / q` add up to half the change of sign of `p * q`. -/
theorem two_mul_cauchyIndex_add_cauchyIndex_Ioo {p q : R[X]} {a b : R} (hab : a < b)
    (ha : (p * q).eval a ≠ 0) (hb : (p * q).eval b ≠ 0) :
    2 * (cauchyIndex p q (Ioo a b) + cauchyIndex q p (Ioo a b)) =
      (sign ((p * q).eval b) : ℤ) - sign ((p * q).eval a) := by
  have hpq : p * q ≠ 0 := fun h => ha (by simp [h])
  rw [sign_eval_sub_sign_eval_eq_sum _ hab ha hb, cauchyIndex_def, cauchyIndex_def,
    ← finsum_mem_add_distrib' ((finite_support_cauchyJump p q).inter_of_right _)
      ((finite_support_cauchyJump q p).inter_of_right _), mul_finsum_mem]
  simp_rw [two_mul_cauchyJump_add_cauchyJump]
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext x
  simp only [mem_inter_iff, Finset.coe_filter, mem_ofPred_eq, Function.mem_support, mem_Ioo,
    Multiset.mem_toFinset, mem_roots hpq, IsRoot.def]
  refine ⟨fun h => ⟨⟨by_contra fun hx => h.2 ?_, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  rw [signRight_eq_sign_eval _ hx, signLeft_eq_sign_eval _ hx, sub_self]

/-- **The Euclidean recurrence for the Cauchy index.** On an interval whose endpoints are not
roots of `p * q`, the index of `q / p` is determined by the change of sign of `p * q` and the
index of `(p % q) / q`. -/
theorem two_mul_cauchyIndex_Ioo {p q : R[X]} {a b : R} (hab : a < b)
    (ha : (p * q).eval a ≠ 0) (hb : (p * q).eval b ≠ 0) :
    2 * cauchyIndex p q (Ioo a b) =
      (sign ((p * q).eval b) : ℤ) - sign ((p * q).eval a) -
        2 * cauchyIndex q (p % q) (Ioo a b) := by
  rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ioo hab ha hb]
  ring

end Field

end Polynomial
