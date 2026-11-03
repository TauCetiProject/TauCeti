/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Basic

/-! # Inversion and Euclidean recurrence for Cauchy indices

The indices of `q / p` and `p / q` on a bounded interval add up to half the
change in the one-sided signs of `p * q`. This gives a Euclidean recurrence
without excluding poles or common roots at either endpoint.

An excluded endpoint uses the sign inside the interval; an included endpoint
uses the sign outside it. Thus the open interval uses the right-hand sign at
the left endpoint and the left-hand sign at the right endpoint. All four
bounded interval conventions are provided, including singleton closed intervals.
Zero polynomials and common factors are allowed throughout.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index and its inversion formula).
-/

public section

namespace TauCeti

open Polynomial Set SignType

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

private theorem inversion_of_eval_ne_zero {p q : R[X]} {a b : R} (hab : a < b)
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
  rw [derivSignRight_eq_sign_eval _ hx, derivSignLeft_eq_sign_eval _ hx, sub_self]

/-- **Inversion on an open interval.** The endpoint signs are taken inside the interval,
so poles and common roots at the endpoints need no special cases. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ioo (p q : R[X])
    {a b : R} (hab : a < b) :
    2 * (cauchyIndex p q (Ioo a b) + cauchyIndex q p (Ioo a b)) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignRight a := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  -- Move both endpoints inward to nonroots, preserving the indices and endpoint signs.
  obtain ⟨u, hau, hu⟩ := [p, q].exists_signs_right a
  obtain ⟨l, hlb, hl⟩ := [p, q].exists_signs_left b
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hau hab)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hlb (ha'.trans_le (min_le_right _ _)))
  have ha'u : a' ∈ Ioo a u := ⟨haa', ha'.trans_le (min_le_left _ _)⟩
  have hb'l : b' ∈ Ioo l b := ⟨(le_max_left _ _).trans_lt hb', hb'b⟩
  have hindex (r s : R[X]) (hr : r ∈ [p, q]) (hr0 : r ≠ 0) :
      cauchyIndex r s (Ioo a b) = cauchyIndex r s (Ioo a' b') := by
    rw [cauchyIndex_def, cauchyIndex_def]
    apply finsum_mem_inter_support_eq'
    intro x hx
    constructor
    · intro hxab
      have ha'x : a' < x := by
        by_contra h
        exact hx (cauchyJump_of_eval_ne_zero s
          (eval_ne_zero_of_sign_eq_derivSignRight hr0
            (hu r hr x ⟨hxab.1, (not_lt.mp h).trans_lt ha'u.2⟩)))
      have hxb' : x < b' := by
        by_contra h
        exact hx (cauchyJump_of_eval_ne_zero s
          (eval_ne_zero_of_sign_eq_derivSignLeft hr0
            (hl r hr x ⟨hb'l.1.trans_le (not_lt.mp h), hxab.2⟩)))
      exact ⟨ha'x, hxb'⟩
    · exact fun hx => ⟨haa'.trans hx.1, hx.2.trans hb'b⟩
  have hpa := hu p (by simp) a' ha'u
  have hqa := hu q (by simp) a' ha'u
  have hpb := hl p (by simp) b' hb'l
  have hqb := hl q (by simp) b' hb'l
  rw [hindex p q (by simp) hp, hindex q p (by simp) hq,
    inversion_of_eval_ne_zero ((le_max_right _ _).trans_lt hb')
      (by simpa using (mul_ne_zero (eval_ne_zero_of_sign_eq_derivSignRight hp hpa)
        (eval_ne_zero_of_sign_eq_derivSignRight hq hqa)))
      (by simpa using (mul_ne_zero (eval_ne_zero_of_sign_eq_derivSignLeft hp hpb)
        (eval_ne_zero_of_sign_eq_derivSignLeft hq hqb)))]
  simp only [eval_mul, sign_mul, hpa, hqa, hpb, hqb, derivSignLeft_mul, derivSignRight_mul]

/-- Inversion on a left-open, right-closed interval uses right-hand signs at both endpoints. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ioc (p q : R[X])
    {a b : R} (hab : a ≤ b) :
    2 * (cauchyIndex p q (Ioc a b) + cauchyIndex q p (Ioc a b)) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignRight a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hi (r s : R[X]) :
      cauchyIndex r s (Ioc a b) = cauchyIndex r s (Ioo a b) + cauchyJump r s b := by
    rw [← Ioo_insert_right hab, insert_eq, union_comm,
      cauchyIndex_union _ _ (disjoint_singleton_right.mpr (by simp)), cauchyIndex_singleton]
  have h := two_mul_cauchyIndex_add_cauchyIndex_Ioo p q hab
  have hj := two_mul_cauchyJump_add_cauchyJump p q b
  rw [hi, hi]
  linarith

/-- Inversion on a left-closed, right-open interval uses left-hand signs at both endpoints. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Ico (p q : R[X])
    {a b : R} (hab : a ≤ b) :
    2 * (cauchyIndex p q (Ico a b) + cauchyIndex q p (Ico a b)) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignLeft a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hi (r s : R[X]) :
      cauchyIndex r s (Ico a b) = cauchyJump r s a + cauchyIndex r s (Ioo a b) := by
    rw [← Ioo_insert_left hab, insert_eq,
      cauchyIndex_union _ _ (disjoint_singleton_left.mpr (by simp)), cauchyIndex_singleton]
  have h := two_mul_cauchyIndex_add_cauchyIndex_Ioo p q hab
  have hj := two_mul_cauchyJump_add_cauchyJump p q a
  rw [hi, hi]
  linarith

/-- Inversion on a closed interval uses the signs outside it, including when it is a singleton. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_add_cauchyIndex_Icc (p q : R[X])
    {a b : R} (hab : a ≤ b) :
    2 * (cauchyIndex p q (Icc a b) + cauchyIndex q p (Icc a b)) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignLeft a := by
  have hi (r s : R[X]) :
      cauchyIndex r s (Icc a b) = cauchyJump r s a + cauchyIndex r s (Ioc a b) := by
    rw [← Ioc_insert_left hab, insert_eq,
      cauchyIndex_union _ _ (disjoint_singleton_left.mpr (by simp)), cauchyIndex_singleton]
  have h := two_mul_cauchyIndex_add_cauchyIndex_Ioc p q hab
  have hj := two_mul_cauchyJump_add_cauchyJump p q a
  rw [hi, hi]
  linarith

/-- **Euclidean recurrence on an open interval**, allowing arbitrary endpoint roots. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Ioo (p q : R[X]) {a b : R} (hab : a < b) :
    2 * cauchyIndex p q (Ioo a b) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignRight a -
        2 * cauchyIndex q (p % q) (Ioo a b) := by
  rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ioo p q hab]
  ring

/-- Euclidean recurrence on a left-open, right-closed interval. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Ioc (p q : R[X]) {a b : R} (hab : a ≤ b) :
    2 * cauchyIndex p q (Ioc a b) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignRight a -
        2 * cauchyIndex q (p % q) (Ioc a b) := by
  rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ioc p q hab]
  ring

/-- Euclidean recurrence on a left-closed, right-open interval. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Ico (p q : R[X]) {a b : R} (hab : a ≤ b) :
    2 * cauchyIndex p q (Ico a b) =
      ((p * q).derivSignLeft b : ℤ) - (p * q).derivSignLeft a -
        2 * cauchyIndex q (p % q) (Ico a b) := by
  rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Ico p q hab]
  ring

/-- Euclidean recurrence on a closed interval, including singleton intervals. -/
theorem _root_.Polynomial.two_mul_cauchyIndex_Icc (p q : R[X]) {a b : R} (hab : a ≤ b) :
    2 * cauchyIndex p q (Icc a b) =
      ((p * q).derivSignRight b : ℤ) - (p * q).derivSignLeft a -
        2 * cauchyIndex q (p % q) (Icc a b) := by
  rw [cauchyIndex_mod, ← two_mul_cauchyIndex_add_cauchyIndex_Icc p q hab]
  ring

end TauCeti
