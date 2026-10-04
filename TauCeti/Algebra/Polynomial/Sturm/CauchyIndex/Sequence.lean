/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Basic
public import TauCeti.Algebra.Polynomial.Sturm.Infinity
import TauCeti.Algebra.Polynomial.Sturm.Variation
import TauCeti.Data.SignType.Parity

/-! # Computing Cauchy indices by Sturm sequences

The Cauchy index of an arbitrary quotient `q / p` is the difference of the
sign variations of `Polynomial.sturmSeq p q` at the two endpoints. On the
whole line these variations depend only on leading coefficients and degree
parities. The numerator need not be a multiple of the derivative of the
denominator, and common factors and multiple roots are allowed.

This connects signed Euclidean remainder sequences to Cauchy indices, so
coefficient formulas for the sequences can compute indices and Tarski queries.
In particular, one Euclidean step changes the whole-line index of `q / p` only
by the contribution of the leading coefficients of `p` and `q`
(`Polynomial.cauchyIndex_univ_eq_add_cauchyIndex_neg_mod`).

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index and signed remainder sequences).
The sequence used here is Mathlib's `Polynomial.sturmSeq`, by Tomaz Mascarenhas,
Pedro Saccomani, and Sarah Pereira.
-/

public section

namespace TauCeti

open Polynomial Set SignType Sturm

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The Cauchy index of `q / p` between endpoints where every entry of its
Sturm sequence is nonzero is the drop in evaluated sign variations. -/
private theorem cauchyIndex_Ioo_aux (p q : R[X]) {a b : R} (hab : a < b)
    (ha : ∀ r ∈ sturmSeq p q, r.eval a ≠ 0)
    (hb : ∀ r ∈ sturmSeq p q, r.eval b ≠ 0) :
    cauchyIndex p q (Ioo a b) =
      (signVariationsAt (sturmSeq p q) a : ℤ) - signVariationsAt (sturmSeq p q) b := by
  classical
  induction p, q using sturmSeq.induct with
  | case1 q => simp
  | case2 p q hp ih =>
    by_cases hq : q = 0
    · simp [hq, hp]
    have hat : ∀ r ∈ sturmSeq q (-p % q), r.eval a ≠ 0 := by
      intro r hr
      exact ha r (by rw [sturmSeq_cons hp]; simp [hr])
    have hbt : ∀ r ∈ sturmSeq q (-p % q), r.eval b ≠ 0 := by
      intro r hr
      exact hb r (by rw [sturmSeq_cons hp]; simp [hr])
    have hpa := ha p (mem_sturmSeq_self hp)
    have hpb := hb p (mem_sturmSeq_self hp)
    have hqa := hat q (mem_sturmSeq_self hq)
    have hqb := hbt q (mem_sturmSeq_self hq)
    have hrec := two_mul_cauchyIndex_Ioo hab
      (by simpa using mul_ne_zero hpa hqa) (by simpa using mul_ne_zero hpb hqb)
    have ht := ih hat hbt
    rw [neg_mod, cauchyIndex_neg_right] at ht
    rw [signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero hpa hqa,
      signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero hpb hqb]
    have hs :
        2 * ((if sign (p.eval a) = sign (q.eval a) then 0 else 1 : ℤ) -
          (if sign (p.eval b) = sign (q.eval b) then 0 else 1 : ℤ)) =
        (sign ((p * q).eval b) : ℤ) - sign ((p * q).eval a) := by
      simp only [eval_mul, sign_mul, SignType.coe_mul]
      have step (s t : SignType) (hs : s ≠ 0) (ht : t ≠ 0) :
          2 * (if s = t then 0 else 1 : ℤ) = 1 - (s : ℤ) * t := by
        cases s <;> cases t <;> simp_all
      rw [mul_sub, step _ _ (sign_ne_zero.mpr hpa) (sign_ne_zero.mpr hqa),
        step _ _ (sign_ne_zero.mpr hpb) (sign_ne_zero.mpr hqb)]
      ring
    simp only [neg_mod]
    push_cast
    linarith only [hrec, ht, hs]

/-- On an arbitrary open interval, the Cauchy index is the right-hand variation
at the left endpoint minus the left-hand variation at the right endpoint.
Either endpoint may be a pole or a common root. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_Ioo (p q : R[X]) {a b : R}
    (hab : a < b) :
    cauchyIndex p q (Ioo a b) =
      (signVariationsRight (sturmSeq p q) a : ℤ) - signVariationsLeft (sturmSeq p q) b := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  let cs := sturmSeq p q
  have hnonzero : ∀ r ∈ cs, r ≠ 0 := fun _ hr => ne_zero_of_mem_sturmSeq hr
  obtain ⟨u, hau, hu⟩ := cs.exists_signs_right a
  obtain ⟨l, hlb, hl⟩ := cs.exists_signs_left b
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hau hab)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hlb (ha'.trans_le (min_le_right _ _)))
  have ha'u : a' ∈ Ioo a u := ⟨haa', ha'.trans_le (min_le_left _ _)⟩
  have hb'l : b' ∈ Ioo l b := ⟨(le_max_left _ _).trans_lt hb', hb'b⟩
  have hpu (x : R) (hx : x ∈ Ioo a u) : p.eval x ≠ 0 :=
    eval_ne_zero_of_sign_eq_signRight hp (hu p (mem_sturmSeq_self hp) x hx)
  have hpl (x : R) (hx : x ∈ Ioo l b) : p.eval x ≠ 0 :=
    eval_ne_zero_of_sign_eq_signLeft hp (hl p (mem_sturmSeq_self hp) x hx)
  have hindex : cauchyIndex p q (Ioo a b) = cauchyIndex p q (Ioo a' b') := by
    rw [cauchyIndex_eq_sum, cauchyIndex_eq_sum]
    symm
    apply Finset.sum_subset
    · intro r hr
      simp only [Finset.mem_filter, mem_Ioo] at hr ⊢
      exact ⟨hr.1, haa'.trans hr.2.1, hr.2.2.trans hb'b⟩
    · intro r hr hr'
      have hrab := (Finset.mem_filter.mp hr).2
      have hrout : ¬ (a' < r ∧ r < b') := by
        simpa only [Finset.mem_filter, (Finset.mem_filter.mp hr).1, mem_Ioo, true_and] using hr'
      apply cauchyJump_of_eval_ne_zero
      rcases le_or_gt r a' with hra' | ha'r
      · exact hpu r ⟨hrab.1, hra'.trans_lt ha'u.2⟩
      · exact hpl r ⟨hb'l.1.trans_le (not_lt.mp fun hrb' => hrout ⟨ha'r, hrb'⟩), hrab.2⟩
  rw [hindex, cauchyIndex_Ioo_aux p q ((le_max_right _ _).trans_lt hb')
    (fun r hr => eval_ne_zero_of_sign_eq_signRight (hnonzero r hr) (hu r hr a' ha'u))
    (fun r hr => eval_ne_zero_of_sign_eq_signLeft (hnonzero r hr) (hl r hr b' hb'l)),
    signVariationsAt_eq_right (fun r hr => hu r hr a' ha'u),
    signVariationsAt_eq_left (fun r hr => hl r hr b' hb'l)]

/-- The Cauchy index of `q / p` on the whole ordered real closed field is
computed by the degree-parity and leading-coefficient variations of its Sturm
sequence. No squarefreeness or coprimality assumption is needed. For a zero
denominator both sides are zero by convention. -/
theorem _root_.Polynomial.cauchyIndex_eq_sub_signVariations_univ (p q : R[X]) :
    cauchyIndex p q univ =
      (signVariationsAtBot (sturmSeq p q) : ℤ) - signVariationsAtTop (sturmSeq p q) := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨A, hA, hRA⟩ := exists_atBot (sturmSeq p q)
    (fun _ hr => ne_zero_of_mem_sturmSeq hr)
  obtain ⟨B, hB, hRB⟩ := exists_atTop (sturmSeq p q)
    (fun _ hr => ne_zero_of_mem_sturmSeq hr)
  let a := min A B - 1
  let b := max A B + 1
  have haA : a < A := (sub_one_lt _).trans_le (min_le_left _ _)
  have hBb : B < b := (le_max_right _ _).trans_lt (lt_add_one _)
  have hab : a < b := (haA.trans_le (le_max_left _ _)).trans (lt_add_one _)
  have hroots : ∀ r ∈ p.roots.toFinset, a < r ∧ r < b := by
    intro r hr
    have hr0 := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    exact ⟨haA.trans_le (hRA p (mem_sturmSeq_self hp) r hr0),
      (hRB p (mem_sturmSeq_self hp) r hr0).trans_lt hBb⟩
  have hindex : cauchyIndex p q univ = cauchyIndex p q (Ioo a b) := by
    simp only [cauchyIndex_eq_sum, mem_univ, Finset.filter_true, mem_Ioo,
      Finset.filter_true_of_mem hroots]
  rw [hindex, cauchyIndex_Ioo_aux p q hab
    (fun r hr hz => (hRA r hr a hz).not_gt haA)
    (fun r hr hz => (hRB r hr b hz).not_gt hBb), hA a haA, hB b hBb]

/-- The Euclidean recurrence for the whole-line Cauchy index. Passing from `q / p` to
`-(p % q) / q` changes the index by `sign p.leadingCoeff * sign q.leadingCoeff` when the degrees
of `p` and `q` have opposite parities, and leaves it unchanged otherwise. -/
theorem _root_.Polynomial.cauchyIndex_univ_eq_add_cauchyIndex_neg_mod {p q : R[X]} (hp : p ≠ 0)
    (hq : q ≠ 0) :
    cauchyIndex p q univ =
      (if Odd (p.natDegree + q.natDegree) then
        (sign p.leadingCoeff : ℤ) * sign q.leadingCoeff else 0) +
        cauchyIndex q (-(p % q)) univ := by
  classical
  have hp' : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  rw [cauchyIndex_eq_sub_signVariations_univ, cauchyIndex_eq_sub_signVariations_univ,
    sturmSeq_cons hp, neg_mod, sturmSeq_cons hq]
  simp only [signVariationsAtTop_def, signVariationsAtBot_def, List.map_cons]
  rw [List.signVariations_cons_cons_of_ne_zero _ (by simpa using hp') (by simpa using hq'),
    List.signVariations_cons_cons_of_ne_zero _ hp' hq']
  simp only [sign_mul, sign_pow, Left.sign_neg, sign_one]
  rw [← SignType.ite_mul_neg_one_pow_sub_ite _ _ (sign_ne_zero.mpr hp') (sign_ne_zero.mpr hq')]
  push_cast
  ring

end TauCeti
