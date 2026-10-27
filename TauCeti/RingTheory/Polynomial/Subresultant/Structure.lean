/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Subresultant.Scaling

/-!
# The structure theorem for subresultants

Let `p` and `q` be polynomials over a field, with `q` of degree `n`, and let
`p, q, -(p % q), …` be their signed remainder sequence `Polynomial.sturmSeq p q`. The
subresultant polynomials of `p` and `q` are determined, up to nonzero scalars, by this sequence.
For consecutive entries `s` and `t` after the first:

* the subresultant at index `deg s - 1` is a nonzero multiple of `t`;
* the subresultant at index `deg t` is a nonzero multiple of `t`;
* the subresultants at the indices strictly between `deg t` and `deg s - 1` vanish.

The two indices coincide unless the degree drops by more than one from `s` to `t`; in that case
the indices between them form a *degree gap*. Together with the vanishing of all subresultants
below the degree of the last entry, which divides `p` and `q`
(`Polynomial.getLast?_sturmSeq_dvd` and
`Polynomial.subresultant_eq_zero_of_lt_natDegree_commonDivisor`), this determines every
subresultant polynomial of `p` and `q` at an index below `n`, up to nonzero scalars. The left
input is taken at a formal bound `m` dominating its degree, as in the rest of the subresultant
API, and the first two statements need `n ≤ m` only for the initial pair; the right input is
taken at its actual degree.

The structure theorem rests on one Euclidean step, which is available on its own. Below the
remainder bound, `Polynomial.subresultant_eq_C_mul_subresultant_mod` and its signed form
`Polynomial.subresultant_eq_C_mul_subresultant_neg_mod` express the subresultants of `(p, q)`
through those of `(q, -(p % q))`, with the explicit factor `± q.leadingCoeff ^ (m - r)`. From
the degree of `p % q` up to `n - 1`, `Polynomial.subresultant_eq_C_mul_mod` expresses them as
explicit multiples of `p % q` itself, and these multiples vanish strictly inside the degree gap.

## Main results

* `Polynomial.subresultant_eq_C_mul_subresultant_neg_mod`: the polynomial Euclidean recurrence.
* `Polynomial.subresultant_eq_C_mul_mod`, `Polynomial.subresultant_natDegree_sub_one`,
  `Polynomial.subresultant_eq_zero_of_degree_mod_lt`: the subresultants from the remainder
  degree up to `deg q - 1`.
* `Polynomial.exists_subresultant_eq_C_mul_subresultant_of_getElem?_sturmSeq`: the subresultants
  of `p` and `q` are nonzero multiples of those of any two consecutive later entries of the
  signed remainder sequence.
* `Polynomial.exists_subresultant_natDegree_sub_one_eq_C_mul_of_getElem?_sturmSeq`,
  `Polynomial.exists_subresultant_natDegree_eq_C_mul_of_getElem?_sturmSeq`,
  `Polynomial.subresultant_eq_zero_of_getElem?_sturmSeq`: the structure theorem.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 8 (the structure theorem for subresultants and signed remainder sequences).
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K]

/-! ### Along the signed remainder sequence -/

variable [DecidableEq K]

/-- The subresultants of `p` and `q` are nonzero multiples of those of any two consecutive
entries `a, b` of the signed remainder sequence after the first, each taken at its actual
degree, at every index below the degree of `b`. -/
theorem _root_.Polynomial.exists_subresultant_eq_C_mul_subresultant_of_getElem?_sturmSeq
    {p q a b : K[X]} {m i j : ℕ} (hp : p.natDegree ≤ m)
    (ha : (sturmSeq p q)[i + 1]? = some a) (hb : (sturmSeq p q)[i + 2]? = some b)
    (hj : j < b.natDegree) :
    ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree j =
      C c * subresultant a b a.natDegree b.natDegree j := by
  refine ⟨_, sturmSubresultantFactor_ne_zero ha m j, ?_⟩
  simpa using subresultant_eq_sturmSubresultantFactor_mul hp ha hb hj

/-- **Structure theorem for subresultants**, upper index. For consecutive entries `s, t` of the
signed remainder sequence of `p` and `q` after the first, the subresultant of `p` and `q` at
index `deg s - 1` is a nonzero multiple of `t`. Only the initial pair additionally requires
`q.natDegree ≤ m`. -/
theorem _root_.Polynomial.exists_subresultant_natDegree_sub_one_eq_C_mul_of_getElem?_sturmSeq
    {p q s t : K[X]} {m i : ℕ} (hp : p.natDegree ≤ m) (hq : i = 0 → q.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree (s.natDegree - 1) = C c * t := by
  obtain ⟨a, ha⟩ : ∃ a, (sturmSeq p q)[i]? = some a := by
    have hi := (List.getElem?_eq_some_iff.mp hs).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  refine ⟨_, neg_ne_zero.mpr (mul_ne_zero
    (sturmSubresultantFactor_ne_zero ha m (s.natDegree - 1))
    (pow_ne_zero _ (neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr
      (ne_zero_of_mem_sturmSeq (List.mem_of_getElem? hs)))))),
    subresultant_natDegree_sub_one_eq_sturmSubresultantFactor_mul hp hq ha hs ht⟩

/-- **Structure theorem for subresultants**, lower index. For consecutive entries `s, t` of the
signed remainder sequence of `p` and `q` after the first, the subresultant of `p` and `q` at
index `deg t` is a nonzero multiple of `t`. Only the initial pair additionally requires
`q.natDegree ≤ m`. -/
theorem _root_.Polynomial.exists_subresultant_natDegree_eq_C_mul_of_getElem?_sturmSeq
    {p q s t : K[X]} {m i : ℕ} (hp : p.natDegree ≤ m) (hq : i = 0 → q.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree t.natDegree = C c * t := by
  obtain ⟨a, ha⟩ : ∃ a, (sturmSeq p q)[i]? = some a := by
    have hi := (List.getElem?_eq_some_iff.mp hs).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  refine ⟨_, neg_ne_zero.mpr (mul_ne_zero
    (sturmSubresultantFactor_ne_zero ha m t.natDegree)
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr
        (ne_zero_of_mem_sturmSeq (List.mem_of_getElem? hs)))))
      (pow_ne_zero _ (neg_ne_zero.mpr (leadingCoeff_ne_zero.mpr
        (ne_zero_of_mem_sturmSeq (List.mem_of_getElem? ht))))))),
    subresultant_natDegree_eq_sturmSubresultantFactor_mul hp hq ha hs ht⟩

end TauCeti
