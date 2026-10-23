/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Sequence
public import TauCeti.RingTheory.Polynomial.Subresultant.DegreeDrop.Polynomial
public import TauCeti.RingTheory.Polynomial.Subresultant.Euclidean

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
API, and the first two statements also need `n ≤ m`; the right input is taken at its actual
degree.

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

/-! ### One Euclidean step -/

/-- A Euclidean step for subresultant polynomials. Below the remainder bound `r`, the
subresultant of `(p, q)` is that of `(q, p % q)` times `± q.leadingCoeff ^ (m - r)`. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_subresultant_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hj : j < min r q.natDegree) :
    subresultant p q m q.natDegree j =
      C ((-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) *
        subresultant q (p % q) q.natDegree r j := by
  rw [← subresultant_mod_left hp,
    subresultant_eq_C_sign_mul_coeff_pow_mul_of_left_degree_drop hr le_rfl hrm hj,
    subresultant_comm (p % q) q r q.natDegree j, coeff_natDegree, ← mul_assoc, ← C_mul]
  congr 2
  have hmj : m - j = (m - r) + (r - j) := by omega
  rw [hmj, add_mul, pow_add]
  ring

/-- The Euclidean step for the signed remainder `-(p % q)`, the next entry of the signed
remainder sequence. Negating the remainder adds the sign of its `q.natDegree - j` columns. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_subresultant_neg_mod {p q : K[X]} {m r j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ r) (hrm : r ≤ m)
    (hj : j < min r q.natDegree) :
    subresultant p q m q.natDegree j =
      C ((-1) ^ ((m - j + 1) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) *
        subresultant q (-(p % q)) q.natDegree r j := by
  have hneg : -(p % q) = C (-1) * (p % q) := by simp
  have hsq : ((-1 : K) ^ (q.natDegree - j)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hneg, subresultant_C_mul_right, subresultant_eq_C_mul_subresultant_mod hp hr hrm hj,
    ← mul_assoc, ← C_mul, add_mul, one_mul, pow_add]
  congr 2
  linear_combination -((-1 : K) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - r)) * hsq

/-! ### The degree gap -/

/-- From the degree of the remainder up to `q.natDegree - 1`, the subresultant of `(p, q)` is an
explicit multiple of the remainder `p % q`. -/
theorem _root_.Polynomial.subresultant_eq_C_mul_mod {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).natDegree ≤ j) (hjq : j < q.natDegree)
    (hjm : j < m) :
    subresultant p q m q.natDegree j =
      C ((-1) ^ ((m - j) * (q.natDegree - j)) * q.leadingCoeff ^ (m - j) *
        (p % q).coeff j ^ (q.natDegree - j - 1)) * (p % q) := by
  rw [← subresultant_mod_left hp, subresultant_left_bound_of_degree_drop hr le_rfl hjq hjm,
    coeff_natDegree]

/-- The subresultant at index `q.natDegree - 1` is `(-q.leadingCoeff) ^ (m + 1 - q.natDegree)`
times the remainder `p % q`. -/
theorem _root_.Polynomial.subresultant_natDegree_sub_one {p q : K[X]} {m : ℕ}
    (hp : p.natDegree ≤ m) (hq : 0 < q.natDegree) (hqm : q.natDegree ≤ m) :
    subresultant p q m q.natDegree (q.natDegree - 1) =
      C ((-q.leadingCoeff) ^ (m + 1 - q.natDegree)) * (p % q) := by
  have hm : m - (q.natDegree - 1) = m + 1 - q.natDegree := by omega
  have hq1 : q.natDegree - (q.natDegree - 1) = 1 := by omega
  rw [subresultant_eq_C_mul_mod hp (Nat.le_sub_one_of_lt (natDegree_mod_lt p hq.ne')) (by omega)
    (by omega), hm, hq1, Nat.sub_self, pow_zero, mul_one, mul_one, neg_pow q.leadingCoeff]

/-- Strictly inside the degree gap, between the degree of the remainder and
`q.natDegree - 1`, the subresultants of `(p, q)` vanish. This includes every index below
`q.natDegree - 1` when `q` divides `p`. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_degree_mod_lt {p q : K[X]} {m j : ℕ}
    (hp : p.natDegree ≤ m) (hr : (p % q).degree < j) (hjq : j + 1 < q.natDegree) :
    subresultant p q m q.natDegree j = 0 := by
  by_cases hjm : j < m
  · rw [subresultant_eq_C_mul_mod hp (natDegree_le_of_degree_le hr.le) (by omega) hjm,
      coeff_eq_zero_of_degree_lt hr, zero_pow (by omega), mul_zero, C_0, zero_mul]
  · exact subresultant_eq_zero_of_min_le _ _ _ _ _ (by omega)

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
  induction p, q using sturmSeq.induct generalizing m i j a b with
  | case1 q => simp at ha
  | case2 p q hp0 ih =>
    rw [sturmSeq_cons hp0] at ha hb
    simp only [List.getElem?_cons_succ] at ha hb
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at ha
    have hr0 : -p % q ≠ 0 := by
      rintro hr
      simp [sturmSeq_cons hq0, hr] at hb
    have hmod : -p % q = -(p % q) := neg_mod
    have hr : (p % q).natDegree < q.natDegree := by
      rw [← natDegree_neg, ← hmod]
      exact natDegree_lt_natDegree hr0 (degree_mod_lt _ hq0)
    have hrm : (p % q).natDegree ≤ m := by
      rw [mod_def]
      exact natDegree_modByMonic_le_left.trans hp
    -- The first Euclidean step, from `(p, q)` to `(q, -p % q)`.
    have hstep (j : ℕ) (hj : j < (-p % q).natDegree) :
        ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree j =
          C c * subresultant q (-p % q) q.natDegree (-p % q).natDegree j := by
      rw [hmod, natDegree_neg] at hj ⊢
      exact ⟨_, mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hq0)),
        subresultant_eq_C_mul_subresultant_neg_mod hp le_rfl hrm (by omega)⟩
    rcases i with _ | i
    · simp only [sturmSeq_cons hq0, List.getElem?_cons_zero, Option.some.injEq] at ha
      simp only [sturmSeq_cons hq0, sturmSeq_cons hr0, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.some.injEq] at hb
      subst ha hb
      exact hstep j hj
    · -- Later pairs: compose the first step with the statement for `(q, -p % q)`.
      have hle : b.natDegree ≤ (-p % q).natDegree := by
        have hb' := hb
        rw [sturmSeq_cons hq0] at hb'
        simp only [List.getElem?_cons_succ] at hb'
        exact natDegree_le_of_mem_sturmSeq (List.mem_of_getElem? hb')
          (natDegree_le_natDegree (degree_mod_lt _ hr0).le)
      obtain ⟨c₁, hc₁, h₁⟩ := hstep j (by omega)
      obtain ⟨c₂, hc₂, h₂⟩ := ih (m := q.natDegree) le_rfl ha hb hj
      exact ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, by rw [h₁, h₂, ← mul_assoc, ← C_mul]⟩

/-- For consecutive entries `s, t` of the signed remainder sequence after the first, the
subresultants of `p` and `q` below `deg s` are nonzero multiples of those of `(a, s)` for an
entry `a` with `t = -(a % s)`, at a formal bound `M` for `a`. For the second entry `s = q` this
is `(p, q)` itself, and `M = m` bounds `deg s` only if `q.natDegree ≤ m`. -/
private theorem exists_subresultant_eq_C_mul_subresultant_pred {p q s t : K[X]} {m i : ℕ}
    (hp : p.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    ∃ (a : K[X]) (M : ℕ), a.natDegree ≤ M ∧ (q.natDegree ≤ m → s.natDegree ≤ M) ∧
      t = -(a % s) ∧
      ∀ j < s.natDegree, ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree j =
        C c * subresultant a s M s.natDegree j := by
  rcases i with _ | i
  · have hp0 : p ≠ 0 := by
      rintro rfl
      simp at hs
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp [sturmSeq_cons hp0] at hs
    have hs' : s = q := by
      simpa [sturmSeq_cons hp0, sturmSeq_cons hq0, eq_comm] using hs
    subst hs'
    refine ⟨p, m, hp, id, ?_, fun j _ ↦ ⟨1, one_ne_zero, by simp⟩⟩
    rw [eq_neg_mod_of_getElem?_sturmSeq (a := p) (by simp [sturmSeq_cons hp0]) hs ht, neg_mod]
  · obtain ⟨a, ha⟩ : ∃ a, (sturmSeq p q)[i + 1]? = some a := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hs
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨a, a.natDegree, le_rfl, fun _ ↦ (natDegree_lt_of_getElem?_sturmSeq ha hs).le, ?_,
      fun j hj ↦ exists_subresultant_eq_C_mul_subresultant_of_getElem?_sturmSeq hp ha hs hj⟩
    rw [eq_neg_mod_of_getElem?_sturmSeq ha hs ht, neg_mod]

/-- **Structure theorem for subresultants**, upper index. For consecutive entries `s, t` of the
signed remainder sequence of `p` and `q` after the first, the subresultant of `p` and `q` at
index `deg s - 1` is a nonzero multiple of `t`. -/
theorem _root_.Polynomial.exists_subresultant_natDegree_sub_one_eq_C_mul_of_getElem?_sturmSeq
    {p q s t : K[X]} {m i : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree (s.natDegree - 1) = C c * t := by
  have hts := natDegree_lt_of_getElem?_sturmSeq hs ht
  obtain ⟨a, M, haM, hsM, rfl, h⟩ := exists_subresultant_eq_C_mul_subresultant_pred hp hs ht
  replace hsM := hsM hq
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hts
  obtain ⟨c, hc, hS⟩ := h (s.natDegree - 1) (by omega)
  refine ⟨-(c * (-s.leadingCoeff) ^ (M + 1 - s.natDegree)),
    neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero _ (neg_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr hs0)))), ?_⟩
  rw [hS, subresultant_natDegree_sub_one haM (by omega) hsM, ← mul_assoc, ← C_mul]
  simp

/-- **Structure theorem for subresultants**, lower index. For consecutive entries `s, t` of the
signed remainder sequence of `p` and `q` after the first, the subresultant of `p` and `q` at
index `deg t` is a nonzero multiple of `t`. -/
theorem _root_.Polynomial.exists_subresultant_natDegree_eq_C_mul_of_getElem?_sturmSeq
    {p q s t : K[X]} {m i : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    ∃ c : K, c ≠ 0 ∧ subresultant p q m q.natDegree t.natDegree = C c * t := by
  have hts := natDegree_lt_of_getElem?_sturmSeq hs ht
  have ht0 : t ≠ 0 := ne_zero_of_mem_sturmSeq (List.mem_of_getElem? ht)
  obtain ⟨a, M, haM, hsM, rfl, h⟩ := exists_subresultant_eq_C_mul_subresultant_pred hp hs ht
  replace hsM := hsM hq
  rw [natDegree_neg] at hts ⊢
  have hr0 : a % s ≠ 0 := neg_ne_zero.mp ht0
  obtain ⟨c, hc, hS⟩ := h (a % s).natDegree hts
  refine ⟨-(c * ((-1) ^ ((M - (a % s).natDegree) * (s.natDegree - (a % s).natDegree)) *
      s.leadingCoeff ^ (M - (a % s).natDegree) *
      (a % s).leadingCoeff ^ (s.natDegree - (a % s).natDegree - 1))),
    neg_ne_zero.mpr (mul_ne_zero hc (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (leadingCoeff_ne_zero.mpr ?_)))
      (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hr0)))), ?_⟩
  · rintro rfl
    simp at hts
  rw [hS, subresultant_eq_C_mul_mod haM le_rfl hts (by omega), coeff_natDegree, ← mul_assoc,
    ← C_mul]
  simp

/-- **Structure theorem for subresultants**, degree gap. For consecutive entries `s, t` of the
signed remainder sequence of `p` and `q` after the first, the subresultants of `p` and `q` at
the indices strictly between `deg t` and `deg s - 1` vanish. -/
theorem _root_.Polynomial.subresultant_eq_zero_of_getElem?_sturmSeq
    {p q s t : K[X]} {m i j : ℕ} (hp : p.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t)
    (htj : t.natDegree < j) (hjs : j + 1 < s.natDegree) :
    subresultant p q m q.natDegree j = 0 := by
  obtain ⟨a, M, haM, -, rfl, h⟩ := exists_subresultant_eq_C_mul_subresultant_pred hp hs ht
  rw [natDegree_neg] at htj
  obtain ⟨c, -, hS⟩ := h j (by omega)
  rw [hS, subresultant_eq_zero_of_degree_mod_lt haM
    ((degree_le_natDegree).trans_lt (by exact_mod_cast htj)) hjs, mul_zero]

end TauCeti
