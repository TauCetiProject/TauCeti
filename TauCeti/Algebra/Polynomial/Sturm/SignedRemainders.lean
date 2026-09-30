/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Local
public import TauCeti.Algebra.Polynomial.Sturm.Sequence

/-! # Positive-scaled signed remainder chains

The defining relations allow pseudo-remainder scaling. The terminal entry
may be nonconstant; no coprimality is imposed on the first two entries.

`Polynomial.sturmSeq` satisfies these relations. The relational formulation also
allows positive pseudo-remainder scalings without changing root sign sums.
-/

public section

namespace TauCeti.Sturm

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A positively scaled signed remainder identity. -/
def IsRemainder (p q r : Polynomial R) : Prop :=
  ∃ a b : R, ∃ u : Polynomial R, 0 < a ∧ 0 < b ∧ C a * p = u * q - C b * r

/-- The algebraic relations of a signed remainder chain, including its exact
termination. Degree descent is needed to construct such a chain, but not to
verify its signed root-sum identity. -/
structure IsSignedRemainderSeq (cs : List (Polynomial R)) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero : ∀ p ∈ cs, p ≠ 0
  /-- Successive triples satisfy a positively scaled signed remainder identity. -/
  relation : ∀ (i : ℕ) (p q r : Polynomial R), cs[i]? = some p →
    cs[i + 1]? = some q → cs[i + 2]? = some r → IsRemainder p q r
  /-- The final remainder vanishes, so the last entry divides its predecessor. -/
  terminal : ∀ pre p q, cs = pre ++ [p, q] → q ∣ p

namespace IsRemainder

omit [IsStrictOrderedRing R] in
/-- Construct the signed remainder relation from positive scalings and a polynomial identity. -/
theorem of_identity {p q r : Polynomial R} (a b : R) (u : Polynomial R)
    (ha : 0 < a) (hb : 0 < b) (heq : C a * p = u * q - C b * r) : IsRemainder p q r :=
  ⟨a, b, u, ha, hb, heq⟩

omit [IsStrictOrderedRing R] in
/-- A signed remainder relation supplies positive scalings and its polynomial identity. -/
theorem exists_identity {p q r : Polynomial R} (h : IsRemainder p q r) :
    ∃ a b : R, ∃ u : Polynomial R, 0 < a ∧ 0 < b ∧ C a * p = u * q - C b * r := h

omit [IsStrictOrderedRing R] in
/-- A common divisor of the two later entries divides the earlier entry. -/
theorem dvd {p q r d : Polynomial R} (h : IsRemainder p q r) (hq : d ∣ q) (hr : d ∣ r) :
    d ∣ p := by
  obtain ⟨a, b, u, ha, _, heq⟩ := h.exists_identity
  have hu : IsUnit (C a) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha.ne')
  apply hu.dvd_mul_left.mp
  rw [heq]
  exact dvd_sub (dvd_mul_of_dvd_right hq _) (dvd_mul_of_dvd_right hr _)

/-- At a zero of the middle entry, the neighbors have opposite signs,
provided the right neighbor does not vanish. -/
theorem alternate {p q r : Polynomial R} (h : IsRemainder p q r) {x : R}
    (hq : q.eval x = 0) (hr : r.eval x ≠ 0) :
    p.eval x * r.eval x < 0 := by
  obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
  have he := congrArg (Polynomial.eval x) heq
  simp only [eval_mul, eval_C, eval_sub, hq, mul_zero, zero_sub] at he
  rcases lt_or_gt_of_ne hr with hr | hr
  · have hp' : 0 < p.eval x := (mul_pos_iff_of_pos_left ha).mp (by
      rw [he]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hb hr))
    exact mul_neg_of_pos_of_neg hp' hr
  · have hn : a * p.eval x < 0 := by
      rw [he]; exact neg_neg_of_pos (mul_pos hb hr)
    have hp' : p.eval x < 0 := by
      by_contra! hp
      exact (mul_nonneg ha.le hp).not_gt hn
    exact mul_neg_of_neg_of_pos hp' hr

end IsRemainder

namespace IsSignedRemainderSeq

omit [IsStrictOrderedRing R] in
/-- A nonzero polynomial alone forms a signed remainder sequence. -/
theorem singleton {p : Polynomial R} (hp : p ≠ 0) : IsSignedRemainderSeq [p] where
  nonzero := by simpa
  relation i p0 p1 p2 h0 h1 h2 := by
    have hi : i + 2 < 1 := by
      simpa using (List.getElem?_eq_some_iff.mp h2).1
    omega
  terminal pre p0 p1 heq := by
    have := congrArg List.length heq
    simp only [List.length_cons, List.length_nil, List.length_append] at this
    omega

omit [IsStrictOrderedRing R] in
/-- A two-entry chain terminates when its second polynomial divides its first. -/
theorem pair {p q : Polynomial R} (hp : p ≠ 0) (hdvd : q ∣ p) :
    IsSignedRemainderSeq [p, q] where
  nonzero s hs := by
    have hq : q ≠ 0 := fun h => hp (zero_dvd_iff.mp (h ▸ hdvd))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hp
    · exact hq
  relation i p0 p1 p2 h0 h1 h2 := by
    have hi : i + 2 < 2 := by
      have := List.getElem?_eq_some_iff.mp h2
      simpa using this.1
    omega
  terminal pre p0 p1 heq := by
    have hlen : 2 = pre.length + 2 := by
      simpa only [List.length_cons, List.length_nil, List.length_append] using
        congrArg List.length heq
    have hpre : pre = [] := List.length_eq_zero_iff.mp (by omega)
    subst pre
    simp only [List.nil_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl, _⟩
    exact hdvd

omit [IsStrictOrderedRing R] in
/-- Prepend one signed recurrence to a chain. -/
theorem cons {p q r : Polynomial R} {cs : List (Polynomial R)}
    (hp : p ≠ 0) (hrel : IsRemainder p q r) (h : IsSignedRemainderSeq (q :: r :: cs)) :
    IsSignedRemainderSeq (p :: q :: r :: cs) where
  nonzero s hs := by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hp
    · exact h.nonzero s hs
  relation i p0 p1 p2 h0 h1 h2 := by
    cases i with
    | zero =>
      have he0 : p = p0 := by simpa using h0
      have he1 : q = p1 := by simpa using h1
      have he2 : r = p2 := by simpa using h2
      simpa [← he0, ← he1, ← he2] using hrel
    | succ i =>
      exact h.relation i p0 p1 p2 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  terminal pre p0 p1 heq := by
    cases pre with
    | nil => simp at heq
    | cons s pre =>
      have ht : q :: r :: cs = pre ++ [p0, p1] := (List.cons.inj heq).2
      exact h.terminal pre p0 p1 ht

omit [IsStrictOrderedRing R] in
theorem tail {p : Polynomial R} {cs : List (Polynomial R)} (h : IsSignedRemainderSeq (p :: cs)) :
    IsSignedRemainderSeq cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  relation i q0 q1 q2 h0 h1 h2 :=
    h.relation (i + 1) q0 q1 q2 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  terminal pre q r heq := h.terminal (p :: pre) q r (by simp [heq])

omit [IsStrictOrderedRing R] in
/-- The terminal polynomial divides every chain entry. -/
theorem last_dvd {cs : List (Polynomial R)} (h : IsSignedRemainderSeq cs) {d : Polynomial R}
    (hd : cs.getLast? = some d) : ∀ p ∈ cs, d ∣ p := by
  induction cs with
  | nil => simp at hd
  | cons p cs ih =>
    cases cs with
    | nil =>
      have hpd : p = d := by simpa using hd
      subst p
      simp
    | cons q cs =>
      have hd' : (q :: cs).getLast? = some d := by simpa using hd
      have ht := ih h.tail hd'
      have hdp : d ∣ p := by
        cases cs with
        | nil => exact dvd_trans (ht q (by simp)) (h.terminal [] p q rfl)
        | cons r cs =>
          exact (h.relation 0 p q r rfl rfl rfl).dvd
            (ht q (by simp)) (ht r (by simp))
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hdp
      · exact ht s hs

/-- A signed remainder chain with a root-free last entry is alternating. -/
theorem isAlternating {cs : List (Polynomial R)} (h : IsSignedRemainderSeq cs)
    (hlast : ∀ q, cs.getLast? = some q → ∀ x, q.eval x ≠ 0) : IsAlternating cs := by
  induction cs with
  | nil => exact ⟨h.nonzero, hlast, by simp⟩
  | cons p cs ih =>
    have ht : IsAlternating cs := ih h.tail (fun q hq x => by
      cases cs with
      | nil => simp at hq
      | cons s cs => exact hlast q (by simpa using hq) x)
    refine ⟨h.nonzero, hlast, ?_⟩
    intro i q0 q1 q2 h0 h1 h2 x hz
    cases i with
    | succ i =>
      exact ht.alternate i q0 q1 q2
        (by simpa using h0) (by simpa using h1) (by simpa using h2) x hz
    | zero =>
      have h0' : p = q0 := by simpa using h0
      subst q0
      cases cs with
      | nil => simp at h1
      | cons q cs =>
        have h1' : q = q1 := by simpa using h1
        subst q1
        cases cs with
        | nil => simp at h2
        | cons r cs =>
          have h2' : r = q2 := by simpa using h2
          subst q2
          exact (h.relation 0 p q r rfl rfl rfl).alternate hz (ht.second_eval_ne_zero hz)

end IsSignedRemainderSeq

/-- Mathlib's signed remainder sequence satisfies the algebraic chain conditions. -/
theorem IsSignedRemainderSeq.sturmSeq (p q : R[X]) : IsSignedRemainderSeq (sturmSeq p q) := by
  classical
  induction p, q using sturmSeq.induct
  next q =>
    rw [sturmSeq_zero_left]
    exact ⟨by simp, by simp, by simp⟩
  next p q hp ih =>
    by_cases hq : q = 0
    · subst q
      rw [sturmSeq_zero_right, ite_eq_right hp]
      exact IsSignedRemainderSeq.singleton hp
    rw [sturmSeq_cons hp, sturmSeq_cons hq]
    by_cases hr : -p % q = 0
    · rw [hr, sturmSeq_zero_left]
      exact IsSignedRemainderSeq.pair hp (dvd_neg.mp (EuclideanDomain.mod_eq_zero.mp hr))
    · rw [sturmSeq_cons hr]
      refine IsSignedRemainderSeq.cons hp ?_ ?_
      · refine IsRemainder.of_identity 1 1 (p / q) zero_lt_one zero_lt_one ?_
        rw [map_one, one_mul, one_mul, neg_mod, sub_neg_eq_add]
        exact (EuclideanDomain.mod_add_div p q).symm.trans (by ring)
      · rwa [sturmSeq_cons hq, sturmSeq_cons hr] at ih

omit [IsStrictOrderedRing R] in
/-- Cancel a nonzero common polynomial factor from a signed remainder identity. -/
theorem IsRemainder.cancel {d p q r : Polynomial R} (hd : d ≠ 0)
    (h : IsRemainder (d * p) (d * q) (d * r)) : IsRemainder p q r := by
  obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
  refine IsRemainder.of_identity a b u ha hb (mul_left_cancel₀ hd ?_)
  calc
    d * (C a * p) = C a * (d * p) := by ring
    _ = u * (d * q) - C b * (d * r) := heq
    _ = d * (u * q - C b * r) := by ring

namespace IsSignedRemainderSeq

omit [IsStrictOrderedRing R] in
/-- Dividing out a nonzero common factor preserves the signed chain conditions:
if `cs.map (d * ·)` is signed, so is `cs`. -/
theorem cancel {d : Polynomial R} {cs : List (Polynomial R)} (hd : d ≠ 0)
    (h : IsSignedRemainderSeq (cs.map (d * ·))) : IsSignedRemainderSeq cs where
  nonzero p hp hp0 := h.nonzero (d * p) (List.mem_map.mpr ⟨p, hp, rfl⟩) (by simp [hp0])
  relation i p q r h0 h1 h2 := IsRemainder.cancel hd (h.relation i (d * p) (d * q) (d * r)
    (by simp [List.getElem?_map, h0]) (by simp [List.getElem?_map, h1])
    (by simp [List.getElem?_map, h2]))
  terminal pre p q heq := (mul_dvd_mul_iff_left hd).mp
    (h.terminal (pre.map (d * ·)) (d * p) (d * q) (by simp [heq]))

/-- Divide every entry by the terminal common factor. The resulting chain is
alternating and ends at `1`, even when the original terminal factor is nonconstant. -/
theorem exists_isAlternating {cs : List (Polynomial R)} (h : IsSignedRemainderSeq cs)
    {d : Polynomial R}
    (hd : cs.getLast? = some d) :
    ∃ ds : List (Polynomial R), cs = ds.map (d * ·) ∧
      ds.getLast? = some 1 ∧ IsSignedRemainderSeq ds ∧ IsAlternating ds := by
  have hdm : d ∈ cs := List.mem_of_getLast? hd
  have hd0 : d ≠ 0 := h.nonzero d hdm
  let ds := cs.map (· / d)
  have hmap : cs = ds.map (d * ·) := by
    symm
    rw [List.map_map]
    conv_rhs => rw [← List.map_id cs]
    exact List.map_congr_left (fun p hp => EuclideanDomain.mul_div_cancel' hd0 (h.last_dvd hd p hp))
  have hlast : ds.getLast? = some 1 := by
    simp [ds, List.getLast?_map, hd, EuclideanDomain.div_self hd0]
  have hs : IsSignedRemainderSeq ds := cancel hd0 (hmap ▸ h)
  refine ⟨ds, hmap, hlast, hs, hs.isAlternating ?_⟩
  intro q hq x
  rw [hlast] at hq
  cases hq
  simp

end IsSignedRemainderSeq

end TauCeti.Sturm
