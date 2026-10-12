/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Filter
public import TauCeti.Algebra.Polynomial.Eval.OneSided
public import TauCeti.Algebra.Polynomial.Sturm.Tarski

/-! # Sturm–Tarski with one-sided endpoints

`TauCeti.Sturm.signVariationsRight cs a` and `TauCeti.Sturm.signVariationsLeft cs a` count the
sign variations of a polynomial list immediately to the right and to the left of `a`. They are
computed algebraically from the one-sided signs `Polynomial.signRight` and
`Polynomial.signLeft`, and are realized by evaluation at every point of a small enough interval
on the corresponding side of `a`.

With these, Sturm–Tarski holds on every bounded interval, with no condition on the endpoints.
Write `V(a⁺)` and `V(b⁻)` for the right-hand variations at `a` and the left-hand variations at
`b` of a signed remainder chain whose head is `p` and whose second entry is the seed of the
query `f`. For `a < b`, the difference `V(a⁺) - V(b⁻)` is the sum of the signs of `f` at the
distinct roots of `p` in `(a, b)`, even when `a` or `b` is a root of `p` or of another chain
entry. A root `c` of `p` contributes the sign of `f` at `c` to a closed endpoint, and this
contribution is the drop `V(c⁻) - V(c⁺)` in variations across `c`. The formulas for
`(a, b]`, `[a, b)` and `[a, b]` add these endpoint contributions explicitly to `V(a⁺) - V(b⁻)`.
Specializing to `Polynomial.sturmSeq` and to the query `1` counts distinct roots.

## Main declarations

* `TauCeti.Sturm.signVariationsRight`, `TauCeti.Sturm.signVariationsLeft`: one-sided
  variations.
* `TauCeti.Sturm.sum_sign_Ioo`: Sturm–Tarski on `(a, b)` as `V(a⁺) - V(b⁻)`.
* `TauCeti.Sturm.signVariationsLeft_sub_signVariationsRight`: the contribution of a point.
* `TauCeti.Sturm.sum_sign_Ioc`, `TauCeti.Sturm.sum_sign_Ico`, `TauCeti.Sturm.sum_sign_Icc`:
  Sturm–Tarski on half-open and closed intervals.
* `TauCeti.Sturm.card_roots_toFinset_Ioo` and its half-open and closed analogues: Sturm's
  count of distinct roots.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (Tarski's theorem) and Chapter 10.
-/

public section

namespace TauCeti.Sturm

open Polynomial Set SignType

section Basic

variable {R : Type*} [CommRing R] [LinearOrder R]

/-- The sign variations of a polynomial list immediately to the right of `a`: the variations
of the right-hand signs `Polynomial.signRight` of its entries at `a`. -/
noncomputable def signVariationsRight (cs : List R[X]) (a : R) : ℕ :=
  List.signVariations (cs.map (·.signRight a))

/-- The sign variations of a polynomial list immediately to the left of `a`: the variations
of the left-hand signs `Polynomial.signLeft` of its entries at `a`. -/
noncomputable def signVariationsLeft (cs : List R[X]) (a : R) : ℕ :=
  List.signVariations (cs.map (·.signLeft a))

theorem signVariationsRight_def (cs : List R[X]) (a : R) :
    signVariationsRight cs a = List.signVariations (cs.map (·.signRight a)) := (rfl)

theorem signVariationsLeft_def (cs : List R[X]) (a : R) :
    signVariationsLeft cs a = List.signVariations (cs.map (·.signLeft a)) := (rfl)

@[simp, grind =]
theorem signVariationsRight_nil (a : R) : signVariationsRight ([] : List R[X]) a = 0 := by
  simp [signVariationsRight_def]

@[simp, grind =]
theorem signVariationsLeft_nil (a : R) : signVariationsLeft ([] : List R[X]) a = 0 := by
  simp [signVariationsLeft_def]

@[simp, grind =]
theorem signVariationsRight_singleton (p : R[X]) (a : R) : signVariationsRight [p] a = 0 := by
  simp [signVariationsRight_def]

@[simp, grind =]
theorem signVariationsLeft_singleton (p : R[X]) (a : R) : signVariationsLeft [p] a = 0 := by
  simp [signVariationsLeft_def]

/-- Evaluation at a point where every entry has its right-hand sign at `a` realizes the
right-hand variations at `a`. -/
theorem signVariationsAt_eq_right {cs : List R[X]} {a x : R}
    (h : ∀ p ∈ cs, sign (p.eval x) = p.signRight a) :
    signVariationsAt cs x = signVariationsRight cs a := by
  rw [signVariationsAt_def, signVariationsRight_def,
    ← List.signVariations_map_sign (cs.map (eval x)), List.map_map]
  exact congrArg _ (List.map_congr_left h)

/-- Evaluation at a point where every entry has its left-hand sign at `a` realizes the
left-hand variations at `a`. -/
theorem signVariationsAt_eq_left {cs : List R[X]} {a x : R}
    (h : ∀ p ∈ cs, sign (p.eval x) = p.signLeft a) :
    signVariationsAt cs x = signVariationsLeft cs a := by
  rw [signVariationsAt_def, signVariationsLeft_def,
    ← List.signVariations_map_sign (cs.map (eval x)), List.map_map]
  exact congrArg _ (List.map_congr_left h)

/-- If no entry vanishes at `a`, the right-hand variations are the variations at `a`. -/
theorem signVariationsRight_eq_signVariationsAt {cs : List R[X]} {a : R}
    (h : ∀ p ∈ cs, p.eval a ≠ 0) : signVariationsRight cs a = signVariationsAt cs a :=
  (signVariationsAt_eq_right fun p hp => (signRight_eq_sign_eval p (h p hp)).symm).symm

/-- If no entry vanishes at `a`, the left-hand variations are the variations at `a`. -/
theorem signVariationsLeft_eq_signVariationsAt {cs : List R[X]} {a : R}
    (h : ∀ p ∈ cs, p.eval a ≠ 0) : signVariationsLeft cs a = signVariationsAt cs a :=
  (signVariationsAt_eq_left fun p hp => (signLeft_eq_sign_eval p (h p hp)).symm).symm

end Basic

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The right-hand variations at `a` are the variations at every point of a small enough
interval to the right of `a`. -/
theorem exists_signVariationsRight (cs : List R[X]) (a : R) :
    ∃ u, a < u ∧ ∀ x ∈ Ioo a u, signVariationsAt cs x = signVariationsRight cs a := by
  obtain ⟨u, hau, hu⟩ := cs.exists_signs_right a
  exact ⟨u, hau, fun x hx => signVariationsAt_eq_right fun p hp => hu p hp x hx⟩

/-- The left-hand variations at `a` are the variations at every point of a small enough
interval to the left of `a`. -/
theorem exists_signVariationsLeft (cs : List R[X]) (a : R) :
    ∃ l, l < a ∧ ∀ x ∈ Ioo l a, signVariationsAt cs x = signVariationsLeft cs a := by
  obtain ⟨l, hla, hl⟩ := cs.exists_signs_left a
  exact ⟨l, hla, fun x hx => signVariationsAt_eq_left fun p hp => hl p hp x hx⟩

variable [IsRealClosed R]

section Chain

variable {p f : R[X]} {cs : List R[X]}

/-- **Sturm–Tarski with one-sided endpoints.** For a signed remainder chain with head `p` and
query seed `f`, and any `a < b`, the right-hand variations at `a` minus the left-hand
variations at `b` is the sum of the signs of `f` at the distinct roots of `p` in `(a, b)`.
The endpoints may be roots of any chain entry. -/
theorem sum_sign_Ioo (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a < b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r < b, (sign (f.eval r) : ℤ) := by
  have hp : p ≠ 0 := h.nonzero p (by simp)
  -- Move the endpoints inwards to nearby points `a' < b'` realizing the one-sided signs.
  -- Then `p` has no roots in `(a, a']` or `[b', b)`, and `sum_sign` applies on `(a', b')`.
  obtain ⟨u, hau, hu⟩ := (p :: cs).exists_signs_right a
  obtain ⟨l, hlb, hl⟩ := (p :: cs).exists_signs_left b
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hau hab)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hlb (ha'.trans_le (min_le_right _ _)))
  have hpu (x : R) (hx : x ∈ Ioo a u) : p.eval x ≠ 0 :=
    eval_ne_zero_of_sign_eq_signRight hp (hu p (by simp) x hx)
  have hpl (x : R) (hx : x ∈ Ioo l b) : p.eval x ≠ 0 :=
    eval_ne_zero_of_sign_eq_signLeft hp (hl p (by simp) x hx)
  have ha'u : a' ∈ Ioo a u := ⟨haa', ha'.trans_le (min_le_left _ _)⟩
  have hb'l : b' ∈ Ioo l b := ⟨(le_max_left _ _).trans_lt hb', hb'b⟩
  have hfilter : p.roots.toFinset.filter (fun r => a < r ∧ r < b) =
      p.roots.toFinset.filter (fun r => a' < r ∧ r < b') := by
    refine Finset.filter_congr fun r hr => ?_
    have hr0 : p.eval r = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
    refine ⟨fun ⟨har, hrb⟩ => ⟨lt_of_not_ge fun hra' => hpu r ⟨har, hra'.trans_lt ha'u.2⟩ hr0,
      lt_of_not_ge fun hb'r => hpl r ⟨hb'l.1.trans_le hb'r, hrb⟩ hr0⟩,
      fun ⟨ha'r, hrb'⟩ => ⟨haa'.trans ha'r, hrb'.trans hb'b⟩⟩
  rw [hfilter, ← signVariationsAt_eq_right fun q hq => hu q hq a' ha'u,
    ← signVariationsAt_eq_left fun q hq => hl q hq b' hb'l]
  exact sum_sign h hseed ((le_max_right _ _).trans_lt hb') (hpu a' ha'u) (hpl b' hb'l)

/-- **The contribution of a point.** For a signed remainder chain with head `p` and query seed
`f`, the variations drop across `a` by the sign of `f` at `a` if `a` is a root of `p`, and do
not change otherwise. -/
theorem signVariationsLeft_sub_signVariationsRight (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) (a : R) :
    (signVariationsLeft (p :: cs) a : ℤ) - signVariationsRight (p :: cs) a =
      if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0 := by
  have hp : p ≠ 0 := h.nonzero p (by simp)
  -- Compare with Sturm–Tarski on an interval around `a` containing no other root of `p`.
  obtain ⟨l, hla, hl⟩ := (p :: cs).exists_signs_left a
  obtain ⟨u, hau, hu⟩ := (p :: cs).exists_signs_right a
  obtain ⟨l', hll', hl'a⟩ := exists_between hla
  obtain ⟨u', hau', hu'u⟩ := exists_between hau
  have hpl (x : R) (hx : x ∈ Ioo l a) : p.eval x ≠ 0 :=
    eval_ne_zero_of_sign_eq_signLeft hp (hl p (by simp) x hx)
  have hpu (x : R) (hx : x ∈ Ioo a u) : p.eval x ≠ 0 :=
    eval_ne_zero_of_sign_eq_signRight hp (hu p (by simp) x hx)
  have hfilter : p.roots.toFinset.filter (fun r => l' < r ∧ r < u') =
      p.roots.toFinset.filter (fun r => False ∨ r = a) := by
    refine Finset.filter_congr fun r hr => ?_
    have hr0 : p.eval r = 0 := (mem_roots hp).mp (Multiset.mem_toFinset.mp hr)
    refine ⟨fun ⟨hl'r, hru'⟩ => .inr ?_, ?_⟩
    · rcases lt_trichotomy r a with hra | rfl | har
      · exact absurd hr0 (hpl r ⟨hll'.trans hl'r, hra⟩)
      · rfl
      · exact absurd hr0 (hpu r ⟨har, hru'.trans hu'u⟩)
    · rintro (h | rfl)
      exacts [h.elim, ⟨hl'a, hau'⟩]
  have hs := sum_sign h hseed (hl'a.trans hau') (hpl l' ⟨hll', hl'a⟩) (hpu u' ⟨hau', hu'u⟩)
  rw [signVariationsAt_eq_left fun q hq => hl q hq l' ⟨hll', hl'a⟩,
    signVariationsAt_eq_right fun q hq => hu q hq u' ⟨hau', hu'u⟩, hfilter,
    Finset.sum_filter_or_eq_of_not _ _ _ not_false] at hs
  simpa [mem_roots hp] using hs

/-- **Sturm–Tarski on `(a, b]`.** The contribution of the closed endpoint `b` is added
explicitly to the open-interval formula. -/
theorem sum_sign_Ioc (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a ≤ b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  rcases hab.lt_or_eq with hab | rfl
  · have hIoc (r : R) : a < r ∧ r ≤ b ↔ (a < r ∧ r < b) ∨ r = b := by
      rw [← mem_Ioc, ← Ioo_insert_right hab, mem_insert_iff, mem_Ioo, or_comm]
    rw [Finset.filter_congr fun r _ => hIoc r,
      Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.2.false,
      sum_sign_Ioo h hseed hab]
    simp [mem_roots (h.nonzero p (by simp))]
  · rw [← signVariationsLeft_sub_signVariationsRight h hseed a,
      Finset.filter_false_of_mem fun r _ h => h.1.not_ge h.2]
    simp

/-- **Sturm–Tarski on `[a, b)`.** The contribution of the closed endpoint `a` is added
explicitly to the open-interval formula. -/
theorem sum_sign_Ico (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a ≤ b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r < b, (sign (f.eval r) : ℤ) := by
  rcases hab.lt_or_eq with hab | rfl
  · have hIco (r : R) : a ≤ r ∧ r < b ↔ (a < r ∧ r < b) ∨ r = a := by
      rw [← mem_Ico, ← Ioo_insert_left hab, mem_insert_iff, mem_Ioo, or_comm]
    rw [Finset.filter_congr fun r _ => hIco r,
      Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.1.false,
      sum_sign_Ioo h hseed hab]
    simp [mem_roots (h.nonzero p (by simp))]
  · rw [← signVariationsLeft_sub_signVariationsRight h hseed a,
      Finset.filter_false_of_mem fun r _ h => h.2.not_ge h.1]
    simp

/-- **Sturm–Tarski on `[a, b]`.** The contributions of both closed endpoints are added
explicitly to the open-interval formula. For `a = b` this is the contribution of a point. -/
theorem sum_sign_Icc (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) {a b : R} (hab : a ≤ b) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  have hIcc (r : R) : a ≤ r ∧ r ≤ b ↔ (a < r ∧ r ≤ b) ∨ r = a := by
    rw [← mem_Icc, ← Ioc_insert_left hab, mem_insert_iff, mem_Ioc, or_comm]
  rw [Finset.filter_congr fun r _ => hIcc r,
    Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.1.false, ← sum_sign_Ioc h hseed hab]
  simp [mem_roots (h.nonzero p (by simp))]
  ring

end Chain

section SturmSeq

variable {a b : R}

/-- One-sided Sturm–Tarski on `(a, b)` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Ioo (p f : R[X]) (hab : a < b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r < b, (sign (f.eval r) : ℤ) := by
  by_cases hp : p = 0
  · simp [hp]
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Ioo hsigned hseed hab

/-- One-sided Sturm–Tarski on `(a, b]` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Ioc {p : R[X]} (hp : p ≠ 0) (f : R[X]) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a < r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Ioc hsigned hseed hab

/-- One-sided Sturm–Tarski on `[a, b)` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Ico {p : R[X]} (hp : p ≠ 0) (f : R[X]) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r < b, (sign (f.eval r) : ℤ) := by
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Ico hsigned hseed hab

/-- One-sided Sturm–Tarski on `[a, b]` for Mathlib's signed remainder sequence. -/
theorem sum_sign_sturmSeq_Icc {p : R[X]} (hp : p ≠ 0) (f : R[X]) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r ∧ r ≤ b, (sign (f.eval r) : ℤ) := by
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Icc hsigned hseed hab

/-- Sturm's count of the distinct roots in `(a, b)`, with no condition on the endpoints. -/
theorem card_roots_toFinset_Ioo (p : R[X]) (hab : a < b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter fun r => a < r ∧ r < b).card := by
  simpa using sum_sign_sturmSeq_Ioo p 1 hab

/-- Sturm's count of the distinct roots in `(a, b]`. -/
theorem card_roots_toFinset_Ioc {p : R[X]} (hp : p ≠ 0) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval b = 0 then 1 else 0) =
      (p.roots.toFinset.filter fun r => a < r ∧ r ≤ b).card := by
  simpa using sum_sign_sturmSeq_Ioc hp 1 hab

/-- Sturm's count of the distinct roots in `[a, b)`. -/
theorem card_roots_toFinset_Ico {p : R[X]} (hp : p ≠ 0) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval a = 0 then 1 else 0) =
      (p.roots.toFinset.filter fun r => a ≤ r ∧ r < b).card := by
  simpa using sum_sign_sturmSeq_Ico hp 1 hab

/-- Sturm's count of the distinct roots in `[a, b]`. -/
theorem card_roots_toFinset_Icc {p : R[X]} (hp : p ≠ 0) (hab : a ≤ b) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval a = 0 then 1 else 0) + (if p.eval b = 0 then 1 else 0) =
      (p.roots.toFinset.filter fun r => a ≤ r ∧ r ≤ b).card := by
  simpa using sum_sign_sturmSeq_Icc hp 1 hab

end SturmSeq

end TauCeti.Sturm
