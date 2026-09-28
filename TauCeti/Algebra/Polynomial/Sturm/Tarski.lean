/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.SignedRemainders
public import TauCeti.Algebra.Polynomial.Sturm.Sum

/-! # Sturm–Tarski over an arbitrary real closed ordered field

`IsTarskiSeed` relates the second chain entry to `f * p'` modulo `p`.
`sum_sign` identifies the variation difference of a signed remainder chain
with the sum of query signs at the roots in an open interval. Positive
pseudo-remainder scalings and a nonconstant terminal common factor are allowed.
The concrete `Polynomial.sturmSeq` specialization supplies sign sums and root
counts, and is the finite-interval basis for the infinite-endpoint formulas.

## References

For the classical sign-sum identity, see S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://mariefrancoiseroy.pages.math.cnrs.fr/bpr-ed2-posted3.pdf),
revised second edition, §2.2.2, Theorem 2.73 (Tarski’s theorem).
-/

public section

namespace TauCeti.Sturm

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The positive-scaled seed congruence between the second entry and `f * p'`
modulo `p`. Both scalings are explicit to cover signed pseudo-remainders.
A degree bound identifies the actual remainder, but is unnecessary for soundness. -/
def IsTarskiSeed (p f q : Polynomial R) : Prop :=
  IsRemainder (f * p.derivative) p (-q)

namespace IsTarskiSeed

omit [IsStrictOrderedRing R] in
/-- Construct a query seed from its positive-scaled congruence identity. -/
theorem of_identity {p f q : Polynomial R} (a b : R) (u : Polynomial R)
    (ha : 0 < a) (hb : 0 < b)
    (heq : C a * (f * p.derivative) = u * p + C b * q) : IsTarskiSeed p f q := by
  exact IsRemainder.of_identity a b u ha hb (by simpa using heq)

omit [IsStrictOrderedRing R] in
/-- A query seed supplies positive scalings and the congruence identity. -/
theorem exists_identity {p f q : Polynomial R} (h : IsTarskiSeed p f q) :
    ∃ a b : R, ∃ u : Polynomial R,
      0 < a ∧ 0 < b ∧ C a * (f * p.derivative) = u * p + C b * q := by
  obtain ⟨a, b, u, ha, hb, heq⟩ := IsRemainder.exists_identity h
  exact ⟨a, b, u, ha, hb, by simpa using heq⟩

/-- The unreduced derivative query is a valid Tarski seed. -/
theorem mul_derivative (p f : R[X]) : IsTarskiSeed p f (f * p.derivative) :=
  of_identity 1 1 0 zero_lt_one zero_lt_one (by simp)

/-- Reducing the derivative query modulo the head gives a valid Tarski seed. -/
theorem mod (p f : R[X]) : IsTarskiSeed p f ((f * p.derivative) % p) := by
  classical
  refine of_identity 1 1 ((f * p.derivative) / p) zero_lt_one zero_lt_one ?_
  rw [map_one, one_mul, one_mul]
  exact (EuclideanDomain.mod_add_div (f * p.derivative) p).symm.trans (by ring)

/-- At a simple root of `p`, the signed-chain jump is the sign of the query. -/
theorem sign_eq {p f q : Polynomial R} (h : IsTarskiSeed p f q) {r : R}
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0) :
    SignType.sign (p.derivative.eval r * q.eval r) = SignType.sign (f.eval r) := by
  obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
  have he := congrArg (Polynomial.eval r) heq
  simp only [eval_mul, eval_C, eval_add, hr, mul_zero, zero_add] at he
  have hs : SignType.sign (f.eval r) * SignType.sign (p.derivative.eval r) =
      SignType.sign (q.eval r) := by
    have := congrArg SignType.sign he
    simpa only [sign_mul, sign_pos ha, sign_pos hb, one_mul] using this
  rw [sign_mul, ← hs]
  have hd' : SignType.sign (p.derivative.eval r) ≠ 0 := by simpa using hd
  have numeric : ∀ s t : SignType, s ≠ 0 → s * (t * s) = t := by decide
  exact numeric _ _ hd'

/-- Common roots of the head and second entry contribute zero to the query. -/
theorem eval_eq_zero {p f q : Polynomial R} (h : IsTarskiSeed p f q) {r : R}
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0) (hq : q.eval r = 0) :
    f.eval r = 0 := by
  have hs := h.sign_eq hr hd
  rw [hq, mul_zero, sign_zero] at hs
  exact sign_eq_zero_iff.mp hs.symm

/-- A valid query seed remains valid as the second entry of Mathlib's sequence,
including the singleton case. -/
theorem sturmSeq {p f q : R[X]} (h : IsTarskiSeed p f q) :
    IsTarskiSeed p f ((Polynomial.sturmSeq p q).tail.head?.getD 0) := by
  classical
  by_cases hp : p = 0
  · subst p
    simpa using mul_derivative (0 : R[X]) f
  simpa only [List.head?_tail, getD_getElem?_sturmSeq hp] using h

end IsTarskiSeed

/-- Removing a common factor preserves the query sum: its lost roots have zero query sign. -/
private theorem IsTarskiSeed.sum_roots_mul {p f q d p0 q0 : R[X]}
    (hseed : IsTarskiSeed p f q) (hp : p = d * p0) (hq : q = d * q0)
    (hpne : p ≠ 0) (hp0 : p0 ≠ 0) {a b : R}
    (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0) :
    (∑ r ∈ p0.roots.toFinset.filter (fun r => a < r ∧ r < b),
      (SignType.sign (f.eval r) : ℤ)) =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  apply Finset.sum_subset
  · intro r hr
    obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
    have hr0 : p0.eval r = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hr)
    exact Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr ((mem_roots hpne).mpr (by simp [hp, hr0])), hi⟩
  · intro r hr hn
    obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
    have hpr : p.eval r = 0 := (mem_roots hpne).mp (Multiset.mem_toFinset.mp hr)
    have hpr0 : p0.eval r ≠ 0 := by
      intro hz
      exact hn (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr hz), hi⟩)
    have hdr : d.eval r = 0 := by
      rw [hp, eval_mul] at hpr
      exact (mul_eq_zero.mp hpr).resolve_right hpr0
    have hqr : q.eval r = 0 := by simp [hq, hdr]
    rw [hseed.eval_eq_zero hpr (hsimple r hi.1 hi.2 hpr) hqr, sign_zero]
    rfl

/-- A zero query seed makes the query vanish at every simple root, so its
sign sum is zero on any finite set of such roots. -/
theorem IsTarskiSeed.sum_sign_eq_zero {p f : Polynomial R} (hseed : IsTarskiSeed p f 0)
    (Z : Finset R) (hsimple : ∀ r ∈ Z, p.derivative.eval r ≠ 0)
    (hZ : ∀ r ∈ Z, p.eval r = 0) :
    ∑ r ∈ Z, (SignType.sign (f.eval r) : ℤ) = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  rw [hseed.eval_eq_zero (hZ r hr) (hsimple r hr) (by simp), sign_zero]
  rfl

variable [IsRealClosed R]

/-- **Sturm–Tarski**, for a positively scaled signed remainder chain. The last
entry may be a nonconstant common factor. Roots at which the query vanishes
contribute zero, and roots of interior entries at the endpoints are allowed.
The head polynomial is required to have simple roots only inside the interval. -/
private theorem sum_sign_cons {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: q :: cs)) (hseed : IsTarskiSeed p f q)
    {a b : R} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  -- Remove the terminal common factor, apply the alternating-chain formula,
  -- then restore roots of the common factor, whose query contributions vanish.
  obtain ⟨d, hd⟩ : ∃ d, (p :: q :: cs).getLast? = some d :=
    ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
  obtain ⟨ds, hmap, _, _, hreg⟩ := h.exists_isAlternating hd
  cases ds with
  | nil => simp at hmap
  | cons p0 ds =>
    cases ds with
    | nil => simp at hmap
    | cons q0 ds =>
      have hp : p = d * p0 := by
        have := hmap
        simp only [List.map_cons, List.cons.injEq] at this
        exact this.1
      have hq : q = d * q0 := by
        have := hmap
        simp only [List.map_cons, List.cons.injEq] at this
        exact this.2.1
      have ha0 : d.eval a ≠ 0 ∧ p0.eval a ≠ 0 := by simpa [hp, eval_mul] using ha
      have hb0 : d.eval b ≠ 0 ∧ p0.eval b ≠ 0 := by simpa [hp, eval_mul] using hb
      have hroot (r : R) (hr : p0.eval r = 0) : p.eval r = 0 := by simp [hp, hr]
      have hder (r : R) (hr : p0.eval r = 0) :
          p.derivative.eval r = d.eval r * p0.derivative.eval r := by
        rw [hp, derivative_mul]
        simp [hr]
      have hsimple0 (r : R) (har : a < r) (hrb : r < b)
          (hr : p0.eval r = 0) : p0.derivative.eval r ≠ 0 := by
        have := hsimple r har hrb (hroot r hr)
        rw [hder r hr] at this
        exact (mul_ne_zero_iff.mp this).2
      have hsign (r : R) (har : a < r) (hrb : r < b) (hr : p0.eval r = 0) :
          SignType.sign (p0.derivative.eval r * q0.eval r) = SignType.sign (f.eval r) := by
        have hs := hseed.sign_eq (hroot r hr) (hsimple r har hrb (hroot r hr))
        have hd0 : d.eval r ≠ 0 := by
          have := hsimple r har hrb (hroot r hr)
          rw [hder r hr] at this
          exact (mul_ne_zero_iff.mp this).1
        rw [hder r hr, hq, eval_mul] at hs
        have he : d.eval r * p0.derivative.eval r * (d.eval r * q0.eval r) =
            (d.eval r) ^ 2 * (p0.derivative.eval r * q0.eval r) := by ring
        rw [he, sign_mul, sign_pos (sq_pos_of_ne_zero hd0), one_mul] at hs
        exact hs
      have hV (x : R) (hx : d.eval x ≠ 0) :
          signVariationsAt (p :: q :: cs) x = signVariationsAt (p0 :: q0 :: ds) x := by
        rw [hmap]
        exact signVariationsAt_map_mul _ hx
      rw [hV a ha0.1, hV b hb0.1, hreg.sum_sign hsimple0 hab ha0.2 hb0.2]
      have hp0 : p0 ≠ 0 := hreg.nonzero p0 (by simp)
      calc
        _ = ∑ r ∈ p0.roots.toFinset.filter (fun r => a < r ∧ r < b),
            (SignType.sign (f.eval r) : ℤ) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hsign r (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr).2.2
            ((mem_roots hp0).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))]
        _ = _ := hseed.sum_roots_mul hp hq (h.nonzero p (by simp)) hp0 hsimple

/-- **Sturm–Tarski** for any nonempty signed remainder chain, including a singleton.
The seed is the second entry, or zero when the chain has only its head.
Only roots inside the queried interval must be simple; squarefreeness is sufficient.
See `TauCeti.Algebra.Polynomial.Squarefree` for that implication. -/
theorem sum_sign {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    {a b : R} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: cs) a : ℤ) - signVariationsAt (p :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  cases cs with
  | nil =>
    simpa using (hseed.sum_sign_eq_zero _
      (fun r hr => hsimple r (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr).2.2
        (isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)))
      (fun r hr => isRoot_of_mem_roots
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))).symm
  | cons q cs => exact sum_sign_cons h hseed hsimple hab ha hb

/-- Sturm–Tarski directly for Mathlib's concrete signed remainder sequence. -/
theorem sum_sign_sturmSeq (p f : R[X])
    {a b : R} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAt (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hp : p ≠ 0 := fun h => ha (by simp [h])
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign hsigned hseed hsimple hab ha hb

/-- Classical Sturm counting of distinct roots in `(a, b)`. Only roots inside
that interval must be simple; neither endpoint may be a root. -/
theorem card_roots (p : R[X])
    {a b : R} (hsimple : ∀ r, a < r → r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAt (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r < b)).card := by
  simpa using sum_sign_sturmSeq p 1 hsimple hab ha hb

end TauCeti.Sturm
