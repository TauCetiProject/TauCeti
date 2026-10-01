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
with the sum of query signs at the distinct roots in an open interval. Positive
pseudo-remainder scalings and a nonconstant terminal common factor are allowed,
and the head polynomial need not be squarefree. `IsTarskiSeed.sign_eq` and
`IsTarskiSeed.eval_eq_zero` describe the query at the roots of a seed from which a
common factor of the head and second entry has been removed.
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

/-- Clearing every factor `X - C r` of a common factor `d` from the seed identity of
`d * p` and `d * q`. The scalar `k` is the multiplicity of `r` as a root of `d`, and `e` is the
cofactor of `(X - C r) ^ k` in `d`. -/
private theorem exists_identity_X_sub_C {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q))
    (hd : d ≠ 0) (r : R) :
    ∃ a b : R, ∃ u e : R[X], ∃ k : ℕ, 0 < a ∧ 0 < b ∧ e.eval r ≠ 0 ∧
      (d.eval r = 0 → k ≠ 0) ∧
      C a * f * (C (k : R) * (e * p) + (X - C r) * derivative (e * p)) =
        (X - C r) * (e * (u * p + C b * q)) := by
  obtain ⟨a, b, u, ha, hb, heq⟩ := h.exists_identity
  obtain ⟨e, hde, he⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd r
  refine ⟨a, b, u, e, rootMultiplicity r d, ha, hb, fun h => he (dvd_iff_isRoot.mpr h),
    fun h => (rootMultiplicity_pos hd).mpr h |>.ne', ?_⟩
  -- Multiplying by `X - C r` turns the derivative of `(X - C r) ^ k * g` into a multiple
  -- of `(X - C r) ^ k`, which is then cancelled.
  have hpow (k : ℕ) (g : R[X]) : (X - C r) * derivative ((X - C r) ^ k * g) =
      (X - C r) ^ k * (C (k : R) * g + (X - C r) * derivative g) := by
    rcases k with _ | k
    · simp
    · rw [derivative_mul, derivative_X_sub_C_pow, Nat.add_sub_cancel]
      ring
  have hd' := hpow (rootMultiplicity r d) (e * p)
  rw [← mul_assoc] at hd'
  rw [hde] at heq
  apply mul_left_cancel₀ (pow_ne_zero (rootMultiplicity r d) (X_sub_C_ne_zero r))
  linear_combination (X - C r) * heq - C a * f * hd'

/-- If `q` is a Tarski seed for the head `d * p` and query `f` after the common factor `d` is
removed from it, then at every root `r` of `p` the sign of `p' r * f r` is the sign of `q r`.
The point `r` may be a multiple root of `d * p`. -/
theorem sign_eq {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q)) (hd : d ≠ 0) {r : R}
    (hr : p.eval r = 0) :
    SignType.sign (p.derivative.eval r * f.eval r) = SignType.sign (q.eval r) := by
  obtain ⟨a, b, u, e, k, ha, hb, he, -, heq⟩ := exists_identity_X_sub_C h hd r
  obtain ⟨s, rfl⟩ := dvd_iff_isRoot.mpr hr
  have hcancel : C a * f * (C (k : R) * (e * s) + derivative (e * ((X - C r) * s))) =
      e * (u * ((X - C r) * s) + C b * q) :=
    mul_left_cancel₀ (X_sub_C_ne_zero r) (by linear_combination heq)
  have hev := congrArg (eval r) hcancel
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_mul, eval_add,
    eval_sub, eval_C, eval_X, sub_self, sub_zero, zero_mul, mul_zero, zero_add, add_zero,
    one_mul] at hev
  have hk : (0 : R) < a * (k + 1) := by positivity
  have hbq : b * q.eval r = a * (k + 1) * (s.eval r * f.eval r) :=
    mul_left_cancel₀ he (by linear_combination -hev)
  have hs := congrArg SignType.sign hbq
  rw [sign_mul, sign_mul (a * (k + 1)), sign_pos hb, sign_pos hk, one_mul, one_mul] at hs
  simpa [derivative_mul] using hs.symm

/-- A root of the removed common factor `d` that is not a root of the reduced head `p` is a
zero of the query. -/
theorem eval_eq_zero {d p f q : R[X]} (h : IsTarskiSeed (d * p) f (d * q)) (hd : d ≠ 0) {r : R}
    (hdr : d.eval r = 0) (hp : p.eval r ≠ 0) : f.eval r = 0 := by
  obtain ⟨a, b, u, e, k, ha, hb, he, hk, heq⟩ := exists_identity_X_sub_C h hd r
  have hev := congrArg (eval r) heq
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, sub_self, zero_mul, add_zero] at hev
  simpa [ha.ne', hk hdr, he, hp] using hev

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
private theorem IsTarskiSeed.sum_roots_mul {d p0 f q0 : R[X]}
    (hseed : IsTarskiSeed (d * p0) f (d * q0)) (hd : d ≠ 0) (hp0 : p0 ≠ 0) (P : R → Prop)
    [DecidablePred P] :
    (∑ r ∈ p0.roots.toFinset.filter P, (SignType.sign (f.eval r) : ℤ)) =
      ∑ r ∈ (d * p0).roots.toFinset.filter P, (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hpne : d * p0 ≠ 0 := mul_ne_zero hd hp0
  apply Finset.sum_subset
  · intro r hr
    obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
    have hr0 : p0.eval r = 0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp hr)
    exact Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr ((mem_roots hpne).mpr (by simp [hr0])), hi⟩
  · intro r hr hn
    obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
    have hpr : (d * p0).eval r = 0 := (mem_roots hpne).mp (Multiset.mem_toFinset.mp hr)
    have hpr0 : p0.eval r ≠ 0 := by
      intro hz
      exact hn (Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr hz), hi⟩)
    have hdr : d.eval r = 0 := by
      rw [eval_mul] at hpr
      exact (mul_eq_zero.mp hpr).resolve_right hpr0
    rw [hseed.eval_eq_zero hd hdr hpr0, sign_zero]
    rfl

/-- A zero query seed makes the query vanish at every root of the nonzero head, so its
sign sum is zero on any finite set of such roots. -/
theorem IsTarskiSeed.sum_sign_eq_zero {p f : Polynomial R} (hseed : IsTarskiSeed p f 0)
    (hp : p ≠ 0) (Z : Finset R) (hZ : ∀ r ∈ Z, p.eval r = 0) :
    ∑ r ∈ Z, (SignType.sign (f.eval r) : ℤ) = 0 := by
  have hseed' : IsTarskiSeed (p * 1) f (p * 0) := by simpa using hseed
  apply Finset.sum_eq_zero
  intro r hr
  rw [hseed'.eval_eq_zero hp (hZ r hr) (by simp), sign_zero]
  rfl

variable [IsRealClosed R]

/-- **Sturm–Tarski**, for a positively scaled signed remainder chain. The last
entry may be a nonconstant common factor. Roots at which the query vanishes
contribute zero, and roots of interior entries at the endpoints are allowed.
The roots of the head polynomial may be multiple. -/
private theorem sum_sign_cons {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: q :: cs)) (hseed : IsTarskiSeed p f q)
    {a b : R} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  -- Remove the terminal common factor, apply the alternating-chain formula,
  -- then restore roots of the common factor, whose query contributions vanish.
  obtain ⟨d, hd⟩ : ∃ d, (p :: q :: cs).getLast? = some d :=
    ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
  have hd0 : d ≠ 0 := h.nonzero d (List.mem_of_getLast? hd)
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
      subst hp hq
      have ha0 : d.eval a ≠ 0 ∧ p0.eval a ≠ 0 := by simpa [eval_mul] using ha
      have hb0 : d.eval b ≠ 0 ∧ p0.eval b ≠ 0 := by simpa [eval_mul] using hb
      -- The reduced head has only simple roots, with the reduced query sign there.
      have hsimple0 (r : R) (hr : p0.eval r = 0) : p0.derivative.eval r ≠ 0 := by
        intro hz
        have hs := hseed.sign_eq hd0 hr
        rw [hz, zero_mul, sign_zero] at hs
        exact hreg.second_eval_ne_zero hr (sign_eq_zero_iff.mp hs.symm)
      have hsign (r : R) (hr : p0.eval r = 0) :
          SignType.sign (p0.derivative.eval r * q0.eval r) = SignType.sign (f.eval r) := by
        have hd' : SignType.sign (p0.derivative.eval r) ≠ 0 := by simpa using hsimple0 r hr
        have numeric : ∀ s t : SignType, s ≠ 0 → s * (s * t) = t := by decide
        rw [sign_mul, ← hseed.sign_eq hd0 hr, sign_mul]
        exact numeric _ _ hd'
      have hV (x : R) (hx : d.eval x ≠ 0) :
          signVariationsAt (d * p0 :: d * q0 :: cs) x = signVariationsAt (p0 :: q0 :: ds) x := by
        rw [hmap]
        exact signVariationsAt_map_mul _ hx
      rw [hV a ha0.1, hV b hb0.1,
        hreg.sum_sign (fun r _ _ => hsimple0 r) hab ha0.2 hb0.2]
      have hp0 : p0 ≠ 0 := hreg.nonzero p0 (by simp)
      calc
        _ = ∑ r ∈ p0.roots.toFinset.filter (fun r => a < r ∧ r < b),
            (SignType.sign (f.eval r) : ℤ) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr0 := (mem_roots hp0).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)
          rw [hsign r hr0]
        _ = _ := hseed.sum_roots_mul hd0 hp0 _

/-- **Sturm–Tarski** for any nonempty signed remainder chain, including a singleton.
The seed is the second entry, or zero when the chain has only its head.
The head polynomial may have multiple roots. -/
theorem sum_sign {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    {a b : R} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (p :: cs) a : ℤ) - signVariationsAt (p :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  cases cs with
  | nil =>
    simpa using (hseed.sum_sign_eq_zero (h.nonzero p (by simp)) _
      (fun r hr => isRoot_of_mem_roots
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))).symm
  | cons q cs => exact sum_sign_cons h hseed hab ha hb

/-- Sturm–Tarski directly for Mathlib's concrete signed remainder sequence. -/
theorem sum_sign_sturmSeq (p f : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0) :
    (signVariationsAt (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAt (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hp : p ≠ 0 := fun h => ha (by simp [h])
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign hsigned hseed hab ha hb

/-- Classical Sturm counting of distinct roots in `(a, b)`, counted without
multiplicity. Neither endpoint may be a root. -/
theorem card_roots (p : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (signVariationsAt (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAt (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r < b)).card := by
  simpa using sum_sign_sturmSeq p 1 hab ha hb

end TauCeti.Sturm
