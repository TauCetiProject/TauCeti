/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Infinity

/-! # Sturm–Tarski on closed half-lines

The sign sum on `[a, ∞)` is `V(a⁺) - V(+∞)` plus the query sign at `a` if `a` is a root.
Likewise the sign sum on `(-∞, b]` is `V(-∞) - V(b⁻)` plus the endpoint contribution.
These formulas complement the open half-line formulas in `Sturm.Infinity`. They apply to
positively scaled signed remainder chains, including singleton chains and chains with a
nonconstant terminal common factor. Specializing to `Polynomial.sturmSeq` computes sign sums
and distinct root counts without requiring squarefreeness or excluding endpoint roots.

A nonzero head polynomial is required. In particular, the empty root multiset of the zero
polynomial is not interpreted as its zero set. All statements are over an arbitrary ordered
real closed field; no Archimedean or completeness assumption is used.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
§2.2.2 (Sturm–Tarski and endpoint contributions).
-/

public section

namespace TauCeti.Sturm

open Polynomial SignType

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

section Chain

variable {p f : R[X]} {cs : List R[X]}

/-- Sturm–Tarski on `[a, ∞)`, with the contribution of the closed endpoint added explicitly. -/
theorem sum_sign_Ici (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) (a : R) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsAtTop (p :: cs) +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r, (sign (f.eval r) : ℤ) := by
  classical
  have hsplit (r : R) : a ≤ r ↔ a < r ∨ r = a := le_iff_lt_or_eq.trans
    (or_congr_right eq_comm)
  rw [Finset.filter_congr fun r _ => hsplit r,
    Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.false, ← sum_sign_Ioi h hseed a]
  simp [mem_roots (h.nonzero p (by simp))]

/-- Sturm–Tarski on `(-∞, b]`, with the contribution of the closed endpoint added explicitly. -/
theorem sum_sign_Iic (h : IsSignedRemainderSeq (p :: cs))
    (hseed : IsTarskiSeed p f (cs.head?.getD 0)) (b : R) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsLeft (p :: cs) b +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with r ≤ b, (sign (f.eval r) : ℤ) := by
  classical
  rw [Finset.filter_congr fun r _ => (le_iff_lt_or_eq : r ≤ b ↔ r < b ∨ r = b),
    Finset.sum_filter_or_eq_of_not _ _ _ fun h => h.false, ← sum_sign_Iio h hseed b]
  simp [mem_roots (h.nonzero p (by simp))]

end Chain

section SturmSeq

/-- Sturm–Tarski for Mathlib's signed remainder sequence on `[a, ∞)`. -/
theorem sum_sign_sturmSeq_Ici {p : R[X]} (hp : p ≠ 0) (f : R[X]) (a : R) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) +
        (if p.eval a = 0 then (sign (f.eval a) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with a ≤ r, (sign (f.eval r) : ℤ) := by
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Ici hsigned hseed a

/-- Sturm–Tarski for Mathlib's signed remainder sequence on `(-∞, b]`. -/
theorem sum_sign_sturmSeq_Iic {p : R[X]} (hp : p ≠ 0) (f : R[X]) (b : R) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b +
        (if p.eval b = 0 then (sign (f.eval b) : ℤ) else 0) =
      ∑ r ∈ p.roots.toFinset with r ≤ b, (sign (f.eval r) : ℤ) := by
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Iic hsigned hseed b

/-- Sturm counting of distinct roots in `[a, ∞)`, including a possible root at `a`. -/
theorem card_roots_toFinset_Ici {p : R[X]} (hp : p ≠ 0) (a : R) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) +
        (if p.eval a = 0 then 1 else 0) =
      (p.roots.toFinset.filter (a ≤ ·)).card := by
  simpa using sum_sign_sturmSeq_Ici hp 1 a

/-- Sturm counting of distinct roots in `(-∞, b]`, including a possible root at `b`. -/
theorem card_roots_toFinset_Iic {p : R[X]} (hp : p ≠ 0) (b : R) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b +
        (if p.eval b = 0 then 1 else 0) =
      (p.roots.toFinset.filter (· ≤ b)).card := by
  simpa using sum_sign_sturmSeq_Iic hp 1 b

end SturmSeq

end TauCeti.Sturm
