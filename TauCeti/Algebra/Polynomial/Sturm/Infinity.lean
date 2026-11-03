/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.OneSided
public import TauCeti.Algebra.Polynomial.Eval.Infinity

/-! # Sturm–Tarski with infinite endpoints

Leading coefficients and degree parity compute the sign variations at both
infinities. These satisfy the append, negation and zero-deletion laws of
`List.signVariations`, and are unchanged by multiplying every entry by a common
nonzero polynomial. Together with one-sided signs at finite endpoints, they give
half-line and whole-field Sturm–Tarski identities for signed remainder chains
and for `Polynomial.sturmSeq`, including root counts. Finite endpoints may be
roots of any chain entry.
-/

public section

namespace TauCeti.Sturm

open Polynomial

section Semiring

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- Sign variations at positive infinity. -/
noncomputable def signVariationsAtTop (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map Polynomial.leadingCoeff)

/-- Unfold positive-infinity variations as variations of the leading coefficients. -/
theorem signVariationsAtTop_def (cs : List (Polynomial R)) :
    signVariationsAtTop cs = List.signVariations (cs.map Polynomial.leadingCoeff) := (rfl)

@[simp, grind =]
theorem signVariationsAtTop_nil : signVariationsAtTop ([] : List R[X]) = 0 := by
  simp [signVariationsAtTop_def]

@[simp, grind =]
theorem signVariationsAtTop_singleton (p : R[X]) : signVariationsAtTop [p] = 0 := by
  simp [signVariationsAtTop_def]

/-- Matching the leading-coefficient signs realizes positive-infinity variations. -/
theorem signVariationsAt_eq_atTop {cs : List (Polynomial R)} {x : R}
    (h : ∀ p ∈ cs, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff) :
    signVariationsAt cs x = signVariationsAtTop cs := by
  rw [signVariationsAt_def, signVariationsAtTop_def]
  apply List.signVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left h

/-- Ordered coefficient embeddings preserve variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_map {S : Type*} [Semiring S] [LinearOrder S]
    (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) :
    signVariationsAtTop (cs.map (Polynomial.map f)) = signVariationsAtTop cs := by
  rw [signVariationsAtTop_def, signVariationsAtTop_def]
  apply List.signVariations_congr
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun p _ ↦ by
    rw [leadingCoeff_map_of_injective hf.injective]
    exact hf.sign_comp _

/-- The variations at positive infinity of a concatenation are those of the two parts, plus one
exactly when the last nonzero leading coefficient of the first part and the first nonzero leading
coefficient of the second part have opposite signs. -/
theorem signVariationsAtTop_append (cs ds : List R[X]) :
    signVariationsAtTop (cs ++ ds) =
      signVariationsAtTop cs +
        (if List.lastSign (cs.map leadingCoeff) * List.firstSign (ds.map leadingCoeff) = -1
          then 1 else 0) +
        signVariationsAtTop ds := by
  simp only [signVariationsAtTop_def, List.map_append, List.signVariations_append]

/-- The variations at positive infinity split at any nonzero entry. -/
theorem signVariationsAtTop_append_cons_of_ne_zero (cs ds : List R[X]) {p : R[X]} (hp : p ≠ 0) :
    signVariationsAtTop (cs ++ p :: ds) =
      signVariationsAtTop (cs ++ [p]) + signVariationsAtTop (p :: ds) := by
  simpa only [signVariationsAtTop_def, List.map_append, List.map_cons, List.map_nil] using
    List.signVariations_append_cons_of_ne_zero _ _ (leadingCoeff_ne_zero.2 hp)

/-- Deleting the zero entries does not change the variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_filter_ne_zero (cs : List R[X]) :
    signVariationsAtTop (cs.filter fun p ↦ !decide (p = 0)) = signVariationsAtTop cs := by
  rw [signVariationsAtTop_def, signVariationsAtTop_def,
    ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
  simp [Function.comp_def]

end Semiring

section Ring

variable {R : Type*} [Ring R] [LinearOrder R]

/-- Sign variations at negative infinity. -/
noncomputable def signVariationsAtBot (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree))

/-- Unfold negative-infinity variations using leading coefficients and degree parity. -/
theorem signVariationsAtBot_def (cs : List (Polynomial R)) :
    signVariationsAtBot cs =
      List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree)) := (rfl)

@[simp, grind =]
theorem signVariationsAtBot_nil : signVariationsAtBot ([] : List R[X]) = 0 := by
  simp [signVariationsAtBot_def]

@[simp, grind =]
theorem signVariationsAtBot_singleton (p : R[X]) : signVariationsAtBot [p] = 0 := by
  simp [signVariationsAtBot_def]

/-- Matching the parity-adjusted leading signs realizes negative-infinity variations. -/
theorem signVariationsAt_eq_atBot {cs : List (Polynomial R)} {x : R}
    (h : ∀ p ∈ cs,
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree)) :
    signVariationsAt cs x = signVariationsAtBot cs := by
  rw [signVariationsAt_def, signVariationsAtBot_def]
  apply List.signVariations_congr
  simp only [List.map_map]
  exact List.map_congr_left h

/-- Ordered coefficient embeddings preserve variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_map {S : Type*} [Ring S] [LinearOrder S]
    (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) :
    signVariationsAtBot (cs.map (Polynomial.map f)) = signVariationsAtBot cs := by
  rw [signVariationsAtBot_def, signVariationsAtBot_def]
  apply List.signVariations_congr
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun p _ ↦ by
    rw [leadingCoeff_map_of_injective hf.injective, natDegree_map_eq_of_injective hf.injective]
    simpa only [map_mul, map_pow, map_neg, map_one] using
      hf.sign_comp (p.leadingCoeff * (-1) ^ p.natDegree)

/-- The variations at negative infinity of a concatenation are those of the two parts, plus one
exactly when the last nonzero parity-adjusted leading coefficient of the first part and the first
nonzero one of the second part have opposite signs. -/
theorem signVariationsAtBot_append (cs ds : List R[X]) :
    signVariationsAtBot (cs ++ ds) =
      signVariationsAtBot cs +
        (if List.lastSign (cs.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree) *
            List.firstSign (ds.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree) = -1
          then 1 else 0) +
        signVariationsAtBot ds := by
  simp only [signVariationsAtBot_def, List.map_append, List.signVariations_append]

/-- The variations at negative infinity split at any nonzero entry. -/
theorem signVariationsAtBot_append_cons_of_ne_zero (cs ds : List R[X]) {p : R[X]} (hp : p ≠ 0) :
    signVariationsAtBot (cs ++ p :: ds) =
      signVariationsAtBot (cs ++ [p]) + signVariationsAtBot (p :: ds) := by
  simpa only [signVariationsAtBot_def, List.map_append, List.map_cons, List.map_nil] using
    List.signVariations_append_cons_of_ne_zero _ _
      ((isUnit_neg_one.pow _).mul_left_eq_zero.not.2 (leadingCoeff_ne_zero.2 hp))

/-- Deleting the zero entries does not change the variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_filter_ne_zero (cs : List R[X]) :
    signVariationsAtBot (cs.filter fun p ↦ !decide (p = 0)) = signVariationsAtBot cs := by
  rw [signVariationsAtBot_def, signVariationsAtBot_def,
    ← List.signVariations_filter_ne_zero (cs.map _), List.filter_map]
  simp [Function.comp_def, (isUnit_neg_one.pow _).mul_left_eq_zero]

/-- Negating every entry does not change the variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_map_neg [AddLeftStrictMono R] (cs : List R[X]) :
    signVariationsAtTop (cs.map Neg.neg) = signVariationsAtTop cs := by
  simpa only [signVariationsAtTop_def, List.map_map, Function.comp_def, leadingCoeff_neg] using
    List.signVariations_map_of_sign_eq_neg Left.sign_neg (cs.map leadingCoeff)

/-- Negating every entry does not change the variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_map_neg [AddLeftStrictMono R] (cs : List R[X]) :
    signVariationsAtBot (cs.map Neg.neg) = signVariationsAtBot cs := by
  simpa only [signVariationsAtBot_def, List.map_map, Function.comp_def, leadingCoeff_neg,
    natDegree_neg, neg_mul] using
    List.signVariations_map_of_sign_eq_neg Left.sign_neg
      (cs.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree)

variable [IsStrictOrderedRing R]

/-- Multiplying every entry by a common nonzero polynomial does not change the variations at
positive infinity. -/
theorem signVariationsAtTop_map_mul (cs : List R[X]) {d : R[X]} (hd : d ≠ 0) :
    signVariationsAtTop (cs.map (d * ·)) = signVariationsAtTop cs := by
  simpa only [signVariationsAtTop_def, List.map_map, Function.comp_def, leadingCoeff_mul] using
    List.signVariations_map_mul_left (cs.map leadingCoeff) (leadingCoeff_ne_zero.2 hd)

/-- Multiplying every entry by a common nonzero polynomial does not change the variations at
negative infinity. -/
theorem signVariationsAtBot_map_mul (cs : List R[X]) {d : R[X]} (hd : d ≠ 0) :
    signVariationsAtBot (cs.map (d * ·)) = signVariationsAtBot cs := by
  have h (p : R[X]) : (d * p).leadingCoeff * (-1) ^ (d * p).natDegree =
      d.leadingCoeff * (-1) ^ d.natDegree * (p.leadingCoeff * (-1) ^ p.natDegree) := by
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    rw [leadingCoeff_mul, natDegree_mul hd hp, pow_add]
    rcases neg_one_pow_eq_or R d.natDegree with h | h <;> simp [h, mul_assoc]
  simpa only [signVariationsAtBot_def, List.map_map, Function.comp_def, h] using
    List.signVariations_map_mul_left (cs.map fun p ↦ p.leadingCoeff * (-1) ^ p.natDegree)
      ((isUnit_neg_one.pow _).mul_left_eq_zero.not.2 (leadingCoeff_ne_zero.2 hd))

end Ring

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying both inputs by a common nonzero polynomial does not change the variations at
positive infinity of their signed remainder sequence. -/
@[simp]
theorem signVariationsAtTop_sturmSeq_mul_left {r : R[X]} (hr : r ≠ 0) (p q : R[X]) :
    signVariationsAtTop (sturmSeq (r * p) (r * q)) = signVariationsAtTop (sturmSeq p q) := by
  rw [sturmSeq_mul_left hr, signVariationsAtTop_map_mul _ hr]

/-- Multiplying both inputs by a common nonzero polynomial does not change the variations at
negative infinity of their signed remainder sequence. -/
@[simp]
theorem signVariationsAtBot_sturmSeq_mul_left {r : R[X]} (hr : r ≠ 0) (p q : R[X]) :
    signVariationsAtBot (sturmSeq (r * p) (r * q)) = signVariationsAtBot (sturmSeq p q) := by
  rw [sturmSeq_mul_left hr, signVariationsAtBot_map_mul _ hr]

/-- The variation count stabilizes at positive infinity, even for lists containing zero. -/
theorem exists_signVariationsAtTop (cs : List (Polynomial R)) :
    ∃ B : R, ∀ x, B < x → signVariationsAt cs x = signVariationsAtTop cs := by
  obtain ⟨B, hB⟩ := List.exists_signs_atTop cs
  exact ⟨B, fun x hx => signVariationsAt_eq_atTop (fun p hp => hB p hp x hx)⟩

/-- The variation count stabilizes at negative infinity, even for lists containing zero. -/
theorem exists_signVariationsAtBot (cs : List (Polynomial R)) :
    ∃ B : R, ∀ x, x < B → signVariationsAt cs x = signVariationsAtBot cs := by
  obtain ⟨B, hB⟩ := List.exists_signs_atBot cs
  exact ⟨B, fun x hx => signVariationsAt_eq_atBot (fun p hp => hB p hp x hx)⟩

/-- Far enough to the right, finite evaluation realizes the infinity signs and
lies beyond every chain root. The bound belongs to the ordered field itself. -/
theorem exists_atTop (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, (∀ x, B < x → signVariationsAt cs x = signVariationsAtTop cs) ∧
      ∀ p ∈ cs, ∀ r, p.eval r = 0 → r ≤ B := by
  obtain ⟨B, hB⟩ := List.exists_signs_atTop cs
  refine ⟨B, ?_, ?_⟩
  · exact fun x hx => signVariationsAt_eq_atTop (fun p hp => hB p hp x hx)
  · intro p hp r hr
    by_contra! hBr
    have hs := hB p hp r hBr
    rw [hr, sign_zero] at hs
    exact leadingCoeff_ne_zero.mpr (hne p hp) (sign_eq_zero_iff.mp hs.symm)

/-- Far enough to the left, finite evaluation realizes the negative-infinity
variations, and every chain root lies above the bound. -/
theorem exists_atBot (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, (∀ x, x < B → signVariationsAt cs x = signVariationsAtBot cs) ∧
      ∀ p ∈ cs, ∀ r, p.eval r = 0 → B ≤ r := by
  obtain ⟨B, hB⟩ := List.exists_signs_atBot cs
  refine ⟨B, ?_, ?_⟩
  · exact fun x hx => signVariationsAt_eq_atBot (fun p hp => hB p hp x hx)
  · intro p hp r hr
    by_contra! hrB
    have hs := hB p hp r hrB
    rw [hr, sign_zero] at hs
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr (hne p hp))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (sign_eq_zero_iff.mp hs.symm)

variable [IsRealClosed R]

/-- Sturm–Tarski on `(a, ∞)`, using right-hand variations at any finite endpoint. -/
theorem sum_sign_Ioi {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    (a : R) :
    (signVariationsRight (p :: cs) a : ℤ) - signVariationsAtTop (p :: cs) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨B, hB, hR⟩ := exists_atTop _ h.nonzero
  let b := max a B + 1
  have hab : a < b := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hBb : B < b := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hroots : ∀ r ∈ p.roots.toFinset, r < b := fun r hr =>
    (hR p (by simp) r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))).trans_lt hBb
  have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset.filter (a < ·) := by
    apply Finset.filter_congr
    intro r hr
    simp [hroots r hr]
  have hne : ∀ q ∈ p :: cs, q.eval b ≠ 0 :=
    fun q hq hz => (hR q hq b hz).not_gt hBb
  have ht := sum_sign_Ioo h hseed hab
  rwa [signVariationsLeft_eq_signVariationsAt hne, hB b hBb, hf] at ht

/-- Sturm–Tarski on `(-∞, b)`, using left-hand variations at any finite endpoint. -/
theorem sum_sign_Iio {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    (b : R) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsLeft (p :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨B, hB, hR⟩ := exists_atBot _ h.nonzero
  let a := min b B - 1
  have hab : a < b := lt_of_lt_of_le (sub_one_lt _) (min_le_left _ _)
  have haB : a < B := lt_of_lt_of_le (sub_one_lt _) (min_le_right _ _)
  have hroots : ∀ r ∈ p.roots.toFinset, a < r := fun r hr =>
    haB.trans_le (hR p (by simp) r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)))
  have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset.filter (· < b) := by
    apply Finset.filter_congr
    intro r hr
    simp [hroots r hr]
  have hne : ∀ q ∈ p :: cs, q.eval a ≠ 0 :=
    fun q hq hz => (hR q hq a hz).not_gt haB
  have ht := sum_sign_Ioo h hseed hab
  rwa [signVariationsRight_eq_signVariationsAt hne, hB a haB, hf] at ht

/-- Sturm–Tarski on the whole real closed field. -/
theorem sum_sign_univ {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0)) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsAtTop (p :: cs) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨B, hB, hR⟩ := exists_atBot _ h.nonzero
  let a := B - 1
  have haB : a < B := sub_one_lt _
  have hroots : ∀ r ∈ p.roots.toFinset, a < r := fun r hr =>
    haB.trans_le (hR p (by simp) r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)))
  have hf : p.roots.toFinset.filter (a < ·) = p.roots.toFinset := Finset.filter_true_of_mem hroots
  have hne : ∀ q ∈ p :: cs, q.eval a ≠ 0 :=
    fun q hq hz => (hR q hq a hz).not_gt haB
  have ht := sum_sign_Ioi h hseed a
  rwa [signVariationsRight_eq_signVariationsAt hne, hB a haB, hf] at ht


/-- Sturm–Tarski for Mathlib's sequence on `(a, ∞)`, even when `a` is a root. -/
theorem sum_sign_sturmSeq_Ioi {p : R[X]} (hp : p ≠ 0) (f : R[X]) (a : R) :
    (signVariationsRight (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Ioi hsigned hseed a

/-- Sturm–Tarski for Mathlib's sequence on `(-∞, b)`, even when `b` is a root. -/
theorem sum_sign_sturmSeq_Iio {p : R[X]} (hp : p ≠ 0) (f : R[X]) (b : R) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsLeft (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Iio hsigned hseed b

/-- Sturm–Tarski for Mathlib's signed remainder sequence on the whole real closed field. -/
theorem sum_sign_sturmSeq_univ (p f : R[X]) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_univ hsigned hseed

/-- Sturm counting of distinct roots in `(a, ∞)`, with no restriction on the endpoint. -/
theorem card_roots_toFinset_Ioi {p : R[X]} (hp : p ≠ 0) (a : R) :
    (signVariationsRight (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      (p.roots.toFinset.filter (a < ·)).card := by
  classical
  simpa using sum_sign_sturmSeq_Ioi hp 1 a

/-- Sturm counting of distinct roots in `(-∞, b)`, with no restriction on the endpoint. -/
theorem card_roots_toFinset_Iio {p : R[X]} (hp : p ≠ 0) (b : R) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsLeft (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (· < b)).card := by
  classical
  simpa using sum_sign_sturmSeq_Iio hp 1 b

/-- Classical Sturm counting of all distinct roots of a nonzero polynomial. For `p = 0` both
sides are zero: `sturmSeq 0 _ = []` and `Polynomial.roots 0 = 0` by convention. -/
theorem card_roots_toFinset_univ (p : R[X]) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      p.roots.toFinset.card := by
  simpa using sum_sign_sturmSeq_univ p 1

end TauCeti.Sturm
