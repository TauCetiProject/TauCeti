/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Tarski
public import TauCeti.Algebra.Polynomial.Eval.Infinity

/-! # Sturm–Tarski with infinite endpoints

Leading coefficients and degree parity compute the sign variations at both
infinities. These give half-line and whole-field Sturm–Tarski identities for
signed remainder chains and for `Polynomial.sturmSeq`, including root counts.
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

end Ring

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

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

/-- Sturm–Tarski on a right-unbounded interval. -/
theorem sum_sign_Ioi {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    {a : R} (ha : p.eval a ≠ 0) :
    (signVariationsAt (p :: cs) a : ℤ) - signVariationsAtTop (p :: cs) =
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
  have ht := sum_sign h hseed hab ha
    (fun hz => (hR p (by simp) b hz).not_gt hBb)
  rwa [hB b hBb, hf] at ht

/-- Sturm–Tarski on a left-unbounded interval. -/
theorem sum_sign_Iio {p f : Polynomial R} {cs : List (Polynomial R)}
    (h : IsSignedRemainderSeq (p :: cs)) (hseed : IsTarskiSeed p f (cs.head?.getD 0))
    {b : R} (hb : p.eval b ≠ 0) :
    (signVariationsAtBot (p :: cs) : ℤ) - signVariationsAt (p :: cs) b =
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
  have ht := sum_sign h hseed hab
    (fun hz => (hR p (by simp) a hz).not_gt haB) hb
  rwa [hB a haB, hf] at ht

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
  have ht := sum_sign_Ioi h hseed
    (fun hz => (hR p (by simp) a hz).not_gt haB)
  rwa [hB a haB, hf] at ht


/-- Sturm–Tarski for Mathlib's signed remainder sequence on a right-unbounded interval. -/
theorem sum_sign_sturmSeq_Ioi (p f : R[X])
    {a : R} (ha : p.eval a ≠ 0) :
    (signVariationsAt (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hp : p ≠ 0 := fun h => ha (by simp [h])
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Ioi hsigned hseed ha

/-- Sturm–Tarski for Mathlib's signed remainder sequence on a left-unbounded interval. -/
theorem sum_sign_sturmSeq_Iio (p f : R[X])
    {b : R} (hb : p.eval b ≠ 0) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsAt (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hp : p ≠ 0 := fun h => hb (by simp [h])
  have hsigned := IsSignedRemainderSeq.sturmSeq p (f * p.derivative)
  have hseed := (IsTarskiSeed.mul_derivative p f).sturmSeq
  rw [sturmSeq_cons hp] at hsigned hseed ⊢
  exact sum_sign_Iio hsigned hseed hb

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

/-- Classical Sturm counting of distinct roots in a right-unbounded interval. -/
theorem card_roots_Ioi (p : R[X]) {a : R} (ha : p.eval a ≠ 0) :
    (signVariationsAt (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      (p.roots.toFinset.filter (a < ·)).card := by
  classical
  simpa using sum_sign_sturmSeq_Ioi p 1 ha

/-- Classical Sturm counting of distinct roots in a left-unbounded interval. -/
theorem card_roots_Iio (p : R[X]) {b : R} (hb : p.eval b ≠ 0) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAt (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (· < b)).card := by
  classical
  simpa using sum_sign_sturmSeq_Iio p 1 hb

/-- Classical Sturm counting of all distinct roots of a polynomial. -/
theorem card_roots_univ (p : R[X]) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      p.roots.toFinset.card := by
  simpa using sum_sign_sturmSeq_univ p 1

end TauCeti.Sturm
