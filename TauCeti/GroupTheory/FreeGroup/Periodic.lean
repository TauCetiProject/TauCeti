/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.FreeGroup.Basic

import TauCeti.Data.List.Commutation
import TauCeti.Data.List.Infix
import TauCeti.Data.List.PeriodicityLemma
import TauCeti.Data.List.Rotate
import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic
import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Periodic words in a free group

Let `P` be a word over `α^{±1}`. A word `w` is *`P`-periodic* when it is at least as long as `P`
and is a factor of the concatenation `Pⁿ` of `n` copies of `P` or of `P⁻¹ = invRev P`, for some
`n`. Such a word has the period `|P|` and begins with a cyclic permutation `A` of `P` or of `P⁻¹`.
For `P` nonempty, the `P`-periodic words are exactly the words with these two properties, and
exactly the words `w = A^r A₁` with `A` a cyclic permutation of `P` or of `P⁻¹`, `r ≥ 1` and `A₁`
a proper prefix of `A`, as in [IFT], §5.4, (22). When `P` is cyclically reduced, for instance when
it is the reduced word of a period `A` (`FreeGroup.IsPeriod A`), the reduced powers of `P` and of
`P⁻¹` are these concatenations, and the `P`-periodic words are the subwords of length at least
`|P|` of the powers of `mk P` in `F(α)`.

For a word `P` that is not a power `uⁿ`, `n ≥ 2`, of a word, a word at least as long as `P` occurs
in the powers of `P` only at positions in a single residue class modulo `|P|`, so the place where it
cuts `P` is unique (`List.modEq_of_prefix_drop_flatten_replicate`; likewise for `P⁻¹`). If `P` is
not a cyclic permutation of `P⁻¹`, for instance if `P` represents a nontrivial element of `F(α)`
(`FreeGroup.not_isRotated_invRev_of_mk_ne_one`), then a word at least as long as `P` is not a
factor of both a power of `P` and a power of `P⁻¹` (`FreeGroup.not_infix_flatten_replicate_invRev`).
Under both conditions a `P`-periodic word determines its orientation, `P` or `P⁻¹`, and the offset
`o < |P|` at which it starts in the powers of that word. Two overlapping periodicities agree: if a
word is `P`-periodic and `Q`-periodic for words `P`, `Q` that are not powers `uⁿ`, `n ≥ 2`, of
words, and it has length at least `|P| + |Q| - gcd(|P|, |Q|)`, then `Q` is a cyclic permutation of
`P` or of `P⁻¹` (the consequence of [Adian], Lemma I.2.9, that the proof of [IFT], Lemma 20 uses).
This follows from the periodicity lemma of Fine and Wilf (`List.HasPeriod.gcd`), through
`List.HasPeriod.eq_of_hasPeriod`. A word whose element of `F(α)` is not a proper power is not a
power `uⁿ`, `n ≥ 2`, of a word (`FreeGroup.not_exists_eq_flatten_replicate_of_not_isProperPower`),
so all of this applies to the reduced word of a period.

These are the words that periodic solutions of generalised equations take on their periodic
sections ([IFT], §5.4).

## Main definitions

* `FreeGroup.IsPeriodicWord`: `P`-periodic words.

## Main results

* `FreeGroup.IsPeriodicWord.hasPeriod` and
  `FreeGroup.IsPeriodicWord.take_isRotated_or_isRotated_invRev`: a `P`-periodic word has the period
  `|P|` and begins with a cyclic permutation of `P` or of `P⁻¹`; for nonempty `P` these two
  properties characterise the `P`-periodic words (`FreeGroup.isPeriodicWord_iff_hasPeriod`).
* `FreeGroup.isPeriodicWord_iff_exists_eq_flatten_replicate_append`: for nonempty `P`, the
  `P`-periodic words are the words `A^r A₁`.
* `FreeGroup.not_infix_flatten_replicate_invRev`: if `P` is not a cyclic permutation of `P⁻¹`, a
  word at least as long as `P` is not a factor of both a power of `P` and a power of `P⁻¹`; this
  applies when `mk P ≠ 1`.
* `FreeGroup.IsPeriodicWord.existsUnique_prefix_drop_flatten_replicate`: if `P` is not a power
  `uⁿ`, `n ≥ 2`, and not a cyclic permutation of `P⁻¹`, the orientation and the offset of a
  `P`-periodic word are unique.
* `FreeGroup.isRotated_or_isRotated_invRev_of_isPeriodicWord`: overlapping periodicities.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.4, (22) and the proof of Lemma 20.
* [Adian] S. I. Adian, *The Burnside problem and identities in groups*, Nauka, Moscow (1975),
  Chapter I, §2.
* N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic functions*, Proc. Amer. Math. Soc. 16
  (1965), 109–114.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- A word `w` is `P`-periodic when `|P| ≤ |w|` and `w` is a factor of the concatenation of `n`
copies of `P` or of `n` copies of `P⁻¹ = invRev P`, for some natural number `n`. -/
def IsPeriodicWord (P w : List (α × Bool)) : Prop :=
  P.length ≤ w.length ∧
    ∃ n, w <:+: (List.replicate n P).flatten ∨ w <:+: (List.replicate n (invRev P)).flatten

/-- Unfolds `FreeGroup.IsPeriodicWord`. -/
theorem isPeriodicWord_iff {P w : List (α × Bool)} :
    IsPeriodicWord P w ↔ P.length ≤ w.length ∧
      ∃ n, w <:+: (List.replicate n P).flatten ∨ w <:+: (List.replicate n (invRev P)).flatten :=
  Iff.rfl

/-- A `P`-periodic word is at least as long as `P`. -/
theorem IsPeriodicWord.length_le {P w : List (α × Bool)} (h : IsPeriodicWord P w) :
    P.length ≤ w.length :=
  h.1

/-- The only word that is periodic with respect to the empty word is the empty word. -/
@[simp]
theorem isPeriodicWord_nil_left {w : List (α × Bool)} : IsPeriodicWord [] w ↔ w = [] := by
  simp [IsPeriodicWord]

/-- The empty word is `P`-periodic exactly when `P` is empty. -/
@[simp]
theorem isPeriodicWord_nil_right {P : List (α × Bool)} : IsPeriodicWord P [] ↔ P = [] := by
  simp [IsPeriodicWord]

/-- The concatenation of at least one copy of `P` is `P`-periodic. -/
theorem isPeriodicWord_flatten_replicate (P : List (α × Bool)) {n : ℕ} (hn : n ≠ 0) :
    IsPeriodicWord P (List.replicate n P).flatten := by
  refine ⟨?_, n, .inl (List.infix_refl _)⟩
  simpa using Nat.le_mul_of_pos_left P.length (Nat.pos_of_ne_zero hn)

/-- Every word is periodic with respect to itself. -/
@[simp]
theorem isPeriodicWord_self (P : List (α × Bool)) : IsPeriodicWord P P := by
  simpa using isPeriodicWord_flatten_replicate P one_ne_zero

/-- The `P⁻¹`-periodic words are the `P`-periodic words. -/
@[simp]
theorem isPeriodicWord_invRev_left {P w : List (α × Bool)} :
    IsPeriodicWord (invRev P) w ↔ IsPeriodicWord P w := by
  simp [IsPeriodicWord, or_comm]

/-- The formal inverse of a word is `P`-periodic exactly when the word is. -/
@[simp]
theorem isPeriodicWord_invRev_right {P w : List (α × Bool)} :
    IsPeriodicWord P (invRev w) ↔ IsPeriodicWord P w := by
  simp only [IsPeriodicWord, invRev_length, ← invRev_isInfix_invRev (u := invRev w), invRev_invRev,
    invRev_flatten_replicate, or_comm]

/-- A factor of a `P`-periodic word that is at least as long as `P` is `P`-periodic. -/
theorem IsPeriodicWord.infix {P w v : List (α × Bool)} (h : IsPeriodicWord P w) (hv : v <:+: w)
    (hl : P.length ≤ v.length) : IsPeriodicWord P v := by
  obtain ⟨-, n, hw⟩ := h
  exact ⟨hl, n, hw.imp hv.trans hv.trans⟩

/-- A `P`-periodic word has the period `|P|`. -/
theorem IsPeriodicWord.hasPeriod {P w : List (α × Bool)} (h : IsPeriodicWord P w) :
    w.HasPeriod P.length := by
  obtain ⟨-, n, hw | hw⟩ := h
  · exact (List.hasPeriod_flatten_replicate P n).infix hw
  · simpa using (List.hasPeriod_flatten_replicate (invRev P) n).infix hw

/-- A `P`-periodic word begins with a cyclic permutation of `P` or of `P⁻¹`. -/
theorem IsPeriodicWord.take_isRotated_or_isRotated_invRev {P w : List (α × Bool)}
    (h : IsPeriodicWord P w) : w.take P.length ~r P ∨ w.take P.length ~r invRev P := by
  obtain ⟨hl, n, hw | hw⟩ := h
  · exact .inl (hw.take_isRotated_of_flatten_replicate hl)
  · simpa using Or.inr (hw.take_isRotated_of_flatten_replicate (by simpa using hl))

/-- Periodicity with respect to a word only depends on the word up to cyclic permutation. -/
theorem _root_.List.IsRotated.isPeriodicWord_iff {P Q w : List (α × Bool)} (h : Q ~r P) :
    IsPeriodicWord Q w ↔ IsPeriodicWord P w := by
  suffices ∀ {P Q : List (α × Bool)}, Q ~r P → IsPeriodicWord Q w → IsPeriodicWord P w from
    ⟨this h, this h.symm⟩
  rintro P Q h ⟨hl, n, hw | hw⟩
  · exact ⟨h.perm.length_eq ▸ hl, n + 1, .inl (hw.trans (h.flatten_replicate_infix n))⟩
  · exact ⟨h.perm.length_eq ▸ hl, n + 1, .inr (hw.trans (h.invRev.flatten_replicate_infix n))⟩

/-- For a nonempty word `P`, a word `w` is `P`-periodic exactly when it has the period `|P|` and
begins with a cyclic permutation of `P` or of `P⁻¹`. -/
theorem isPeriodicWord_iff_hasPeriod {P w : List (α × Bool)} (hP : P ≠ []) :
    IsPeriodicWord P w ↔
      w.HasPeriod P.length ∧ (w.take P.length ~r P ∨ w.take P.length ~r invRev P) := by
  have h := List.length_le_and_exists_infix_flatten_replicate_iff (w := w) (l := invRev P)
    (by simpa [invRev] using hP)
  rw [invRev_length] at h
  rw [isPeriodicWord_iff, exists_or, and_or_left,
    List.length_le_and_exists_infix_flatten_replicate_iff hP, h, and_or_left]

/-- **The form `A^r A₁` of a periodic word** ([IFT], §5.4, (22)). For a nonempty word `P`, a word
`w` is `P`-periodic exactly when `w = A^r A₁` for a cyclic permutation `A` of `P` or of `P⁻¹`, some
`r ≥ 1` and a proper prefix `A₁` of `A`. -/
theorem isPeriodicWord_iff_exists_eq_flatten_replicate_append {P w : List (α × Bool)}
    (hP : P ≠ []) : IsPeriodicWord P w ↔ ∃ A r A₁, (A ~r P ∨ A ~r invRev P) ∧ 0 < r ∧
      A₁ <+: A ∧ A₁.length < A.length ∧ w = (List.replicate r A).flatten ++ A₁ := by
  have h :=
    List.length_le_and_exists_infix_flatten_replicate_iff_exists_eq_flatten_replicate_append
      (w := w) (l := invRev P) (by simpa [invRev] using hP)
  rw [invRev_length] at h
  rw [isPeriodicWord_iff, exists_or, and_or_left,
    List.length_le_and_exists_infix_flatten_replicate_iff_exists_eq_flatten_replicate_append hP, h]
  simp only [or_and_right, exists_or]

/-- Let `P` be a word that is not a cyclic permutation of its formal inverse `P⁻¹`, for instance
a word representing a nontrivial element of the free group
(`FreeGroup.not_isRotated_invRev_of_mk_ne_one`). A word at least as long as `P` is not a factor
both of a concatenation of copies of `P` and of a concatenation of copies of `P⁻¹` ([IFT], proof
of Lemma 20). -/
theorem not_infix_flatten_replicate_invRev {P w : List (α × Bool)} (hP : ¬P ~r invRev P)
    (hw : P.length ≤ w.length) {m n : ℕ} (h : w <:+: (List.replicate m P).flatten) :
    ¬w <:+: (List.replicate n (invRev P)).flatten := fun h' =>
  hP ((h.take_isRotated_of_flatten_replicate hw).symm.trans
    (by simpa using h'.take_isRotated_of_flatten_replicate (by simpa using hw)))

/-- **Uniqueness of the cut** ([IFT], §5.4). Let `P` be a word that is not a power `uⁿ` of a word
with `n ≥ 2` and not a cyclic permutation of its formal inverse `P⁻¹`. For a `P`-periodic word `w`
there is exactly one orientation `b` and offset `o < |P|` such that `w` starts at position `o` of
a concatenation of copies of `P` (for `b = true`) or of `P⁻¹` (for `b = false`). -/
theorem IsPeriodicWord.existsUnique_prefix_drop_flatten_replicate {P w : List (α × Bool)}
    (hP : ¬∃ u n, 2 ≤ n ∧ P = (List.replicate n u).flatten) (hPi : ¬P ~r invRev P)
    (h : IsPeriodicWord P w) :
    ∃! c : Bool × ℕ, c.2 < P.length ∧
      ∃ n, w <+: ((List.replicate n (bif c.1 then P else invRev P)).flatten).drop c.2 := by
  have hP0 := List.ne_nil_of_not_exists_eq_flatten_replicate hP
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨-, n, hw | hw⟩ := h
    · obtain ⟨o, ho, hwo⟩ := hw.exists_prefix_drop_flatten_replicate hP0
      exact ⟨(true, o), ho, n, hwo⟩
    · obtain ⟨o, ho, hwo⟩ := hw.exists_prefix_drop_flatten_replicate
        (by simpa [invRev] using hP0)
      exact ⟨(false, o), by simpa using ho, n, hwo⟩
  -- one orientation forces congruent offsets, and two orientations are impossible
  rintro ⟨b, o⟩ ⟨b', o'⟩ ⟨ho, n, hw⟩ ⟨ho', n', hw'⟩
  have hl := h.length_le
  have hinf {X : List (α × Bool)} {m k : ℕ} (hX : w <+: ((List.replicate m X).flatten).drop k) :
      w <:+: (List.replicate m X).flatten :=
    hX.isInfix.trans (List.drop_suffix _ _).isInfix
  cases b <;> cases b' <;> simp only [Bool.cond_true, Bool.cond_false] at hw hw' ho ho'
  · exact Prod.ext rfl ((List.modEq_of_prefix_drop_flatten_replicate (by simpa using hP)
      (by simpa using hl) hw hw').eq_of_lt_of_lt (by simpa using ho) (by simpa using ho'))
  · exact absurd (hinf hw) (not_infix_flatten_replicate_invRev hPi hl (hinf hw'))
  · exact absurd (hinf hw') (not_infix_flatten_replicate_invRev hPi hl (hinf hw))
  · exact Prod.ext rfl
      ((List.modEq_of_prefix_drop_flatten_replicate hP hl hw hw').eq_of_lt_of_lt ho ho')

/-- **Overlapping periodicities** (the consequence of [Adian], Lemma I.2.9, used in [IFT], proof of
Lemma 20). Let `P` and `Q` be words that are not powers `uⁿ` of words with `n ≥ 2`. If a word of
length at least `|P| + |Q| - gcd(|P|, |Q|)` is both `P`-periodic and `Q`-periodic, then `Q` is a
cyclic permutation of `P` or of `P⁻¹`. -/
theorem isRotated_or_isRotated_invRev_of_isPeriodicWord {P Q w : List (α × Bool)}
    (hP : ¬∃ u n, 2 ≤ n ∧ P = (List.replicate n u).flatten)
    (hQ : ¬∃ u n, 2 ≤ n ∧ Q = (List.replicate n u).flatten) (hwP : IsPeriodicWord P w)
    (hwQ : IsPeriodicWord Q w) (hw : P.length + Q.length - P.length.gcd Q.length ≤ w.length) :
    Q ~r P ∨ Q ~r invRev P := by
  -- the prefixes of `w` of lengths `|P|` and `|Q|` are rotations of `P` or `P⁻¹` and of `Q` or
  -- `Q⁻¹`, so they are not powers, and the two periods agree
  have hP' := hwP.take_isRotated_or_isRotated_invRev
  have hQ' := hwQ.take_isRotated_or_isRotated_invRev
  have hnp {X Y : List (α × Bool)} (hX : ¬∃ u n, 2 ≤ n ∧ X = (List.replicate n u).flatten)
      (h : Y ~r X ∨ Y ~r invRev X) : ¬∃ u n, 2 ≤ n ∧ Y = (List.replicate n u).flatten := by
    rcases h with h | h <;> rw [h.exists_eq_flatten_replicate_iff] <;> simpa using hX
  rw [← hwP.hasPeriod.eq_of_hasPeriod hwQ.hasPeriod (hnp hP hP') (hnp hQ hQ') hw] at hQ'
  rcases hP' with hP' | hP' <;> rcases hQ' with hQ' | hQ'
  · exact .inl (hQ'.symm.trans hP')
  · exact .inr (by simpa using (hQ'.symm.trans hP').invRev)
  · exact .inr (hQ'.symm.trans hP')
  · exact .inl (by simpa using (hQ'.symm.trans hP').invRev)

/-! ### Examples -/

/- A word over `{a, b}` whose exponent sum in `b` is `1` is not a power of a word. -/
private theorem not_exists_eq_flatten_replicate_of_lift_eq {w : List (Fin 2 × Bool)}
    (h : lift (fun c => if c = 1 then Multiplicative.ofAdd (1 : ℤ) else 1) (mk w) =
      Multiplicative.ofAdd 1) : ¬∃ u n, 2 ≤ n ∧ w = (List.replicate n u).flatten :=
  not_exists_eq_flatten_replicate_of_not_isProperPower
    (Group.not_isProperPower_of_map_eq_ofAdd_one _ h)

/-- The length bound of overlapping periodicities is sharp: in `F(a, b)` the word `aabaa`, of length
`5 < 3 + 4 - gcd(3, 4)`, is both `aab`-periodic and `aaba`-periodic, and neither `aab` nor `aaba`
is a power of a word, but `aaba` is not a cyclic permutation of `aab` or of its inverse. -/
example : (¬∃ u n, 2 ≤ n ∧
      [((0 : Fin 2), true), (0, true), (1, true)] = (List.replicate n u).flatten) ∧
    (¬∃ u n, 2 ≤ n ∧
      [((0 : Fin 2), true), (0, true), (1, true), (0, true)] = (List.replicate n u).flatten) ∧
    IsPeriodicWord [(0, true), (0, true), (1, true)]
      [((0 : Fin 2), true), (0, true), (1, true), (0, true), (0, true)] ∧
    IsPeriodicWord [(0, true), (0, true), (1, true), (0, true)]
      [((0 : Fin 2), true), (0, true), (1, true), (0, true), (0, true)] ∧
    ¬([((0 : Fin 2), true), (0, true), (1, true), (0, true)] ~r [(0, true), (0, true), (1, true)] ∨
      [((0 : Fin 2), true), (0, true), (1, true), (0, true)] ~r
        invRev [(0, true), (0, true), (1, true)]) :=
  ⟨not_exists_eq_flatten_replicate_of_lift_eq (by decide),
    not_exists_eq_flatten_replicate_of_lift_eq (by decide),
    ⟨by decide, 2, .inl (by decide)⟩, ⟨by decide, 2, .inl (by decide)⟩, by decide⟩

end FreeGroup
