/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.GroupTheory.FreeGroup.Basic
public import TauCeti.GroupTheory.ProperPower

import TauCeti.Data.List.PeriodicityLemma
import TauCeti.GroupTheory.FreeGroup.CSA
import TauCeti.GroupTheory.FreeGroup.Conjugacy.Basic
import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Periodic words in a free group

Let `P` be a word over `α^{±1}`. A word `w` is *`P`-periodic* when it is at least as long as `P`
and is a factor of the concatenation `Pⁿ` of `n` copies of `P` or of `P⁻¹ = invRev P`, for some
`n`. Such a word has the period `|P|` and begins with a cyclic permutation `A` of `P` or of `P⁻¹`,
so that, for `P` nonempty, it is `w = A^r A₁` with `r ≥ 1` and `A₁` a proper prefix of `A`, as in
[IFT], §5.4, (22) (`List.HasPeriod.flatten_replicate_take_append_take`). When `P` is cyclically
reduced, for instance when it is the reduced word of a period `A` (`FreeGroup.IsPeriod A`), the
reduced powers of `P` and of `P⁻¹` are these concatenations, and the `P`-periodic words are the
subwords of length at least `|P|` of the powers of `mk P` in `F(α)`.

For a word `P` that is not a proper power in `F(α)`, the place where a `P`-periodic word cuts `P`
is unique: the rotations of `P` are pairwise distinct, so a word at least as long as `P` occurs in
the powers of `P` only at positions in a single residue class modulo `|P|`
(`FreeGroup.modEq_of_prefix_drop_flatten_replicate`); and, `P` being nontrivial in `F(α)`, such a
word is not a factor of both a power of `P` and a power of `P⁻¹`
(`FreeGroup.not_infix_flatten_replicate_invRev`). Two overlapping periodicities agree: if a word
is `P`-periodic and `Q`-periodic for words `P`, `Q` that are not proper powers, and it has length at
least `|P| + |Q| - gcd(|P|, |Q|)`, then `Q` is a cyclic permutation of `P` or of `P⁻¹`
(`FreeGroup.isRotated_or_isRotated_invRev_of_isPeriodicWord`: the consequence of [Adian],
Lemma I.2.9, that the proof of [IFT], Lemma 20 uses). This is the periodicity lemma of Fine and
Wilf (`List.HasPeriod.gcd`) combined with the fact that a word that is not a proper power in `F(α)`
has no period properly dividing its length (`FreeGroup.eq_length_of_hasPeriod`).

These are the words that periodic solutions of generalised equations take on their periodic
sections ([IFT], §5.4).

## Main definitions

* `FreeGroup.IsPeriodicWord`: `P`-periodic words.

## Main results

* `FreeGroup.IsPeriodicWord.hasPeriod`, `FreeGroup.IsPeriodicWord.take_isRotated`: a `P`-periodic
  word has the period `|P|` and begins with a cyclic permutation of `P` or of `P⁻¹`.
* `FreeGroup.eq_length_of_hasPeriod`: a word that is not a proper power has no period properly
  dividing its length.
* `FreeGroup.rotate_eq_rotate_iff_of_not_isProperPower`: the rotations of a word that is not a
  proper power are pairwise distinct.
* `FreeGroup.modEq_of_prefix_drop_flatten_replicate`: uniqueness of the place where a periodic
  word cuts the period.
* `FreeGroup.not_infix_flatten_replicate_invRev`: a word at least as long as `P` is not a factor
  of both a power of `P` and a power of `P⁻¹`.
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

/-! ### Formal inverses and rotations of words -/

/-- The formal inverse of the concatenation of `n` copies of a word is the concatenation of `n`
copies of its formal inverse. -/
@[simp]
theorem invRev_flatten_replicate (P : List (α × Bool)) (n : ℕ) :
    invRev (List.replicate n P).flatten = (List.replicate n (invRev P)).flatten := by
  simp [invRev, List.map_flatten, List.reverse_flatten]

/-- The formal inverses of two cyclic permutations of each other are cyclic permutations of each
other. -/
theorem _root_.List.IsRotated.invRev {P Q : List (α × Bool)} (h : Q ~r P) : invRev Q ~r invRev P :=
  (h.map _).reverse

/-- Cyclic permutations of each other represent conjugate elements of the free group, so one is a
proper power exactly when the other is. -/
theorem _root_.List.IsRotated.isProperPower_mk_iff {P Q : List (α × Bool)} (h : Q ~r P) :
    Group.IsProperPower (mk Q) ↔ Group.IsProperPower (mk P) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_mk_of_isRotated h)
  rw [← hc, Group.isProperPower_conj_iff]

/-! ### Periodic words -/

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

/-- The concatenation of at least one copy of `P` is `P`-periodic. -/
theorem isPeriodicWord_flatten_replicate (P : List (α × Bool)) {n : ℕ} (hn : n ≠ 0) :
    IsPeriodicWord P (List.replicate n P).flatten := by
  refine ⟨?_, n, .inl (List.infix_refl _)⟩
  simpa using Nat.le_mul_of_pos_left P.length (Nat.pos_of_ne_zero hn)

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
theorem IsPeriodicWord.take_isRotated {P w : List (α × Bool)} (h : IsPeriodicWord P w) :
    w.take P.length ~r P ∨ w.take P.length ~r invRev P := by
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

/-- A word that is not a proper power in the free group has no period properly dividing its
length: a period `d` dividing the length is the length itself. -/
theorem eq_length_of_hasPeriod {P : List (α × Bool)} (hP : ¬Group.IsProperPower (mk P)) {d : ℕ}
    (h : P.HasPeriod d) (hd : d ∣ P.length) : d = P.length := by
  have hpos : 0 < P.length := List.length_pos_iff.2 fun h => hP (by simp [h, ← one_eq_mk])
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hpos
  obtain ⟨k, hk⟩ := hd
  by_contra hne
  -- otherwise `P` is the power `(take d P) ^ k` with `k ≥ 2`
  refine hP (Group.isProperPower_iff.2 ⟨mk (P.take d), k, ?_, ?_⟩)
  · rcases k with _ | _ | k <;> simp_all
  · have := h.flatten_replicate_take_append_take
    rw [hk, Nat.mul_mod_right, List.take_zero, List.append_nil,
      Nat.mul_div_cancel_left k hd0] at this
    rw [pow_mk, this]

/- A word that is not a proper power in the free group is fixed by a rotation only if the length
of the word divides it: otherwise it would have two periods whose greatest common divisor properly
divides its length. -/
private theorem length_dvd_of_rotate_eq_self {P : List (α × Bool)}
    (hP : ¬Group.IsProperPower (mk P)) {k : ℕ} (hk : P.rotate k = P) : P.length ∣ k := by
  have hpos : 0 < P.length := List.length_pos_iff.2 fun h => hP (by simp [h, ← one_eq_mk])
  have hlt := Nat.mod_lt k hpos
  rw [← List.rotate_mod] at hk
  rw [Nat.dvd_iff_mod_eq_zero]
  generalize k % P.length = r at hk hlt ⊢
  by_contra hr
  -- `P` has the periods `r` and `|P| - r`, hence their greatest common divisor
  have h₁ : P.HasPeriod r := List.hasPeriod_iff_getElem?.2 fun i hi => by
    conv_lhs => rw [← hk]
    rw [List.getElem?_rotate (by lia), Nat.mod_eq_of_lt (by lia)]
  have h₂ : P.HasPeriod (P.length - r) := List.hasPeriod_iff_getElem?.2 fun i hi => by
    have e : (P.rotate r)[i + (P.length - r)]? = P[i + (P.length - r)]? := by rw [hk]
    rw [← e, List.getElem?_rotate (by lia), Nat.add_assoc, Nat.sub_add_cancel hlt.le,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by lia)]
  have hdvd : r.gcd (P.length - r) ∣ P.length := by
    simpa [Nat.add_sub_cancel' hlt.le] using
      Nat.dvd_add (Nat.gcd_dvd_left r (P.length - r)) (Nat.gcd_dvd_right r (P.length - r))
  have := eq_length_of_hasPeriod hP (h₁.gcd h₂ (by lia)) hdvd
  have := Nat.gcd_le_left (P.length - r) (Nat.pos_of_ne_zero hr)
  lia

/-- The rotations of a word that is not a proper power in the free group are pairwise distinct:
rotating it by `i` and by `j` gives the same word exactly when `i ≡ j` modulo its length. -/
theorem rotate_eq_rotate_iff_of_not_isProperPower {P : List (α × Bool)}
    (hP : ¬Group.IsProperPower (mk P)) {i j : ℕ} :
    P.rotate i = P.rotate j ↔ i ≡ j [MOD P.length] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · wlog hij : i ≤ j generalizing i j
    · exact (this h.symm (by lia)).symm
    have hk : (P.rotate i).rotate (j - i) = P.rotate i := by
      rw [List.rotate_rotate, Nat.add_sub_cancel' hij, h]
    have := length_dvd_of_rotate_eq_self
      (by rwa [(List.IsRotated.forall P i).isProperPower_mk_iff]) hk
    rw [List.length_rotate] at this
    exact (Nat.modEq_iff_dvd' hij).2 this
  · rw [← List.rotate_mod P i, h, List.rotate_mod]

/-- **Uniqueness of the cut** ([IFT], §5.4, before Lemma 20). Let `P` be a word that is not a proper
power in the free group. If a word `w` at least as long as `P` occurs in the concatenation of
copies of `P` at the positions `o` and `o'` (of possibly different numbers of copies), then
`o ≡ o'` modulo `|P|`. -/
theorem modEq_of_prefix_drop_flatten_replicate {P w : List (α × Bool)}
    (hP : ¬Group.IsProperPower (mk P)) (hw : P.length ≤ w.length) {m m' o o' : ℕ}
    (h : w <+: ((List.replicate m P).flatten).drop o)
    (h' : w <+: ((List.replicate m' P).flatten).drop o') : o ≡ o' [MOD P.length] := by
  rw [← rotate_eq_rotate_iff_of_not_isProperPower hP,
    ← List.take_eq_rotate_of_prefix_drop_flatten_replicate h hw,
    List.take_eq_rotate_of_prefix_drop_flatten_replicate h' hw]

/-- A word that is at least as long as a word `P` representing a nontrivial element of the free
group is not a factor both of a concatenation of copies of `P` and of a concatenation of copies of
`P⁻¹` ([IFT], proof of Lemma 20); equivalently, no cyclic permutation of `P` is one of `P⁻¹`. -/
theorem not_infix_flatten_replicate_invRev {P w : List (α × Bool)} (hP : mk P ≠ 1)
    (hw : P.length ≤ w.length) {m n : ℕ} (h : w <:+: (List.replicate m P).flatten) :
    ¬w <:+: (List.replicate n (invRev P)).flatten := by
  classical
  intro h'
  have h₁ := h.take_isRotated_of_flatten_replicate hw
  have h₂ := h'.take_isRotated_of_flatten_replicate (by simpa using hw)
  rw [invRev_length] at h₂
  -- a cyclic permutation of `P` and of `P⁻¹` would make `mk P` conjugate to its inverse
  refine IsFreeGroup.isCommTransitive.not_isConj_inv hP ?_
  rw [inv_mk]
  exact isConj_mk_of_isRotated (h₁.symm.trans h₂)

/-- **Overlapping periodicities** (the consequence of [Adian], Lemma I.2.9, used in [IFT], proof of
Lemma 20). Let `P` and
`Q` be words that are not proper powers in the free group. If a word of length at least
`|P| + |Q| - gcd(|P|, |Q|)` is both `P`-periodic and `Q`-periodic, then `Q` is a cyclic
permutation of `P` or of `P⁻¹`. -/
theorem isRotated_or_isRotated_invRev_of_isPeriodicWord {P Q w : List (α × Bool)}
    (hP : ¬Group.IsProperPower (mk P)) (hQ : ¬Group.IsProperPower (mk Q)) (hwP : IsPeriodicWord P w)
    (hwQ : IsPeriodicWord Q w) (hw : P.length + Q.length - P.length.gcd Q.length ≤ w.length) :
    Q ~r P ∨ Q ~r invRev P := by
  have hg := hwP.hasPeriod.gcd hwQ.hasPeriod hw
  -- the prefix of `w` of length `|X|` is a rotation of `X^{±1}` with the period `gcd(|P|, |Q|)`
  have key {X : List (α × Bool)} (hX : ¬Group.IsProperPower (mk X)) (hwX : IsPeriodicWord X w)
      (hdvd : P.length.gcd Q.length ∣ X.length) : P.length.gcd Q.length = X.length := by
    have hlen : (w.take X.length).length = X.length := by simpa using hwX.length_le
    have hnp : ¬Group.IsProperPower (mk (w.take X.length)) := by
      rcases hwX.take_isRotated with hx | hx
      · rwa [hx.isProperPower_mk_iff]
      · rwa [hx.isProperPower_mk_iff, ← inv_mk, Group.isProperPower_inv]
    have := eq_length_of_hasPeriod hnp (hg.infix (List.take_prefix _ _).isInfix) (by rwa [hlen])
    rwa [hlen] at this
  have hPQ : Q.length = P.length :=
    (key hQ hwQ (Nat.gcd_dvd_right _ _)).symm.trans (key hP hwP (Nat.gcd_dvd_left _ _))
  rcases hwP.take_isRotated with h₁ | h₁ <;> rcases hwQ.take_isRotated with h₂ | h₂ <;>
    rw [hPQ] at h₂
  · exact .inl (h₂.symm.trans h₁)
  · exact .inr (by simpa using (h₂.symm.trans h₁).invRev)
  · exact .inr (h₂.symm.trans h₁)
  · exact .inl (by simpa using (h₂.symm.trans h₁).invRev)

/-! ### Examples -/

/- A word over `{a, b}` whose exponent sum in `b` is `1` is not a proper power. -/
private theorem not_isProperPower_mk_of_lift_eq {w : List (Fin 2 × Bool)}
    (h : lift (fun c => if c = 1 then Multiplicative.ofAdd (1 : ℤ) else 1) (mk w) =
      Multiplicative.ofAdd 1) : ¬Group.IsProperPower (mk w) :=
  fun hw => Group.not_isProperPower_ofAdd_one (h ▸ hw.map _)

/-- The length bound of overlapping periodicities is sharp: in `F(a, b)` the word `aabaa`, of length
`5 < 3 + 4 - gcd(3, 4)`, is both `aab`-periodic and `aaba`-periodic, and neither `aab` nor `aaba`
is a proper power, but `aaba` is not a cyclic permutation of `aab` or of its inverse. -/
example : ¬Group.IsProperPower (mk [((0 : Fin 2), true), (0, true), (1, true)]) ∧
    ¬Group.IsProperPower (mk [((0 : Fin 2), true), (0, true), (1, true), (0, true)]) ∧
    IsPeriodicWord [(0, true), (0, true), (1, true)]
      [((0 : Fin 2), true), (0, true), (1, true), (0, true), (0, true)] ∧
    IsPeriodicWord [(0, true), (0, true), (1, true), (0, true)]
      [((0 : Fin 2), true), (0, true), (1, true), (0, true), (0, true)] ∧
    ¬([((0 : Fin 2), true), (0, true), (1, true), (0, true)] ~r [(0, true), (0, true), (1, true)] ∨
      [((0 : Fin 2), true), (0, true), (1, true), (0, true)] ~r
        invRev [(0, true), (0, true), (1, true)]) :=
  ⟨not_isProperPower_mk_of_lift_eq (by decide), not_isProperPower_mk_of_lift_eq (by decide),
    ⟨by decide, 2, .inl (by decide)⟩, ⟨by decide, 2, .inl (by decide)⟩, by decide⟩

/-- The cut of a periodic word is not unique for a proper power: the word `aa` occurs in `aaaa` at
the positions `0` and `1`, which differ modulo `|aa| = 2`. -/
example : Group.IsProperPower (mk [((0 : Fin 2), true), (0, true)]) ∧
    [((0 : Fin 2), true), (0, true)] <+:
      ((List.replicate 2 [((0 : Fin 2), true), (0, true)]).flatten).drop 0 ∧
    [((0 : Fin 2), true), (0, true)] <+:
      ((List.replicate 2 [((0 : Fin 2), true), (0, true)]).flatten).drop 1 ∧
    ¬0 ≡ 1 [MOD [((0 : Fin 2), true), (0, true)].length] :=
  ⟨Group.isProperPower_iff.2 ⟨of 0, 2, le_rfl, by simp [pow_mk, of]⟩, by decide, by decide,
    by decide⟩

end FreeGroup
