/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import TauCeti.Algebra.Order.SuccPred
public import Mathlib.Tactic.Abel

/-!
# Infinite words over an ordered abelian group

Let `Λ` be a discretely ordered abelian group, i.e. a linearly ordered abelian group with a least
positive element `1`, and let `X` be a set. A *`Λ`-word* (an *infinite word*) over `X` is a function
`w : [1, α] → X^{±1}` on a closed interval `[1, α] = {β | 1 ≤ β ≤ α}` of `Λ`, where `α ≥ 0` is the
*length* `|w|` of `w`. For `Λ = ℤ` these are the finite words in the letters `X^{±1}`; for a
non-Archimedean `Λ` such as `ℤ[t]` they include words like `a^t`, the constant function `a` on
`[1, t]`.

This file defines the type `TauCeti.InfWord Λ X` of all `Λ`-words, with the letters `X^{±1}`
represented as `X × Bool` as for Mathlib's `FreeGroup`, together with

* the empty word `ε`, of length `0`;
* the concatenation `u ++ v`, of length `|u| + |v|`, equal to `u` on `[1, |u|]` and to
  `β ↦ v(β - |u|)` on `[|u| + 1, |u| + |v|]`;
* the inverse `w⁻¹`, of length `|w|`, with `w⁻¹(β) = w(|w| + 1 - β)⁻¹`;
* the initial segment `w.take β`, the restriction of `w` to `[1, β]`, and the complementary final
  segment `w.drop β`, so that `w = w.take β ++ w.drop β`;
* the predicate `TauCeti.InfWord.IsReduced`: `w(β + 1) ≠ w(β)⁻¹` for `1 ≤ β < |w|`, where
  `β + 1` is the successor `Order.succ β` of `β`.

The reduced `Λ`-words form the set `R(Λ, X)` on which Myasnikov, Remeslennikov and Serbin define a
partial multiplication. They write `u ∘ v` for the concatenation of two reduced words when it is
again reduced; `TauCeti.InfWord.isReduced_append_iff` says that this happens exactly when the last
letter of `u` is not the inverse of the first letter of `v`.

## Implementation notes

A word is stored as its length together with a function `letter : Λ → Option (X × Bool)` that is
`none` exactly outside the domain. Two words are therefore equal as soon as they have the same
length and the same letters (`TauCeti.InfWord.ext`), and no dependent types are needed to
concatenate or restrict words.

The domain is written `{β | 0 < β ≤ |w|}`. When `Λ` has no largest element this is the interval
`[succ 0, |w|]` (`TauCeti.InfWord.isSome_letter_iff_mem_Icc`); the formulation with `0 < β` keeps
the domain of the empty word empty also over the trivial group, where `succ 0 = 0`.

The discreteness of `Λ` is Mathlib's `SuccOrder` on a linearly ordered additive commutative group,
and the position `β + 1` is written `Order.succ β`. Since translations commute with `succ`, this is
`β + succ 0` (`TauCeti.Order.succ_eq_add_succ_zero`), so `succ 0` is the least positive element when
there is one. The instance `One Λ` is not used, because it need not be that element: on
`Lex (Fin n → ℤ)` it is the constant function `1`. For `Λ = ℤ`, `Order.succ_eq_add_one` rewrites
`Order.succ β` to `β + 1`.

## Main definitions

* `TauCeti.InfWord Λ X`: the `Λ`-words over `X`, with length `InfWord.length` and letters
  `InfWord.letter`.
* `TauCeti.InfWord.empty`: the empty word.
* `TauCeti.InfWord.ofFun`: the word of a given length with letters given by a function on `Λ`.
* `u ++ v`, `w⁻¹`, `TauCeti.InfWord.take`, `TauCeti.InfWord.drop`: concatenation, inverse, initial
  and final segments.
* `TauCeti.InfWord.IsReduced`: reduced words.

## Main results

* `TauCeti.InfWord.append_assoc`, `TauCeti.InfWord.empty_append`, `TauCeti.InfWord.append_empty`:
  concatenation is associative with unit the empty word.
* `TauCeti.InfWord.append_right_inj`, `TauCeti.InfWord.append_left_inj`: concatenation is
  cancellative on both sides.
* `TauCeti.InfWord.inv_append`: `(u ++ v)⁻¹ = v⁻¹ ++ u⁻¹`; inversion is an involution.
* `TauCeti.InfWord.take_append_drop`: `w.take β ++ w.drop β = w`.
* `TauCeti.InfWord.take_append`, `TauCeti.InfWord.drop_append`: the segments of a concatenation.
* `TauCeti.InfWord.take_take`, `TauCeti.InfWord.drop_drop`: segments of segments.
* `TauCeti.InfWord.inv_take`, `TauCeti.InfWord.inv_drop`: inversion exchanges initial and final
  segments, `(w.take β)⁻¹ = w⁻¹.drop (|w| - β)`.
* `TauCeti.InfWord.isReduced_append_iff`: the criterion for a concatenation to be reduced.
* `TauCeti.InfWord.isReduced_inv`, `TauCeti.InfWord.IsReduced.take`,
  `TauCeti.InfWord.IsReduced.drop`: inverses and segments of reduced words are reduced.
* `TauCeti.InfWord.isReduced_ofFun_const`: the constant word `x^α` is reduced.
* `TauCeti.InfWord.ofFun_const_append_ofFun_const`: `x^α x^β = x^(α + β)` for `α, β ≥ 0`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.1, Definition 3.1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), 325–455, §6.1.
-/

public section

namespace TauCeti

/-- A *`Λ`-word* over `X`: a function `w : [1, α] → X^{±1}` on an interval of an ordered abelian
group `Λ`, where `α ≥ 0` is the length of the word. The letters `X^{±1}` are represented by
`X × Bool`, and the function by `letter : Λ → Option (X × Bool)`, which is `none` exactly outside
the domain `{β | 0 < β ≤ α}`. -/
structure InfWord (Λ X : Type*) [Zero Λ] [Preorder Λ] where
  /-- The length `|w|` of the word. -/
  length : Λ
  /-- The letter at a position, which is `none` outside the domain `{β | 0 < β ≤ |w|}`. -/
  letter : Λ → Option (X × Bool)
  /-- The length is nonnegative. -/
  length_nonneg : 0 ≤ length
  /-- The letters are defined exactly at the positions `0 < β ≤ |w|`. -/
  isSome_letter (β : Λ) : (letter β).isSome ↔ 0 < β ∧ β ≤ length

namespace InfWord

variable {Λ X : Type*}

section Preorder

variable [Zero Λ] [Preorder Λ] {u v w : InfWord Λ X} {β : Λ}

attribute [simp] length_nonneg

attribute [simp, grind =] isSome_letter

grind_pattern length_nonneg => self.length

@[simp, grind =]
theorem letter_eq_none_iff : w.letter β = none ↔ ¬(0 < β ∧ β ≤ w.length) := by
  rw [← w.isSome_letter, Option.not_isSome_iff_eq_none]

theorem letter_eq_none_of_not_pos (h : ¬0 < β) : w.letter β = none :=
  letter_eq_none_iff.2 fun h' => h h'.1

theorem letter_eq_none_of_not_le (h : ¬β ≤ w.length) : w.letter β = none :=
  letter_eq_none_iff.2 fun h' => h h'.2

/-- Two words are equal when they have the same length and the same letters. -/
@[ext]
theorem ext (hlen : u.length = v.length)
    (h : ∀ β, 0 < β → β ≤ u.length → u.letter β = v.letter β) : u = v := by
  obtain ⟨lu, fu, hu, hfu⟩ := u
  obtain ⟨lv, fv, hv, hfv⟩ := v
  obtain rfl : lu = lv := hlen
  obtain rfl : fu = fv := by
    funext β
    by_cases hβ : 0 < β ∧ β ≤ lu
    · exact h β hβ.1 hβ.2
    · rw [Option.not_isSome_iff_eq_none.1 (mt (hfu β).1 hβ),
        Option.not_isSome_iff_eq_none.1 (mt (hfv β).1 hβ)]
  rfl

variable (Λ X) in
/-- The empty word `ε`, of length `0`. -/
def empty : InfWord Λ X where
  length := 0
  letter _ := none
  length_nonneg := le_rfl
  isSome_letter β := by simpa using fun h : 0 < β => h.not_ge

instance : Inhabited (InfWord Λ X) := ⟨empty Λ X⟩

@[simp, grind =] theorem length_empty : (empty Λ X).length = 0 := (rfl)

@[simp, grind =] theorem letter_empty (β : Λ) : (empty Λ X).letter β = none := (rfl)

@[simp]
theorem length_eq_zero_iff : w.length = 0 ↔ w = empty Λ X := by
  refine ⟨fun h => ext (by simp [h]) fun β h0 hβ => ?_, fun h => by simp [h]⟩
  exact absurd (h ▸ hβ) h0.not_ge

end Preorder

section PartialOrder

variable [Zero Λ] [PartialOrder Λ] {w : InfWord Λ X}

@[simp]
theorem length_pos_iff : 0 < w.length ↔ w ≠ empty Λ X :=
  w.length_nonneg.lt_iff_ne'.trans (not_congr length_eq_zero_iff)

@[simp]
theorem length_nonpos_iff : w.length ≤ 0 ↔ w = empty Λ X :=
  w.length_nonneg.ge_iff_eq'.trans length_eq_zero_iff

end PartialOrder

section LinearOrder

variable [Zero Λ] [LinearOrder Λ]

/-- The word of length `max α 0` with letter `f β` at each position `0 < β ≤ α`. -/
def ofFun (α : Λ) (f : Λ → X × Bool) : InfWord Λ X where
  length := max α 0
  letter β := if 0 < β ∧ β ≤ α then some (f β) else none
  length_nonneg := le_max_right _ _
  isSome_letter β := by split_ifs with h <;> grind

@[simp, grind =]
theorem length_ofFun (α : Λ) (f : Λ → X × Bool) : (ofFun α f).length = max α 0 := (rfl)

@[grind =]
theorem letter_ofFun (α : Λ) (f : Λ → X × Bool) (β : Λ) :
    (ofFun α f).letter β = if 0 < β ∧ β ≤ α then some (f β) else none := (rfl)

theorem letter_ofFun_of_pos_of_le {α β : Λ} (f : Λ → X × Bool) (h0 : 0 < β) (hβ : β ≤ α) :
    (ofFun α f).letter β = some (f β) := by
  simp [letter_ofFun, h0, hβ]

@[simp]
theorem ofFun_eq_empty_iff {α : Λ} {f : Λ → X × Bool} : ofFun α f = empty Λ X ↔ α ≤ 0 := by
  simp [← length_eq_zero_iff]

theorem ofFun_of_nonpos {α : Λ} (f : Λ → X × Bool) (h : α ≤ 0) : ofFun α f = empty Λ X :=
  ofFun_eq_empty_iff.2 h

@[simp]
theorem ofFun_zero (f : Λ → X × Bool) : ofFun 0 f = empty Λ X :=
  ofFun_of_nonpos f le_rfl

@[simp]
theorem ofFun_max_zero (α : Λ) (f : Λ → X × Bool) : ofFun (max α 0) f = ofFun α f :=
  ext (by simp) fun _ _ _ => by grind

@[simp]
theorem ofFun_zero_max (α : Λ) (f : Λ → X × Bool) : ofFun (max 0 α) f = ofFun α f := by
  rw [max_comm, ofFun_max_zero]

/-- The word `ofFun α f` only depends on the values of `f` on its domain `{β | 0 < β ≤ α}`. -/
theorem ofFun_congr {α : Λ} {f g : Λ → X × Bool} (h : ∀ β, 0 < β → β ≤ α → f β = g β) :
    ofFun α f = ofFun α g :=
  ext rfl fun _ _ _ => by simp +contextual [letter_ofFun, h]

/-- The initial segment `w|_β` of a word: its restriction to the positions `≤ β`. -/
def take (w : InfWord Λ X) (β : Λ) : InfWord Λ X where
  length := max 0 (min β w.length)
  letter γ := if γ ≤ β then w.letter γ else none
  length_nonneg := le_max_left _ _
  isSome_letter γ := by split_ifs <;> grind

@[simp, grind =]
theorem length_take (w : InfWord Λ X) (β : Λ) :
    (w.take β).length = max 0 (min β w.length) := (rfl)

theorem length_take_of_le {w : InfWord Λ X} {β : Λ} (h0 : 0 ≤ β) (hβ : β ≤ w.length) :
    (w.take β).length = β := by
  simp [h0, hβ]

@[grind =]
theorem letter_take (w : InfWord Λ X) (β γ : Λ) :
    (w.take β).letter γ = if γ ≤ β then w.letter γ else none := (rfl)

@[simp]
theorem letter_take_of_le (w : InfWord Λ X) {β γ : Λ} (h : γ ≤ β) :
    (w.take β).letter γ = w.letter γ := by
  simp [letter_take, h]

theorem take_of_nonpos (w : InfWord Λ X) {β : Λ} (h : β ≤ 0) : w.take β = empty Λ X := by
  simp [← length_eq_zero_iff, h]

@[simp]
theorem take_zero (w : InfWord Λ X) : w.take 0 = empty Λ X :=
  w.take_of_nonpos le_rfl

theorem take_of_length_le (w : InfWord Λ X) {β : Λ} (h : w.length ≤ β) : w.take β = w :=
  ext (by simp [min_eq_right h]) fun _ _ hγ => w.letter_take_of_le (by simp at hγ; grind)

@[simp]
theorem take_length (w : InfWord Λ X) : w.take w.length = w :=
  w.take_of_length_le le_rfl

@[simp]
theorem take_max_zero (w : InfWord Λ X) (β : Λ) : w.take (max β 0) = w.take β :=
  ext (by simp; grind) fun _ _ _ => by grind

@[simp]
theorem take_zero_max (w : InfWord Λ X) (β : Λ) : w.take (max 0 β) = w.take β := by
  rw [max_comm, take_max_zero]

@[simp]
theorem take_empty (β : Λ) : (empty Λ X).take β = empty Λ X := by
  simp [← length_eq_zero_iff]

@[simp]
theorem take_take (w : InfWord Λ X) (β γ : Λ) : (w.take β).take γ = w.take (min γ β) :=
  ext (by simp; grind) fun _ _ _ => by grind

@[simp]
theorem take_eq_empty_iff {w : InfWord Λ X} {β : Λ} :
    w.take β = empty Λ X ↔ β ≤ 0 ∨ w = empty Λ X := by
  simp only [← length_eq_zero_iff, length_take]
  grind

@[simp]
theorem take_eq_self_iff {w : InfWord Λ X} {β : Λ} :
    w.take β = w ↔ w.length ≤ β ∨ w = empty Λ X := by
  refine ⟨fun h => ?_, by rintro (h | rfl) <;> simp [take_of_length_le, *]⟩
  rw [← length_eq_zero_iff]
  grind

@[simp]
theorem take_ofFun (α β : Λ) (f : Λ → X × Bool) : (ofFun α f).take β = ofFun (min β α) f :=
  ext (by simp; grind) fun _ _ _ => by grind

end LinearOrder

section IsReduced

variable [Zero Λ] [Preorder Λ] [SuccOrder Λ] {w : InfWord Λ X}

/-- A word is *reduced* if no letter is followed by its inverse: `w(β + 1) ≠ w(β)⁻¹` for
`1 ≤ β < |w|`, where `β + 1` is the successor `Order.succ β` of `β`. -/
def IsReduced (w : InfWord Λ X) : Prop :=
  ∀ β, 0 < β → β < w.length → w.letter (Order.succ β) ≠ (w.letter β).map (Prod.map id not)

theorem isReduced_iff : w.IsReduced ↔ ∀ β, 0 < β → β < w.length →
    w.letter (Order.succ β) ≠ (w.letter β).map (Prod.map id not) := Iff.rfl

@[simp]
theorem isReduced_empty : (empty Λ X).IsReduced := fun _ h0 h => (h0.not_gt h).elim

/-- When there is no largest element, as in a nontrivial discretely ordered abelian group, the
domain of a word is the interval `[succ 0, |w|]`. -/
theorem isSome_letter_iff_mem_Icc [NoMaxOrder Λ] {β : Λ} :
    (w.letter β).isSome ↔ β ∈ Set.Icc (Order.succ 0) w.length := by
  rw [isSome_letter, Set.mem_Icc, Order.succ_le_iff]

end IsReduced

section LinearOrder

variable [Zero Λ] [LinearOrder Λ] [SuccOrder Λ] {w : InfWord Λ X} {α : Λ}

theorem isReduced_ofFun_iff {f : Λ → X × Bool} : (ofFun α f).IsReduced ↔
    ∀ β, 0 < β → β < α → f (Order.succ β) ≠ Prod.map id not (f β) := by
  refine forall_congr' fun β => forall_congr' fun h0 => ?_
  by_cases hβ : β < α
  · simp [letter_ofFun, h0, hβ, hβ.le, Order.succ_le_of_lt hβ, h0.trans_le (Order.le_succ β)]
  · simp only [length_ofFun, hβ, false_imp_iff, iff_true]
    grind

/-- The constant word `x^α`, with the letter `x` at every position of `[1, α]`, is reduced. -/
@[simp]
theorem isReduced_ofFun_const (α : Λ) (x : X × Bool) : (ofFun α fun _ => x).IsReduced := by
  simp [isReduced_ofFun_iff, Prod.ext_iff]

theorem IsReduced.take (h : w.IsReduced) (β : Λ) : (w.take β).IsReduced := by
  intro γ h0 hγ
  obtain ⟨hγβ, hγw⟩ : γ < β ∧ γ < w.length := by simp at hγ; grind
  rw [letter_take_of_le _ (Order.succ_le_of_lt hγβ), letter_take_of_le _ hγβ.le]
  exact h γ h0 hγw

end LinearOrder

section Group

variable [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] {u v w : InfWord Λ X} {β : Λ}

/-- Concatenation of words. -/
instance : Append (InfWord Λ X) where
  append u v :=
    { length := u.length + v.length
      letter β := if β ≤ u.length then u.letter β else v.letter (β - u.length)
      length_nonneg := add_nonneg u.length_nonneg v.length_nonneg
      isSome_letter β := by split_ifs <;> grind }

@[simp, grind =]
theorem length_append (u v : InfWord Λ X) : (u ++ v).length = u.length + v.length := (rfl)

@[grind =]
theorem letter_append (u v : InfWord Λ X) (β : Λ) :
    (u ++ v).letter β = if β ≤ u.length then u.letter β else v.letter (β - u.length) := (rfl)

theorem letter_append_of_le (v : InfWord Λ X) (h : β ≤ u.length) :
    (u ++ v).letter β = u.letter β := by
  simp [letter_append, h]

theorem letter_append_of_lt (v : InfWord Λ X) (h : u.length < β) :
    (u ++ v).letter β = v.letter (β - u.length) := by
  simp [letter_append, h.not_ge]

@[simp]
theorem letter_append_add_length (u v : InfWord Λ X) (h : 0 < β) :
    (u ++ v).letter (β + u.length) = v.letter β := by
  rw [letter_append_of_lt _ (by grind), add_sub_cancel_right]

@[simp]
theorem letter_append_length_add (u v : InfWord Λ X) (h : 0 < β) :
    (u ++ v).letter (u.length + β) = v.letter β := by
  rw [add_comm, letter_append_add_length _ _ h]

@[simp]
theorem empty_append (w : InfWord Λ X) : empty Λ X ++ w = w :=
  ext (by simp) fun _ h0 _ => by simp [letter_append, h0.not_ge]

@[simp]
theorem append_empty (w : InfWord Λ X) : w ++ empty Λ X = w :=
  ext (by simp) fun β _ hβ => by simp [letter_append, show β ≤ w.length by simpa using hβ]

@[simp]
theorem append_assoc (u v w : InfWord Λ X) : u ++ v ++ w = u ++ (v ++ w) := by
  refine ext (by simp [add_assoc]) fun β _ _ => ?_
  simp only [letter_append, length_append]
  split_ifs <;> first | rfl | (exfalso; grind) | rw [sub_sub]

@[simp]
theorem append_right_inj (u : InfWord Λ X) : u ++ v = u ++ w ↔ v = w := by
  refine ⟨fun h => ext ?_ fun β h0 _ => ?_, fun h => h ▸ rfl⟩
  · simpa using congrArg length h
  · simpa [h0] using congrArg (letter · (β + u.length)) h

@[simp]
theorem append_left_inj (u : InfWord Λ X) : v ++ u = w ++ u ↔ v = w := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hlen : v.length = w.length := by simpa using congrArg length h
  refine ext hlen fun β _ hβ => ?_
  simpa [letter_append, hβ, hlen ▸ hβ] using congrArg (letter · β) h

@[simp]
theorem append_eq_empty_iff : u ++ v = empty Λ X ↔ u = empty Λ X ∧ v = empty Λ X := by
  simp_rw [← length_eq_zero_iff, length_append]
  exact add_eq_zero_iff_of_nonneg u.length_nonneg v.length_nonneg

@[simp]
theorem append_left_eq_self : u ++ v = v ↔ u = empty Λ X := by
  refine ⟨fun h => ?_, fun h => h ▸ empty_append v⟩
  simpa [← length_eq_zero_iff] using congrArg length h

@[simp]
theorem self_eq_append_left : v = u ++ v ↔ u = empty Λ X :=
  eq_comm.trans append_left_eq_self

@[simp]
theorem append_right_eq_self : u ++ v = u ↔ v = empty Λ X := by
  refine ⟨fun h => ?_, fun h => h ▸ append_empty u⟩
  simpa [← length_eq_zero_iff] using congrArg length h

@[simp]
theorem self_eq_append_right : u = u ++ v ↔ v = empty Λ X :=
  eq_comm.trans append_right_eq_self

/-- For `α, β ≥ 0` the concatenation `ofFun α f ++ ofFun β g` is the word of length `α + β` that
reads `f` on `[1, α]` and `γ ↦ g (γ - α)` on `[α + 1, α + β]`. -/
theorem ofFun_append_ofFun {α : Λ} (f g : Λ → X × Bool) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ofFun α f ++ ofFun β g = ofFun (α + β) fun γ => if γ ≤ α then f γ else g (γ - α) :=
  ext (by simp; grind) fun _ _ _ => by grind

/-- The constant word `x^α x^β` is `x^(α + β)`. -/
theorem ofFun_const_append_ofFun_const {α : Λ} (x : X × Bool) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (ofFun α fun _ => x) ++ ofFun β (fun _ => x) = ofFun (α + β) fun _ => x := by
  simp [ofFun_append_ofFun _ _ hα hβ]

/-- The final segment of a word complementary to `w.take β`: for `0 ≤ β` the letter of `w.drop β`
at a position `γ > 0` is the letter of `w` at `γ + β`, and `w.drop β = w` for `β ≤ 0`. -/
def drop (w : InfWord Λ X) (β : Λ) : InfWord Λ X where
  length := w.length - max 0 (min β w.length)
  letter γ := if 0 < γ then w.letter (γ + max 0 β) else none
  length_nonneg := by grind
  isSome_letter γ := by split_ifs <;> grind

@[simp, grind =]
theorem length_drop (w : InfWord Λ X) (β : Λ) :
    (w.drop β).length = w.length - max 0 (min β w.length) := (rfl)

theorem length_drop_of_le {w : InfWord Λ X} {β : Λ} (h0 : 0 ≤ β) (hβ : β ≤ w.length) :
    (w.drop β).length = w.length - β := by
  simp [h0, hβ]

@[grind =]
theorem letter_drop (w : InfWord Λ X) (β γ : Λ) :
    (w.drop β).letter γ = if 0 < γ then w.letter (γ + max 0 β) else none := (rfl)

@[simp]
theorem letter_drop_of_pos (w : InfWord Λ X) (β : Λ) {γ : Λ} (h : 0 < γ) :
    (w.drop β).letter γ = w.letter (γ + max 0 β) := by
  simp [letter_drop, h]

/-- A word is the concatenation of its initial segment `w.take β` and the complementary final
segment `w.drop β`. -/
@[simp]
theorem take_append_drop (w : InfWord Λ X) (β : Λ) : w.take β ++ w.drop β = w := by
  refine ext (by simp) fun γ _ hγ => ?_
  simp only [length_append, length_take, length_drop] at hγ
  simp only [letter_append, letter_take, letter_drop, length_take]
  split_ifs <;> first | rfl | (exfalso; grind) | (congr 1; grind)

theorem drop_of_nonpos (w : InfWord Λ X) (h : β ≤ 0) : w.drop β = w := by
  simpa [w.take_of_nonpos h] using w.take_append_drop β

@[simp]
theorem drop_zero (w : InfWord Λ X) : w.drop 0 = w :=
  w.drop_of_nonpos le_rfl

theorem drop_of_length_le (w : InfWord Λ X) (h : w.length ≤ β) : w.drop β = empty Λ X := by
  rw [← length_eq_zero_iff, length_drop, min_eq_right h, max_eq_right w.length_nonneg, sub_self]

@[simp]
theorem drop_length (w : InfWord Λ X) : w.drop w.length = empty Λ X :=
  w.drop_of_length_le le_rfl

@[simp]
theorem drop_max_zero (w : InfWord Λ X) (β : Λ) : w.drop (max β 0) = w.drop β :=
  ext (by simp; grind) fun _ _ _ => by grind

@[simp]
theorem drop_zero_max (w : InfWord Λ X) (β : Λ) : w.drop (max 0 β) = w.drop β := by
  rw [max_comm, drop_max_zero]

@[simp]
theorem drop_empty (β : Λ) : (empty Λ X).drop β = empty Λ X := by
  simp [← length_eq_zero_iff]

@[simp]
theorem drop_eq_empty_iff : w.drop β = empty Λ X ↔ w.length ≤ β ∨ w = empty Λ X := by
  simp only [← length_eq_zero_iff, length_drop]
  grind

@[simp]
theorem drop_eq_self_iff : w.drop β = w ↔ β ≤ 0 ∨ w = empty Λ X := by
  refine ⟨fun h => ?_, by rintro (h | rfl) <;> simp [drop_of_nonpos, *]⟩
  rw [← length_eq_zero_iff]
  grind

theorem drop_ofFun {α : Λ} (f : Λ → X × Bool) (hβ : 0 ≤ β) :
    (ofFun α f).drop β = ofFun (α - β) fun γ => f (γ + β) :=
  ext (by simp; grind) fun _ _ _ => by grind

theorem drop_drop (w : InfWord Λ X) {γ : Λ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    (w.drop β).drop γ = w.drop (β + γ) :=
  ext (by simp; grind) fun δ h0 _ => by
    rw [letter_drop_of_pos _ _ h0, letter_drop_of_pos _ _ h0,
      letter_drop_of_pos _ _ (add_pos_of_pos_of_nonneg h0 (le_max_left _ _)), max_eq_right hβ,
      max_eq_right hγ, max_eq_right (add_nonneg hβ hγ), add_assoc, add_comm γ]

theorem take_append (u v : InfWord Λ X) (β : Λ) :
    (u ++ v).take β = u.take β ++ v.take (β - u.length) :=
  ext (by simp; grind) fun _ _ _ => by grind

theorem take_append_of_le_length (v : InfWord Λ X) (h : β ≤ u.length) :
    (u ++ v).take β = u.take β := by
  rw [take_append, v.take_of_nonpos (sub_nonpos.2 h), append_empty]

theorem take_append_length_add (u v : InfWord Λ X) (h : 0 ≤ β) :
    (u ++ v).take (u.length + β) = u ++ v.take β := by
  rw [take_append, u.take_of_length_le (le_add_of_nonneg_right h), add_sub_cancel_left]

theorem drop_append (u v : InfWord Λ X) (β : Λ) :
    (u ++ v).drop β = u.drop β ++ v.drop (β - u.length) := by
  rw [← append_right_inj ((u ++ v).take β), take_append_drop, take_append]
  rcases le_total β u.length with h | h
  · rw [v.take_of_nonpos (sub_nonpos.2 h), v.drop_of_nonpos (sub_nonpos.2 h), append_empty,
      ← append_assoc, take_append_drop]
  · rw [u.take_of_length_le h, u.drop_of_length_le h, empty_append, append_assoc,
      take_append_drop]

theorem drop_append_of_le_length (v : InfWord Λ X) (h : β ≤ u.length) :
    (u ++ v).drop β = u.drop β ++ v := by
  rw [drop_append, v.drop_of_nonpos (sub_nonpos.2 h)]

theorem drop_append_length_add (u v : InfWord Λ X) (h : 0 ≤ β) :
    (u ++ v).drop (u.length + β) = v.drop β := by
  rw [drop_append, u.drop_of_length_le (le_add_of_nonneg_right h), add_sub_cancel_left,
    empty_append]

@[simp]
theorem take_append_length (u v : InfWord Λ X) : (u ++ v).take u.length = u := by
  rw [take_append_of_le_length _ le_rfl, take_length]

@[simp]
theorem drop_append_length (u v : InfWord Λ X) : (u ++ v).drop u.length = v := by
  rw [drop_append_of_le_length _ le_rfl, drop_length, empty_append]

end Group

section Discrete

variable [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]
  {u v w : InfWord Λ X} {β : Λ}

/-- The inverse of a word: `w⁻¹(β) = w(|w| + 1 - β)⁻¹`, where `|w| + 1` is the successor
`Order.succ |w|` of the length. -/
instance : Inv (InfWord Λ X) where
  inv w :=
    { length := w.length
      letter β := (w.letter (Order.succ w.length - β)).map (Prod.map id not)
      length_nonneg := w.length_nonneg
      isSome_letter β := by
        simp only [Option.isSome_map, isSome_letter]
        grind [Order.succ_eq_add_succ_zero, Order.le_of_lt_succ, Order.lt_succ_of_not_isMax,
          not_isMax_of_lt] }

@[simp, grind =] theorem length_inv (w : InfWord Λ X) : w⁻¹.length = w.length := (rfl)

@[grind =]
theorem letter_inv (w : InfWord Λ X) (β : Λ) :
    w⁻¹.letter β = (w.letter (Order.succ w.length - β)).map (Prod.map id not) := (rfl)

instance : InvolutiveInv (InfWord Λ X) where
  inv_inv w := ext (by simp) fun β _ _ => by
    simp [letter_inv, Function.comp_def, Prod.map]

@[simp]
theorem inv_empty : (empty Λ X)⁻¹ = empty Λ X := by
  simp [← length_eq_zero_iff]

@[simp]
theorem inv_eq_empty_iff : w⁻¹ = empty Λ X ↔ w = empty Λ X := by
  simp [← length_eq_zero_iff]

/-- The inverse of `ofFun α f` reads the inverses of the letters of `f` backwards:
`(ofFun α f)⁻¹(γ) = f(α + 1 - γ)⁻¹`. -/
theorem inv_ofFun (α : Λ) (f : Λ → X × Bool) :
    (ofFun α f)⁻¹ = ofFun α fun γ => Prod.map id not (f (Order.succ α - γ)) :=
  ext (by simp) fun _ _ _ => by
    grind [Order.succ_eq_add_succ_zero, Order.le_of_lt_succ, Order.lt_succ_of_not_isMax,
      not_isMax_of_lt]

@[simp]
theorem inv_append (u v : InfWord Λ X) : (u ++ v)⁻¹ = v⁻¹ ++ u⁻¹ := by
  refine ext (by simp [add_comm]) fun β h0 _ => ?_
  simp only [letter_inv, letter_append, length_append, length_inv]
  split_ifs <;> first
    | (exfalso; grind [Order.succ_eq_add_succ_zero, Order.le_of_lt_succ,
        Order.lt_succ_of_not_isMax, not_isMax_of_lt])
    | (congr 2; grind [Order.succ_eq_add_succ_zero])

/-- Inversion turns the initial segment of length `β` into the final segment of `w⁻¹` of the same
length. -/
theorem inv_take (w : InfWord Λ X) (β : Λ) : (w.take β)⁻¹ = w⁻¹.drop (w.length - β) := by
  refine ext (by simp; grind) fun γ h0 hγ => ?_
  simp only [length_inv, length_take] at hγ
  simp only [letter_inv, letter_take, letter_drop, length_take, h0, ↓reduceIte]
  split_ifs <;> first
    | (exfalso; grind [Order.succ_eq_add_succ_zero, Order.le_of_lt_succ,
        Order.lt_succ_of_not_isMax, not_isMax_of_lt])
    | (congr 2; grind [Order.succ_eq_add_succ_zero])

/-- Inversion turns the final segment `w.drop β` into the initial segment of `w⁻¹` of the same
length. -/
theorem inv_drop (w : InfWord Λ X) (β : Λ) : (w.drop β)⁻¹ = w⁻¹.take (w.length - β) := by
  rw [inv_eq_iff_eq_inv, inv_take, inv_inv, length_inv, sub_sub_cancel]

theorem IsReduced.inv (h : w.IsReduced) : w⁻¹.IsReduced := by
  intro β h0 hβ h'
  rw [letter_inv, letter_inv, Option.map_map, Order.succ_eq_add_succ_zero β,
    Order.succ_eq_add_succ_zero w.length,
    show w.length + Order.succ 0 - (β + Order.succ 0) = w.length - β by abel,
    show w.length + Order.succ 0 - β = Order.succ (w.length - β) by
      rw [Order.succ_eq_add_succ_zero (w.length - β)]; abel] at h'
  refine h (w.length - β) (by simpa using hβ) (by simpa using h0) ?_
  rw [h']
  simp [Function.comp_def, Prod.map]

@[simp]
theorem isReduced_inv : w⁻¹.IsReduced ↔ w.IsReduced :=
  ⟨fun h => by simpa using h.inv, IsReduced.inv⟩

theorem IsReduced.left_of_append (h : (u ++ v).IsReduced) : u.IsReduced := by
  intro β h0 hβ
  have := h β h0 (by simpa using hβ.trans_le (le_add_of_nonneg_right v.length_nonneg))
  rwa [letter_append_of_le _ (Order.succ_le_of_lt hβ), letter_append_of_le _ hβ.le] at this

theorem IsReduced.right_of_append (h : (u ++ v).IsReduced) : v.IsReduced := by
  intro β h0 hβ
  have := h (u.length + β) (add_pos_of_nonneg_of_pos u.length_nonneg h0) (by simpa using hβ)
  rwa [← Order.add_succ, letter_append_length_add _ _ (h0.trans_le (Order.le_succ β)),
    letter_append_length_add _ _ h0] at this

/-- In a reduced concatenation the last letter of the first word is not the inverse of the first
letter of the second. -/
theorem IsReduced.letter_succ_zero_ne_of_append (h : (u ++ v).IsReduced) (hu : 0 < u.length)
    (hv : 0 < v.length) :
    v.letter (Order.succ 0) ≠ (u.letter u.length).map (Prod.map id not) := by
  have := h u.length hu (by simpa using hv)
  rwa [Order.succ_eq_add_succ_zero, letter_append_length_add _ _
    (Order.lt_succ_of_not_isMax (not_isMax_of_lt hu)), letter_append_of_le _ le_rfl] at this

/-- The concatenation `u ++ v` of two words is reduced, written `u ∘ v`, exactly when `u` and `v`
are reduced and the last letter of `u` is not the inverse of the first letter of `v`. -/
theorem isReduced_append_iff : (u ++ v).IsReduced ↔ u.IsReduced ∧ v.IsReduced ∧
    (0 < u.length → 0 < v.length →
      v.letter (Order.succ 0) ≠ (u.letter u.length).map (Prod.map id not)) := by
  refine ⟨fun h => ⟨h.left_of_append, h.right_of_append, h.letter_succ_zero_ne_of_append⟩, ?_⟩
  rintro ⟨hu, hv, huv⟩ β h0 hβ
  rw [length_append] at hβ
  rcases lt_trichotomy β u.length with h | rfl | h
  · rw [letter_append_of_le _ (Order.succ_le_of_lt h), letter_append_of_le _ h.le]
    exact hu β h0 h
  · rw [Order.succ_eq_add_succ_zero, letter_append_length_add _ _
      (Order.lt_succ_of_not_isMax (not_isMax_of_lt h0)), letter_append_of_le _ le_rfl]
    exact huv h0 (by simpa using hβ)
  · obtain ⟨γ, rfl⟩ : ∃ γ, β = u.length + γ := ⟨β - u.length, by abel⟩
    have hγ : 0 < γ := by simpa using h
    rw [← Order.add_succ, letter_append_length_add _ _ (hγ.trans_le (Order.le_succ γ)),
      letter_append_length_add _ _ hγ]
    exact hv γ hγ (by simpa using hβ)

theorem IsReduced.drop (h : w.IsReduced) (β : Λ) : (w.drop β).IsReduced :=
  IsReduced.right_of_append (u := w.take β) (by rwa [take_append_drop])

end Discrete

end InfWord

end TauCeti
