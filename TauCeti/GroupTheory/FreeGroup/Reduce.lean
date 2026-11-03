/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Reduced words in free groups

Elementary facts about reduced words complementing `Mathlib.GroupTheory.FreeGroup.Reduce`:
the formal inverse of a one-letter word, uniqueness of reduced representatives, reducedness of
formal inverses, and reducedness of words `w u w⁻¹` in which no letter cancels at either join.

The last section controls cancellation under left multiplication: if the reduced word of `g` does
not begin with the formal inverse of `x₂`, then the reduced word of `(x₁ ++ x₂) * g` still begins
with `x₁` whenever `x₁ ++ x₂` is reduced. This is the prefix calculus behind ping-pong arguments
on reduced words, such as the big powers property of free groups.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- The inverse of a one-letter word is the inverse letter. -/
theorem inv_mk_singleton (w : α × Bool) : (mk [w])⁻¹ = mk [(w.1, !w.2)] := by
  simp [inv_mk, invRev]

/-- Reduced words representing the same element of a free group are equal. -/
theorem IsReduced.eq_of_mk_eq {u v : List (α × Bool)} (hu : IsReduced u) (hv : IsReduced v)
    (h : mk u = mk v) : u = v := by
  classical
  rw [← hu.reduce_eq, ← hv.reduce_eq, reduce.sound h]

/-- The formal inverse of a reduced word is reduced. -/
theorem IsReduced.invRev {w : List (α × Bool)} (hw : IsReduced w) :
    IsReduced (invRev w) := by
  classical
  have h := isReduced_toWord (x := mk (FreeGroup.invRev w))
  rwa [toWord_mk, reduce_invRev, hw.reduce_eq] at h

/-- A formal inverse is reduced exactly when the original word is. -/
@[simp]
theorem isReduced_invRev {w : List (α × Bool)} : IsReduced (invRev w) ↔ IsReduced w :=
  ⟨fun h => by simpa using IsReduced.invRev h, IsReduced.invRev⟩

/-- If `w` and the nonempty word `u` are reduced, the last letter of `w` does not cancel against
the first letter of `u`, and the last letter of `u` does not cancel against the first letter of
`invRev w`, then `w ++ u ++ invRev w` is reduced. -/
theorem IsReduced.append_append_invRev {w u : List (α × Bool)} (hw : IsReduced w)
    (hu : IsReduced u) (hu₀ : u ≠ [])
    (hhead : ∀ a ∈ w.getLast?, (a.1, !a.2) ∉ u.head?)
    (hlast : ∀ a ∈ w.getLast?, a ∉ u.getLast?) :
    IsReduced (w ++ u ++ FreeGroup.invRev w) := by
  refine List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨hw, hu, ?_⟩, hw.invRev, ?_⟩
  · intro x hx y hy hxy
    have := hhead x hx
    rw [Option.mem_def.mp hy] at this
    cases x; cases y
    simp_all
  · intro x hx y hy hxy
    rw [List.getLast?_append_of_ne_nil _ hu₀] at hx
    simp only [FreeGroup.invRev, List.head?_reverse, List.getLast?_map, Option.mem_def,
      Option.map_eq_some_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := hlast z hz
    rw [Option.mem_def.mp hx] at this
    cases x; cases z
    simp_all [Bool.eq_not]

section Prefix

open List

variable [DecidableEq α]

/-- If the reduced word of `g` begins with the formal inverse of `x`, then left multiplication by
`x` cancels that prefix. -/
theorem toWord_mk_mul_of_invRev_prefix {x : List (α × Bool)} {g : FreeGroup α}
    (h : invRev x <+: g.toWord) : (mk x * g).toWord = g.toWord.drop x.length := by
  obtain ⟨y, hy⟩ := h
  have hred : IsReduced y := isReduced_toWord.infix ⟨invRev x, [], by rw [append_nil, hy]⟩
  have hmul : mk x * g = mk y := by
    rw [← mk_toWord (x := g), ← hy, ← mul_mk, ← inv_mk]
    exact mul_inv_cancel_left _ _
  rw [hmul, toWord_mk, hred.reduce_eq, ← hy, drop_left' invRev_length]

omit [DecidableEq α] in
/-- In a reduced word, a letter is never followed by its inverse. -/
theorem ne_inv_of_isReduced_cons_cons {a b : α × Bool} {l : List (α × Bool)}
    (h : IsReduced (a :: b :: l)) : b ≠ (a.1, !a.2) := by
  rintro rfl
  simpa using (isReduced_cons_cons.1 h).1 rfl

/-- Left multiplication by a letter that does not cancel prepends it to the reduced word. -/
theorem toWord_mk_singleton_mul_of_head?_ne {a : α × Bool} {g : FreeGroup α}
    (h : g.toWord.head? ≠ some (a.1, !a.2)) : (mk [a] * g).toWord = a :: g.toWord := by
  obtain ⟨a₁, a₂⟩ := a
  simp [toWord_mk_mul_eq, h]

/-- If `x` is reduced and the reduced word of `g` does not begin with the formal inverse of `x`,
then the first letter of `x` survives in the reduced word of `x * g`. -/
theorem head?_toWord_mk_mul {x : List (α × Bool)} {g : FreeGroup α} (hx : IsReduced x)
    (h : ¬invRev x <+: g.toWord) : (mk x * g).toWord.head? = x.head? := by
  induction x with
  | nil => simp [invRev] at h
  | cons b x ih =>
    rw [← singleton_append, ← mul_mk, mul_assoc]
    suffices hb : (mk x * g).toWord.head? ≠ some (b.1, !b.2) by
      rw [toWord_mk_singleton_mul_of_head?_ne hb, head?_cons, singleton_append, head?_cons]
    by_cases hx' : invRev x <+: g.toWord
    · -- The word `x` cancels completely; the letter after it is not `b⁻¹`.
      rw [toWord_mk_mul_of_invRev_prefix hx']
      intro hhead
      apply h
      obtain ⟨y, hy⟩ := hx'
      rw [← hy, drop_left' invRev_length] at hhead
      obtain ⟨y', rfl⟩ : ∃ y', y = (b.1, !b.2) :: y' := ⟨y.tail, (cons_head?_tail hhead).symm⟩
      exact ⟨y', by simpa [invRev_cons, invRev] using hy⟩
    · -- The word `x` is not cancelled, so its first letter survives and is not `b⁻¹`.
      cases x with
      | nil => simp [invRev] at hx'
      | cons c x =>
        rw [ih (hx.infix ⟨[b], [], by simp⟩) hx', head?_cons, Ne, Option.some_inj]
        exact ne_inv_of_isReduced_cons_cons hx

/-- If `x₁ ++ x₂` is reduced and the reduced word of `g` does not begin with the formal inverse of
`x₂`, then the reduced word of `(x₁ ++ x₂) * g` begins with `x₁`: the cancellation between the
two factors stops inside `x₂`. -/
theorem prefix_toWord_mk_append_mul {x₁ x₂ : List (α × Bool)} {g : FreeGroup α}
    (hx : IsReduced (x₁ ++ x₂)) (h : ¬invRev x₂ <+: g.toWord) :
    x₁ <+: (mk (x₁ ++ x₂) * g).toWord := by
  induction x₁ with
  | nil => exact nil_prefix
  | cons a x₁ ih =>
    have hx' : IsReduced (x₁ ++ x₂) := hx.infix ⟨[a], [], by simp⟩
    have hhead : (mk (x₁ ++ x₂) * g).toWord.head? ≠ some (a.1, !a.2) := by
      cases x₁ with
      | cons b x₁ =>
        obtain ⟨z, hz⟩ := ih hx'
        rw [← hz, cons_append, head?_cons, Ne, Option.some_inj]
        exact ne_inv_of_isReduced_cons_cons hx
      | nil =>
        rw [nil_append] at hx' ⊢
        rw [head?_toWord_mk_mul hx' h]
        cases x₂ with
        | nil => simp [invRev] at h
        | cons b x₂ =>
          rw [head?_cons, Ne, Option.some_inj]
          exact ne_inv_of_isReduced_cons_cons hx
    rw [cons_append, ← singleton_append (l := x₁ ++ x₂), ← mul_mk, mul_assoc,
      toWord_mk_singleton_mul_of_head?_ne hhead]
    exact (prefix_cons_inj a).2 (ih hx')

end Prefix

end FreeGroup
