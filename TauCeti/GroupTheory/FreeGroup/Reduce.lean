/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.Data.List.CommonPrefix
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Reduced words in free groups

Elementary facts about reduced words complementing `Mathlib.GroupTheory.FreeGroup.Reduce`:
the formal inverse of a one-letter word, uniqueness of reduced representatives, reducedness of
formal inverses, and reducedness of words `w u w⁻¹` in which no letter cancels at either join.

The last section controls cancellation under left multiplication: if the reduced word of `g` does
not begin with the formal inverse of `x₂`, then the reduced word of `(x₁ ++ x₂) * g` still begins
with `x₁` whenever `x₁ ++ x₂` is reduced. This is the prefix calculus behind ping-pong arguments
on reduced words, such as the big powers property of free groups.

Finally, the reduced word of `g⁻¹ * f` arises from those of `g` and `f` by cancelling their
longest common prefix, so `‖g⁻¹ * f‖ + 2 * commonPrefixLength g f = ‖g‖ + ‖f‖` for the word
length `‖·‖`. Thus the Gromov product of word length is the common prefix length of reduced
words.
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

/-- A nonempty reduced word is never its own formal inverse: otherwise it would represent an
element of order at most two of the torsion-free group `FreeGroup α`. -/
theorem IsReduced.invRev_ne_self {w : List (α × Bool)} (hw : IsReduced w) (hw₀ : w ≠ []) :
    FreeGroup.invRev w ≠ w := by
  intro h
  have hsq : mk w ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [← h]
    rw [← inv_mk, inv_mul_cancel]
  rw [pow_eq_one_iff_left (Nat.succ_ne_zero 1), one_eq_mk] at hsq
  exact hw₀ (hw.eq_of_mk_eq IsReduced.nil hsq)

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

section CommonPrefix

variable [DecidableEq α]

/-- For reduced words `u` and `v`, the reduced word of `(mk u)⁻¹ * mk v` has length
`u.length + v.length - 2 * commonPrefixLength u v`. Intuitively, this reduced word arises from
`invRev u ++ v` by cancelling the longest common prefix of `u` and `v`. -/
theorem length_toWord_inv_mk_mul_mk {u v : List (α × Bool)} (hu : IsReduced u)
    (hv : IsReduced v) :
    ((mk u)⁻¹ * mk v).toWord.length + 2 * List.commonPrefixLength u v = u.length + v.length := by
  induction u generalizing v with
  | nil => simp [hv.reduce_eq]
  | cons a u ih =>
    cases v with
    | nil => simp [inv_mk, hu.invRev.reduce_eq]
    | cons b v =>
      by_cases hab : a = b
      · subst hab
        have hmul : (mk (a :: u))⁻¹ * mk (a :: v) = (mk u)⁻¹ * mk v := by
          simp only [← List.singleton_append (l := u), ← List.singleton_append (l := v), ← mul_mk,
            mul_inv_rev, mul_assoc, inv_mul_cancel_left]
        have := ih (hu.infix (List.suffix_cons a u).isInfix)
          (hv.infix (List.suffix_cons a v).isInfix)
        simp only [hmul, List.commonPrefixLength_cons_cons, ite_true, List.length_cons]
        omega
      · -- No letter cancels: `invRev (a :: u)` ends with `a⁻¹`, and `b ≠ a`.
        have hred : IsReduced (invRev (a :: u) ++ b :: v) := by
          refine List.isChain_append.2 ⟨hu.invRev, hv, fun x hx y hy hxy => ?_⟩
          simp only [invRev, List.map_cons, List.reverse_cons, List.getLast?_append,
            List.getLast?_singleton, Option.some_or, Option.mem_def, Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hx hy
          obtain ⟨a₁, a₂⟩ := a
          obtain ⟨b₁, b₂⟩ := b
          simp only at hxy ⊢
          subst hxy
          cases a₂ <;> cases b₂ <;> simp_all
        rw [inv_mk, mul_mk, toWord_mk, hred.reduce_eq]
        simp [hab]

/-- The word length of `g⁻¹ * f` is the sum of the word lengths of `g` and `f` minus twice the
length of the longest common prefix of their reduced words. -/
theorem norm_inv_mul_add_two_mul_commonPrefixLength (g f : FreeGroup α) :
    norm (g⁻¹ * f) + 2 * List.commonPrefixLength g.toWord f.toWord = norm g + norm f := by
  have h := length_toWord_inv_mk_mul_mk (isReduced_toWord (x := g)) (isReduced_toWord (x := f))
  rwa [mk_toWord, mk_toWord] at h

end CommonPrefix

section Induction

variable [DecidableEq α]

/-- Induction along reduced words: a property of `1` that passes from `g` to `g * mk [x]`
whenever the reduced word of `g * mk [x]` is that of `g` followed by `x` holds for every element
of the free group. -/
@[elab_as_elim]
theorem induction_on_reduced {motive : FreeGroup α → Prop} (g : FreeGroup α) (one : motive 1)
    (mul_mk_singleton : ∀ g x, (g * mk [x]).toWord = g.toWord ++ [x] → motive g →
      motive (g * mk [x])) :
    motive g := by
  suffices ∀ L : List (α × Bool), IsReduced L → motive (mk L) by
    simpa only [mk_toWord] using this g.toWord isReduced_toWord
  intro L
  induction L using List.reverseRecOn with
  | nil => exact fun _ => one_eq_mk (α := α) ▸ one
  | append_singleton L x ih =>
    intro hL
    have hL' : IsReduced L := hL.infix (List.prefix_append L [x]).isInfix
    rw [← mul_mk]
    refine mul_mk_singleton _ _ ?_ (ih hL')
    rw [mul_mk, toWord_mk, hL.reduce_eq, toWord_mk, hL'.reduce_eq]

end Induction

end FreeGroup
