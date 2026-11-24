/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.FreeGroup.Orbit
public import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Free group elements sorted by the first letter of their reduced word

For a letter `w : α × Bool`, Mathlib's `FreeGroup.startsWith w` is the set of elements of
`FreeGroup α` whose reduced word begins with `w`. Write `w⁻¹ = (w.1, !w.2)` for the inverse letter.
Mathlib proves that the sets `startsWith w` for distinct letters are disjoint
(`FreeGroup.startsWith.disjoint_iff_ne`). This file proves that they cover the nontrivial elements
of the free group, so that together with `{1}` they partition it, and the cancellation identity

```text
FreeGroup α = startsWith w ⊔ mk [w] • startsWith w⁻¹.
```

That is, left multiplication by `w` maps the elements starting with `w⁻¹` bijectively onto the
elements that do not start with `w`: it cancels the leading `w⁻¹`, and the next letter of a reduced
word cannot be `w`.

For the free group on two generators `a = of 0` and `b = of 1`, these results give the four
pairwise disjoint sets `W(a)`, `W(a⁻¹)`, `W(b)`, `W(b⁻¹)` of reduced words by first letter, with

```text
F₂ = {1} ⊔ W(a) ⊔ W(a⁻¹) ⊔ W(b) ⊔ W(b⁻¹),
F₂ = W(a) ⊔ a • W(a⁻¹) = W(b) ⊔ b • W(b⁻¹).
```

These are the combinatorial input to the paradoxical decomposition of the free group of rank two
for its left regular action, and hence to its nonamenability.

Finally, the file splits off the leading power of a generator `b`: every element factors as
`b ^ k * g'` with `g'` beginning with neither `b` nor `b⁻¹`, and when `g` does not begin with the
inverse of the letter `b ^ sign k`, nothing cancels in `b ^ k * g`.

## Main results

* `FreeGroup.mem_startsWith_iff_exists_toWord_eq_cons`: membership in `startsWith w` means the
  reduced word is `w :: l` for some `l`.
* `FreeGroup.iUnion_startsWith`: the sets `startsWith w` cover exactly the nontrivial elements.
* `FreeGroup.mk_singleton_mul_mem_startsWith_iff`: `w * g` starts with `w` exactly when `g` does
  not start with `w⁻¹`.
* `FreeGroup.mk_singleton_smul_startsWith`: `w • startsWith w⁻¹` is the complement of
  `startsWith w`.
* `FreeGroup.isCompl_startsWith_of_smul`, `FreeGroup.isCompl_startsWith_inv_of_smul`: the
  decompositions `FreeGroup α = W(a) ⊔ a • W(a⁻¹) = W(a⁻¹) ⊔ a⁻¹ • W(a)` for a generator `a`.
* `FreeGroup.mul_mem_startsWith_of_not_invRev_prefix`: `u * v` keeps the first letter of `u`
  when the reduced word of `u` does not cancel completely against `v`.
* `FreeGroup.toWord_of_zpow_mul`: if `g` does not begin with the inverse of the letter
  `b ^ sign k`, the reduced word of `b ^ k * g` is `|k|` copies of that letter followed by the
  reduced word of `g`.
* `FreeGroup.exists_eq_of_zpow_mul`: every element is `b ^ k * g'` with `g'` beginning with
  neither `b` nor `b⁻¹`.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 1.5.
* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, Theorem 1.2.
-/

public section

open Pointwise

namespace FreeGroup

variable {α : Type*}

variable [DecidableEq α]

section Prefix

/-- An element starts with the letter `w` exactly when `w` is the head of its reduced word. -/
theorem mem_startsWith_iff_head?_eq {w : α × Bool} {g : FreeGroup α} :
    g ∈ startsWith w ↔ g.toWord.head? = some w := by
  rw [List.head?_eq_getElem?, startsWith, Set.mem_ofPred_eq]

/-- An element starts with the letter `w` exactly when its reduced word is `w :: l` for some
`l`. -/
theorem mem_startsWith_iff_exists_toWord_eq_cons {w : α × Bool} {g : FreeGroup α} :
    g ∈ startsWith w ↔ ∃ l, g.toWord = w :: l := by
  rw [mem_startsWith_iff_head?_eq, List.head?_eq_some_iff]

/-- The element represented by a reduced word `w :: l` starts with `w`. -/
theorem mk_cons_mem_startsWith {w : α × Bool} {l : List (α × Bool)} (h : IsReduced (w :: l)) :
    mk (w :: l) ∈ startsWith w :=
  mem_startsWith_iff_exists_toWord_eq_cons.2 ⟨l, by rw [toWord_mk, h.reduce_eq]⟩

/-- A generator starts with itself. -/
@[simp]
theorem of_mem_startsWith (a : α) : of a ∈ startsWith (a, true) := by
  rw [of]
  exact mk_cons_mem_startsWith .singleton

/-- The inverse of a generator starts with the inverse letter. -/
@[simp]
theorem inv_of_mem_startsWith (a : α) : (of a)⁻¹ ∈ startsWith (a, false) := by
  rw [of, inv_mk_singleton]
  exact mk_cons_mem_startsWith .singleton

end Prefix

section Partition

/-- A nontrivial element starts with the first letter of its reduced word. -/
theorem exists_mem_startsWith_of_ne_one {g : FreeGroup α} (hg : g ≠ 1) :
    ∃ w, g ∈ startsWith w := by
  obtain ⟨w, l, hl⟩ := List.exists_cons_of_ne_nil (mt toWord_eq_nil_iff.1 hg)
  exact ⟨w, mem_startsWith_iff_exists_toWord_eq_cons.2 ⟨l, hl⟩⟩

/-- The sets `startsWith w` cover exactly the nontrivial elements of the free group. -/
theorem iUnion_startsWith : ⋃ w : α × Bool, startsWith w = {1}ᶜ := by
  ext g
  simp only [Set.mem_iUnion, Set.mem_compl_singleton_iff]
  exact ⟨fun ⟨w, hw⟩ => startsWith.ne_one g hw, exists_mem_startsWith_of_ne_one⟩

end Partition

section Cancellation

/-- Left multiplication by the letter `w` cancels the leading inverse letter `w⁻¹`. -/
theorem toWord_mk_singleton_mul_of_mem_startsWith {w : α × Bool} {g : FreeGroup α}
    (hg : g ∈ startsWith (w.1, !w.2)) : (mk [w] * g).toWord = g.toWord.tail := by
  obtain ⟨a, b⟩ := w
  rw [mem_startsWith_iff_head?_eq] at hg
  simp [toWord_mk_mul_eq, hg]

/-- The product `w * g` starts with the letter `w` exactly when `g` does not start with the
inverse letter `w⁻¹`. -/
@[simp]
theorem mk_singleton_mul_mem_startsWith_iff {w : α × Bool} {g : FreeGroup α} :
    mk [w] * g ∈ startsWith w ↔ g ∉ startsWith (w.1, !w.2) := by
  refine ⟨fun h hg => ?_, startsWith_mk_mul g⟩
  obtain ⟨l, hl⟩ := mem_startsWith_iff_exists_toWord_eq_cons.1 hg
  obtain ⟨l', hl'⟩ := mem_startsWith_iff_exists_toWord_eq_cons.1 h
  rw [toWord_mk_singleton_mul_of_mem_startsWith hg, hl, List.tail_cons] at hl'
  have hred : IsReduced ((w.1, !w.2) :: w :: l') := hl' ▸ hl ▸ isReduced_toWord
  simpa using (isReduced_cons_cons.1 hred).1 rfl

/-- Left multiplication by the letter `w` maps the elements starting with `w⁻¹` onto the elements
not starting with `w`. -/
@[simp]
theorem mk_singleton_smul_startsWith (w : α × Bool) :
    mk [w] • startsWith (w.1, !w.2) = (startsWith w)ᶜ := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_mk_singleton, smul_eq_mul,
    mk_singleton_mul_mem_startsWith_iff, Bool.not_not, Set.mem_compl_iff]

/-- The free group is the disjoint union of `startsWith w` and `w • startsWith w⁻¹`. -/
theorem isCompl_startsWith_mk_singleton_smul (w : α × Bool) :
    IsCompl (startsWith w) (mk [w] • startsWith (w.1, !w.2)) := by
  rw [mk_singleton_smul_startsWith]
  exact isCompl_compl

/-- For a generator `a`, the free group is the disjoint union of `W(a)` and `a • W(a⁻¹)`, where
`W(c)` is the set of elements whose reduced word starts with `c`. -/
theorem isCompl_startsWith_of_smul (a : α) :
    IsCompl (startsWith (a, true)) (of a • startsWith (a, false)) := by
  rw [of]
  exact isCompl_startsWith_mk_singleton_smul (a, true)

/-- For a generator `a`, the free group is the disjoint union of `W(a⁻¹)` and `a⁻¹ • W(a)`, where
`W(c)` is the set of elements whose reduced word starts with `c`. -/
theorem isCompl_startsWith_inv_of_smul (a : α) :
    IsCompl (startsWith (a, false)) ((of a)⁻¹ • startsWith (a, true)) := by
  rw [of, inv_mk_singleton]
  exact isCompl_startsWith_mk_singleton_smul (a, false)

/-- If `u` starts with the letter `w` and the reduced word of `u` does not cancel completely
against `v`, then `u * v` still starts with `w`. -/
theorem mul_mem_startsWith_of_not_invRev_prefix {w : α × Bool} {u v : FreeGroup α}
    (hu : u ∈ startsWith w) (h : ¬invRev u.toWord <+: v.toWord) : u * v ∈ startsWith w := by
  have hhead := head?_toWord_mk_mul isReduced_toWord h
  rw [mk_toWord] at hhead
  rwa [mem_startsWith_iff_head?_eq, hhead, ← mem_startsWith_iff_head?_eq]

end Cancellation

section LeadingPower

variable {b : α} {k : ℤ} {g : FreeGroup α}

/-- If the reduced word of `g` does not begin with the inverse of the letter `b ^ sign k`, nothing
cancels in `b ^ k * g`: its reduced word is `|k|` copies of that letter followed by the reduced word
of `g`. -/
theorem toWord_of_zpow_mul (hg : g ∉ startsWith (b, !decide (0 ≤ k))) :
    (of b ^ k * g).toWord = List.replicate k.natAbs (b, decide (0 ≤ k)) ++ g.toWord := by
  rw [toWord_mul, toWord_of_zpow]
  refine IsReduced.reduce_eq
    (List.isChain_append.2 ⟨isReduced_replicate _ _, isReduced_toWord, ?_⟩)
  intro x hx y hy hxy
  obtain rfl := List.eq_of_mem_replicate (List.mem_of_mem_getLast? hx)
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at hxy ⊢
  subst hxy
  by_contra hne
  refine hg (mem_startsWith_iff_head?_eq.2 ?_)
  rw [Option.mem_def.1 hy]
  cases y₂ <;> simp_all

/-- Under the hypothesis of `toWord_of_zpow_mul`, the word length of `b ^ k * g` is `|k|` plus the
word length of `g`. -/
theorem norm_of_zpow_mul (hg : g ∉ startsWith (b, !decide (0 ≤ k))) :
    norm (of b ^ k * g) = k.natAbs + norm g := by
  simp [norm, toWord_of_zpow_mul hg]

/-- A nontrivial power `b ^ k` times an element not beginning with the inverse of the letter
`b ^ sign k` begins with that letter. -/
theorem of_zpow_mul_mem_startsWith (hk : k ≠ 0) (hg : g ∉ startsWith (b, !decide (0 ≤ k))) :
    of b ^ k * g ∈ startsWith (b, decide (0 ≤ k)) := by
  simp [mem_startsWith_iff_head?_eq, toWord_of_zpow_mul hg, List.head?_replicate, hk]

variable (b) in
/-- Every element of a free group factors as `b ^ k * g'` with `g'` beginning with neither `b` nor
`b⁻¹`: `b ^ k` is the leading power of `b` in its reduced word. -/
theorem exists_eq_of_zpow_mul (g : FreeGroup α) :
    ∃ (k : ℤ) (g' : FreeGroup α), (∀ s, g' ∉ startsWith (b, s)) ∧ g = of b ^ k * g' := by
  suffices h : ∀ l : List (α × Bool), IsReduced l →
      ∃ (k : ℤ) (g' : FreeGroup α), (∀ s, g' ∉ startsWith (b, s)) ∧ mk l = of b ^ k * g' by
    obtain ⟨k, g', hg', h⟩ := h g.toWord isReduced_toWord
    exact ⟨k, g', hg', by rwa [mk_toWord] at h⟩
  intro l hl
  induction l with
  | nil => exact ⟨0, 1, fun s h => startsWith.ne_one _ h rfl, by rw [zpow_zero, one_mul, one_eq_mk]⟩
  | cons c l ih =>
    by_cases hc : c.1 = b
    · obtain ⟨k, g', hg', hl'⟩ := ih (hl.infix (List.suffix_cons c l).isInfix)
      obtain ⟨_, s⟩ := c
      dsimp only at hc
      subst hc
      rw [← List.singleton_append, ← mul_mk, hl', ← mul_assoc]
      cases s
      · refine ⟨-1 + k, g', hg', ?_⟩
        rw [zpow_add, zpow_neg_one, of, inv_mk_singleton]
        rfl
      · exact ⟨1 + k, g', hg', by rw [zpow_add, zpow_one, of]⟩
    · refine ⟨0, mk (c :: l), fun s hs => hc ?_, by simp⟩
      rw [mem_startsWith_iff_head?_eq, toWord_mk, hl.reduce_eq, List.head?_cons,
        Option.some_inj] at hs
      rw [hs]

end LeadingPower

end FreeGroup
