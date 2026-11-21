/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Rotate

import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Prefixes of repeated lists, prefix chains, and infixes of concatenations

Concatenating fewer copies of a list gives a prefix of concatenating more copies, and the factor of
length `|l|` of `m` concatenated copies of `l` starting at position `d` is the rotation of `l` by
`d`. Hence a factor of a concatenation of copies of `l` that is at least as long as `l` begins with
a rotation of `l`, and a factor of a concatenation of copies of a nonempty `l` also occurs in it at
a position `o < |l|`. A list which, followed by an entry `y`, begins with `k` copies of an entry
`x ≠ y` itself begins with these `k` copies. A list with no entry in `l₁` that is an infix of
`l₁ ++ l₂` is an infix of `l₂`. An injective map preserves and reflects infixes.
-/

public section

namespace List

variable {α : Type*}

/-- `m` concatenated copies of a list form a prefix of `n` concatenated copies when `m ≤ n`. -/
theorem flatten_replicate_prefix_flatten_replicate (l : List α) {m n : ℕ} (h : m ≤ n) :
    (replicate m l).flatten <+: (replicate n l).flatten := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [replicate_add, flatten_append]
  exact prefix_append _ _

/-- The factor of length `|l|` starting at position `d` of `m` concatenated copies of `l` is the
rotation of `l` by `d`, provided it fits: `d + |l| ≤ m * |l|`. -/
theorem take_drop_flatten_replicate (l : List α) {m d : ℕ} (h : d + l.length ≤ m * l.length) :
    (((replicate m l).flatten).drop d).take l.length = l.rotate d := by
  induction m generalizing d with
  | zero =>
    obtain rfl : l = [] := length_eq_zero_iff.1 (by lia)
    simp
  | succ m ih =>
    rw [replicate_succ, flatten_cons]
    obtain hd | hd := le_or_gt l.length d
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
      rw [drop_length_add_append, ih (by rw [Nat.succ_mul] at h; lia), ← rotate_rotate,
        rotate_length]
    · rw [drop_append_of_le_length hd.le, take_append, length_drop, take_of_length_le (by simp),
        rotate_eq_drop_append_take hd.le, Nat.sub_sub_self hd.le]
      congr 1
      cases m with
      | zero =>
        obtain rfl : d = 0 := by lia
        simp
      | succ m => rw [replicate_succ, flatten_cons, take_append_of_le_length hd.le]

/-- The factor of the concatenation of `m` copies of `l` that starts at position `o` and is at
least as long as `l` begins with the rotation of `l` by `o`. -/
theorem take_eq_rotate_of_prefix_drop_flatten_replicate {w l : List α} {m o : ℕ}
    (h : w <+: ((replicate m l).flatten).drop o) (hl : l.length ≤ w.length) :
    w.take l.length = l.rotate o := by
  rcases eq_or_ne l [] with rfl | hl0
  · simp
  obtain ⟨t, ht⟩ := h
  have hlen := congrArg length ht
  simp only [length_append, length_drop, length_flatten, map_replicate, sum_replicate_nat] at hlen
  have := length_pos_iff.2 hl0
  rw [← take_drop_flatten_replicate l (m := m) (by lia), ← ht, take_append_of_le_length hl]

/-- A factor of the concatenation of `n` copies of a nonempty list `l` also occurs in it at a
position `o < |l|`. -/
theorem IsInfix.exists_prefix_drop_flatten_replicate {w l : List α} {n : ℕ}
    (h : w <:+: (replicate n l).flatten) (hl : l ≠ []) :
    ∃ o < l.length, w <+: ((replicate n l).flatten).drop o := by
  obtain ⟨s, t, hst⟩ := h
  have hq : s.length / l.length ≤ n :=
    Nat.div_le_of_le_mul (by have := congrArg length hst; simp at this; lia)
  -- the position `|s|` is `|s| / |l|` whole copies of `l` followed by `|s| % |l|` letters
  have hdrop := drop_sum_flatten (replicate n l) (s.length / l.length)
  simp only [map_replicate, take_replicate, drop_replicate, Nat.min_eq_left hq,
    sum_replicate_nat] at hdrop
  refine ⟨s.length % l.length, Nat.mod_lt _ (length_pos_iff.2 hl), IsPrefix.trans ⟨t, ?_⟩
    ((flatten_replicate_prefix_flatten_replicate l (Nat.sub_le n (s.length / l.length))).drop _)⟩
  rw [← hdrop, drop_drop, Nat.div_add_mod', ← hst, append_assoc, drop_left]

/-- A factor of a concatenation of copies of `l`, at least as long as `l`, begins with a rotation
of `l`. -/
theorem IsInfix.take_isRotated_of_flatten_replicate {w l : List α} {n : ℕ}
    (h : w <:+: (replicate n l).flatten) (hl : l.length ≤ w.length) : w.take l.length ~r l := by
  obtain ⟨s, t, hst⟩ := h
  rw [take_eq_rotate_of_prefix_drop_flatten_replicate (m := n) (o := s.length)
    ⟨t, by rw [← hst, append_assoc, drop_left]⟩ hl]
  exact IsRotated.forall l _

/-- If `l ++ y :: t` begins with `k` copies of `x` and `x ≠ y`, then `l` begins with these `k`
copies: the entry `y` cannot lie among them. -/
theorem replicate_prefix_of_append_cons_eq {x y : α} (hxy : x ≠ y) {l t r : List α} {k : ℕ}
    (h : l ++ y :: t = replicate k x ++ r) : replicate k x <+: l := by
  obtain ⟨c, hc, hc'⟩ | ⟨c, hc, -⟩ := append_eq_append_iff.1 h
  · cases c with
    | nil => exact ⟨[], by simpa using hc⟩
    | cons z c =>
      obtain rfl : y = z := by simpa using congrArg head? hc'
      exact absurd (eq_of_mem_replicate (hc ▸ by simp : y ∈ replicate k x)).symm hxy
  · exact ⟨c, hc.symm⟩

/-- Along a prefix-monotone sequence of lists `σs`, any two terms defining index `x` assign the
same entry there. -/
theorem eq_of_forall_prefix_succ_of_getElem?_eq_some {σs : ℕ → List α}
    (hpref : ∀ s, σs s <+: σs (s + 1)) {s₁ s₂ x : ℕ} {b₁ b₂ : α}
    (h₁ : (σs s₁)[x]? = some b₁) (h₂ : (σs s₂)[x]? = some b₂) : b₁ = b₂ := by
  have hle : ∀ {m n}, m ≤ n → σs m <+: σs n := by
    intro m n h
    induction h with
    | refl => exact prefix_rfl
    | step _ ih => exact ih.trans (hpref _)
  rcases Nat.le_total s₁ s₂ with h | h
  · obtain ⟨hlt₁, rfl⟩ := getElem?_eq_some_iff.1 h₁
    exact Option.some.inj ((prefix_iff_getElem?.1 (hle h) x hlt₁).symm.trans h₂)
  · obtain ⟨hlt₂, rfl⟩ := getElem?_eq_some_iff.1 h₂
    exact Option.some.inj (h₁.symm.trans (prefix_iff_getElem?.1 (hle h) x hlt₂))

/-- A list with no entry in `l₁` that is an infix of `l₁ ++ l₂` is an infix of `l₂`. This is the
infix analogue of `List.Sublist.of_sublist_append_right`. -/
theorem IsInfix.of_infix_append_right {l l₁ l₂ : List α} (w : ∀ a ∈ l, a ∉ l₁)
    (h : l <:+: l₁ ++ l₂) : l <:+: l₂ := by
  induction l₁ with
  | nil => simpa using h
  | cons e l₁ ih =>
    rcases infix_cons_iff.1 h with h | h
    · rcases l with _ | ⟨e', l⟩
      · exact nil_infix
      · exact absurd ((cons_prefix_cons.1 h).1 ▸ mem_cons_self) (w e' mem_cons_self)
    · exact ih (fun a ha ha' ↦ w a ha (mem_cons_of_mem _ ha')) h

/-- An injective map preserves and reflects `List.IsInfix`. -/
theorem infix_map_iff_of_injective {β : Type*} {f : α → β} (hf : Function.Injective f)
    {l₁ l₂ : List α} : l₁.map f <:+: l₂.map f ↔ l₁ <:+: l₂ :=
  ⟨fun h ↦ by obtain ⟨l, hl, he⟩ := infix_map_iff.1 h; rwa [hf.list_map he], fun h ↦ h.map f⟩

end List
