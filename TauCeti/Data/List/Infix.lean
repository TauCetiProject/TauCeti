/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Infix

/-!
# Prefixes of repeated lists, prefix chains, and infixes of concatenations

Concatenating fewer copies of a list gives a prefix of concatenating more copies. A list which,
followed by an entry `y`, begins with `k` copies of an entry `x ≠ y` itself begins with these `k`
copies. Along a prefix-monotone sequence of lists, any two terms defining an index assign the same
entry there. A list with no entry in `l₁` that is an infix of `l₁ ++ l₂` is an infix of `l₂`.
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
theorem getElem?_eq_of_forall_prefix_succ {σs : ℕ → List α}
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

end List
