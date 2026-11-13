/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Occurrences of a list that are not split by a factorisation

For a list `l` and a list of lists `L`, an occurrence of `l` in the concatenation `L.flatten` is
*split* by `L` when one of the cut points between consecutive members of `L` lies strictly inside
it. `List.IsUnsplit l L` says that no occurrence of `l` in `L.flatten` is split. Then every
occurrence of a nonempty `l` lies inside a single member of `L`.

This is the condition under which an operation on words that only looks at the occurrences of `l`
commutes with the concatenation of the members of `L`.
-/

public section

namespace List

variable {α : Type*} {l : List α} {L L₁ L₂ : List (List α)}

/-- No occurrence of `l` in the concatenation of `L` is split by the factorisation `L`: for every
occurrence `s ++ l ++ t = L.flatten` and every cut `L = L₁ ++ L₂`, the cut point lies before the
occurrence or after it. -/
def IsUnsplit (l : List α) (L : List (List α)) : Prop :=
  ∀ s t L₁ L₂, s ++ l ++ t = L.flatten → L = L₁ ++ L₂ →
    L₁.flatten.length ≤ s.length ∨ s.length + l.length ≤ L₁.flatten.length

/-- The defining condition of `List.IsUnsplit`. -/
theorem isUnsplit_iff : l.IsUnsplit L ↔ ∀ s t L₁ L₂, s ++ l ++ t = L.flatten → L = L₁ ++ L₂ →
    L₁.flatten.length ≤ s.length ∨ s.length + l.length ≤ L₁.flatten.length :=
  Iff.rfl

/-- The empty factorisation splits nothing. -/
@[simp, grind .]
theorem isUnsplit_nil (l : List α) : l.IsUnsplit [] := fun _ _ _ _ _ hL ↦ by
  simp [(append_eq_nil_iff.1 hL.symm).1]

/-- No factorisation splits an occurrence of the empty list. -/
@[simp, grind .]
theorem nil_isUnsplit (L : List (List α)) : ([] : List α).IsUnsplit L := fun _ _ _ _ _ _ ↦ by
  simp only [length_nil, Nat.add_zero]
  omega

/-- A factorisation splits no occurrence of a list that does not occur in its concatenation. -/
theorem isUnsplit_of_not_isInfix (h : ¬ l <:+: L.flatten) : l.IsUnsplit L :=
  fun s t _ _ hs _ ↦ absurd ⟨s, t, hs⟩ h

/-- A factorisation with a single member splits nothing. -/
@[simp, grind .]
theorem isUnsplit_singleton (l u : List α) : l.IsUnsplit [u] := by
  rw [isUnsplit_iff]
  intro s t L₁ L₂ h hL
  rcases L₁ with _ | ⟨v, L₁⟩
  · simp
  · obtain ⟨rfl, hL'⟩ : u = v ∧ [] = L₁ ++ L₂ := by simpa using hL
    obtain ⟨rfl, rfl⟩ : L₁ = [] ∧ L₂ = [] := by simpa using hL'.symm
    have := congrArg length h
    simp at this ⊢
    omega

/-- If `L₁ ++ L₂` splits no occurrence of `l`, neither does `L₁`. -/
@[grind →]
theorem IsUnsplit.of_append_left (h : l.IsUnsplit (L₁ ++ L₂)) : l.IsUnsplit L₁ := by
  rw [isUnsplit_iff] at h ⊢
  intro s t M₁ M₂ hs hM
  exact h s (t ++ L₂.flatten) M₁ (M₂ ++ L₂) (by simp [← hs]) (by simp [hM])

/-- If `L₁ ++ L₂` splits no occurrence of `l`, neither does `L₂`. -/
@[grind →]
theorem IsUnsplit.of_append_right (h : l.IsUnsplit (L₁ ++ L₂)) : l.IsUnsplit L₂ := by
  rw [isUnsplit_iff] at h ⊢
  intro s t M₁ M₂ hs hM
  have := h (L₁.flatten ++ s) t (L₁ ++ M₁) M₂ (by simp [← hs]) (by simp [hM])
  simp only [flatten_append, length_append] at this
  omega

/-- A factorisation `[u, v]` with two members splits no occurrence of `l` exactly when the cut
point between `u` and `v` lies before or after every occurrence of `l` in `u ++ v`. -/
theorem isUnsplit_pair_iff {u v : List α} : l.IsUnsplit [u, v] ↔
    ∀ s t, s ++ l ++ t = u ++ v → u.length ≤ s.length ∨ s.length + l.length ≤ u.length := by
  rw [isUnsplit_iff]
  refine ⟨fun h s t hs ↦ by simpa using h s t [u] [v] (by simpa using hs) rfl,
    fun h s t L₁ L₂ hs hL ↦ ?_⟩
  have hlen := congrArg length hs
  rcases L₁ with _ | ⟨u', _ | ⟨v', L₁⟩⟩
  · simp
  · obtain ⟨rfl, -⟩ : u = u' ∧ [v] = L₂ := by simpa using hL
    simpa using h s t (by simpa using hs)
  · obtain ⟨rfl, rfl, -⟩ : u = u' ∧ v = v' ∧ [] = L₁ ++ L₂ := by simpa using hL
    obtain ⟨rfl, -⟩ : L₁ = [] ∧ L₂ = [] := by simpa using hL
    simp only [flatten_cons, flatten_nil, length_append, length_nil] at hlen ⊢
    omega

/-- If `L₁ ++ L₂` splits no occurrence of `l`, then the cut point between the concatenation of
`L₁` and the concatenation of `L₂` is inside no occurrence of `l`. -/
theorem IsUnsplit.pair_flatten (h : l.IsUnsplit (L₁ ++ L₂)) :
    l.IsUnsplit [L₁.flatten, L₂.flatten] :=
  isUnsplit_pair_iff.2 fun s t hs ↦ isUnsplit_iff.1 h s t L₁ L₂ (by simpa using hs) rfl

/-- The factorisation `L₁ ++ L₂` splits no occurrence of `l` exactly when neither `L₁` nor `L₂`
does and the cut point between the concatenation of `L₁` and that of `L₂` lies inside no
occurrence of `l`. -/
theorem isUnsplit_append : l.IsUnsplit (L₁ ++ L₂) ↔
    l.IsUnsplit L₁ ∧ l.IsUnsplit L₂ ∧ l.IsUnsplit [L₁.flatten, L₂.flatten] := by
  refine ⟨fun h ↦ ⟨h.of_append_left, h.of_append_right, h.pair_flatten⟩,
    fun ⟨h₁, h₂, h₃⟩ s t M₁ M₂ hs hM ↦ ?_⟩
  rw [flatten_append] at hs
  have hlen := congrArg length hs
  simp only [length_append] at hlen
  rcases isUnsplit_pair_iff.1 h₃ s t hs with hle | hle <;>
    rcases append_eq_append_iff.1 hM with ⟨N, rfl, rfl⟩ | ⟨N, rfl, rfl⟩ <;>
    simp only [flatten_append, length_append] at hle ⊢
  · obtain ⟨s', rfl⟩ : L₁.flatten <+: s := prefix_of_prefix_length_le
      (prefix_append _ _) ⟨l ++ t, by simpa using hs⟩ hle
    have := isUnsplit_iff.1 h₂ s' t N M₂ (by simpa using hs) rfl
    simp only [length_append] at this ⊢
    omega
  · omega
  · omega
  · obtain ⟨t', ht'⟩ : s ++ l <+: (M₁ ++ N).flatten := prefix_of_prefix_length_le
      ⟨t, hs⟩ (prefix_append _ _) (by simpa using hle)
    exact isUnsplit_iff.1 h₁ s t' M₁ N ht' rfl

/-- The factorisation `u :: L` splits no occurrence of `l` exactly when `L` does not and the cut
point after `u` lies inside no occurrence of `l`. -/
theorem isUnsplit_cons {u : List α} :
    l.IsUnsplit (u :: L) ↔ l.IsUnsplit [u, L.flatten] ∧ l.IsUnsplit L := by
  simpa [and_comm] using isUnsplit_append (l := l) (L₁ := [u]) (L₂ := L)

/-- If `L` splits no occurrence of a nonempty list `l` and `l` occurs in the concatenation of `L`,
then `l` occurs in a member of `L`. -/
theorem IsUnsplit.exists_isInfix_of_isInfix_flatten (h : l.IsUnsplit L) (hl : l ≠ [])
    (h' : l <:+: L.flatten) : ∃ u ∈ L, l <:+: u := by
  induction L with
  | nil => exact absurd (eq_nil_of_infix_nil h') hl
  | cons u L ih =>
    obtain ⟨hu, hL⟩ := isUnsplit_cons.1 h
    obtain ⟨s, t, hs⟩ := h'
    rw [flatten_cons] at hs
    rcases isUnsplit_pair_iff.1 hu s t hs with hle | hle
    · obtain ⟨s', rfl⟩ : u <+: s := prefix_of_prefix_length_le
        (prefix_append _ _) ⟨l ++ t, by simpa using hs⟩ hle
      obtain ⟨v, hv, hlv⟩ := ih hL ⟨s', t, by simpa using hs⟩
      exact ⟨v, mem_cons_of_mem _ hv, hlv⟩
    · obtain ⟨t', ht'⟩ : s ++ l <+: u :=
        prefix_of_prefix_length_le ⟨t, hs⟩ (prefix_append _ _) (by simpa using hle)
      exact ⟨u, mem_cons_self, s, t', ht'⟩

/-- The factorisation `[0, 1] ++ [0]` splits the occurrence of `[0, 1, 0]` in its
concatenation. -/
example : ¬ ([0, 1, 0] : List ℕ).IsUnsplit [[0, 1], [0]] := fun h ↦ by
  simpa using isUnsplit_pair_iff.1 h [] [] rfl

/-- The factorisation `[0, 1, 0] ++ [1]` does not split the occurrence of `[0, 1, 0]` in its
concatenation. -/
example : ([0, 1, 0] : List ℕ).IsUnsplit [[0, 1, 0], [1]] := by
  refine isUnsplit_pair_iff.2 fun s t hs ↦ ?_
  rcases s with _ | ⟨c, _ | ⟨d, s⟩⟩
  · simp
  · simp at hs
  · have := congrArg length hs
    simp at this
    omega

end List
