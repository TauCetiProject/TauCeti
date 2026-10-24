/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Basic

/-!
# Lifted relations between multisets as parallel enumerations

Mathlib's `Multiset.Rel r s t` lifts a relation `r` to multisets: it holds when the elements of
`s` and `t` can be paired off one-to-one with each pair related by `r`. This file records the
corresponding statement in terms of enumerations: `Multiset.Rel r s t` holds exactly when `s` and
`t` are enumerated by one family indexed by `Fin n`, with entries of equal index related.

This is the form in which a matching of two multisets of roots is usually produced, by
enumerating the roots of two polynomials in parallel. When each element of `t` is related to at
most one element of `s`, the file also characterizes `Multiset.Rel r s t` by counting, for each
element of `s`, the elements of `t` related to it.
-/

public section

namespace Multiset

variable {α β : Type*} {r : α → β → Prop}

/-- Two multisets are related by `Multiset.Rel r` exactly when they can be enumerated in
parallel, by families indexed by the same `Fin n`, with entries of equal index related by `r`. -/
theorem rel_iff_exists_fin {s : Multiset α} {t : Multiset β} :
    Rel r s t ↔ ∃ (n : ℕ) (a : Fin n → α) (b : Fin n → β),
      s = Finset.univ.val.map a ∧ t = Finset.univ.val.map b ∧ ∀ i, r (a i) (b i) := by
  refine ⟨fun h => ?_, fun ⟨n, a, b, hs, ht, hab⟩ => ?_⟩
  · induction h with
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp, by simp, fun i => i.elim0⟩
    | @cons x y _ _ hxy _ ih =>
      obtain ⟨n, a, b, rfl, rfl, hab⟩ := ih
      exact ⟨n + 1, Fin.cons x a, Fin.cons y b, by simp [List.ofFn_succ],
        by simp [List.ofFn_succ], Fin.cases hxy hab⟩
  · subst hs ht
    exact rel_map.2 (rel_refl_of_refl_on fun i _ => hab i)

/-- **Matching versus counting.** Suppose each element of `t` is related by `r` to at most one
element of `s`. Then `s` and `t` are related by `Multiset.Rel r` exactly when each `a ∈ s` is
related to as many elements of `t`, counted with multiplicity, as its multiplicity in `s`, and
every element of `t` is related to some element of `s`. -/
theorem rel_iff_forall_countP_eq_count [DecidableEq α] [∀ a, DecidablePred (r a)]
    {s : Multiset α} {t : Multiset β}
    (huniq : ∀ b ∈ t, ∀ a ∈ s, ∀ a' ∈ s, r a b → r a' b → a = a') :
    Rel r s t ↔ (∀ a ∈ s, t.countP (r a) = s.count a) ∧ ∀ b ∈ t, ∃ a ∈ s, r a b := by
  rcases s.empty_or_exists_mem with rfl | ⟨a₀, -⟩
  · simp [rel_zero_left, eq_zero_iff_forall_notMem]
  have : Nonempty α := ⟨a₀⟩
  -- on both sides `s` is the image of `t` under the map sending each element to its partner
  have hcount : ∀ φ : β → α, (∀ b ∈ t, φ b ∈ s) → (∀ b ∈ t, r (φ b) b) →
      ∀ a ∈ s, (t.map φ).count a = t.countP (r a) := fun φ hφ hφr a ha => by
    rw [count_map, ← countP_eq_card_filter]
    exact countP_congr rfl fun b hb => propext
      ⟨fun h => h ▸ hφr b hb, fun h => huniq b hb a ha (φ b) (hφ b hb) h (hφr b hb)⟩
  refine ⟨fun h => ?_, fun ⟨hst, hex⟩ => ?_⟩
  · have hex : ∀ b ∈ t, ∃ a ∈ s, r a b := fun b hb =>
      exists_mem_of_rel_of_mem (rel_flip.2 h) hb
    choose! φ hφ hφr using hex
    have hs : s = t.map φ := rel_eq.1 <| rel_map_right.2 <|
      h.mono fun a ha b hb hab => huniq b hb a ha (φ b) (hφ b hb) hab (hφr b hb)
    refine ⟨fun a ha => ?_, fun b hb => ⟨φ b, hφ b hb, hφr b hb⟩⟩
    rw [← hcount φ hφ hφr a ha, ← hs]
  · choose! φ hφ hφr using hex
    have hs : s = t.map φ := ext.2 fun a => by
      by_cases ha : a ∈ s
      · rw [hcount φ hφ hφr a ha, hst a ha]
      · rw [count_eq_zero.2 ha, count_eq_zero.2 fun hm => ha <| by
          obtain ⟨b, hb, rfl⟩ := mem_map.1 hm
          exact hφ b hb]
    rw [hs]
    exact rel_map_left.2 (rel_refl_of_refl_on hφr)

end Multiset
