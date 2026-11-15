/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lifted relations between multisets as parallel enumerations

Mathlib's `Multiset.Rel r s t` lifts a relation `r` to multisets: it holds when the elements of
`s` and `t` can be paired off one-to-one with each pair related by `r`. This file records the
corresponding statement in terms of enumerations: `Multiset.Rel r s t` holds exactly when `s` and
`t` are enumerated by one family indexed by `Fin n`, with entries of equal index related.

This is the form in which a matching of two multisets of roots is usually produced, by
enumerating the roots of two polynomials in parallel. When each element of `t` is related to at
most one element of `s`, the file also characterizes `Multiset.Rel r s t` by counting, for each
element of `s`, the elements of `t` related to it; when `s` and `t` have the same cardinality the
counts alone suffice (`Multiset.rel_of_forall_countP_eq_count_of_card_eq`), because these counts
and the number of unrelated elements of `t` add up to the cardinality of `t`
(`Multiset.sum_countP_add_countP_eq_card`). Lifted relations compose (`Multiset.Rel.comp`), as
matchings do.
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

/-- If each element of `t` is related by `r` to at most one element of `s`, the elements of `t`
related to some element of `s` are counted by summing, over the distinct elements of `s`, the
elements of `t` related to each. -/
theorem sum_countP_add_countP_eq_card [DecidableEq α] [∀ a, DecidablePred (r a)]
    {s : Multiset α} {t : Multiset β}
    (huniq : ∀ b ∈ t, ∀ a ∈ s, ∀ a' ∈ s, r a b → r a' b → a = a') :
    ∑ a ∈ s.toFinset, t.countP (r a) + t.countP (fun b => ∀ a ∈ s, ¬ r a b) = card t := by
  classical
  induction t using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have ih := ih fun b' hb' => huniq b' (mem_cons_of_mem hb')
    simp only [countP_cons, Finset.sum_add_distrib, card_cons]
    -- `b` is related to exactly one element of `s`, or to none
    have hb : ∑ a ∈ s.toFinset, (if r a b then 1 else 0) +
        (if ∀ a ∈ s, ¬ r a b then 1 else 0) = 1 := by
      by_cases h : ∃ a ∈ s, r a b
      · obtain ⟨a, ha, hab⟩ := h
        have hnot : ¬ ∀ a ∈ s, ¬ r a b := fun h' => h' a ha hab
        rw [Finset.sum_eq_single_of_mem a (mem_toFinset.2 ha) fun a' ha' hne => by
          simp only [ite_eq_right_iff, one_ne_zero, imp_false]
          exact fun hr => hne (huniq b (mem_cons_self b t) a' (mem_toFinset.1 ha') a ha hr hab)]
        simp [hab, hnot]
      · simp only [not_exists, not_and] at h
        rw [Finset.sum_eq_zero fun a ha => by simp [h a (mem_toFinset.1 ha)]]
        simpa using h
    omega

/-- **Matching by counting, with equal cardinalities.** Suppose each element of `t` is related by
`r` to at most one element of `s`, and each `a ∈ s` is related to as many elements of `t`,
counted with multiplicity, as its multiplicity in `s`. If `s` and `t` have the same cardinality,
then `s` and `t` are related by `Multiset.Rel r`: no element of `t` is left over. -/
theorem rel_of_forall_countP_eq_count_of_card_eq [DecidableEq α] [∀ a, DecidablePred (r a)]
    {s : Multiset α} {t : Multiset β}
    (huniq : ∀ b ∈ t, ∀ a ∈ s, ∀ a' ∈ s, r a b → r a' b → a = a')
    (hcount : ∀ a ∈ s, t.countP (r a) = s.count a) (hcard : card t = card s) : Rel r s t := by
  refine (rel_iff_forall_countP_eq_count huniq).2 ⟨hcount, fun b hb => ?_⟩
  have hsum := sum_countP_add_countP_eq_card huniq
  rw [Finset.sum_congr rfl fun a ha => hcount a (mem_toFinset.1 ha), toFinset_sum_count_eq,
    hcard, Nat.add_eq_left, countP_eq_zero] at hsum
  by_contra h
  exact hsum b hb fun a ha hab => h ⟨a, ha, hab⟩

/-- **Lifted relations compose.** If `s` and `t` are paired off by `r`, and `t` and `u` by `r'`,
then `s` and `u` are paired off by the composite relation `Relation.Comp r r'`. -/
theorem Rel.comp {γ : Type*} {r' : β → γ → Prop} {s : Multiset α} {t : Multiset β}
    {u : Multiset γ} (h₁ : Rel r s t) (h₂ : Rel r' t u) : Rel (Relation.Comp r r') s u := by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.1 h₁, rel_zero_left.1 h₂, rel_zero_left]
  | cons x t ih =>
    obtain ⟨a, as, ha, has, rfl⟩ := rel_cons_right.1 h₁
    obtain ⟨b, bs, hb, hbs, rfl⟩ := rel_cons_left.1 h₂
    exact (ih has hbs).cons ⟨x, ha, hb⟩

end Multiset
