/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Set.PowersetCard
import TauCeti.Data.Set.PowersetCard

/-!
# Embeddings with a prescribed image of a finite subset

Fix two subsets of cardinality `r` in finite types. There are at most
`r! * |β|^(|α| - r)` embeddings from `α` to `β` taking the first subset onto the second.
This separates the choices on a prescribed subset from the unconstrained remaining vertices,
as needed when bounding the number of copies affected by a hyperedge edit.

When the source is `Fin r` itself, `Set.powersetCard.card_filter_ofFinEmb_eq` counts the `r!`
injective `r`-tuples in a finite type with a prescribed unordered image `t`, and
`Finset.card_filter_ofFinEmb_eq_sum_factorial` decomposes any unordered predicate count on a finite
set of injective `r`-tuples by fiber multiplicity in `{1, …, r!}`.
-/

public section

namespace TauCeti

/-- The embeddings taking one prescribed `r`-element subset onto another are bounded by the
`r!` bijections on those subsets and arbitrary choices on the complement. -/
theorem card_embedding_map_eq_le {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    {s : Set.powersetCard α r} {t : Set.powersetCard β r} :
    Nat.card {f : α ↪ β // Set.powersetCard.map r f s = t} ≤
      r.factorial * Fintype.card β ^ (Fintype.card α - r) := by
  classical
  let code : {f : α ↪ β // Set.powersetCard.map r f s = t} →
      (s.val ↪ t.val) × (↥(s.valᶜ) → β) := fun f ↦
    (⟨fun a ↦ ⟨f.val a, by
        have hm : f.val a ∈ (Set.powersetCard.map r f.val s).val := by
          simp only [Set.powersetCard.val_map, Finset.mem_map]
          exact ⟨a, a.prop, rfl⟩
        simpa only [f.prop] using hm⟩,
      fun a b h ↦ Subtype.ext (f.val.injective (congrArg Subtype.val h))⟩,
      fun a ↦ f.val a)
  have hinj : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    ext a
    by_cases ha : a ∈ s.val
    · exact congrArg Subtype.val
        (congrFun (congrArg (fun p ↦ (p.1 : s.val → t.val)) h) ⟨a, ha⟩)
    · exact congrFun (congrArg Prod.snd h) ⟨a, Finset.mem_compl.mpr ha⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fun, Fintype.card_coe, Set.powersetCard.card_eq, Finset.card_compl,
    Nat.descFactorial_self] using Nat.card_le_card_of_injective code hinj

end TauCeti

namespace Set.powersetCard

/-- Among injective `r`-tuples in a finite type, `r!` have a prescribed `r`-element subset `t` as
unordered image. -/
theorem card_filter_ofFinEmb_eq {β : Type*} [Fintype β] [DecidableEq β] {r : ℕ}
    (t : Set.powersetCard β r) :
    Finset.card (Finset.univ.filter fun x : {x : Fin r → β // Function.Injective x} ↦
      ofFinEmb r β ⟨x.val, x.property⟩ = t) = r.factorial := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← natCard_ofFinEmb_eq t]
  exact Nat.card_congr ((Equiv.subtypeInjectiveEquivEmbedding (Fin r) β).subtypeEquiv fun _ ↦
    Iff.rfl)

end Set.powersetCard

namespace Finset

/-- Partitioning a finite set `W` of injective `r`-tuples by unordered `r`-subset `ofFinEmb`
expresses the count of tuples in `W` satisfying an unordered predicate `P` as a weighted sum over
the `r!` possible positive fiber multiplicities `1, …, r!`. -/
theorem card_filter_ofFinEmb_eq_sum_factorial {β : Type*} [Fintype β] [DecidableEq β] {r : ℕ}
    (W : Finset {x : Fin r → β // Function.Injective x})
    (P : Set.powersetCard β r → Prop) [DecidablePred P] :
    (W.filter fun x ↦ P (Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩)).card =
      ∑ k : Fin r.factorial, (k.val + 1) *
        (univ.filter fun s : Set.powersetCard β r ↦
          P s ∧ (W.filter fun x ↦ Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩ = s).card =
            k.val + 1).card := by
  classical
  have hlhs : (W.filter fun x ↦ P (Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩)).card =
      ∑ s : Set.powersetCard β r,
        if P s then (W.filter fun x ↦ Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩ = s).card
        else 0 := by
    rw [← sum_filter, card_eq_sum_card_fiberwise
      (f := fun x : {x : Fin r → β // Function.Injective x} ↦
        Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩)
      (t := univ.filter P) (fun x hx ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩)]
    refine sum_congr rfl fun s hs ↦ congrArg card (ext fun x ↦ ?_)
    simp only [mem_filter]
    exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩,
      fun hx ↦ ⟨⟨hx.1, hx.2 ▸ (mem_filter.1 hs).2⟩, hx.2⟩⟩
  have hrhs (k : Fin r.factorial) :
      (k.val + 1) * (univ.filter fun s : Set.powersetCard β r ↦
          P s ∧ (W.filter fun x ↦ Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩ = s).card =
            k.val + 1).card =
        ∑ s : Set.powersetCard β r,
          if P s ∧ (W.filter fun x ↦ Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩ = s).card =
            k.val + 1 then k.val + 1 else 0 := by
    rw [← sum_filter, sum_const, Nat.nsmul_eq_mul, mul_comm]
  rw [hlhs]
  simp_rw [hrhs]
  rw [sum_comm]
  refine sum_congr rfl fun s _ ↦ ?_
  set ms := (W.filter fun x ↦ Set.powersetCard.ofFinEmb r β ⟨x.val, x.property⟩ = s).card
  have hms_le : ms ≤ r.factorial :=
    (card_le_card (filter_subset_filter _ (subset_univ W))).trans_eq
      (Set.powersetCard.card_filter_ofFinEmb_eq s)
  by_cases hPs : P s
  · rcases ms.eq_zero_or_pos with hm0 | hmpos
    · simp [hPs, hm0]
    · have hklt : ms - 1 < r.factorial := by omega
      let k₀ : Fin r.factorial := ⟨ms - 1, hklt⟩
      simp only [hPs, ↓reduceIte, true_and]
      rw [sum_eq_single k₀]
      · simp [k₀, Nat.sub_add_cancel hmpos]
      · intro k _ hkne
        simp only [ite_eq_right_iff]
        intro hmk
        exact absurd (Fin.ext (by dsimp [k₀]; omega)) hkne
      · intro hk
        exact absurd (mem_univ k₀) hk
  · simp [hPs]

end Finset
