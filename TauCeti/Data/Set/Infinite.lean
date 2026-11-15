/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Set.Piecewise
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Injections into infinite sets

An infinite subset of a countable type admits a self-injection that fixes any prescribed finite
subset of the target. This lets us reindex a countable sequence or an array axis into an infinite
coordinate subset while leaving distinguished coordinates unchanged.

A set is infinite exactly when it contains injective tuples of every finite length
(`Set.forall_exists_injective_iff_infinite`).
-/

public section

namespace Set.Infinite

/-- An injection into an infinite subset of a countable type can fix any prescribed finite
subset of its target. -/
theorem exists_injective_into_eqOn_of_finite {ι : Type*} [Countable ι]
    {S F : Set ι} (hS : S.Infinite) (hF : F.Finite) (hFS : F ⊆ S) :
    ∃ a : ι → ι, Function.Injective a ∧ (∀ i ∈ F, a i = i) ∧ ∀ k, a k ∈ S := by
  classical
  -- Fix `F` pointwise and send its complement injectively into the infinite set `S \ F`.
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  let e := (hS.sdiff hF).natEmbedding
  let g : ι → ι := fun i ↦ e (f i)
  have hg : ∀ i, g i ∈ S \ F := fun i ↦ (e (f i)).2
  refine ⟨F.piecewise id g, (F.injective_piecewise_iff).2 ⟨Set.injOn_id F, ?_, ?_⟩,
    fun i hi ↦ by simp [hi], fun k ↦ ?_⟩
  · exact (Subtype.val_injective.comp (e.injective.comp hf)).injOn
  · exact fun x hx y _ h ↦ (hg y).2 (h ▸ hx)
  · by_cases hk : k ∈ F
    · simpa [hk] using hFS hk
    · simpa [hk] using (hg k).1

end Set.Infinite

namespace Set

/-- A set contains injective tuples of every finite length exactly when it is infinite. -/
theorem forall_exists_injective_iff_infinite {α : Type*} (s : Set α) :
    (∀ n : ℕ, ∃ y : Fin n → α, Function.Injective y ∧ ∀ i, y i ∈ s) ↔ s.Infinite := by
  refine ⟨fun h hs => ?_, fun hs n => ?_⟩
  · have := hs.to_subtype
    obtain ⟨y, hy, hys⟩ := h (Nat.card s + 1)
    have hle := Nat.card_le_card_of_injective (fun i => (⟨y i, hys i⟩ : s))
      fun i j hij => hy (congrArg Subtype.val hij)
    simp at hle
  · exact ⟨fun i => (hs.natEmbedding s i : α),
      fun i j hij => Fin.val_injective ((hs.natEmbedding s).injective
        (Subtype.val_injective hij)),
      fun i => (hs.natEmbedding s i).2⟩

end Set
