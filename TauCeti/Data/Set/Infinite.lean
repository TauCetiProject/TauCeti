/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Denumerable
import Mathlib.Logic.Equiv.Basic

/-!
# Injections into infinite sets of countable indices

An infinite subset of a countable type admits a self-injection that fixes any prescribed finite
subset of the target. This lets us reindex a countable sequence or an array axis into an infinite
coordinate subset while leaving distinguished coordinates unchanged.
-/

public section

noncomputable section

namespace Set.Infinite

/-- An injection into an infinite subset of a countable type can fix any prescribed finite
subset of its target. -/
theorem exists_injective_into_eqOn_of_finite {ι : Type*} [Countable ι]
    {S F : Set ι} (hS : S.Infinite) (hF : F.Finite) (hFS : F ⊆ S) :
    ∃ a : ι → ι, Function.Injective a ∧ (∀ i ∈ F, a i = i) ∧ ∀ k, a k ∈ S := by
  classical
  have := hS.to_subtype
  have : Infinite ι := Infinite.of_injective (fun i : S ↦ (i : ι)) Subtype.val_injective
  obtain ⟨e₀⟩ := nonempty_equiv_of_countable (α := ι) (β := S)
  have aux : ∀ t : Finset ι, (∀ i ∈ t, i ∈ S) →
      ∃ e : ι ≃ S, ∀ i ∈ t, (e i).1 = i := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨e₀, by simp⟩
    | @insert i t hit ih =>
        intro ht
        obtain ⟨e, he⟩ := ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))
        have hiS : i ∈ S := ht i (Finset.mem_insert_self i t)
        let j := e.symm ⟨i, hiS⟩
        refine ⟨(Equiv.swap i j).trans e, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hkt
        · simp [j]
        · have hki : k ≠ i := fun h => hit (h ▸ hkt)
          have hkj : k ≠ j := by
            intro h
            have h' := he k hkt
            have : e k = (⟨i, hiS⟩ : S) := by simp [h, j]
            exact hki (by simpa [this] using h'.symm)
          simp [Equiv.swap_apply_of_ne_of_ne hki hkj, he k hkt]
  obtain ⟨e, he⟩ := aux hF.toFinset (fun i hi => hFS (hF.mem_toFinset.mp hi))
  refine ⟨fun i => (e i).1, Subtype.val_injective.comp e.injective, ?_, fun i => (e i).2⟩
  intro i hi
  exact he i (hF.mem_toFinset.mpr hi)

end Set.Infinite
