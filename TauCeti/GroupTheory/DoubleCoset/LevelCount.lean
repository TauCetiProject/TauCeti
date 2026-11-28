/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
import TauCeti.GroupTheory.DoubleCoset.Fiber

/-!
# Counting orbits after a subgroup restriction

Restricting an action to a subgroup of finite relative index splits each orbit into at most
that many smaller orbits. Applied to the action on a coset space, this bounds the number of
double cosets after shrinking the right-hand subgroup, without a freeness assumption.
-/

public section

open MulAction

namespace TauCeti

/-- Restricting the action from `K` to `J` increases the orbit count by at most `[K : J]`.
The inequality uses the convention `Nat.card = 0` for infinite types. -/
theorem natCard_orbitRelQuotient_le_mul_relIndex {G X : Type*} [Group G] [MulAction G X]
    {J K : Subgroup G} (hJK : J ≤ K) [J.IsFiniteRelIndex K] :
    Nat.card (orbitRel.Quotient J X) ≤ Nat.card (orbitRel.Quotient K X) * J.relIndex K := by
  classical
  let f : orbitRel.Quotient J X → orbitRel.Quotient K X :=
    Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le hJK)
  have hsurj : Function.Surjective f := by
    intro q
    refine ⟨Quotient.mk'' q.out, ?_⟩
    simp only [f, TauCeti.Setoid.map_of_le_mk, Quotient.out_eq]
  by_cases hfin : Finite (orbitRel.Quotient K X)
  · have : (J.subgroupOf K).FiniteIndex := inferInstance
    have hfiber (q : orbitRel.Quotient K X) :
        ∃ g : (K ⧸ J.subgroupOf K) → {p // f p = q}, Function.Surjective g := by
      induction q using Quotient.inductionOn' with
      | h x => exact ⟨cosetToOrbitRelMapFiber hJK x, cosetToOrbitRelMapFiber_surjective hJK x⟩
    choose g hg using hfiber
    let e := Equiv.sigmaFiberEquiv f
    have h : Function.Surjective (fun p : orbitRel.Quotient K X × (K ⧸ J.subgroupOf K) ↦
        e ⟨p.1, g p.1 p.2⟩) := by
      intro q
      obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective q
      obtain ⟨c, rfl⟩ := hg a b
      exact ⟨(a, c), rfl⟩
    simpa only [Nat.card_prod, ← Subgroup.index_eq_card, Subgroup.relIndex] using
      Nat.card_le_card_of_surjective _ h
  · have hfin' : ¬ Finite (orbitRel.Quotient J X) := fun h ↦ hfin (Finite.of_surjective f hsurj)
    have := not_finite_iff_infinite.mp hfin'
    simp [Nat.card_eq_zero_of_infinite]

end TauCeti

namespace DoubleCoset

/-- A finer right-hand level has at most `[K : J]` double cosets for every coarse double coset. -/
theorem natCard_quotient_le_mul_relIndex {G : Type*} [Group G] (Γ : Subgroup G)
    {J K : Subgroup G} (hJK : J ≤ K) [J.IsFiniteRelIndex K] :
    Nat.card (Quotient (Γ : Set G) J) ≤ Nat.card (Quotient (Γ : Set G) K) * J.relIndex K := by
  rw [Nat.card_congr (TauCeti.doubleCosetQuotientEquivOrbitRelQuotient Γ J),
    Nat.card_congr (TauCeti.doubleCosetQuotientEquivOrbitRelQuotient Γ K)]
  exact TauCeti.natCard_orbitRelQuotient_le_mul_relIndex (X := G ⧸ Γ) hJK

end DoubleCoset
