/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Topology.Constructions

/-!
# Groups with finitely many open subgroups of bounded index

Let `G` be a group with a topology, with only finitely many open subgroups of finite index at most
`n`. Then there are only finitely many continuous homomorphisms from `G` to a finite discrete
group `Q` with `#Q ≤ n`. The property passes to open subgroups of finite index.

For the Galois group of the maximal extension of a number field unramified outside a finite set
of places, Hermite's theorem gives this property, and these two statements turn it into the
finiteness of its first cohomology with finite coefficients.

## Main results

* `TauCeti.finite_continuousMonoidHom_of_finite_setOf_isOpen_index_le`: finitely many open
  subgroups of index at most `#Q` give finitely many continuous homomorphisms to `Q`.
* `TauCeti.finite_setOf_isOpen_index_le_of_isOpen`: the property passes to an open subgroup of
  finite index.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Finitely many continuous homomorphisms to a finite group.** If a group `G` with a topology has
only finitely many open subgroups of finite index at most `#Q`, then there are only finitely many
continuous homomorphisms from `G` to the finite discrete group `Q`. -/
theorem finite_continuousMonoidHom_of_finite_setOf_isOpen_index_le {Q : Type*} [Group Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (h : {H : Subgroup G | IsOpen (H : Set G) ∧ H.FiniteIndex ∧ H.index ≤ Nat.card Q}.Finite) :
    Finite (G →ₜ* Q) := by
  let 𝒲 := {H : Subgroup G | IsOpen (H : Set G) ∧ H.FiniteIndex ∧ H.index ≤ Nat.card Q}
  have : Finite 𝒲 := h.to_subtype
  -- the intersection `N` of the open subgroups of index at most `#Q` has finite index
  let N : Subgroup G := ⨅ H : 𝒲, H.val
  have : N.FiniteIndex := Subgroup.finiteIndex_iInf fun H ↦ H.property.2.1
  -- and lies in every kernel
  have hN (χ : G →ₜ* Q) : N ≤ (χ : G →* Q).ker := by
    refine iInf_le_of_le ⟨(χ : G →* Q).ker, ?_, ⟨?_⟩, ?_⟩ le_rfl
    · rw [MonoidHom.coe_ker]
      exact (isOpen_discrete _).preimage χ.continuous
    · rw [Subgroup.index_ker]
      exact Nat.card_pos.ne'
    · rw [Subgroup.index_ker]
      exact Subgroup.card_le_card_group _
  refine Finite.of_injective (fun (χ : G →ₜ* Q) (q : G ⧸ N) ↦
    Quotient.liftOn' q χ fun a b hab ↦ ?_) fun χ₁ χ₂ hχ ↦ ?_
  · have := hN χ (QuotientGroup.leftRel_apply.1 hab)
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this
  · ext g
    exact congrFun hχ (g : G ⧸ N)

/-- **Open subgroups of bounded index of an open subgroup.** Let `V` be an open subgroup of finite
index of `G`. If `G` has only finitely many open subgroups of finite index at most `[G : V] * n`,
then `V` has only finitely many open subgroups of finite index at most `n`. -/
theorem finite_setOf_isOpen_index_le_of_isOpen {V : Subgroup G} (hV : IsOpen (V : Set G))
    [V.FiniteIndex] (n : ℕ)
    (h : {W : Subgroup G | IsOpen (W : Set G) ∧ W.FiniteIndex ∧ W.index ≤ V.index * n}.Finite) :
    {H : Subgroup V | IsOpen (H : Set V) ∧ H.FiniteIndex ∧ H.index ≤ n}.Finite := by
  refine (h.preimage (Subgroup.map_injective V.subtype_injective).injOn).subset ?_
  rintro H ⟨hH, hfin, hn⟩
  refine ⟨?_, ⟨?_⟩, ?_⟩
  · rw [Subgroup.coe_map]
    exact IsOpen.isOpenMap_subtypeVal hV _ hH
  · rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hfin.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.index_map_subtype, mul_comm]
    exact Nat.mul_le_mul_left _ hn

end TauCeti
