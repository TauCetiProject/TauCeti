/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ReidemeisterThree.Basic

/-!
# Local permutation calculus for the third Reidemeister move

The Kauffman bracket and planarity proofs use the same twelve-slot inclusion and the same
remainder after removing the three internal triangle arcs. This module supplies their common
permutation calculus; smoothing and face traversal are handled by the two consumers.
-/

public section

namespace TauCeti.PDCode.ReidemeisterThree

open Equiv Equiv.Perm

variable {n : ℕ} (D : PDCode n) (c : Fin 3 ↪ Fin n)
  (h : D.HasReidemeisterThreeTriangleArcs c)

/-- The three internal arcs of the original Reidemeister triangle, extended by identity. -/
def localInternalMatching : Perm (Fin 3 × Fin 4) :=
  swap (0, 2) (1, 0) * swap (1, 1) (2, 3) * swap (0, 1) (2, 0)

/-- The internal matching is the product of the three disjoint triangle-arc swaps. -/
theorem localInternalMatching_def : localInternalMatching =
    swap (0, 2) (1, 0) * swap (1, 1) (2, 3) * swap (0, 1) (2, 0) := (rfl)

/-- Traversing an internal arc twice returns to the original slot. -/
theorem localInternalMatching_apply_apply (p : Fin 3 × Fin 4) :
    localInternalMatching (localInternalMatching p) = p := by revert p; decide

/-- The internal matching is an involutive permutation. -/
theorem localInternalMatching_mul_self : localInternalMatching * localInternalMatching = 1 := by
  decide

/-- The six slots incident to the internal arcs of the original triangle. -/
def localInternal (p : Fin 3 × Fin 4) : Prop :=
  p = (0, 1) ∨ p = (0, 2) ∨ p = (1, 0) ∨ p = (1, 1) ∨ p = (2, 0) ∨ p = (2, 3)

/-- The internal slots are exactly the six endpoints of the three triangle arcs. -/
theorem localInternal_iff (p : Fin 3 × Fin 4) :
    localInternal p ↔ p = (0, 1) ∨ p = (0, 2) ∨ p = (1, 0) ∨ p = (1, 1) ∨
      p = (2, 0) ∨ p = (2, 3) := Iff.rfl

/-- Membership in the six internal slots is decidable. -/
instance (p : Fin 3 × Fin 4) : Decidable (localInternal p) :=
  inferInstanceAs (Decidable (p = (0, 1) ∨ p = (0, 2) ∨ p = (1, 0) ∨
    p = (1, 1) ∨ p = (2, 0) ∨ p = (2, 3)))

/-- Extend a permutation of the twelve selected slots by identity on other crossings. -/
def localLift : Perm (Fin 3 × Fin 4) →* Perm (Fin (4 * n)) :=
  Perm.extendDomainHom (triangleEmbedding D c).toEquivRange

/-- A lifted permutation acts according to its local slot permutation. -/
theorem localLift_apply (p : Perm (Fin 3 × Fin 4)) (x : Fin 3 × Fin 4) :
    localLift D c p (triangleEmbedding D c x) = triangleEmbedding D c (p x) :=
  p.viaFintypeEmbedding_apply_image (triangleEmbedding D c) x

/-- Lifting fixes every half-edge at an unselected crossing. -/
theorem localLift_fixed (p : Perm (Fin 3 × Fin 4)) {i : Fin n}
    (hi : i ∉ Set.range c) (s : Fin 4) :
    localLift D c p (D.crossing i s) = D.crossing i s := by
  apply Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨⟨j, t⟩, hj⟩
  simp only [triangleEmbedding_apply, crossing_apply] at hj
  exact hi ⟨j, congrArg Prod.fst ((crossingSlotEquiv n).injective (D.halfEdge.injective hj))⟩

/-- Lifting a transposition gives the transposition of its two ambient half-edges. -/
theorem localLift_swap (a b : Fin 3 × Fin 4) :
    localLift D c (swap a b) = swap (triangleEmbedding D c a) (triangleEmbedding D c b) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range (triangleEmbedding D c)
  · obtain ⟨y, rfl⟩ := hx
    rw [localLift_apply]
    exact (triangleEmbedding D c).injective.map_swap a b y
  · have he : localLift D c (swap a b) x = x :=
      Perm.viaFintypeEmbedding_apply_notMem_range _ _ hx
    rw [he, swap_apply_of_ne_of_ne]
    · exact fun h ↦ hx ⟨a, h.symm⟩
    · exact fun h ↦ hx ⟨b, h.symm⟩

include h in
/-- The prescribed triangle arcs agree with the local internal matching. -/
theorem internalMatching_edgePair (p : Fin 3 × Fin 4) (hp : localInternal p) :
    D.edgePair.val (triangleEmbedding D c p) =
      triangleEmbedding D c (localInternalMatching p) := by
  have ht := (hasReidemeisterThreeTriangleArcs_iff D c).mp h
  obtain hp | hp | hp | hp | hp | hp := hp
  all_goals subst p
  · have he := ht.2.2
    have hm : localInternalMatching (0, 1) = (2, 0) := by decide
    simpa only [hm, triangleEmbedding_apply] using he
  · have hm : localInternalMatching (0, 2) = (1, 0) := by decide
    simpa only [hm, triangleEmbedding_apply] using ht.1
  · have hm : localInternalMatching (1, 0) = (0, 2) := by decide
    simpa only [hm, triangleEmbedding_apply] using D.edgePair.apply_eq_of_apply_eq ht.1
  · have hm : localInternalMatching (1, 1) = (2, 3) := by decide
    simpa only [hm, triangleEmbedding_apply] using ht.2.1
  · have hm : localInternalMatching (2, 0) = (0, 1) := by decide
    simpa only [hm, triangleEmbedding_apply] using D.edgePair.apply_eq_of_apply_eq ht.2.2
  · have hm : localInternalMatching (2, 3) = (1, 1) := by decide
    simpa only [hm, triangleEmbedding_apply] using D.edgePair.apply_eq_of_apply_eq ht.2.1

/-- Remove the three internal arcs, leaving their six slots fixed by the remainder. -/
def outsideEdges : Perm (Fin (4 * n)) :=
  localLift D c localInternalMatching * D.edgePair.val

/-- Removing the internal arcs composes the original matching with their three swaps. -/
theorem outsideEdges_def : outsideEdges D c =
    localLift D c localInternalMatching * D.edgePair.val := (rfl)

include h in
/-- Removing the triangle arcs fixes each of their six incident slots. -/
theorem outsideEdges_internal (p : Fin 3 × Fin 4) (hp : localInternal p) :
    outsideEdges D c (triangleEmbedding D c p) = triangleEmbedding D c p := by
  rw [outsideEdges, Perm.mul_apply, internalMatching_edgePair D c h p hp, localLift_apply]
  rw [localInternalMatching_apply_apply]

/-- The lifted twelve-slot rewire is the half-edge permutation of the move. -/
theorem localLift_slots :
    localLift D c reidemeisterThreeSlots = D.reidemeisterThreePerm c := by
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv n).surjective y
  rw [← crossing_apply]
  by_cases hi : i ∈ Set.range c
  · obtain ⟨j, rfl⟩ := hi
    rw [← triangleEmbedding_apply D c, localLift_apply, triangleEmbedding_apply,
      triangleEmbedding_apply, reidemeisterThreePerm_apply_crossing]
  · rw [localLift_fixed D c _ hi, reidemeisterThreePerm_crossing_of_notMem D c hi]

end TauCeti.PDCode.ReidemeisterThree
