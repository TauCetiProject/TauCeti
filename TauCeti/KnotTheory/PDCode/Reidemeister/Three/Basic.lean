/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components
import Mathlib.Logic.Equiv.Fintype

/-!
# The third Reidemeister move on PD-codes

The braid form of the third Reidemeister move replaces the three-crossing tangle
`σ₁ σ₂ σ₁` by `σ₂ σ₁ σ₂`, inside an arbitrary surrounding PD-code. The crossing slots
are read counterclockwise as northwest, southwest, southeast, northeast. Its six boundary
attachments are transported to the corresponding ports of the replacement tangle; every
half-edge outside the three selected crossings stays fixed. The three over-pair indicators
give an acyclic height order on the three strands for a valid Reidemeister move.
All six orders are allowed. The raw rewire and its component identities are defined without
this condition. The over-pair indicators at the first and third crossing exchange
places, so each pair of physical strands keeps its over-strand.

The construction uses a permutation of the twelve local half-edges. This permutation mixes
crossings, so the operation is not a relabelling of a PD-code. It commutes with opposite-slot
traversal, however, which proves preservation of the link components. The triangular arcs
and the boundary attachments are specified explicitly below.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapter 1 (Reidemeister moves) and Chapter 3 (the Kauffman bracket).
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ}

/-- The twelve local half-edge positions are transported from `σ₁ σ₂ σ₁` to
`σ₂ σ₁ σ₂`. The first coordinate is the crossing and the second its cyclic slot. -/
def reidemeisterThreeSlots : Perm (Fin 3 × Fin 4) where
  toFun p := ![![(1, 0), (0, 2), (1, 2), (0, 0)],
    ![(2, 0), (0, 1), (2, 2), (0, 3)],
    ![(2, 3), (1, 1), (2, 1), (1, 3)]] p.1 p.2
  invFun p := ![![(0, 3), (1, 1), (0, 1), (1, 3)],
    ![(0, 0), (2, 1), (0, 2), (2, 3)],
    ![(1, 0), (2, 2), (1, 2), (2, 0)]] p.1 p.2
  left_inv := by decide
  right_inv := by decide

/-- The twelve-slot table defining the local rewire. -/
theorem reidemeisterThreeSlots_apply (i : Fin 3) (s : Fin 4) :
    reidemeisterThreeSlots (i, s) =
      ![![(1, 0), (0, 2), (1, 2), (0, 0)],
        ![(2, 0), (0, 1), (2, 2), (0, 3)],
        ![(2, 3), (1, 1), (2, 1), (1, 3)]] i s := (rfl)

/-- The inverse twelve-slot table reconstructs the original tangle positions. -/
theorem reidemeisterThreeSlots_symm_apply (i : Fin 3) (s : Fin 4) :
    reidemeisterThreeSlots.symm (i, s) =
      ![![(0, 3), (1, 1), (0, 1), (1, 3)],
        ![(0, 0), (2, 1), (0, 2), (2, 3)],
        ![(1, 0), (2, 2), (1, 2), (2, 0)]] i s := (rfl)

private theorem reidemeisterThreeSlots_opposite (p : Fin 3 × Fin 4) :
    reidemeisterThreeSlots (p.1, oppositeCrossingSlot p.2) =
      ((reidemeisterThreeSlots p).1, oppositeCrossingSlot (reidemeisterThreeSlots p).2) := by
  simp only [reidemeisterThreeSlots.eq_def, oppositeCrossingSlot_eq_swap_mul_swap]
  revert p
  decide

namespace ReidemeisterThree

/-- Include the twelve selected crossing slots in the ambient half-edge type. -/
def triangleEmbedding (D : PDCode n) (c : Fin 3 ↪ Fin n) :
    Fin 3 × Fin 4 ↪ Fin (4 * n) :=
  (c.prodMap (Function.Embedding.refl _)).trans
    ((crossingSlotEquiv n).toEmbedding.trans D.halfEdge.toEmbedding)

/-- The selected-slot inclusion agrees with the named crossing half-edges. -/
theorem triangleEmbedding_apply (D : PDCode n) (c : Fin 3 ↪ Fin n)
    (i : Fin 3) (s : Fin 4) : triangleEmbedding D c (i, s) = D.crossing (c i) s := by
  simp [triangleEmbedding, crossing_apply]

end ReidemeisterThree

open ReidemeisterThree

/-- The local half-edge permutation transporting the boundary ports and triangular arcs
from `σ₁ σ₂ σ₁` to `σ₂ σ₁ σ₂`, fixing half-edges at every other crossing. -/
def reidemeisterThreePerm (D : PDCode n) (c : Fin 3 ↪ Fin n) : Perm (Fin (4 * n)) :=
  reidemeisterThreeSlots.viaFintypeEmbedding (triangleEmbedding D c)

private theorem reidemeisterThreePerm_crossing (D : PDCode n) (c : Fin 3 ↪ Fin n)
    (i : Fin 3) (s : Fin 4) :
    reidemeisterThreePerm D c (D.crossing (c i) s) =
      triangleEmbedding D c (reidemeisterThreeSlots (i, s)) :=
  by simpa only [reidemeisterThreePerm, triangleEmbedding_apply] using
    reidemeisterThreeSlots.viaFintypeEmbedding_apply_image (triangleEmbedding D c) (i, s)

/-- On a selected crossing, the half-edge permutation follows the twelve-slot table. -/
theorem reidemeisterThreePerm_apply_crossing (D : PDCode n) (c : Fin 3 ↪ Fin n)
    (i : Fin 3) (s : Fin 4) :
    D.reidemeisterThreePerm c (D.crossing (c i) s) =
      D.crossing (c (reidemeisterThreeSlots (i, s)).1)
        (reidemeisterThreeSlots (i, s)).2 := by
  rw [reidemeisterThreePerm_crossing, triangleEmbedding_apply]

/-- Half-edges at unselected crossings are fixed by the local permutation. -/
theorem reidemeisterThreePerm_crossing_of_notMem (D : PDCode n) (c : Fin 3 ↪ Fin n)
    {i : Fin n} (hi : i ∉ Set.range c) (s : Fin 4) :
    reidemeisterThreePerm D c (D.crossing i s) = D.crossing i s := by
  apply Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨⟨j, t⟩, h⟩
  simp only [triangleEmbedding_apply, crossing_apply] at h
  have h' := (D.halfEdge.injective h)
  have h'' := (crossingSlotEquiv n).injective h'
  exact hi ⟨j, congrArg Prod.fst h''⟩

/-- The local rewire commutes with the crossing turn: it carries each pair of opposite slots of a
crossing to a pair of opposite slots of a crossing. -/
theorem reidemeisterThreePerm_crossingTurn (D : PDCode n) (c : Fin 3 ↪ Fin n) :
    (reidemeisterThreePerm D c).permCongr D.crossingTurn = D.crossingTurn := by
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (reidemeisterThreePerm D c).surjective x
  obtain ⟨z, rfl⟩ := D.halfEdge.surjective y
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, crossingTurn_crossing,
    ← crossing_apply]
  by_cases hi : i ∈ Set.range c
  · obtain ⟨j, rfl⟩ := hi
    rw [reidemeisterThreePerm_crossing, reidemeisterThreePerm_crossing]
    rw [reidemeisterThreeSlots_opposite (j, s)]
    rw [triangleEmbedding_apply, triangleEmbedding_apply]
    simp only [crossing_apply]
    simpa only [crossing_apply] using (D.crossingTurn_crossing _ _).symm
  · rw [reidemeisterThreePerm_crossing_of_notMem D c hi,
      reidemeisterThreePerm_crossing_of_notMem D c hi]
    simp only [crossing_apply]
    simpa only [crossing_apply] using (D.crossingTurn_crossing _ _).symm

/-- The three internal arcs of the triangular tangle `σ₁ σ₂ σ₁`. Crossing slots are
northwest, southwest, southeast, northeast. This condition is independent of strand heights;
no condition is imposed on the surrounding arcs. -/
def HasReidemeisterThreeTriangleArcs (D : PDCode n) (c : Fin 3 ↪ Fin n) : Prop :=
  D.edgePair.val (D.crossing (c 0) 2) = D.crossing (c 1) 0 ∧
  D.edgePair.val (D.crossing (c 1) 1) = D.crossing (c 2) 3 ∧
  D.edgePair.val (D.crossing (c 0) 1) = D.crossing (c 2) 0

/-- The triangle arc condition specifies exactly its three internal arcs. -/
theorem hasReidemeisterThreeTriangleArcs_iff (D : PDCode n) (c : Fin 3 ↪ Fin n) :
    D.HasReidemeisterThreeTriangleArcs c ↔
      D.edgePair.val (D.crossing (c 0) 2) = D.crossing (c 1) 0 ∧
      D.edgePair.val (D.crossing (c 1) 1) = D.crossing (c 2) 3 ∧
      D.edgePair.val (D.crossing (c 0) 1) = D.crossing (c 2) 0 := Iff.rfl

/-- The three crossings form the triangular tangle of `σ₁ σ₂ σ₁`, with a consistent
height order on its three strands. No condition is imposed on the surrounding arcs. -/
def HasReidemeisterThreeTriangle (D : PDCode n) (c : Fin 3 ↪ Fin n) : Prop :=
  D.HasReidemeisterThreeTriangleArcs c ∧
  (D.overPair (c 0) = D.overPair (c 2) → D.overPair (c 1) = D.overPair (c 0))

/-- A Reidemeister triangle has the prescribed internal arcs, independently of its heights. -/
theorem HasReidemeisterThreeTriangle.arcs {D : PDCode n} {c : Fin 3 ↪ Fin n}
    (h : D.HasReidemeisterThreeTriangle c) : D.HasReidemeisterThreeTriangleArcs c := h.1

/-- A triangle consists of the three internal arcs and an acyclic strand height order. -/
theorem hasReidemeisterThreeTriangle_iff (D : PDCode n) (c : Fin 3 ↪ Fin n) :
    D.HasReidemeisterThreeTriangle c ↔
      D.edgePair.val (D.crossing (c 0) 2) = D.crossing (c 1) 0 ∧
      D.edgePair.val (D.crossing (c 1) 1) = D.crossing (c 2) 3 ∧
      D.edgePair.val (D.crossing (c 0) 1) = D.crossing (c 2) 0 ∧
      (D.overPair (c 0) = D.overPair (c 2) → D.overPair (c 1) = D.overPair (c 0)) := by
  simp only [HasReidemeisterThreeTriangle, HasReidemeisterThreeTriangleArcs, and_assoc]

/-- The third Reidemeister rewire in braid form at three distinct crossings.
The rewire is defined for every PD-code. It is a Reidemeister move when the selected crossings
satisfy `HasReidemeisterThreeTriangle`. -/
def reidemeisterThree (D : PDCode n) (c : Fin 3 ↪ Fin n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := PerfectMatching.congr (reidemeisterThreePerm D c) D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := D.overPair ∘ Equiv.swap (c 0) (c 2)

variable (D : PDCode n) (c : Fin 3 ↪ Fin n)

/-- The move keeps the names of its half-edges. -/
@[simp] theorem reidemeisterThree_halfEdge :
    (D.reidemeisterThree c).halfEdge = D.halfEdge := (rfl)

/-- The move keeps the slots at each named crossing. -/
theorem reidemeisterThree_crossing (i : Fin n) (s : Fin 4) :
    (D.reidemeisterThree c).crossing i s = D.crossing i s := by
  simp [crossing_apply, reidemeisterThree]

/-- The first and third crossing exchange their over-pair indicators; all other crossing
indicators stay at their old names. -/
@[simp] theorem reidemeisterThree_overPair (i : Fin n) :
    (D.reidemeisterThree c).overPair i = D.overPair (Equiv.swap (c 0) (c 2) i) := by
  simp [reidemeisterThree]

/-- The move keeps crossing-free circles. -/
@[simp] theorem reidemeisterThree_crossinglessComponentCount :
    (D.reidemeisterThree c).crossinglessComponentCount = D.crossinglessComponentCount := by
  simp [reidemeisterThree]

/-- The arc matching after the move is the transport of the original matching by the local
half-edge permutation. -/
theorem reidemeisterThree_edgePair :
    (D.reidemeisterThree c).edgePair.val =
      (reidemeisterThreePerm D c).permCongr D.edgePair.val := by
  simp [reidemeisterThree, PerfectMatching.congr_val]

/-- Transport an arc across the replacement of the local twelve half-edges. -/
theorem reidemeisterThree_edgePair_transport (x : Fin (4 * n)) :
    (D.reidemeisterThree c).edgePair.val (reidemeisterThreePerm D c x) =
      reidemeisterThreePerm D c (D.edgePair.val x) := by
  simp [reidemeisterThree_edgePair]

/-- The replacement has the three internal arcs of `σ₂ σ₁ σ₂`. -/
theorem reidemeisterThree_triangleArcs (h : D.HasReidemeisterThreeTriangleArcs c) :
    (D.reidemeisterThree c).edgePair.val (D.crossing (c 0) 1) = D.crossing (c 1) 3 ∧
    (D.reidemeisterThree c).edgePair.val (D.crossing (c 1) 2) = D.crossing (c 2) 0 ∧
    (D.reidemeisterThree c).edgePair.val (D.crossing (c 0) 2) = D.crossing (c 2) 3 := by
  have h₁ := reidemeisterThree_edgePair_transport D c (D.crossing (c 1) 1)
  have h₂ := reidemeisterThree_edgePair_transport D c (D.crossing (c 0) 2)
  have h₃ := reidemeisterThree_edgePair_transport D c (D.crossing (c 0) 1)
  rw [h.2.1] at h₁
  rw [h.1] at h₂
  rw [h.2.2] at h₃
  have hp₁ : reidemeisterThreeSlots (1, 1) = (0, 1) := by
    simp only [reidemeisterThreeSlots.eq_def]; decide
  have hp₂ : reidemeisterThreeSlots (2, 3) = (1, 3) := by
    simp only [reidemeisterThreeSlots.eq_def]; decide
  have hp₃ : reidemeisterThreeSlots (0, 2) = (1, 2) := by
    simp only [reidemeisterThreeSlots.eq_def]; decide
  have hp₄ : reidemeisterThreeSlots (1, 0) = (2, 0) := by
    simp only [reidemeisterThreeSlots.eq_def]; decide
  have hp₅ : reidemeisterThreeSlots (0, 1) = (0, 2) := by
    simp only [reidemeisterThreeSlots.eq_def]; decide
  have hp₆ : reidemeisterThreeSlots (2, 0) = (2, 3) := by
    simp only [reidemeisterThreeSlots.eq_def]; decide
  rw [reidemeisterThreePerm_crossing, reidemeisterThreePerm_crossing, hp₁, hp₂,
    triangleEmbedding_apply, triangleEmbedding_apply] at h₁
  rw [reidemeisterThreePerm_crossing, reidemeisterThreePerm_crossing, hp₃, hp₄,
    triangleEmbedding_apply, triangleEmbedding_apply] at h₂
  rw [reidemeisterThreePerm_crossing, reidemeisterThreePerm_crossing, hp₅, hp₆,
    triangleEmbedding_apply, triangleEmbedding_apply] at h₃
  exact ⟨h₁, h₂, h₃⟩

/-- Component traversal is conjugated by the local rewire. -/
theorem componentPerm_reidemeisterThree :
    (D.reidemeisterThree c).componentPerm =
      (reidemeisterThreePerm D c).permCongr D.componentPerm := by
  rw [componentPerm_def, componentPerm_def, Equiv.permCongr_mul,
    reidemeisterThreePerm_crossingTurn, reidemeisterThree_edgePair]
  simp only [crossingTurn_def, reidemeisterThree]

/-- The third Reidemeister move preserves crossing-bearing link components. -/
@[simp] theorem crossingComponentCount_reidemeisterThree :
    (D.reidemeisterThree c).crossingComponentCount = D.crossingComponentCount := by
  simp [crossingComponentCount_def, componentPerm_reidemeisterThree]

/-- The third Reidemeister move preserves the total number of link components. -/
@[simp] theorem componentCount_reidemeisterThree :
    (D.reidemeisterThree c).componentCount = D.componentCount := by
  simp [componentCount_eq]

/-- Reversing every strand height preserves the three internal triangle arcs. -/
@[simp] theorem hasReidemeisterThreeTriangleArcs_mirror_iff :
    D.mirror.HasReidemeisterThreeTriangleArcs c ↔ D.HasReidemeisterThreeTriangleArcs c := by
  simp only [hasReidemeisterThreeTriangleArcs_iff, mirror_edgePair, crossing_mirror]

/-- Reversing every strand height preserves the triangle condition. -/
@[simp] theorem hasReidemeisterThreeTriangle_mirror_iff :
    D.mirror.HasReidemeisterThreeTriangle c ↔ D.HasReidemeisterThreeTriangle c := by
  simp only [hasReidemeisterThreeTriangle_iff, mirror_edgePair, crossing_mirror,
    mirror_overPair, Bool.not_inj_iff]

/-- The local half-edge rewire is independent of the strand heights. -/
@[simp] theorem reidemeisterThreePerm_mirror :
    D.mirror.reidemeisterThreePerm c = D.reidemeisterThreePerm c := by
  simp [reidemeisterThreePerm, triangleEmbedding]

/-- Mirroring commutes with the third Reidemeister move. -/
@[simp] theorem mirror_reidemeisterThree :
    (D.reidemeisterThree c).mirror =
      D.mirror.reidemeisterThree c := by
  apply PDCode.ext
  · simp
  · simp [reidemeisterThree]
  · simp
  · funext i
    simp

end TauCeti.PDCode
