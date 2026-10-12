/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
public import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Disjoint unions of PD-codes

Placing two diagrams in disjoint discs concatenates their crossings and arcs. Crossing-free
circles are retained separately. This operation allows a local diagram replacement on an isolated
component to be used in the presence of an arbitrary surrounding diagram.

The number of link components and the number of circles in each smoothing are additive. For
nonempty diagrams the normalized convention `⟨unknot⟩ = 1` gives
`⟨D ⊔ E⟩ = δ ⟨D⟩ ⟨E⟩`, where `δ = -(a² + a⁻²)`. The nonemptiness conditions matter:
the empty diagram has bracket `1`, and adjoining it contributes no factor of `δ`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the state sum and its circle normalization).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm TemperleyLieb

variable {n m : ℕ}

/-- Number the half-edges of two disjoint diagrams consecutively. -/
def disjointUnionHalfEdgeEquiv (n m : ℕ) :
    Fin (4 * n) ⊕ Fin (4 * m) ≃ Fin (4 * (n + m)) :=
  finSumFinEquiv.trans (finCongr (Nat.mul_add 4 n m).symm)

/-- The first diagram's crossing slots occupy the first block of crossings. -/
@[simp]
theorem disjointUnionHalfEdgeEquiv_inl_crossingSlot (i : Fin n) (slot : Fin 4) :
    disjointUnionHalfEdgeEquiv n m (.inl (crossingSlotEquiv n (i, slot))) =
      crossingSlotEquiv (n + m) (Fin.castAdd m i, slot) := by
  apply Fin.ext
  simp [disjointUnionHalfEdgeEquiv, crossingSlotEquiv_apply_val]

/-- The second diagram's crossing slots occupy the second block of crossings. -/
@[simp]
theorem disjointUnionHalfEdgeEquiv_inr_crossingSlot (i : Fin m) (slot : Fin 4) :
    disjointUnionHalfEdgeEquiv n m (.inr (crossingSlotEquiv m (i, slot))) =
      crossingSlotEquiv (n + m) (Fin.natAdd n i, slot) := by
  apply Fin.ext
  simp [disjointUnionHalfEdgeEquiv, crossingSlotEquiv_apply_val]
  omega

/-- Splitting a slot in the first crossing block recovers its original label. -/
@[simp]
theorem disjointUnionHalfEdgeEquiv_symm_crossingSlot_castAdd (i : Fin n) (slot : Fin 4) :
    (disjointUnionHalfEdgeEquiv n m).symm
        (crossingSlotEquiv (n + m) (Fin.castAdd m i, slot)) =
      .inl (crossingSlotEquiv n (i, slot)) := by
  apply (disjointUnionHalfEdgeEquiv n m).injective
  simp

/-- Splitting a slot in the second crossing block recovers its original label. -/
@[simp]
theorem disjointUnionHalfEdgeEquiv_symm_crossingSlot_natAdd (i : Fin m) (slot : Fin 4) :
    (disjointUnionHalfEdgeEquiv n m).symm
        (crossingSlotEquiv (n + m) (Fin.natAdd n i, slot)) =
      .inr (crossingSlotEquiv m (i, slot)) := by
  apply (disjointUnionHalfEdgeEquiv n m).injective
  simp

/-- The disjoint union of two PD-codes. Both the crossing labels and the half-edge labels are
concatenated, and the arc matching never joins the two blocks. -/
def disjointUnion (D : PDCode n) (E : PDCode m) : PDCode (n + m) where
  halfEdge := (disjointUnionHalfEdgeEquiv n m).permCongr (Perm.sumCongr D.halfEdge E.halfEdge)
  edgePair := (PerfectMatching.mk (Perm.sumCongr D.edgePair.val E.edgePair.val)
    (by rintro (x | x) <;> simp)
    (by rintro (x | x) <;> simp)).congr (disjointUnionHalfEdgeEquiv n m)
  overPair := Fin.addCases D.overPair E.overPair
  crossinglessComponentCount := D.crossinglessComponentCount + E.crossinglessComponentCount

variable (D : PDCode n) (E : PDCode m)

/-- The half-edge labelling acts separately on the two blocks. -/
@[simp]
theorem disjointUnion_halfEdge :
    (D.disjointUnion E).halfEdge =
      (disjointUnionHalfEdgeEquiv n m).permCongr (Perm.sumCongr D.halfEdge E.halfEdge) := (rfl)

/-- The arc matching acts separately on the two blocks. -/
@[simp]
theorem disjointUnion_edgePair_val :
    (D.disjointUnion E).edgePair.val =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr D.edgePair.val E.edgePair.val) := by
  simp [disjointUnion, PerfectMatching.congr_val]

/-- Disjoint union adds the crossing-free circles. -/
@[simp]
theorem disjointUnion_crossinglessComponentCount :
    (D.disjointUnion E).crossinglessComponentCount =
      D.crossinglessComponentCount + E.crossinglessComponentCount := (rfl)

/-- The over-strand at a crossing of the first summand is unchanged. -/
@[simp]
theorem disjointUnion_overPair_castAdd (i : Fin n) :
    (D.disjointUnion E).overPair (Fin.castAdd m i) = D.overPair i := by
  simp [disjointUnion]

/-- The over-strand at a crossing of the second summand is unchanged. -/
@[simp]
theorem disjointUnion_overPair_natAdd (i : Fin m) :
    (D.disjointUnion E).overPair (Fin.natAdd n i) = E.overPair i := by
  simp [disjointUnion]

/-- A crossing of the first diagram retains its four incident half-edges. -/
theorem crossing_disjointUnion_castAdd (i : Fin n) (slot : Fin 4) :
    (D.disjointUnion E).crossing (Fin.castAdd m i) slot =
      disjointUnionHalfEdgeEquiv n m (.inl (D.crossing i slot)) := by
  rw [crossing_apply, ← disjointUnionHalfEdgeEquiv_inl_crossingSlot,
    disjointUnion_halfEdge]
  simp [crossing_apply]

/-- A crossing of the second diagram retains its four incident half-edges. -/
theorem crossing_disjointUnion_natAdd (i : Fin m) (slot : Fin 4) :
    (D.disjointUnion E).crossing (Fin.natAdd n i) slot =
      disjointUnionHalfEdgeEquiv n m (.inr (E.crossing i slot)) := by
  rw [crossing_apply, ← disjointUnionHalfEdgeEquiv_inr_crossingSlot,
    disjointUnion_halfEdge]
  simp [crossing_apply]

/-- The strand traversal acts separately on the two diagrams. -/
@[simp]
theorem crossingTurn_disjointUnion :
    (D.disjointUnion E).crossingTurn =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr D.crossingTurn E.crossingTurn) := by
  ext x
  obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
  rcases x with x | x
  · obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    rw [← D.crossing_apply, ← crossing_disjointUnion_castAdd, crossing_apply,
      crossingTurn_crossing]
    simp [crossing_apply]
  · obtain ⟨x, rfl⟩ := E.halfEdge.surjective x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv m).surjective x
    rw [← E.crossing_apply, ← crossing_disjointUnion_natAdd, crossing_apply,
      crossingTurn_crossing]
    simp [crossing_apply]

/-- The component permutation is the disjoint sum of the two component permutations. -/
@[simp]
theorem componentPerm_disjointUnion :
    (D.disjointUnion E).componentPerm =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr D.componentPerm E.componentPerm) := by
  simp only [componentPerm_def, crossingTurn_disjointUnion, disjointUnion_edgePair_val,
    ← permCongr_mul, Perm.sumCongr_mul]

/-- The number of components meeting crossings is additive under disjoint union. -/
@[simp]
theorem crossingComponentCount_disjointUnion :
    (D.disjointUnion E).crossingComponentCount =
      D.crossingComponentCount + E.crossingComponentCount := by
  rw [crossingComponentCount_def, componentPerm_disjointUnion, orbitCount_permCongr,
    orbitCount_sumCongr, crossingComponentCount_def, crossingComponentCount_def,
    Nat.add_div_of_dvd_right (D.even_orbitCount_componentPerm.two_dvd)]

/-- The number of link components is additive under disjoint union, including crossing-free
components. -/
@[simp]
theorem componentCount_disjointUnion :
    (D.disjointUnion E).componentCount = D.componentCount + E.componentCount := by
  simp only [componentCount_eq, crossingComponentCount_disjointUnion,
    disjointUnion_crossinglessComponentCount]
  omega

/-- Reflection commutes with disjoint union. -/
@[simp]
theorem mirror_disjointUnion :
    (D.disjointUnion E).mirror = D.mirror.disjointUnion E.mirror := by
  apply PDCode.ext
  · simp
  · apply Subtype.ext
    simp
  · simp
  · funext i
    induction i using Fin.addCases <;> simp

/-- Smoothing a disjoint union smooths each diagram independently. -/
@[simp]
theorem smoothingTurn_disjointUnion (b : Fin (n + m) → Bool) :
    (D.disjointUnion E).smoothingTurn b =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr (D.smoothingTurn (b ∘ Fin.castAdd m))
          (E.smoothingTurn (b ∘ Fin.natAdd n))) := by
  ext x
  obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
  rcases x with x | x
  · obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    rw [← D.crossing_apply, ← crossing_disjointUnion_castAdd, crossing_apply,
      smoothingTurn_crossing]
    simp [crossing_apply]
  · obtain ⟨x, rfl⟩ := E.halfEdge.surjective x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv m).surjective x
    rw [← E.crossing_apply, ← crossing_disjointUnion_natAdd, crossing_apply,
      smoothingTurn_crossing]
    simp [crossing_apply]

/-- The state traversal is the disjoint sum of the traversals of the restricted states. -/
@[simp]
theorem statePerm_disjointUnion (s : Fin (n + m) → Bool) :
    (D.disjointUnion E).statePerm s =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr (D.statePerm (s ∘ Fin.castAdd m))
          (E.statePerm (s ∘ Fin.natAdd n))) := by
  have hleft : (D.disjointUnion E).smoothingChoice s ∘ Fin.castAdd m =
      D.smoothingChoice (s ∘ Fin.castAdd m) := by
    funext i
    cases hs : s (Fin.castAdd m i) <;> simp [hs, Function.comp_def]
  have hright : (D.disjointUnion E).smoothingChoice s ∘ Fin.natAdd n =
      E.smoothingChoice (s ∘ Fin.natAdd n) := by
    funext i
    cases hs : s (Fin.natAdd n i) <;> simp [hs, Function.comp_def]
  simp only [statePerm_def, smoothingTurn_disjointUnion, hleft, hright,
    disjointUnion_edgePair_val, ← permCongr_mul, Perm.sumCongr_mul]

/-- The smoothing circles of a disjoint union are the circles from the two summands. -/
@[simp]
theorem stateLoopCount_disjointUnion (s : Fin (n + m) → Bool) :
    (D.disjointUnion E).stateLoopCount s =
      D.stateLoopCount (s ∘ Fin.castAdd m) + E.stateLoopCount (s ∘ Fin.natAdd n) := by
  rw [stateLoopCount_def, statePerm_disjointUnion, orbitCount_permCongr, orbitCount_sumCongr,
    Nat.add_div_of_dvd_right ((D.even_orbitCount_statePerm _).two_dvd)]
  simp only [disjointUnion_crossinglessComponentCount, stateLoopCount_def]
  omega

/-! ### The state sum -/

/-- The bracket of the disjoint union of two nonempty diagrams is the product of their brackets
times the circle value. Nonemptiness is measured by the component count, so crossing-free diagrams
are included. -/
@[simp]
theorem kauffmanBracket_disjointUnion {R : Type*} [CommRing R] (a : Rˣ)
    (hD : 0 < D.componentCount) (hE : 0 < E.componentCount) :
    (D.disjointUnion E).kauffmanBracket a =
      jonesDelta a * D.kauffmanBracket a * E.kauffmanBracket a := by
  rw [kauffmanBracket_def, ← (Fin.appendEquiv n m).sum_comp]
  simp only [Fintype.sum_prod_type]
  have hterm (s : Fin n → Bool) (t : Fin m → Bool) :
      (stateWeight (Fin.append s t) a : R) *
          jonesDelta a ^ ((D.disjointUnion E).stateLoopCount (Fin.append s t) - 1) =
        jonesDelta a *
          ((stateWeight s a : R) * jonesDelta a ^ (D.stateLoopCount s - 1)) *
          ((stateWeight t a : R) * jonesDelta a ^ (E.stateLoopCount t - 1)) := by
    have hs := D.one_le_stateLoopCount_of_componentCount_pos hD s
    have ht := E.one_le_stateLoopCount_of_componentCount_pos hE t
    have hexp : D.stateLoopCount s + E.stateLoopCount t - 1 =
        1 + (D.stateLoopCount s - 1) + (E.stateLoopCount t - 1) := by omega
    simp only [stateLoopCount_disjointUnion, Function.comp_def, Fin.append_left,
      Fin.append_right, stateWeight_append, Units.val_mul]
    rw [hexp, pow_add, pow_add, pow_one]
    ring
  simp only [funext (Fin.appendEquiv_apply n m _)]
  simp only [hterm]
  simp only [kauffmanBracket_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- An empty first summand contributes no factor of the circle value. -/
@[simp]
theorem kauffmanBracket_disjointUnion_of_componentCount_eq_zero_left
    {R : Type*} [CommRing R] (a : Rˣ) (hD : D.componentCount = 0) :
    (D.disjointUnion E).kauffmanBracket a = E.kauffmanBracket a := by
  have hn : n = 0 := by
    by_contra hn
    have := D.componentCount_pos hn
    omega
  subst n
  have hc : D.crossinglessComponentCount = 0 := by
    simpa [componentCount_eq] using hD
  rw [kauffmanBracket_def, ← (Fin.appendEquiv 0 m).sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [funext (Fin.appendEquiv_apply 0 m _)]
  simp only [stateLoopCount_disjointUnion, Function.comp_def, Fin.append_left,
    Fin.append_right, stateWeight_append, Units.val_mul]
  simp [hc, stateWeight_def, kauffmanBracket_def]

/-- An empty second summand contributes no factor of the circle value. -/
@[simp]
theorem kauffmanBracket_disjointUnion_of_componentCount_eq_zero_right
    {R : Type*} [CommRing R] (a : Rˣ) (hE : E.componentCount = 0) :
    (D.disjointUnion E).kauffmanBracket a = D.kauffmanBracket a := by
  have hm : m = 0 := by
    by_contra hm
    have := E.componentCount_pos hm
    omega
  subst m
  have hc : E.crossinglessComponentCount = 0 := by
    simpa [componentCount_eq] using hE
  rw [kauffmanBracket_def, ← (Fin.appendEquiv n 0).sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [funext (Fin.appendEquiv_apply n 0 _)]
  simp only [stateLoopCount_disjointUnion, Function.comp_def, Fin.append_left,
    Fin.append_right, stateWeight_append, Units.val_mul]
  simp [hc, stateWeight_def, kauffmanBracket_def]

end TauCeti.PDCode
