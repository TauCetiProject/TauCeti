/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Basic.Real.Basic
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Field

/-!
# Related-pair counts between finsets

Facts about Mathlib's `Rel.interedges` and `Rel.edgeDensity` used when comparing edge densities
across a refinement of finite partitions: the edge count between two finsets is their size product
times their edge density (with no nonemptiness hypothesis, since both sides vanish on an empty
finset), edge counts are additive over disjoint unions on either side, and the edge count between
two finsets splits along the traces of the parts of finite partitions on them. The corresponding
`SimpleGraph` results are specializations to the adjacency relation. Edge densities are invariant
under relabelling the vertices along an equivalence (`SimpleGraph.edgeDensity_comap_symm`).

For graphs, `SimpleGraph.patternDensity G e s t` is the edge density of `(s, t)` if `e` holds and
the nonedge density `1 - d(s, t)` otherwise: the density factor of a pair in the predicted count
of an induced pattern. It lies in `[0, 1]` and changes by exactly as much as the edge density.
-/

public section

open Finset

namespace Rel

variable {α β ι : Type*} (r : α → β → Prop) [∀ a, DecidablePred (r a)]

/-- The number of related pairs between two finsets is their size product times their density.
This holds without nonemptiness hypotheses: if either finset is empty, both sides vanish. -/
theorem card_mul_card_mul_edgeDensity (s : Finset α) (t : Finset β) :
    (#s * #t : ℚ) * Rel.edgeDensity r s t = #(Rel.interedges r s t) := by
  rcases eq_or_ne ((#s : ℚ) * #t) 0 with hst | hst
  · have h0 : #s * #t = 0 := by exact_mod_cast hst
    rw [hst, zero_mul, eq_comm, Nat.cast_eq_zero]
    exact Nat.le_zero.1 (h0 ▸ Rel.card_interedges_le_mul r s t)
  · rw [Rel.edgeDensity, mul_div_cancel₀ _ hst]

/-- The real-valued form of `Rel.card_mul_card_mul_edgeDensity`. -/
theorem card_mul_card_mul_edgeDensity_real (s : Finset α) (t : Finset β) :
    (#s * #t : ℝ) * (Rel.edgeDensity r s t : ℝ) = #(Rel.interedges r s t) := by
  exact_mod_cast card_mul_card_mul_edgeDensity r s t

/-- Related-pair counts are additive over a pairwise disjoint union on the left. -/
theorem card_interedges_biUnion_left [DecidableEq α]
    (s : Finset ι) (t : Finset β) (f : ι → Finset α)
    (hf : (s : Set ι).PairwiseDisjoint f) :
    #(Rel.interedges r (s.biUnion f) t) = ∑ i ∈ s, #(Rel.interedges r (f i) t) := by
  classical
  rw [Rel.interedges_biUnion_left, card_biUnion]
  exact fun i hi j hj hij => Rel.interedges_disjoint_left r (hf hi hj hij) t

/-- Related-pair counts are additive over a pairwise disjoint union on the right. -/
theorem card_interedges_biUnion_right [DecidableEq β]
    (s : Finset α) (t : Finset ι) (f : ι → Finset β)
    (hf : (t : Set ι).PairwiseDisjoint f) :
    #(Rel.interedges r s (t.biUnion f)) = ∑ i ∈ t, #(Rel.interedges r s (f i)) := by
  classical
  rw [Rel.interedges_biUnion_right, card_biUnion]
  exact fun i hi j hj hij => Rel.interedges_disjoint_right r s (hf hi hj hij)

/-- The number of related pairs between `A ⊆ s` and `B ⊆ t` splits along the traces on `A` and on
`B` of the parts of finite partitions of `s` and of `t`. -/
theorem card_interedges_eq_sum_parts [DecidableEq α] [DecidableEq β] {s A : Finset α}
    {t B : Finset β} (P : Finpartition s) (Q : Finpartition t) (hA : A ⊆ s) (hB : B ⊆ t) :
    #(Rel.interedges r A B) =
      ∑ C ∈ P.parts, ∑ D ∈ Q.parts, #(Rel.interedges r (A ∩ C) (B ∩ D)) := by
  rw [Rel.card_interedges_finpartition r (P.restrict hA) (Q.restrict hB), sum_product,
    P.sum_restrict hA (fun X ↦ ∑ Y ∈ (Q.restrict hB).parts, #(Rel.interedges r X Y)) (by simp)]
  refine sum_congr rfl fun C _ ↦ ?_
  rw [Q.sum_restrict hB (fun Y ↦ #(Rel.interedges r (C ⊓ A) Y)) (by simp [Rel.interedges])]
  simp_rw [Finset.inf_eq_inter, inter_comm]

/-- The related-pair count between two coarse parts is the sum of the counts between the fine
parts with those coarse parents. -/
theorem sum_sum_card_interedges_fiber {s : Finset α} {t : Finset β}
    [DecidableEq α] [DecidableEq β] {P Q : Finpartition s} {P' Q' : Finpartition t}
    (h : Q ≤ P) (h' : Q' ≤ P')
    (A : P.parts) (C : P'.parts) :
    ∑ B with Finpartition.refinementParent h B = A,
      ∑ D with Finpartition.refinementParent h' D = C,
        #(Rel.interedges r B.1 D.1) = #(Rel.interedges r A.1 C.1) := by
  conv_rhs => rw [← Finpartition.biUnion_filter_refinementParent_eq h A,
    ← Finpartition.biUnion_filter_refinementParent_eq h' C,
    card_interedges_biUnion_left r _ _ _ (Q.pairwiseDisjoint_subtype_val _)]
  refine sum_congr rfl fun B _ => ?_
  rw [card_interedges_biUnion_right r _ _ _ (Q'.pairwiseDisjoint_subtype_val _)]

/-- The real-valued form of `Rel.sum_sum_card_interedges_fiber`. -/
theorem sum_sum_card_interedges_fiber_real {s : Finset α} {t : Finset β}
    [DecidableEq α] [DecidableEq β] {P Q : Finpartition s} {P' Q' : Finpartition t}
    (h : Q ≤ P) (h' : Q' ≤ P') (A : P.parts) (C : P'.parts) :
    ∑ B with Finpartition.refinementParent h B = A,
      ∑ D with Finpartition.refinementParent h' D = C,
        (#(Rel.interedges r B.1 D.1) : ℝ) = #(Rel.interedges r A.1 C.1) := by
  exact_mod_cast sum_sum_card_interedges_fiber r h h' A C

end Rel

namespace SimpleGraph

variable {V ι : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of edges between two finsets is their size product times their edge density. This
holds without nonemptiness hypotheses: if either finset is empty, both sides vanish. -/
theorem card_mul_card_mul_edgeDensity (s t : Finset V) :
    (#s * #t : ℚ) * G.edgeDensity s t = #(G.interedges s t) :=
  Rel.card_mul_card_mul_edgeDensity G.Adj s t

/-- The real-valued form of `SimpleGraph.card_mul_card_mul_edgeDensity`. -/
theorem card_mul_card_mul_edgeDensity_real (s t : Finset V) :
    (#s * #t : ℝ) * (G.edgeDensity s t : ℝ) = #(G.interedges s t) :=
  Rel.card_mul_card_mul_edgeDensity_real G.Adj s t

/-- **Edge densities are invariant under relabelling.** Relabelling the vertices along `e`, the
graph as `G.comap e.symm` and both finsets by mapping along `e`, leaves the edge density unchanged.
-/
@[simp]
theorem edgeDensity_comap_symm {W : Type*} (e : V ≃ W) (s t : Finset V) :
    (G.comap e.symm).edgeDensity (s.map e.toEmbedding) (t.map e.toEmbedding) =
      G.edgeDensity s t := by
  rw [edgeDensity_def, edgeDensity_def, card_map, card_map]
  congr 3
  -- the related pairs correspond under `e` in each coordinate
  refine card_bij' (fun p _ => (e.symm p.1, e.symm p.2)) (fun p _ => (e p.1, e p.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ h
    simp only [mem_interedges_iff, mem_map, Equiv.coe_toEmbedding, comap_adj] at h ⊢
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hab⟩ := h
    simpa [ha, hb] using hab
  · rintro ⟨x, y⟩ h
    simp only [mem_interedges_iff, mem_map, Equiv.coe_toEmbedding, comap_adj] at h ⊢
    exact ⟨⟨x, h.1, rfl⟩, ⟨y, h.2.1, rfl⟩, by simpa using h.2.2⟩
  · rintro ⟨x, y⟩ _
    simp
  · rintro ⟨x, y⟩ _
    simp

section patternDensity

variable {𝕜 : Type*}

/-- The edge density of `(s, t)` if `e` holds, and its nonedge density `1 - d(s, t)` otherwise.
This is the density factor of a pair in the predicted count of an induced pattern, where `e`
records whether the pattern has an edge there. -/
noncomputable def patternDensity [DivisionRing 𝕜] (e : Prop) [Decidable e] (s t : Finset V) :
    𝕜 :=
  if e then (G.edgeDensity s t : 𝕜) else 1 - G.edgeDensity s t

theorem patternDensity_def [DivisionRing 𝕜] (e : Prop) [Decidable e] (s t : Finset V) :
    (G.patternDensity e s t : 𝕜) = if e then (G.edgeDensity s t : 𝕜) else 1 - G.edgeDensity s t :=
  (rfl)

/-- Where the pattern has an edge, its density factor is the edge density. -/
@[simp]
theorem patternDensity_of_pos [DivisionRing 𝕜] {e : Prop} [Decidable e] (he : e)
    (s t : Finset V) : (G.patternDensity e s t : 𝕜) = G.edgeDensity s t :=
  ite_eq_left he

/-- Where the pattern has no edge, its density factor is the nonedge density. -/
@[simp]
theorem patternDensity_of_neg [DivisionRing 𝕜] {e : Prop} [Decidable e] (he : ¬e)
    (s t : Finset V) : (G.patternDensity e s t : 𝕜) = 1 - G.edgeDensity s t :=
  ite_eq_right he

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- An edge or nonedge density is nonnegative. -/
theorem patternDensity_nonneg (e : Prop) [Decidable e] (s t : Finset V) :
    0 ≤ (G.patternDensity e s t : 𝕜) := by
  rw [patternDensity_def]
  split_ifs
  · exact_mod_cast G.edgeDensity_nonneg s t
  · exact sub_nonneg.2 (mod_cast G.edgeDensity_le_one s t)

/-- An edge or nonedge density is at most one. -/
theorem patternDensity_le_one (e : Prop) [Decidable e] (s t : Finset V) :
    (G.patternDensity e s t : 𝕜) ≤ 1 := by
  rw [patternDensity_def]
  split_ifs
  · exact_mod_cast G.edgeDensity_le_one s t
  · exact sub_le_self _ (mod_cast G.edgeDensity_nonneg s t)

omit [IsStrictOrderedRing 𝕜] in
/-- An edge or nonedge density changes by exactly as much as the edge density. -/
theorem abs_patternDensity_sub (e : Prop) [Decidable e] (s t s' t' : Finset V) :
    |(G.patternDensity e s t : 𝕜) - G.patternDensity e s' t'| =
      |(G.edgeDensity s t : 𝕜) - G.edgeDensity s' t'| := by
  by_cases he : e
  · simp only [patternDensity_of_pos G he]
  · rw [patternDensity_of_neg G he, patternDensity_of_neg G he,
      abs_sub_comm (G.edgeDensity s t : 𝕜)]
    congr 1
    ring

end patternDensity

variable [DecidableEq V]

/-- Edge counts are additive over a pairwise disjoint union on the left. -/
theorem card_interedges_biUnion_left (s : Finset ι) (t : Finset V) (f : ι → Finset V)
    (hf : (s : Set ι).PairwiseDisjoint f) :
    #(G.interedges (s.biUnion f) t) = ∑ i ∈ s, #(G.interedges (f i) t) :=
  Rel.card_interedges_biUnion_left G.Adj s t f hf

/-- Edge counts are additive over a pairwise disjoint union on the right. -/
theorem card_interedges_biUnion_right (s : Finset V) (t : Finset ι) (f : ι → Finset V)
    (hf : (t : Set ι).PairwiseDisjoint f) :
    #(G.interedges s (t.biUnion f)) = ∑ i ∈ t, #(G.interedges s (f i)) :=
  Rel.card_interedges_biUnion_right G.Adj s t f hf

/-- The number of edges between `A ⊆ s` and `B ⊆ t` splits along the traces on `A` and on `B` of
the parts of finite partitions of `s` and of `t`. -/
theorem card_interedges_eq_sum_parts {s t A B : Finset V} (P : Finpartition s)
    (Q : Finpartition t) (hA : A ⊆ s) (hB : B ⊆ t) :
    #(G.interedges A B) = ∑ C ∈ P.parts, ∑ D ∈ Q.parts, #(G.interedges (A ∩ C) (B ∩ D)) :=
  Rel.card_interedges_eq_sum_parts G.Adj P Q hA hB

/-- The edge count between two coarse parts is the sum of the edge counts between the fine parts
with those coarse parents. -/
theorem sum_sum_card_interedges_fiber {s : Finset V} {P Q : Finpartition s} (h : Q ≤ P)
    (A C : P.parts) :
    ∑ B with Finpartition.refinementParent h B = A,
      ∑ D with Finpartition.refinementParent h D = C,
        #(G.interedges B.1 D.1) = #(G.interedges A.1 C.1) :=
  Rel.sum_sum_card_interedges_fiber G.Adj h h A C

/-- The real-valued form of `SimpleGraph.sum_sum_card_interedges_fiber`. -/
theorem sum_sum_card_interedges_fiber_real {s : Finset V} {P Q : Finpartition s} (h : Q ≤ P)
    (A C : P.parts) :
    ∑ B with Finpartition.refinementParent h B = A,
      ∑ D with Finpartition.refinementParent h D = C,
        (#(G.interedges B.1 D.1) : ℝ) = #(G.interedges A.1 C.1) :=
  Rel.sum_sum_card_interedges_fiber_real G.Adj h h A C

end SimpleGraph
