/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.AffineE8.Zigzag
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Tree

/-!
# Graphs which are not Dynkin diagrams contain affine diagrams

A connected finite simple graph which is not a simply-laced Dynkin diagram contains a copy, not
necessarily induced, of the graph `TauCeti.AffineDynkinType.graph` of a valid affine simply-laced
diagram other than `Ã₁`. For a tree the copy can be taken of affine type `Dₙ` (`n ≥ 4`), `E₆`,
`E₇` or `E₈`. So an invariant of graphs which is detected on these affine diagrams and survives
passing to a larger graph is present on every connected non-Dynkin graph, or on every non-Dynkin
tree.

The extended Dynkin trees already occur in Tau Ceti as the underlying graphs of the quivers
`TauCeti.Quiver.AffineD m`, `TauCeti.Quiver.AffineE6`, `TauCeti.Quiver.AffineE7` and
`TauCeti.Quiver.AffineE8`, on which Gabriel's theorem is proved, and the graph-theoretic half of
that theorem, `SimpleGraph.IsTree.posDef_graphCartanMatrix`, says that a finite tree containing
none of them is a Dynkin diagram. This file shows that the affine diagrams `Dₘ₊₄`, `E₆`, `E₇` and
`E₈` of `TauCeti.AffineDynkinType` are contained in those underlying graphs, by explicit vertex
maps, and restates the forbidden-subgraph theorem in terms of `TauCeti.AffineDynkinType`. A graph
with a cycle contains the cycle `Ãₙ`
(`SimpleGraph.exists_isContained_affineDynkinType_A_of_not_isAcyclic`), which gives the statement
for connected graphs.

## Main results

* `TauCeti.AffineDynkinType.graph_D_isContained_underlyingGraph_affineD`,
  `graph_E6_isContained_underlyingGraph_affineE6`,
  `graph_E7_isContained_underlyingGraph_affineE7` and
  `graph_E8_isContained_underlyingGraph_affineE8`: the affine diagrams are contained in the
  underlying graphs of the extended Dynkin quivers.
* `SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`: a finite tree
  which is not a Dynkin diagram contains a copy of affine `Dₙ` (`n ≥ 4`), `E₆`, `E₇` or `E₈`.
* `SimpleGraph.Connected.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso`: a
  connected finite graph which is not a Dynkin diagram contains a copy of the graph of a valid
  affine diagram other than `Ã₁`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4 and Table Aff 1.
-/

public section

namespace TauCeti

namespace AffineDynkinType

open _root_.TauCeti.Quiver

/-- **Affine `Dₘ₊₄` is contained in the underlying graph of `TauCeti.Quiver.AffineD m`.** The
chain `1, …, m + 1` of `Dₘ₊₄` goes to the spine, its ends `0` and `m + 2` to the leaves `0` and
`2`, and the leaves `m + 3` and `m + 4` to the leaves `1` and `3`. -/
theorem graph_D_isContained_underlyingGraph_affineD (m : ℕ) :
    (D (m + 4)).graph.IsContained (underlyingGraph (Quiver.AffineD m)) := by
  let φ : Fin (m + 4 + 1) → Quiver.AffineD m := fun i ↦
    if (i : ℕ) = 0 then .leaf 0 else if h : (i : ℕ) ≤ m + 1 then .spine ⟨i - 1, by omega⟩
    else if (i : ℕ) = m + 2 then .leaf 2 else if (i : ℕ) = m + 3 then .leaf 1 else .leaf 3
  -- The five pieces of the vertex map: the chain end `0`, the chain, its other end, and the leaves.
  have hφ (i : Fin (m + 4 + 1)) : ((i : ℕ) = 0 ∧ φ i = .leaf 0) ∨
      (∃ h : 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m + 1, φ i = .spine ⟨i - 1, by omega⟩) ∨
      ((i : ℕ) = m + 2 ∧ φ i = .leaf 2) ∨ ((i : ℕ) = m + 3 ∧ φ i = .leaf 1) ∨
      ((i : ℕ) = m + 4 ∧ φ i = .leaf 3) := by
    have := i.isLt
    by_cases h₀ : (i : ℕ) = 0
    · exact Or.inl ⟨h₀, by simp only [φ]; split_ifs; rfl⟩
    by_cases h₁ : (i : ℕ) ≤ m + 1
    · exact Or.inr (Or.inl ⟨⟨by omega, h₁⟩, by simp only [φ]; split_ifs; rfl⟩)
    by_cases h₂ : (i : ℕ) = m + 2
    · exact Or.inr (Or.inr (Or.inl ⟨h₂, by simp only [φ]; split_ifs; rfl⟩))
    by_cases h₃ : (i : ℕ) = m + 3
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₃, by simp only [φ]; split_ifs; rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [φ]; split_ifs; rfl⟩)))
  refine isContained_underlyingGraph_of_injective φ (fun i j h ↦ ?_) (fun i j h ↦ ?_)
  · rcases hφ i with ⟨hi, hφi⟩ | ⟨hi, hφi⟩ | ⟨hi, hφi⟩ | ⟨hi, hφi⟩ | ⟨hi, hφi⟩ <;>
      rcases hφ j with ⟨hj, hφj⟩ | ⟨hj, hφj⟩ | ⟨hj, hφj⟩ | ⟨hj, hφj⟩ | ⟨hj, hφj⟩ <;>
      rw [hφi, hφj] at h <;> simp at h <;> exact Fin.ext (by omega)
  · replace h := (graph_D_adj (n := m + 4) (by omega)).mp h
    rcases hφ i with ⟨hi, hφi⟩ | ⟨hi, hφi⟩ | ⟨hi, hφi⟩ | ⟨hi, hφi⟩ | ⟨hi, hφi⟩ <;>
      rcases hφ j with ⟨hj, hφj⟩ | ⟨hj, hφj⟩ | ⟨hj, hφj⟩ | ⟨hj, hφj⟩ | ⟨hj, hφj⟩ <;>
      rw [hφi, hφj] <;> simp [Fin.ext_iff] <;> omega

/-- **Affine `E₆` is contained in the underlying graph of `TauCeti.Quiver.AffineE6`.** The
trivalent node `0` goes to the centre, and the arm `2 k + 1, 2 k + 2` to the inner and outer
vertices of the arm `k`. -/
theorem graph_E6_isContained_underlyingGraph_affineE6 :
    E6.graph.IsContained (underlyingGraph Quiver.AffineE6) := by
  let φ : Fin 7 → Quiver.AffineE6 :=
    ![.center, .inner 0, .outer 0, .inner 1, .outer 1, .inner 2, .outer 2]
  refine isContained_underlyingGraph_of_injective φ
    (fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [φ] at h ⊢) fun i j h ↦ ?_
  rw [graph_E6_adj] at h
  fin_cases i <;> fin_cases j <;> simp at h <;>
    first
      | exact Or.inl ⟨Quiver.AffineE6.innerArrow _⟩
      | exact Or.inr ⟨Quiver.AffineE6.innerArrow _⟩
      | exact Or.inl ⟨Quiver.AffineE6.outerArrow _⟩
      | exact Or.inr ⟨Quiver.AffineE6.outerArrow _⟩

/-- **Affine `E₇` is contained in the underlying graph of `TauCeti.Quiver.AffineE7`.** The
trivalent node `0` goes to the centre, the leaf `1` to the short vertex, and the arms `2, 3, 4`
and `5, 6, 7` to the inner, middle and outer vertices of the two long arms. -/
theorem graph_E7_isContained_underlyingGraph_affineE7 :
    E7.graph.IsContained (underlyingGraph Quiver.AffineE7) := by
  let φ : Fin 8 → Quiver.AffineE7 :=
    ![.center, .short, .inner 0, .middle 0, .outer 0, .inner 1, .middle 1, .outer 1]
  refine isContained_underlyingGraph_of_injective φ
    (fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [φ] at h ⊢) fun i j h ↦ ?_
  rw [graph_E7_adj] at h
  fin_cases i <;> fin_cases j <;> simp at h <;>
    first
      | exact Or.inl ⟨Quiver.AffineE7.Arrow.shortCenter⟩
      | exact Or.inr ⟨Quiver.AffineE7.Arrow.shortCenter⟩
      | exact Or.inl ⟨Quiver.AffineE7.Arrow.innerCenter _⟩
      | exact Or.inr ⟨Quiver.AffineE7.Arrow.innerCenter _⟩
      | exact Or.inl ⟨Quiver.AffineE7.Arrow.middleInner _⟩
      | exact Or.inr ⟨Quiver.AffineE7.Arrow.middleInner _⟩
      | exact Or.inl ⟨Quiver.AffineE7.Arrow.outerMiddle _⟩
      | exact Or.inr ⟨Quiver.AffineE7.Arrow.outerMiddle _⟩

/-- **Affine `E₈` is contained in the underlying graph of `TauCeti.Quiver.AffineE8`.** This is
the graph isomorphism `TauCeti.affineE8UnderlyingGraphIso`, which sends the trivalent node `0` to
the centre, the leaf `1` to the short vertex, the arm `2, 3` to the medium arm, and the arm
`4, …, 8` to the long arm, each numbered outwards. -/
theorem graph_E8_isContained_underlyingGraph_affineE8 :
    E8.graph.IsContained (underlyingGraph Quiver.AffineE8) :=
  affineE8UnderlyingGraphIso.isContained'

end AffineDynkinType

end TauCeti

namespace SimpleGraph

open TauCeti

variable {V : Type*} {G : SimpleGraph V}

/-- **A finite tree which is not a Dynkin diagram contains affine `Dₙ`, `E₆`, `E₇` or `E₈`.** If
a finite tree is not isomorphic to the diagram of any valid Dynkin type, then it contains a copy,
not necessarily induced, of affine `Dₙ` for some `n ≥ 4`, or of affine `E₆`, `E₇` or `E₈`. -/
theorem IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso [Finite V]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    (∃ n, 4 ≤ n ∧ (AffineDynkinType.D n).graph ⊑ G) ∨ AffineDynkinType.E6.graph ⊑ G ∨
      AffineDynkinType.E7.graph ⊑ G ∨ AffineDynkinType.E8.graph ⊑ G := by
  classical
  by_contra h
  rw [not_or, not_or, not_or] at h
  obtain ⟨hDn, hE₆, hE₇, hE₈⟩ := h
  refine hD ((exists_valid_isSimplyLaced_dynkinType_iso_iff G).mp
    ((posDef_graphCartanMatrix_iff hG.connected).mp (hG.posDef_graphCartanMatrix ?_ ?_ ?_ ?_)))
  · exact fun m hm ↦ hDn ⟨m + 4, by omega,
      (AffineDynkinType.graph_D_isContained_underlyingGraph_affineD m).trans hm⟩
  · exact fun h ↦ hE₆ (AffineDynkinType.graph_E6_isContained_underlyingGraph_affineE6.trans h)
  · exact fun h ↦ hE₇ (AffineDynkinType.graph_E7_isContained_underlyingGraph_affineE7.trans h)
  · exact fun h ↦ hE₈ (AffineDynkinType.graph_E8_isContained_underlyingGraph_affineE8.trans h)

/-- **A connected finite graph which is not a Dynkin diagram contains an affine diagram.** If a
connected finite simple graph is not isomorphic to the diagram of any valid Dynkin type, then it
contains a copy, not necessarily induced, of the graph of a valid affine simply-laced diagram other
than `Ã₁`: a cycle `Ãₙ` with `n ≥ 2` if the graph has a cycle, and otherwise affine `Dₙ`, `E₆`,
`E₇` or `E₈`. -/
theorem Connected.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso [Finite V]
    (hG : G.Connected)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ t : AffineDynkinType, t.Valid ∧ t.IsGraphical ∧ t.graph ⊑ G := by
  by_cases hac : G.IsAcyclic
  · rcases IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso ⟨hG, hac⟩ hD with
      ⟨n, hn, h⟩ | h | h | h
    · exact ⟨.D n, AffineDynkinType.valid_D.mpr hn, AffineDynkinType.isGraphical_D n, h⟩
    · exact ⟨.E6, AffineDynkinType.valid_E6, AffineDynkinType.isGraphical_E6, h⟩
    · exact ⟨.E7, AffineDynkinType.valid_E7, AffineDynkinType.isGraphical_E7, h⟩
    · exact ⟨.E8, AffineDynkinType.valid_E8, AffineDynkinType.isGraphical_E8, h⟩
  · obtain ⟨n, hn, h⟩ := exists_isContained_affineDynkinType_A_of_not_isAcyclic hac
    exact ⟨.A n, AffineDynkinType.valid_A.mpr (by omega),
      AffineDynkinType.isGraphical_A.mpr (by omega), h⟩

end SimpleGraph
