/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Elliptic

/-!
# Finite subgroups of the fundamental group of a graph of groups

A finite group acting on a tree without inversions fixes a vertex
(`TauCeti.GTree.isEllipticSubgroup_of_finite`). Applied to the action of the fundamental group
`π₁(𝔸, a)` of a graph of groups on its Bass–Serre tree, whose elliptic subgroups are those
contained in a conjugate `p A_b p⁻¹` of a vertex group
(`TauCeti.GraphOfGroups.bassSerreTree_isEllipticSubgroup_iff`), this shows that every finite
subgroup of `π₁(𝔸, a)`, and every element of finite order, lies in a conjugate of a vertex group.
Consequently the fundamental group of a graph of torsion-free groups is torsion-free.

## Main results

* `TauCeti.GraphOfGroups.π₁.exists_le_range_vertexHom_of_finite`: a finite subgroup of
  `π₁(𝔸, a)` lies in a conjugate `p A_b p⁻¹` of a vertex group.
* `TauCeti.GraphOfGroups.π₁.exists_vertexHom_eq_of_isOfFinOrder`: an element of finite order of
  `π₁(𝔸, a)` is the conjugate `p y p⁻¹` of an element `y` of finite order of a vertex group.
* `TauCeti.GraphOfGroups.π₁.instIsMulTorsionFree`,
  `TauCeti.GraphOfGroups.π₁Tree.isMulTorsionFree`: the fundamental group of a graph of
  torsion-free groups is torsion-free.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12 (the Bass–Serre tree and its vertex
  stabilizers) and §6.5, Proposition 26 and its corollaries (Serre's lemma).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.2, p. 16 (a
  subgroup is elliptic in the Bass–Serre tree exactly when it lies in a conjugate of a vertex
  group; finite groups have Serre's property (FA)).
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

namespace π₁

/-- A finite subgroup of `π₁(𝔸, a)` lies in a conjugate `p A_b p⁻¹` of a vertex group: it fixes a
vertex of the Bass–Serre tree. -/
theorem exists_le_range_vertexHom_of_finite (H : Subgroup (π₁ 𝔸 a)) [Finite H] :
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), H ≤ (vertexHom p).range :=
  bassSerreTree_isEllipticSubgroup_iff.mp (GTree.isEllipticSubgroup_of_finite H)

/-- An element of finite order of `π₁(𝔸, a)` is the conjugate `p y p⁻¹` of an element `y` of finite
order of a vertex group `A_b`. -/
theorem exists_vertexHom_eq_of_isOfFinOrder {g : π₁ 𝔸 a} (hg : IsOfFinOrder g) :
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (y : 𝔸.vertexGroup b),
      IsOfFinOrder y ∧ vertexHom p y = g := by
  obtain ⟨b, p, z, rfl⟩ := bassSerreTree_isElliptic_iff.mp
    (GTree.isElliptic_of_isOfFinOrder (T := bassSerreTree 𝔸 a) hg)
  exact ⟨b, p, z, (vertexHom_injective p).isOfFinOrder_iff.mp hg, rfl⟩

/-- The fundamental group of a graph of torsion-free groups is torsion-free. -/
instance instIsMulTorsionFree [∀ b, IsMulTorsionFree (𝔸.vertexGroup b)] :
    IsMulTorsionFree (π₁ 𝔸 a) :=
  isMulTorsionFree_iff_not_isOfFinOrder.mpr fun g hg1 hg ↦ by
    obtain ⟨b, p, y, hy, rfl⟩ := exists_vertexHom_eq_of_isOfFinOrder hg
    exact hg1 (by rw [hy.eq_one', map_one])

end π₁

/-- The fundamental group `π₁(𝔸, T)` of a graph of torsion-free groups, relative to a spanning
tree `T`, is torsion-free. -/
theorem π₁Tree.isMulTorsionFree [∀ b, IsMulTorsionFree (𝔸.vertexGroup b)] (T : Γ.SpanningTree) :
    IsMulTorsionFree (π₁Tree 𝔸 T.darts) := by
  obtain ⟨v⟩ := ((SerreGraph.connected_iff _).mp T.isTree.connected).1
  exact (π₁Equiv 𝔸 v T).symm.injective.isMulTorsionFree (π₁Equiv 𝔸 v T).symm.toMonoidHom

end GraphOfGroups

end TauCeti
