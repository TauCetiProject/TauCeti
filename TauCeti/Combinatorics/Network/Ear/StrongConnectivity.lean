/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Ear.Basic

/-!
# Strong connectivity from directed ear decompositions

Adjoining a directed open or closed ear to a strongly connected subnetwork preserves strong
connectivity. Consequently, every prefix of a directed ear decomposition is strongly connected,
including its final subnetwork. For a decomposition of the full subnetwork this gives strong
connectivity of the ambient arrow family.

The proof records the two reachability properties of an ear that are useful independently. Every
vertex of an adjoined ear is reachable from an old vertex and can reach an old vertex: for an open
ear, follow a prefix from its old source and a suffix to its old target; for a closed ear, use the
two pieces obtained by splitting its cycle at the chosen vertex.

## Main results

* `TauCeti.Network.Ear.isStronglyConnected_adjoin`: adjoining an ear preserves strong
  connectivity.
* `TauCeti.Network.EarDecomposition.isStronglyConnected_stage`: every prefix stage is strongly
  connected.
* `TauCeti.Network.EarDecomposition.isStronglyConnected`: the final subnetwork of a directed ear
  decomposition is strongly connected.
* `TauCeti.Network.EarDecomposition.isStronglyConnected_full`: a decomposition of the full
  subnetwork makes the ambient arrow family strongly connected.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.3.
-/

public section

namespace TauCeti.Network

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace Ear

variable {S : N.Subnetwork}

/-- Every vertex obtained by adjoining an ear is reachable from some vertex of the old
subnetwork. -/
theorem exists_reachable_from_vertexSet (P : Ear S) {x : V} (hx : x ∈ P.adjoin.vertexSet) :
    ∃ a ∈ S.vertexSet, P.adjoin.Reachable a x := by
  rw [P.adjoin_vertexSet] at hx
  rcases hx with hx | hx
  · exact ⟨x, hx, .refl _ _⟩
  · cases P with
    | «open» P =>
        rw [Ear.toSubnetwork_open] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.open P).adjoin := by
          simpa only [Ear.toSubnetwork_open] using (Ear.open P).toSubnetwork_le_adjoin
        exact ⟨P.source, P.source_mem,
          (P.walk.reachable_of_mem_vertices hx').1.mono hP⟩
    | closed P =>
        rw [Ear.toSubnetwork_closed] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.closed P).adjoin := by
          simpa only [Ear.toSubnetwork_closed] using (Ear.closed P).toSubnetwork_le_adjoin
        exact ⟨P.base, P.base_mem,
          (P.walk.reachable_of_mem_vertices hx').1.mono hP⟩

/-- Every vertex obtained by adjoining an ear can reach some vertex of the old subnetwork. -/
theorem exists_reachable_to_vertexSet (P : Ear S) {x : V} (hx : x ∈ P.adjoin.vertexSet) :
    ∃ a ∈ S.vertexSet, P.adjoin.Reachable x a := by
  rw [P.adjoin_vertexSet] at hx
  rcases hx with hx | hx
  · exact ⟨x, hx, .refl _ _⟩
  · cases P with
    | «open» P =>
        rw [Ear.toSubnetwork_open] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.open P).adjoin := by
          simpa only [Ear.toSubnetwork_open] using (Ear.open P).toSubnetwork_le_adjoin
        exact ⟨P.target, P.target_mem,
          (P.walk.reachable_of_mem_vertices hx').2.mono hP⟩
    | closed P =>
        rw [Ear.toSubnetwork_closed] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.closed P).adjoin := by
          simpa only [Ear.toSubnetwork_closed] using (Ear.closed P).toSubnetwork_le_adjoin
        exact ⟨P.base, P.base_mem,
          (P.walk.reachable_of_mem_vertices hx').2.mono hP⟩

/-- Adjoining a directed open or closed ear to a strongly connected subnetwork preserves strong
connectivity. -/
theorem isStronglyConnected_adjoin (P : Ear S)
    (hS : @Quiver.IsStronglyConnected ↥S.vertexSet ⟨S.Hom⟩) :
    @Quiver.IsStronglyConnected ↥P.adjoin.vertexSet ⟨P.adjoin.Hom⟩ := by
  rw [Subnetwork.isStronglyConnected_iff] at hS ⊢
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := P.exists_reachable_to_vertexSet hx
  obtain ⟨b, hb, hby⟩ := P.exists_reachable_from_vertexSet hy
  exact hxa.trans ((hS a ha b hb).mono P.le_adjoin) |>.trans hby

end Ear

namespace EarDecomposition

variable {T : N.Subnetwork}

/-- Every prefix stage of a directed ear decomposition is strongly connected. -/
theorem isStronglyConnected_stage (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    @Quiver.IsStronglyConnected ↥(D.stage j).vertexSet ⟨(D.stage j).Hom⟩ := by
  refine D.stage_induction
    (fun S ↦ @Quiver.IsStronglyConnected ↥S.vertexSet ⟨S.Hom⟩) ?_ ?_ j
  · exact Subnetwork.isStronglyConnected_singleton D.initialVertex
  · intro i hi
    exact (D.ear i).isStronglyConnected_adjoin hi

/-- The final subnetwork of every directed ear decomposition is strongly connected. -/
theorem isStronglyConnected (D : EarDecomposition T) :
    @Quiver.IsStronglyConnected ↥T.vertexSet ⟨T.Hom⟩ := by
  rw [← D.stage_last]
  exact D.isStronglyConnected_stage (Fin.last D.length)

/-- A directed ear decomposition of the full subnetwork makes the ambient arrow family strongly
connected. -/
theorem isStronglyConnected_full (D : EarDecomposition (⊤ : N.Subnetwork)) :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ := by
  intro x y
  have h := (Subnetwork.isStronglyConnected_iff (⊤ : N.Subnetwork)).1
    D.isStronglyConnected x (by simp) y (by simp)
  exact Subnetwork.reachable_top_iff.1 h

end EarDecomposition

end TauCeti.Network
