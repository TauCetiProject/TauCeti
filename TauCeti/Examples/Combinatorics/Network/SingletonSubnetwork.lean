/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Subnetwork

/-!
# A singleton subnetwork of a larger network

Consider the network on three vertices with one arrow between every ordered pair. Its singleton
subnetwork at vertex `1` has its own one-element vertex type and no arrows, even though the ambient
network contains arrows between the two omitted vertices and every other ordered pair.

The example verifies strong connectivity on the subnetwork's vertex subtype. In particular, the
ambient vertices `0` and `2` are not among the endpoints quantified over by strong connectivity.
-/

namespace TauCeti.Examples.SingletonSubnetwork

public section

/-- A complete directed network on three vertices has a strongly connected singleton subnetwork
whose vertex type excludes the other two ambient vertices. The singleton has no arrows, so its
strong connectivity is witnessed entirely by the zero-length walk at its selected vertex. -/
theorem exists_stronglyConnected_singleton_subnetwork :
    ∃ (N : Network.{0, 0, 0} ℕ (Fin 3)) (S : N.Subnetwork),
      (∀ x y, Nonempty (N.Hom x y)) ∧
      (0 : Fin 3) ∉ S.vertexSet ∧
      (2 : Fin 3) ∉ S.vertexSet ∧
      Nat.card S.vertexSet = 1 ∧
      (∀ x y : S.vertexSet, IsEmpty (S.Hom x y)) ∧
      @Quiver.IsStronglyConnected S.vertexSet ⟨S.Hom⟩ := by
  let N : Network ℕ (Fin 3) :=
    Network.ofCapacity (fun _ _ ↦ Unit) (fun _ ↦ 1) (by simp)
  refine ⟨N, N.singletonSubnetwork 1, fun _ _ ↦ ⟨()⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · intro x y
    exact ⟨fun e ↦ by simpa using e.2⟩
  · exact Network.Subnetwork.isStronglyConnected_singleton (N := N) 1

end

end TauCeti.Examples.SingletonSubnetwork
