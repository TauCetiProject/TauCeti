/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.ArrowWalk
public import TauCeti.Combinatorics.Network.Ear.StrongConnectivity

/-!
# Directed ear decompositions of digraphs

A digraph is viewed through its adjacency arrow family `Digraph.AdjHom`: there is one arrow
`v → w` precisely when `D.Adj v w`.  Giving every such arrow zero lower and upper bounds
packages this family as a network without adding mathematical data.  Directed ears and their
prefix subnetworks can then use the network ear-decomposition API unchanged.

For a finite nonempty vertex type, this identifies strong connectivity of a digraph with the
existence of a decomposition starting at one vertex and adjoining directed open or closed ears
until every vertex and adjacency arrow is covered.  Loops appear as one-arrow closed ears.

The characterization follows J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and
Applications*, 2nd ed., Springer, 2009, Section 5.3.
-/

public section

open TauCeti

universe u

namespace Digraph

variable {V : Type u} (D : Digraph V)

/-- The zero-capacity network whose arrows are the adjacencies of a digraph.

Its bounds are irrelevant to directed ears; this adapter lets the network ear-decomposition API
retain the endpoints and identity of each adjacency arrow. -/
abbrev earNetwork : Network ℕ V :=
  Network.ofCapacity D.AdjHom 0 fun _ ↦ le_rfl

/-- A directed ear decomposition covering every vertex and adjacency arrow of a digraph. -/
abbrev EarDecomposition :=
  Network.EarDecomposition (⊤ : D.earNetwork.Subnetwork)

variable {D}

/-- **Directed ear characterization for digraphs.** A finite digraph on a nonempty vertex type
is strongly connected exactly when it can be built from one vertex by adjoining directed open
and closed ears, covering all vertices and adjacency arrows. -/
theorem isStronglyConnected_iff_nonempty_earDecomposition [Finite V] [Nonempty V] :
    @Quiver.IsStronglyConnected V ⟨D.AdjHom⟩ ↔ Nonempty D.EarDecomposition :=
  Network.isStronglyConnected_iff_nonempty_earDecomposition (N := D.earNetwork)

end Digraph
