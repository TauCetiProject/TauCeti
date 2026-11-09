/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.LinearTopology

/-!
# Linear topologies on subrings

If the topology of a ring `A` is linear for its left ideals, so is the subspace topology of every
subring `S` (for instance a subalgebra, or the center): the preimages in `S` of the open left ideals
of `A` are left ideals of `S` and form a basis of neighbourhoods of zero. This complements Mathlib's
`IsLinearTopology` API in `Mathlib.Topology.Algebra.LinearTopology`.
-/

public section

open Topology

namespace IsLinearTopology

variable {A S : Type*} [Ring A] [TopologicalSpace A] [SetLike S A] [SubringClass S A]

/-- A subring of a ring with a (left) linear topology has a linear topology, for the preimages of
the open left ideals of the ambient ring. -/
instance subringClass [IsLinearTopology A A] (s : S) : IsLinearTopology s s := by
  refine .mk_of_hasBasis (S := Ideal s) s (p := fun I : Ideal A ↦ (I : Set A) ∈ 𝓝 0)
    (s := fun I ↦ Ideal.comap (SubringClass.subtype s) I) ?_
  rw [nhds_subtype, ZeroMemClass.coe_zero]
  exact (hasBasis_ideal (R := A)).comap _

end IsLinearTopology
