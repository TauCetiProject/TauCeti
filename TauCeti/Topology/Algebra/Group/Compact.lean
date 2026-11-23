/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Compact groups with continuous multiplication are topological groups

In a compact `T₁` group whose multiplication is jointly continuous, inversion is continuous, so the
group is a topological group. The graph of inversion is the preimage of `1` under multiplication,
which is closed because points are closed, and Mathlib's closed graph criterion
`continuous_of_isClosed_graph` turns a closed graph into a compact space into continuity.

So a compact, totally disconnected group with continuous multiplication, such as the total group of
a profinite extension, is a profinite group without asking separately that inversion be
continuous: a totally disconnected space is `T₁` (`TotallyDisconnectedSpace.t1Space`).

## Main results

* `IsTopologicalGroup.of_compactSpace` / `IsTopologicalAddGroup.of_compactSpace`: a compact `T₁`
  group with continuous multiplication is a topological group.
-/

public section

/-- **A compact `T₁` group with continuous multiplication is a topological group.** The graph of
inversion is the preimage of the closed point `1` under multiplication, and a map into a compact
space with closed graph is continuous. -/
@[to_additive /-- **A compact `T₁` additive group with continuous addition is a topological
additive group.** The graph of negation is the preimage of the closed point `0` under addition, and
a map into a compact space with closed graph is continuous. -/]
theorem IsTopologicalGroup.of_compactSpace (G : Type*) [Group G] [TopologicalSpace G]
    [ContinuousMul G] [CompactSpace G] [T1Space G] : IsTopologicalGroup G where
  continuous_inv := by
    refine continuous_of_isClosed_graph ?_
    have h : (Inv.inv : G → G).graph = (fun p : G × G => p.1 * p.2) ⁻¹' {1} := by
      ext ⟨x, y⟩
      simp only [Function.mem_graph, Set.mem_preimage, Set.mem_singleton_iff,
        inv_eq_iff_mul_eq_one]
    rw [h]
    exact isClosed_singleton.preimage continuous_mul
