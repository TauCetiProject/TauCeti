/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Double cosets of compact open subgroups

For a compact open subgroup `K` of a topological group `G` and `g ∈ G`, the double coset `K g K`
is compact and `G ⧸ K` is discrete, so `K g K` is a union of finitely many left cosets of `K`. In
the form used for Hecke operators, the indicator of `K g K` is supported on finitely many left
cosets (`QuotientGroup.finite_support_indicator_doubleCoset`).

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), `src/Lib/Adelic/Hecke/Basic.lean` (`New.isHeckeFunction_doubleCoset`).
-/

public section

open Function Set

namespace QuotientGroup

/-- For a compact open subgroup `K` of a topological group and `g ∈ G`, the indicator of the double
coset `K g K` is supported on finitely many left cosets of `K`. This is the finiteness input for the
double coset operator `[K g K]` (`Representation.doubleCosetOperator_apply_mem_weightSpace`). -/
theorem finite_support_indicator_doubleCoset {A G : Type*} [Zero A] [One A] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK_open : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    (support fun q : G ⧸ K ↦
      (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) q.out).Finite := by
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK_open
  have h_cpt : IsCompact (DoubleCoset.doubleCoset g (K : Set G) K) :=
    (hK.mul isCompact_singleton).mul hK
  refine ((h_cpt.image QuotientGroup.continuous_mk).finite_of_discrete).subset fun q hq ↦ ?_
  exact ⟨q.out, support_indicator_subset hq, QuotientGroup.out_eq' q⟩

end QuotientGroup
