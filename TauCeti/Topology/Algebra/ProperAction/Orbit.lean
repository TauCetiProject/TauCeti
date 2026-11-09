/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Orbit maps of proper actions

Let a topological group `G` act properly on a topological space `X`, in the sense of Mathlib's
`ProperSMul`: the map `(g, y) ↦ (g • y, y)` is proper. Restricting this map to `G × {x}` shows that
the **orbit map** `g ↦ g • x` is itself proper (`ProperSMul.isProperMap_smul_const`). Consequently:

* the stabilizer `G_x`, the fibre of the orbit map over `x`, is compact
  (`ProperSMul.isCompact_stabilizer`);
* every orbit, the range of the orbit map, is closed (`ProperSMul.isClosed_orbit`);
* where the stabilizer is trivial, the orbit map is injective, hence a closed embedding of `G`
  onto the orbit (`ProperSMul.isClosedEmbedding_smul_const`).

No separation axiom on `G` or `X` is needed. These are the topological ingredients of the facts
that orbits of proper smooth actions are closed embedded submanifolds and that the stabilizers of
proper actions are compact, used in the proof of the quotient manifold theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Proposition 21.7
  (orbits of proper actions) and Theorem 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Section 1.6 (proper actions).
-/

public section

open Set Topology

namespace ProperSMul

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
  [ProperSMul G X]

/-- **Orbit maps of proper actions are proper.** For a proper action of `G` on `X`, the orbit map
`g ↦ g • x` of any point is a proper map. It is the restriction of the proper map
`(g, y) ↦ (g • y, y)` to `G × {x}`, followed by the proper projection `X × {x} → X`. -/
@[to_additive /-- **Orbit maps of proper actions are proper.** For a proper additive action of `G`
on `X`, the orbit map `g ↦ g +ᵥ x` of any point is a proper map. -/]
theorem isProperMap_smul_const (x : X) : IsProperMap fun g : G ↦ g • x := by
  exact (isProperMap_fst_of_compactSpace.comp ProperSMul.isProperMap_smul_pair_set).comp
    (Homeomorph.prodUnique G ({x} : Set X)).symm.isProperMap

/-- **Stabilizers of proper actions are compact.** The stabilizer of `x` is the fibre over `x` of
the proper orbit map `g ↦ g • x`. -/
@[to_additive /-- **Stabilizers of proper actions are compact.** The stabilizer of `x` is the fibre
over `x` of the proper orbit map `g ↦ g +ᵥ x`. -/]
theorem isCompact_stabilizer (x : X) : IsCompact (MulAction.stabilizer G x : Set G) :=
  (isProperMap_smul_const x).isCompact_preimage isCompact_singleton

/-- **Orbits of proper actions are closed**, as ranges of the proper orbit maps. -/
@[to_additive /-- **Orbits of proper actions are closed**, as ranges of the proper orbit maps. -/]
theorem isClosed_orbit (x : X) : IsClosed (MulAction.orbit G x) :=
  (isProperMap_smul_const x).isClosed_range

/-- **Free orbits of proper actions are closed embeddings.** Where the stabilizer of `x` is
trivial, the orbit map `g ↦ g • x` of a proper action is a closed embedding of `G` onto the orbit
of `x`. -/
@[to_additive /-- **Free orbits of proper actions are closed embeddings.** Where the stabilizer of
`x` is trivial, the orbit map `g ↦ g +ᵥ x` of a proper additive action is a closed embedding of `G`
onto the orbit of `x`. -/]
theorem isClosedEmbedding_smul_const {x : X} (hx : MulAction.stabilizer G x = ⊥) :
    IsClosedEmbedding fun g : G ↦ g • x := by
  refine .of_continuous_injective_isClosedMap (isProperMap_smul_const x).continuous
    (fun g h hgh ↦ ?_) (isProperMap_smul_const x).isClosedMap
  have hmem : h⁻¹ * g ∈ MulAction.stabilizer G x := by
    simp only [MulAction.mem_stabilizer_iff, mul_smul, hgh, inv_smul_smul]
  rw [hx, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

end ProperSMul
