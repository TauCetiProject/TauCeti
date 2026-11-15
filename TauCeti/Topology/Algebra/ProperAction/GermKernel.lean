/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.GermKernel
public import TauCeti.Topology.Algebra.ProperAction.Slice

import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The principal part of a proper action of a discrete group

Let a discrete group `G` act properly on a topological space `X`, in the sense of Mathlib's
`ProperSMul`. This file proves that the points whose stabilizer is their germ kernel form a dense
open subset of `X`. At such a point every element fixing the point acts as the identity near it,
so in the presentation `[X/G]` the isotropy there is exactly its ineffective part. This is the
dense open principal part of `[X/G]`. The group may be infinite and the action need not be
faithful or smooth.

The proof is local. Near a point `x`, a slice `U` for the finite stabilizer `G_x`
(`ProperSMul.exists_slice`) has the property that the stabilizer in `G` of every point of `U` lies
in `G_x`. So on `U` the points whose stabilizer is the germ kernel are the same for `G` and for
`G_x` (`TauCeti.MulAction.stabilizer_eq_germKernel_iff_of_stabilizer_le`). For the finite group
`G_x` they form a dense open set (`TauCeti.MulAction.dense_setOf_stabilizer_eq_germKernel`), and
being dense and open is a local property.

## Main results

* `ProperSMul.isOpen_setOf_stabilizer_eq_germKernel`,
  `ProperSMul.dense_setOf_stabilizer_eq_germKernel`: for a proper action of a discrete group, the
  points whose stabilizer is the germ kernel form a dense open set.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2, for the local isotropy model
  of a proper étale groupoid.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Ch. 1, for ineffective orbifolds.
-/

public section

open Set Topology MulAction TauCeti.MulAction

namespace ProperSMul

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace X] [ProperSMul G X]

/-- Every neighbourhood `W` of `x` contains an open neighbourhood `U` of `x` on which the points
whose stabilizer is the germ kernel are those of a dense open set. -/
private theorem exists_inter_setOf_stabilizer_eq_germKernel_eq (x : X) {W : Set X}
    (hW : W ∈ 𝓝 x) :
    ∃ U T : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧ IsOpen T ∧ Dense T ∧
      U ∩ {y | stabilizer G y = germKernel G y} = U ∩ T := by
  have := t2Space_of_properSMul_of_t1Group (G := G) (X := X)
  have := properlyDiscontinuousSMul G X
  obtain ⟨U, hUo, hxU, hUW, hU⟩ := exists_slice G x hW
  refine ⟨U, {y | stabilizer (stabilizer G x) y = germKernel (stabilizer G x) y}, hUo, hxU, hUW,
    TauCeti.MulAction.isOpen_setOf_stabilizer_eq_germKernel,
    TauCeti.MulAction.dense_setOf_stabilizer_eq_germKernel, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, and_congr_right_iff]
  intro hy
  -- An element fixing a point of the slice fixes `x`.
  refine (stabilizer_eq_germKernel_iff_of_stabilizer_le fun g hg ↦ hU g y hy ?_).symm
  rwa [mem_stabilizer_iff.mp hg]

/-- For a proper action of a discrete group, the points whose stabilizer is the germ kernel form an
open set. -/
theorem isOpen_setOf_stabilizer_eq_germKernel :
    IsOpen {y : X | stabilizer G y = germKernel G y} := by
  refine isOpen_iff_forall_mem_open.mpr fun y hy ↦ ?_
  obtain ⟨U, T, hUo, hyU, -, hTo, -, hUT⟩ :=
    exists_inter_setOf_stabilizer_eq_germKernel_eq (G := G) y Filter.univ_mem
  refine ⟨U ∩ {y | stabilizer G y = germKernel G y}, inter_subset_right, ?_, hyU, hy⟩
  rw [hUT]
  exact hUo.inter hTo

/-- **The principal part of a proper action.** For a proper action of a discrete group, the points
whose stabilizer is the germ kernel form a dense set: generically, an element fixing a point acts as
the identity near it. The set is also open, by `ProperSMul.isOpen_setOf_stabilizer_eq_germKernel`.
-/
theorem dense_setOf_stabilizer_eq_germKernel :
    Dense {y : X | stabilizer G y = germKernel G y} := by
  refine dense_iff_inter_open.mpr fun V hVo ⟨x, hxV⟩ ↦ ?_
  obtain ⟨U, T, hUo, hxU, hUV, -, hTd, hUT⟩ :=
    exists_inter_setOf_stabilizer_eq_germKernel_eq (G := G) x (hVo.mem_nhds hxV)
  obtain ⟨y, hyU, hyT⟩ := hTd.inter_open_nonempty U hUo ⟨x, hxU⟩
  have hy : y ∈ U ∩ {y | stabilizer G y = germKernel G y} := by
    rw [hUT]
    exact ⟨hyU, hyT⟩
  exact ⟨y, hUV hy.1, hy.2⟩

end ProperSMul
