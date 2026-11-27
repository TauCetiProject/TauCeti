/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.Algebra.Module.WeakSpace.Basic
import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic

/-!
# Compact operators on bounded sets in the weak topology

A compact operator `J : V →L[𝕜] F` maps every bounded set `B` into a compact set of `F`, on
which the original topology of `F` agrees with its weak topology. Since `J` is continuous for
the weak topologies, it is therefore continuous from the weak topology of `V`, restricted to
`B`, to the original topology of `F`
(`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`). Consequently, for a
closed set `C` of `F` and a bounded weakly closed set `B`, the set `B ∩ J ⁻¹' C` is weakly
closed, and without any boundedness the preimage `J ⁻¹' C` is weakly sequentially closed,
because weakly convergent sequences are bounded.

The restriction to bounded sets cannot be dropped: in an infinite-dimensional space an injective
linear map into a normed space is never continuous from the weak topology to the norm topology
(`TauCeti.not_continuous_comp_toWeakSpace_symm` in
`TauCeti.Analysis.Normed.Module.WeakSpace.Sphere`). For a compact injective `j` the sphere
`{u | ‖j u‖ = 1}` is weakly sequentially closed but not weakly closed: weak closures of unbounded
sets are not described by sequences.

These facts are the compactness input of the direct method on constraint sets such as
`{u | ‖j u‖ = 1}` for a compact form-domain inclusion `j`.

## Main results

* `IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`: a compact operator is
  continuous from the weak topology to the original topology on every bounded set, and
  `IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded` in topological vector
  spaces.
* `IsCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isBounded`: on a bounded weakly closed
  set, the preimage of a closed set under a compact operator is weakly closed.
* `IsCompactOperator.isSeqClosed_toWeakSpace_preimage`: the preimage of a closed set under a
  compact operator is weakly sequentially closed.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer, 2011, Chapter 6 (compact operators).
-/

public section

open Bornology Filter Set Topology

namespace IsCompactOperator

section TopologicalVectorSpace

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- A compact operator is continuous from the weak topology to the original topology on every
von Neumann bounded set. -/
theorem continuousOn_comp_toWeakSpace_symm_of_isVonNBounded (hJ : IsCompactOperator J)
    {B : Set V} (hB : IsVonNBounded 𝕜 B) :
    ContinuousOn (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B) := by
  obtain ⟨K, hK, hJK⟩ := hJ.image_subset_compact_of_isVonNBounded hB
  rintro _ ⟨u, -, rfl⟩
  -- The images of points of `B` stay in the compact set `K`, where weak convergence in `F` is
  -- convergence in the original topology; and `J` is continuous for the weak topologies.
  refine TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact (𝕜 := 𝕜) hK ?_
    (((WeakSpace.map J).continuous.tendsto _).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨v, hv, rfl⟩ := hw
  simpa using hJK (mem_image_of_mem J hv)

/-- On a von Neumann bounded weakly closed set `B`, the preimage of a closed set under a compact
operator is weakly closed. -/
theorem isClosed_toWeakSpace_inter_preimage_of_isVonNBounded (hJ : IsCompactOperator J)
    {B : Set V} (hB : IsVonNBounded 𝕜 B) (hBc : IsClosed (toWeakSpace 𝕜 V '' B)) {C : Set F}
    (hC : IsClosed C) : IsClosed (toWeakSpace 𝕜 V '' (B ∩ J ⁻¹' C)) := by
  have heq : toWeakSpace 𝕜 V '' (B ∩ J ⁻¹' C) =
      toWeakSpace 𝕜 V '' B ∩ (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w)) ⁻¹' C := by
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, preimage_inter, preimage_preimage]
  rw [heq]
  exact (hJ.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded hB).preimage_isClosed_of_isClosed
    hBc hC

end TopologicalVectorSpace

section SeminormedSpace

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- A compact operator is continuous from the weak topology to the original topology on every
bounded set. -/
theorem continuousOn_comp_toWeakSpace_symm_of_isBounded (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) :
    ContinuousOn (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B) :=
  hJ.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded <| by
    rwa [NormedSpace.isVonNBounded_iff]

/-- On a bounded weakly closed set `B`, the preimage of a closed set under a compact operator is
weakly closed. -/
theorem isClosed_toWeakSpace_inter_preimage_of_isBounded (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) (hBc : IsClosed (toWeakSpace 𝕜 V '' B)) {C : Set F} (hC : IsClosed C) :
    IsClosed (toWeakSpace 𝕜 V '' (B ∩ J ⁻¹' C)) :=
  hJ.isClosed_toWeakSpace_inter_preimage_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff]) hBc hC

end SeminormedSpace

section RCLike

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {J : V →L[𝕜] F}

/-- The preimage of a closed set under a compact operator is weakly sequentially closed. -/
theorem isSeqClosed_toWeakSpace_preimage (hJ : IsCompactOperator J) {C : Set F}
    (hC : IsClosed C) : IsSeqClosed (toWeakSpace 𝕜 V '' (J ⁻¹' C)) :=
  hJ.isDunfordPettis.isSeqClosed_toWeakSpace_preimage hC

end RCLike

end IsCompactOperator
