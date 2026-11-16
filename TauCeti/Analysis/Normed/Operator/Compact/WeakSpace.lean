/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.Algebra.Module.WeakSpace
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

The restriction to bounded sets cannot be dropped. In an infinite-dimensional space every weak
neighbourhood of `0` contains a line through a nonzero vector
(`TauCeti.exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero`). For an injective linear
map `j` into a normed space this line meets the sphere `{u | ‖j u‖ = r}` for every `r ≥ 0`, so
`0` lies in the weak closure of that sphere, the sphere is not weakly closed when `r > 0`, and
`j` is not continuous from the weak topology to the norm topology. For a compact injective `j`
the sphere `{u | ‖j u‖ = 1}` is nevertheless weakly sequentially closed: weak closures of
unbounded sets are not described by sequences.

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
* `TauCeti.zero_mem_closure_toWeakSpace_setOf_norm_eq`,
  `TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq`,
  `TauCeti.not_continuous_comp_toWeakSpace_symm`: in infinite dimension, spheres of an injective
  linear map are not weakly closed, and the map is not weak-to-norm continuous.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer, 2011, §3.2, Example 1 (weak closure of the unit sphere), and Chapter 6 (compact
  operators).
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
    (hC : IsClosed C) : IsSeqClosed (toWeakSpace 𝕜 V '' (J ⁻¹' C)) := by
  rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  exact hC.isSeqClosed.preimage
    (ContinuousLinearMap.isDunfordPettis_iff_seqContinuous.1 hJ.isDunfordPettis)

end RCLike

end IsCompactOperator

namespace TauCeti

section Sphere

variable {𝕜 V F G : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FunLike G V F] [LinearMapClass G 𝕜 V F] {j : G}

/-- In an infinite-dimensional space, `0` lies in the weak closure of every sphere
`{u | ‖j u‖ = r}` of an injective linear map `j` into a normed space. -/
theorem zero_mem_closure_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) {r : ℝ} (hr : 0 ≤ r) :
    (0 : WeakSpace 𝕜 V) ∈ closure (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := by
  refine mem_closure_iff_nhds.2 fun U hU ↦ ?_
  obtain ⟨x, hx, hxU⟩ := exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero hV hU
  have hjx : ‖j x‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero_iff j hj).2 hx)
  -- Rescale `x` so that its image has norm `r`.
  refine ⟨_, hxU ((r / ‖j x‖ : ℝ) : 𝕜), mem_image_of_mem _ ?_⟩
  simp [map_smul, norm_smul, abs_of_nonneg hr, hjx]

/-- In an infinite-dimensional space, a sphere `{u | ‖j u‖ = r}` of positive radius of an
injective linear map `j` into a normed space is not weakly closed. -/
theorem not_isClosed_toWeakSpace_setOf_norm_eq (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) {r : ℝ} (hr : 0 < r) :
    ¬ IsClosed (toWeakSpace 𝕜 V '' {u | ‖j u‖ = r}) := fun hclosed ↦ by
  obtain ⟨u, hu, hu0⟩ :=
    hclosed.closure_subset (zero_mem_closure_toWeakSpace_setOf_norm_eq hV hj hr.le)
  rw [map_eq_zero_iff _ (toWeakSpace 𝕜 V).injective] at hu0
  subst hu0
  simp only [mem_ofPred_eq, map_zero, norm_zero] at hu
  exact hr.ne hu

/-- In an infinite-dimensional space, an injective linear map into a normed space is not
continuous from the weak topology to the norm topology. -/
theorem not_continuous_comp_toWeakSpace_symm (hV : ¬ FiniteDimensional 𝕜 V)
    (hj : Function.Injective j) :
    ¬ Continuous fun w : WeakSpace 𝕜 V ↦ j ((toWeakSpace 𝕜 V).symm w) := fun hcont ↦ by
  refine not_isClosed_toWeakSpace_setOf_norm_eq hV hj one_pos ?_
  rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  exact isClosed_eq (continuous_norm.comp hcont) continuous_const

end Sphere

end TauCeti
