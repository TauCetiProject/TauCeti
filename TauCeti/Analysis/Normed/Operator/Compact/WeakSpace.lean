/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.Sequences
public import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Analysis.Normed.Module.WeakSpace.Sphere
import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic

/-!
# Compact operators on bounded sets in the weak topology

A compact operator `J : V →L[𝕜] F` into a topological vector space with Hausdorff weak topology maps
every bounded set `B` into a compact set of `F`, on which the original topology of `F` agrees with
its weak topology. Since `J` is continuous for the weak topologies, it is therefore continuous from
the weak topology of `V`, restricted to `B`, to the original topology of `F`
(`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`, and
`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded` for von Neumann bounded
sets). Over `ℝ` or `ℂ`, continuity extends to the weak closure of any bounded set
(`IsCompactOperator.continuousOn_closure_toWeakSpace_symm_of_isBounded`) and holds on every weakly
compact set (`IsCompactOperator.continuousOn_toWeakSpace_symm_of_isCompact`).

Consequently:

* compositions `g ∘ J` with continuous or lower semicontinuous maps are weakly continuous or weakly
  lower semicontinuous on bounded sets
  (`IsCompactOperator.continuousOn_postcomp_toWeakSpace_symm_of_isBounded`,
  `IsCompactOperator.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_isBounded`), and sequentially
  weakly continuous on the whole space (`IsCompactOperator.seqContinuous_comp_toWeakSpace_symm`);
* for a closed set `C` of `F` and a bounded weakly closed set `B`, the set `B ∩ J ⁻¹' C` is weakly
  closed (`IsCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isBounded`,
  `IsCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isVonNBounded`), and for weakly compact
  `K`, `K ∩ J ⁻¹' C` is weakly compact (`IsCompactOperator.isCompact_toWeakSpace_inter_preimage`);
* without any boundedness, preimages `J ⁻¹' C` of closed or sequentially closed sets — in
  particular level spheres `{u | ‖J u‖ = r}` — are weakly sequentially closed
  (`IsCompactOperator.isSeqClosed_toWeakSpace_preimage`,
  `IsCompactOperator.isSeqClosed_toWeakSpace_preimage_of_isSeqClosed`,
  `IsCompactOperator.isSeqClosed_toWeakSpace_setOf_norm_apply_eq`), even when they fail to be
  weakly closed in infinite dimensions.

The restriction to bounded sets cannot be dropped: in an infinite-dimensional space an injective
linear map into a normed space is never continuous from the weak topology to the norm topology
(`TauCeti.not_continuous_comp_toWeakSpace_symm` in
`TauCeti.Analysis.Normed.Module.WeakSpace.Sphere`). For a compact injective `j` the sphere
`{u | ‖j u‖ = 1}` is weakly sequentially closed but not weakly closed: weak closures of unbounded
sets are not described by sequences.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer, 2011, Chapter 6 (compact operators).
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Bornology Filter Metric Set Topology

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

/-- Composing a compact operator with a function continuous on `J '' B` yields a weakly continuous
function on any norm-bounded set `B`. -/
theorem continuousOn_postcomp_toWeakSpace_symm_of_isBounded {α : Type*} [TopologicalSpace α]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B)
    {g : F → α} (hg : ContinuousOn g (J '' B)) :
    ContinuousOn (fun w : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' B) :=
  hg.comp (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hB) <| by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem J hx

/-- Composing a compact operator with a function lower semicontinuous on `J '' B` yields a weakly
lower semicontinuous function on any norm-bounded set `B`. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm_of_isBounded {β : Type*} [Preorder β]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B)
    {g : F → β} (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' B) :=
  hg.comp (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hB) <| by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem J hx

/-- On a bounded weakly closed set `B`, the preimage of a closed set under a compact operator is
weakly closed. -/
theorem isClosed_toWeakSpace_inter_preimage_of_isBounded (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) (hBc : IsClosed (toWeakSpace 𝕜 V '' B)) {C : Set F} (hC : IsClosed C) :
    IsClosed (toWeakSpace 𝕜 V '' (B ∩ J ⁻¹' C)) :=
  hJ.isClosed_toWeakSpace_inter_preimage_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff]) hBc hC

end SeminormedSpace

section RCLikeWeak

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousConstSMul 𝕜 F] [T2Space (WeakSpace 𝕜 F)]

/-- Over `ℝ` or `ℂ`, a compact operator is continuous from the weak topology to the target topology
on the weak closure of any norm-bounded set. -/
theorem continuousOn_closure_toWeakSpace_symm_of_isBounded {J : E →L[𝕜] F}
    (hJ : IsCompactOperator J) {B : Set E} (hB : IsBounded B) :
    ContinuousOn (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w))
      (closure (toWeakSpace 𝕜 E '' B)) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hB
  have hsub : closure (toWeakSpace 𝕜 E '' B) ⊆ toWeakSpace 𝕜 E '' closedBall (0 : E) R :=
    closure_minimal (image_mono fun x hx ↦ mem_closedBall_zero_iff.2 (hR x hx))
      (TauCeti.isClosed_toWeakSpace_closedBall 𝕜 (0 : E) R)
  exact (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded isBounded_closedBall).mono hsub

/-- Over `ℝ` or `ℂ`, a compact operator is continuous from the weak topology to the target topology
on every weakly compact set. -/
theorem continuousOn_toWeakSpace_symm_of_isCompact {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K) :
    ContinuousOn (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) K := by
  have hB : IsBounded (toWeakSpace 𝕜 E ⁻¹' K) := hK.isBounded_toWeakSpace_preimage
  simpa only [(toWeakSpace 𝕜 E).surjective.image_preimage] using
    hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hB

/-- Intersecting a weakly compact set with the preimage of a closed set under a compact operator
yields a weakly compact set. -/
theorem isCompact_toWeakSpace_inter_preimage {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    {K : Set E} (hK : IsCompact (toWeakSpace 𝕜 E '' K)) {C : Set F} (hC : IsClosed C) :
    IsCompact (toWeakSpace 𝕜 E '' (K ∩ J ⁻¹' C)) := by
  let s : Set (WeakSpace 𝕜 E) := toWeakSpace 𝕜 E '' K
  have : CompactSpace s := isCompact_iff_compactSpace.1 hK
  have hcont : Continuous (s.domRestrict fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) :=
    continuousOn_iff_continuous_domRestrict.1 (hJ.continuousOn_toWeakSpace_symm_of_isCompact hK)
  have hsub : IsCompact ((↑) '' ((s.domRestrict fun w : WeakSpace 𝕜 E ↦
      J ((toWeakSpace 𝕜 E).symm w)) ⁻¹' C) : Set (WeakSpace 𝕜 E)) :=
    (hC.preimage hcont).isCompact.image continuous_subtypeVal
  have heq : toWeakSpace 𝕜 E '' (K ∩ J ⁻¹' C) =
      ((↑) '' ((s.domRestrict fun w : WeakSpace 𝕜 E ↦
        J ((toWeakSpace 𝕜 E).symm w)) ⁻¹' C) : Set (WeakSpace 𝕜 E)) := by
    ext w
    constructor
    · rintro ⟨x, ⟨hxK, hxC⟩, rfl⟩
      exact ⟨⟨toWeakSpace 𝕜 E x, ⟨x, hxK, rfl⟩⟩, by simpa using hxC, rfl⟩
    · rintro ⟨⟨w, hw⟩, hwC, rfl⟩
      obtain ⟨x, hxK, rfl⟩ := hw
      exact ⟨x, ⟨hxK, by simpa using hwC⟩, rfl⟩
  rw [heq]
  exact hsub

/-- Composing a compact operator with a sequentially continuous map is sequentially weakly
continuous on the whole space. -/
theorem seqContinuous_comp_toWeakSpace_symm {α : Type*} [TopologicalSpace α]
    {J : E →L[𝕜] F} (hJ : IsCompactOperator J) {g : F → α} (hg : SeqContinuous g) :
    SeqContinuous fun w : WeakSpace 𝕜 E ↦ g (J ((toWeakSpace 𝕜 E).symm w)) := by
  intro u a hu
  have hu' : Tendsto (fun n ↦ toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm (u n))) atTop
      (𝓝 (toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm a))) := by
    simpa only [LinearEquiv.apply_symm_apply] using hu
  have hB : IsBounded (insert ((toWeakSpace 𝕜 E).symm a)
      (range fun n ↦ (toWeakSpace 𝕜 E).symm (u n))) :=
    isBounded_insert.2 hu'.isBounded_range_of_toWeakSpace
  have hcont := (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hB) a
    ⟨(toWeakSpace 𝕜 E).symm a, mem_insert _ _, (toWeakSpace 𝕜 E).apply_symm_apply a⟩
  have hlim : Tendsto (fun n ↦ J ((toWeakSpace 𝕜 E).symm (u n))) atTop
      (𝓝 (J ((toWeakSpace 𝕜 E).symm a))) :=
    hcont.tendsto.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu <|
      Eventually.of_forall fun n ↦ ⟨(toWeakSpace 𝕜 E).symm (u n),
        mem_insert_of_mem _ (mem_range_self n), (toWeakSpace 𝕜 E).apply_symm_apply _⟩
  exact hg hlim

/-- The preimage of a sequentially closed set under a compact operator is sequentially weakly
closed. -/
theorem isSeqClosed_toWeakSpace_preimage_of_isSeqClosed {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    {C : Set F} (hC : IsSeqClosed C) :
    IsSeqClosed (toWeakSpace 𝕜 E '' (J ⁻¹' C)) := by
  rw [(toWeakSpace 𝕜 E).image_eq_preimage_symm]
  exact hC.preimage (hJ.seqContinuous_comp_toWeakSpace_symm (g := id) continuous_id.seqContinuous)

end RCLikeWeak

section RCLike

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {J : V →L[𝕜] F}

/-- The preimage of a closed set under a compact operator is weakly sequentially closed. -/
theorem isSeqClosed_toWeakSpace_preimage (hJ : IsCompactOperator J) {C : Set F}
    (hC : IsClosed C) : IsSeqClosed (toWeakSpace 𝕜 V '' (J ⁻¹' C)) :=
  hJ.isDunfordPettis.isSeqClosed_toWeakSpace_preimage hC

/-- For a compact operator `J`, every level sphere `{u | ‖J u‖ = r}` is sequentially weakly
closed, even when `J` has infinite-dimensional range and the sphere is not weakly closed. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_apply_eq (hJ : IsCompactOperator J) (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) := by
  have hpre : J ⁻¹' sphere (0 : F) r = {u : V | ‖J u‖ = r} := by ext u; simp
  rw [← hpre]
  exact hJ.isSeqClosed_toWeakSpace_preimage isClosed_sphere

end RCLike

end IsCompactOperator
