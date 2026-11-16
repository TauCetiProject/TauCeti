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
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Compact operators in the weak topology

A compact linear operator `J : E →L[𝕜] F` into a topological vector space with Hausdorff weak
topology is continuous from the weak topology to the target topology on every bounded subset
(`IsCompactOperator.continuousOn_toWeakSpace_symm_of_isBounded`), and more generally on every von
Neumann bounded subset (`IsCompactOperator.continuousOn_toWeakSpace_symm_of_isVonNBounded`). Over
`ℝ` or `ℂ`, continuity extends to the weak closure of any bounded set
(`IsCompactOperator.continuousOn_closure_toWeakSpace_symm_of_isBounded`) and holds on every weakly
compact set (`IsCompactOperator.continuousOn_toWeakSpace_symm_of_isCompact`).

Consequently:

* compositions `g ∘ J` with continuous or lower semicontinuous maps are weakly continuous or weakly
  lower semicontinuous on bounded sets
  (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`,
  `IsCompactOperator.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_isBounded`), and sequentially
  weakly continuous on the whole space (`IsCompactOperator.seqContinuous_comp_toWeakSpace_symm`);
* preimages `J ⁻¹' C` of closed sets intersect bounded weakly closed sets in weakly closed sets
  (`IsCompactOperator.isClosed_toWeakSpace_inter_preimage`) and intersect weakly compact sets in
  weakly compact sets (`IsCompactOperator.isCompact_toWeakSpace_inter_preimage`);
* preimages of sequentially closed sets — in particular level spheres `{u | ‖J u‖ = r}` — are
  sequentially weakly closed (`IsCompactOperator.isSeqClosed_toWeakSpace_preimage`,
  `IsCompactOperator.isSeqClosed_toWeakSpace_setOf_norm_apply_eq`), even when they fail to be
  weakly closed in infinite dimensions.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Bornology Filter Metric Set Topology

namespace IsCompactOperator

section VonNBounded

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousConstSMul 𝕜 F] [T2Space (WeakSpace 𝕜 F)]

/-- A compact continuous linear operator is continuous from the weak topology to the target
topology on every von Neumann bounded set, whenever the target weak topology is Hausdorff. -/
theorem continuousOn_toWeakSpace_symm_of_isVonNBounded {J : E →L[𝕜] F}
    (hJ : IsCompactOperator J) {B : Set E} (hB : IsVonNBounded 𝕜 B) :
    ContinuousOn (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w))
      (toWeakSpace 𝕜 E '' B) := by
  obtain ⟨K, hK, hJK⟩ := hJ.image_subset_compact_of_isVonNBounded (f := J.toLinearMap) hB
  intro w _
  refine TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact (𝕜 := 𝕜) hK ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with u hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact hJK (mem_image_of_mem J hx)
  · exact (WeakSpace.map J).continuous.continuousWithinAt

end VonNBounded

section Bounded

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousConstSMul 𝕜 F] [T2Space (WeakSpace 𝕜 F)]

/-- A compact continuous linear operator from a seminormed space is continuous from the weak
topology to the target topology on every norm-bounded set. -/
theorem continuousOn_toWeakSpace_symm_of_isBounded {J : E →L[𝕜] F}
    (hJ : IsCompactOperator J) {B : Set E} (hB : IsBounded B) :
    ContinuousOn (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w))
      (toWeakSpace 𝕜 E '' B) :=
  hJ.continuousOn_toWeakSpace_symm_of_isVonNBounded ((NormedSpace.isVonNBounded_iff 𝕜).2 hB)

/-- Composing a compact operator with a function continuous on `J '' B` yields a weakly continuous
function on any norm-bounded set `B`. -/
theorem continuousOn_comp_toWeakSpace_symm_of_isBounded {α : Type*} [TopologicalSpace α]
    {J : E →L[𝕜] F} (hJ : IsCompactOperator J) {B : Set E} (hB : IsBounded B)
    {g : F → α} (hg : ContinuousOn g (J '' B)) :
    ContinuousOn (fun w : WeakSpace 𝕜 E ↦ g (J ((toWeakSpace 𝕜 E).symm w)))
      (toWeakSpace 𝕜 E '' B) :=
  hg.comp (hJ.continuousOn_toWeakSpace_symm_of_isBounded hB) <| by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem J hx

/-- Composing a compact operator with a function lower semicontinuous on `J '' B` yields a weakly
lower semicontinuous function on any norm-bounded set `B`. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm_of_isBounded {β : Type*} [Preorder β]
    {J : E →L[𝕜] F} (hJ : IsCompactOperator J) {B : Set E} (hB : IsBounded B)
    {g : F → β} (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 E ↦ g (J ((toWeakSpace 𝕜 E).symm w)))
      (toWeakSpace 𝕜 E '' B) :=
  hg.comp (hJ.continuousOn_toWeakSpace_symm_of_isBounded hB) <| by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem J hx

/-- Intersecting a bounded weakly closed set with the preimage of a closed set under a compact
operator yields a weakly closed set. -/
theorem isClosed_toWeakSpace_inter_preimage {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    {B : Set E} (hB : IsBounded B) (hBclosed : IsClosed (toWeakSpace 𝕜 E '' B))
    {C : Set F} (hC : IsClosed C) :
    IsClosed (toWeakSpace 𝕜 E '' (B ∩ J ⁻¹' C)) := by
  have heq : toWeakSpace 𝕜 E '' (B ∩ J ⁻¹' C) =
      (toWeakSpace 𝕜 E '' B) ∩
        (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) ⁻¹' C := by
    ext w
    simp [(toWeakSpace 𝕜 E).image_eq_preimage_symm]
  rw [heq]
  exact (hJ.continuousOn_toWeakSpace_symm_of_isBounded hB).preimage_isClosed_of_isClosed
    hBclosed hC

end Bounded

section RCLike

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
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hB
  have hball_closed : IsClosed (toWeakSpace 𝕜 E '' closedBall (0 : E) R) := by
    rw [← isClosed_closedBall.closure_eq, (convex_closedBall (0 : E) R).toWeakSpace_closure 𝕜]
    exact isClosed_closure
  have hsub : closure (toWeakSpace 𝕜 E '' B) ⊆ toWeakSpace 𝕜 E '' closedBall (0 : E) R :=
    closure_minimal (image_mono fun x hx ↦ mem_closedBall_zero_iff.2 (hR x hx)) hball_closed
  exact (hJ.continuousOn_toWeakSpace_symm_of_isBounded isBounded_closedBall).mono hsub

/-- Over `ℝ` or `ℂ`, a compact operator is continuous from the weak topology to the target topology
on every weakly compact set. -/
theorem continuousOn_toWeakSpace_symm_of_isCompact {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K) :
    ContinuousOn (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) K := by
  have hB : IsBounded (toWeakSpace 𝕜 E ⁻¹' K) := hK.isBounded_toWeakSpace_preimage
  simpa only [(toWeakSpace 𝕜 E).surjective.image_preimage] using
    hJ.continuousOn_toWeakSpace_symm_of_isBounded hB

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
    (hC.preimage hcont).isCompact.image continuous_subtype_val
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
  have hcont := (hJ.continuousOn_toWeakSpace_symm_of_isBounded hB) a
    ⟨(toWeakSpace 𝕜 E).symm a, mem_insert _ _, (toWeakSpace 𝕜 E).apply_symm_apply a⟩
  have hlim : Tendsto (fun n ↦ J ((toWeakSpace 𝕜 E).symm (u n))) atTop
      (𝓝 (J ((toWeakSpace 𝕜 E).symm a))) :=
    hcont.tendsto.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu <|
      Eventually.of_forall fun n ↦ ⟨(toWeakSpace 𝕜 E).symm (u n),
        mem_insert_of_mem _ (mem_range_self n), (toWeakSpace 𝕜 E).apply_symm_apply _⟩
  exact hg hlim

/-- The preimage of a sequentially closed set under a compact operator is sequentially weakly
closed. -/
theorem isSeqClosed_toWeakSpace_preimage {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    {C : Set F} (hC : IsSeqClosed C) :
    IsSeqClosed (toWeakSpace 𝕜 E '' (J ⁻¹' C)) := by
  have heq : toWeakSpace 𝕜 E '' (J ⁻¹' C) =
      (fun w : WeakSpace 𝕜 E ↦ J ((toWeakSpace 𝕜 E).symm w)) ⁻¹' C := by
    ext w
    simp [(toWeakSpace 𝕜 E).image_eq_preimage_symm]
  rw [heq]
  exact hC.preimage (hJ.seqContinuous_comp_toWeakSpace_symm (g := id) continuous_id.seqContinuous)

end RCLike

section RCLikeSeminormed

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [T2Space (WeakSpace 𝕜 F)]

/-- For a compact operator `J`, every level sphere `{u | ‖J u‖ = r}` is sequentially weakly
closed, even when `J` has infinite-dimensional range and the sphere is not weakly closed. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_apply_eq {J : E →L[𝕜] F} (hJ : IsCompactOperator J)
    (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 E '' {u : E | ‖J u‖ = r}) := by
  have hpre : J ⁻¹' sphere (0 : F) r = {u : E | ‖J u‖ = r} := by ext u; simp
  rw [← hpre]
  exact hJ.isSeqClosed_toWeakSpace_preimage isClosed_sphere.isSeqClosed

end RCLikeSeminormed

end IsCompactOperator
