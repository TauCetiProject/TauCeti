/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Topology.Algebra.Module.WeakSpace
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Analysis.Normed.Module.WeakSpace.Closure
import TauCeti.Topology.Semicontinuity.Basic

/-!
# Compact operators on bounded sets in the weak topology

A compact linear operator `J : V →L[𝕜] F` maps bounded subsets of `V` into relatively compact
subsets of `F`, on which the weak topology and the original topology agree whenever `WeakSpace 𝕜 F`
is Hausdorff (`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`). Consequently, `J` is
continuous from the weak topology on any von Neumann bounded or norm-bounded subset of `V` to the
topology of `F` (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded`,
`IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`), even for net/filter
convergence without metrizability or reflexivity assumptions on `V`.

This bounded-set weak-to-norm continuity yields:
* weak continuity and weak lower semicontinuity of nonlinear functionals `g ∘ J` and compact
  perturbations `u ↦ E₀ u + g (J u)` on norm-bounded sets
  (`IsCompactOperator.continuousOn_comp_toWeakSpace_symm`,
  `IsCompactOperator.lowerSemicontinuousOn_comp_toWeakSpace_symm`,
  `IsCompactOperator.lowerSemicontinuousOn_add_comp_toWeakSpace_symm`);
* weak closedness and weak compactness of `S ∩ J ⁻¹' C` for a bounded weakly closed or weakly
  compact set `S` and a closed set `C ⊆ F`
  (`IsCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isVonNBounded`,
  `IsCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isBounded`,
  `IsCompactOperator.isCompact_toWeakSpace_inter_preimage_of_isCompact`,
  `IsCompactOperator.isCompact_toWeakSpace_inter_preimage`);
* over `ℝ` or `ℂ`, sequential weak-to-original continuity of `J`
  (`IsCompactOperator.tendsto_of_tendsto_toWeakSpace`,
  `IsCompactOperator.seqContinuous_toWeakSpace_symm`), sequential weak closedness of `J ⁻¹' C` for
  every closed or sequentially closed `C ⊆ F` (`IsCompactOperator.isSeqClosed_toWeakSpace_preimage`,
  `IsCompactOperator.isSeqClosed_toWeakSpace_preimage_of_isSeqClosed`), and sequential weak lower
  semicontinuity of compact perturbations
  (`IsCompactOperator.le_of_tendsto_add_comp_of_tendsto_toWeakSpace`), because weakly convergent
  sequences are norm-bounded (`Filter.Tendsto.isBounded_range_of_toWeakSpace`).

The restriction to bounded sets cannot be dropped: a linear map with infinite-dimensional range
into a normed space is never continuous from the weak topology to the norm topology
(`TauCeti.not_continuous_comp_toWeakSpace_symm` in
`TauCeti.Analysis.Normed.Module.WeakSpace.Sphere`). For the concrete `ℓ^p` counterexample showing
that an infinite-rank compact operator is not globally weak-to-norm continuous and its level spheres
are weakly sequentially closed yet not weakly closed, see
`TauCeti.Analysis.Normed.Lp.Diagonal.WeakSpace`.

## Main results

* `IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isBounded`: weak-to-norm continuity of
  a compact operator on any norm-bounded set, and
  `IsCompactOperator.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded` in topological vector
  spaces.
* `IsCompactOperator.lowerSemicontinuousOn_add_comp_toWeakSpace_symm`: weak lower semicontinuity of
  a compact perturbation `u ↦ E₀ u + g (J u)` on any norm-bounded set.
* `IsCompactOperator.isClosed_toWeakSpace_inter_preimage_of_isBounded`,
  `IsCompactOperator.isCompact_toWeakSpace_inter_preimage_of_isCompact`, and
  `IsCompactOperator.isCompact_toWeakSpace_inter_preimage`: weak closedness and weak compactness of
  `S ∩ J ⁻¹' C` for bounded weakly closed or weakly compact `S` and closed `C`.
* `IsCompactOperator.isSeqClosed_toWeakSpace_preimage`: sequential weak closedness of `J ⁻¹' C` for
  a compact operator `J` and a closed set `C`.
* `IsCompactOperator.le_of_tendsto_add_comp_of_tendsto_toWeakSpace`: sequential weak lower
  semicontinuity of `u ↦ E₀ u + g (J u)`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Springer, 2016, §5.4.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Section 6.1 and Chapter 3.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications, III: Variational Methods and
  Optimization*, Springer, 1985, Chapter 38.
-/

public section

open Bornology Filter Function Metric NormedSpace Set Topology

namespace IsCompactOperator

private theorem image_toWeakSpace_inter_preimage {𝕜 V F : Type*} [CommSemiring 𝕜]
    [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V] (J : V → F) (S : Set V) (C : Set F) :
    toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C) =
      toWeakSpace 𝕜 V '' S ∩
        (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w)) ⁻¹' C := by
  simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, preimage_inter, preimage_preimage]

section TopologicalVectorSpace

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- If a family in `V` eventually stays in a von Neumann bounded set and converges weakly to `a`,
then its image under a compact operator `J` converges to `J a` in the topology of `F`. -/
theorem tendsto_of_tendsto_toWeakSpace_of_isVonNBounded (hJ : IsCompactOperator J) {α : Type*}
    {l : Filter α} {B : Set V} (hB : IsVonNBounded 𝕜 B) {u : α → V} (hu : ∀ᶠ n in l, u n ∈ B)
    {a : V} (h : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) l (𝓝 (toWeakSpace 𝕜 V a))) :
    Tendsto (fun n ↦ J (u n)) l (𝓝 (J a)) := by
  obtain ⟨K, hK, hJK⟩ := hJ.image_subset_compact_of_isVonNBounded hB
  refine TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact (𝕜 := 𝕜) hK
    (hu.mono fun n hn ↦ hJK (mem_image_of_mem J hn)) ?_
  -- `toWeakSpace` is `LinearEquiv.refl`, so `WeakSpace.map_apply` intertwines `WeakSpace.map J`
  -- and `J`.
  have hmap (x : V) : WeakSpace.map J (toWeakSpace 𝕜 V x) = toWeakSpace 𝕜 F (J x) :=
    WeakSpace.map_apply J x
  simpa only [Function.comp_def, hmap] using
    ((WeakSpace.map J).continuous.tendsto (toWeakSpace 𝕜 V a)).comp h

/-- A compact operator `J : V →L[𝕜] F` is continuous within the weak image of any von Neumann
bounded set `B ⊆ V` at every point `w : WeakSpace 𝕜 V`. -/
theorem continuousWithinAt_toWeakSpace_symm_of_isVonNBounded (hJ : IsCompactOperator J)
    {B : Set V} (hB : IsVonNBounded 𝕜 B) (w : WeakSpace 𝕜 V) :
    ContinuousWithinAt (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      (toWeakSpace 𝕜 V '' B) w := by
  refine hJ.tendsto_of_tendsto_toWeakSpace_of_isVonNBounded hB ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨v, hv, rfl⟩ := hz
    simpa only [LinearEquiv.symm_apply_apply] using hv
  · have hid : (fun z : WeakSpace 𝕜 V ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm z)) = id :=
      funext (toWeakSpace 𝕜 V).apply_symm_apply
    rw [hid, LinearEquiv.apply_symm_apply]
    exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- A compact operator is continuous from the weak topology to the original topology on every
von Neumann bounded set. -/
theorem continuousOn_comp_toWeakSpace_symm_of_isVonNBounded (hJ : IsCompactOperator J)
    {B : Set V} (hB : IsVonNBounded 𝕜 B) :
    ContinuousOn (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B) :=
  fun w _ ↦ hJ.continuousWithinAt_toWeakSpace_symm_of_isVonNBounded hB w

/-- On a von Neumann bounded weakly closed set `B`, the preimage of a closed set under a compact
operator is weakly closed. -/
theorem isClosed_toWeakSpace_inter_preimage_of_isVonNBounded (hJ : IsCompactOperator J)
    {B : Set V} (hB : IsVonNBounded 𝕜 B) (hBc : IsClosed (toWeakSpace 𝕜 V '' B)) {C : Set F}
    (hC : IsClosed C) : IsClosed (toWeakSpace 𝕜 V '' (B ∩ J ⁻¹' C)) := by
  rw [image_toWeakSpace_inter_preimage]
  exact (hJ.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded hB).preimage_isClosed_of_isClosed
    hBc hC

end TopologicalVectorSpace

section SeminormedSpace

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- If a family in `V` eventually stays in a norm-bounded set and converges weakly to `a`, then its
image under a compact operator `J` converges to `J a` in the topology of `F`. -/
theorem tendsto_of_tendsto_toWeakSpace_of_isBounded (hJ : IsCompactOperator J) {α : Type*}
    {l : Filter α} {B : Set V} (hB : IsBounded B) {u : α → V} (hu : ∀ᶠ n in l, u n ∈ B) {a : V}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) l (𝓝 (toWeakSpace 𝕜 V a))) :
    Tendsto (fun n ↦ J (u n)) l (𝓝 (J a)) :=
  hJ.tendsto_of_tendsto_toWeakSpace_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff]) hu h

/-- A compact operator `J : V →L[𝕜] F` is continuous within the weak image of any norm-bounded set
`B ⊆ V` at every point `w : WeakSpace 𝕜 V`. -/
theorem continuousWithinAt_toWeakSpace_symm (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) (w : WeakSpace 𝕜 V) :
    ContinuousWithinAt (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      (toWeakSpace 𝕜 V '' B) w :=
  hJ.continuousWithinAt_toWeakSpace_symm_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff]) w

/-- **Weak-to-norm continuity of compact operators on bounded sets.** A compact operator is
continuous from the weak topology to the original topology on every bounded set. -/
theorem continuousOn_comp_toWeakSpace_symm_of_isBounded (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) :
    ContinuousOn (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B) :=
  hJ.continuousOn_comp_toWeakSpace_symm_of_isVonNBounded <| by
    rwa [NormedSpace.isVonNBounded_iff]

/-- Composing a continuous map `g : F → α` on `J '' B` with a compact operator `J` gives a weakly
continuous map on any norm-bounded set `B ⊆ V`. -/
theorem continuousOn_comp_toWeakSpace_symm {α : Type*} [TopologicalSpace α]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B) {g : F → α}
    (hg : ContinuousOn g (J '' B)) :
    ContinuousOn (fun z : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm z)))
      (toWeakSpace 𝕜 V '' B) := by
  refine hg.comp (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hB) ?_
  rintro _ ⟨u, hu, rfl⟩
  simpa only [LinearEquiv.symm_apply_apply] using mem_image_of_mem J hu

/-- Composing a lower semicontinuous map `g : F → β` on `J '' B` with a compact operator `J` gives a
weakly lower semicontinuous functional on any norm-bounded set `B ⊆ V`. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm {β : Type*} [Preorder β]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B) {g : F → β}
    (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn (fun z : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm z)))
      (toWeakSpace 𝕜 V '' B) := by
  refine hg.comp (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hB) ?_
  rintro _ ⟨u, hu, rfl⟩
  simpa only [LinearEquiv.symm_apply_apply] using mem_image_of_mem J hu

/-- On any norm-bounded set `B ⊆ V`, adding `g ∘ J` (with `J` compact and `g` lower semicontinuous
on `J '' B`) to a weakly lower semicontinuous functional `E₀` preserves weak lower semicontinuity.
-/
theorem lowerSemicontinuousOn_add_comp_toWeakSpace_symm {β : Type*}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
    (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B) {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B))
    (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦
        E₀ ((toWeakSpace 𝕜 V).symm w) + g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' B) :=
  hE₀.add (hJ.lowerSemicontinuousOn_comp_toWeakSpace_symm hB hg)

/-- On a bounded weakly closed set `B`, the preimage of a closed set under a compact operator is
weakly closed. -/
theorem isClosed_toWeakSpace_inter_preimage_of_isBounded (hJ : IsCompactOperator J) {B : Set V}
    (hB : IsBounded B) (hBc : IsClosed (toWeakSpace 𝕜 V '' B)) {C : Set F} (hC : IsClosed C) :
    IsClosed (toWeakSpace 𝕜 V '' (B ∩ J ⁻¹' C)) :=
  hJ.isClosed_toWeakSpace_inter_preimage_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff]) hBc hC

/-- If `S ⊆ V` is norm-bounded and weakly compact, `J : V →L[𝕜] F` is compact, and `C ⊆ F` is
closed, then `S ∩ J ⁻¹' C` is weakly compact. -/
theorem isCompact_toWeakSpace_inter_preimage_of_isCompact (hJ : IsCompactOperator J) {S : Set V}
    (hS_bdd : IsBounded S) (hS_cpt : IsCompact (toWeakSpace 𝕜 V '' S)) {C : Set F}
    (hC : IsClosed C) :
    IsCompact (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)) := by
  have : CompactSpace (toWeakSpace 𝕜 V '' S) := isCompact_iff_compactSpace.1 hS_cpt
  have hcont : Continuous ((toWeakSpace 𝕜 V '' S).domRestrict
      fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z)) :=
    continuousOn_iff_continuous_domRestrict.1
      (hJ.continuousOn_comp_toWeakSpace_symm_of_isBounded hS_bdd)
  rw [image_toWeakSpace_inter_preimage, ← Subtype.image_preimage_val]
  exact (hC.preimage hcont).isCompact.image continuous_subtypeVal

/-- In a reflexive seminormed space over a proper nontrivially normed field, if `S ⊆ V` is
norm-bounded and weakly closed, `J : V →L[𝕜] F` is compact, and `C ⊆ F` is closed, then
`S ∩ J ⁻¹' C` is weakly compact. -/
theorem isCompact_toWeakSpace_inter_preimage [ProperSpace 𝕜]
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J) {S : Set V}
    (hS_bdd : IsBounded S) (hS_closed : IsClosed (toWeakSpace 𝕜 V '' S)) {C : Set F}
    (hC : IsClosed C) :
    IsCompact (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)) := by
  have hS_cpt : IsCompact (toWeakSpace 𝕜 V '' S) := by
    simpa only [hS_closed.closure_eq] using
      TauCeti.isCompact_closure_toWeakSpace_of_isBounded hV hS_bdd
  exact hJ.isCompact_toWeakSpace_inter_preimage_of_isCompact hS_bdd hS_cpt hC

end SeminormedSpace

section RCLike

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)] {J : V →L[𝕜] F}

/-- If `S ⊆ V` is weakly closed, `J : V →L[𝕜] F` is compact, and `C ⊆ F` is closed, then
intersecting `S ∩ J ⁻¹' C` with any closed norm ball in `V` yields a weakly closed set. -/
theorem isClosed_toWeakSpace_inter_preimage_inter_closedBall (hJ : IsCompactOperator J) {S : Set V}
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) {C : Set F} (hC : IsClosed C) (x : V) (r : ℝ) :
    IsClosed (toWeakSpace 𝕜 V '' ((S ∩ J ⁻¹' C) ∩ closedBall x r)) := by
  rw [Set.inter_right_comm]
  have hSR : IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall x r)) := by
    rw [image_inter (toWeakSpace 𝕜 V).injective]
    exact hS.inter (TauCeti.isClosed_toWeakSpace_closedBall x r)
  exact hJ.isClosed_toWeakSpace_inter_preimage_of_isBounded
    (isBounded_closedBall.subset inter_subset_right) hSR hC

/-- Over `ℝ` or `ℂ`, a compact operator `J : V →L[𝕜] F` sends every weakly convergent sequence in
`V` to a convergent sequence in `F`. -/
theorem tendsto_of_tendsto_toWeakSpace (hJ : IsCompactOperator J) {u : ℕ → V} {a : V}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V a))) :
    Tendsto (fun n ↦ J (u n)) atTop (𝓝 (J a)) :=
  hJ.tendsto_of_tendsto_toWeakSpace_of_isBounded hu.isBounded_range_of_toWeakSpace
    (Eventually.of_forall mem_range_self) hu

/-- Over `ℝ` or `ℂ`, a compact operator `J : V →L[𝕜] F` is sequentially continuous from the weak
topology on `V` to the topology of `F`. -/
theorem seqContinuous_toWeakSpace_symm (hJ : IsCompactOperator J) :
    SeqContinuous (fun w : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm w)) :=
  fun _ _ hw ↦ hJ.tendsto_of_tendsto_toWeakSpace
    (by simpa only [LinearEquiv.apply_symm_apply] using hw)

/-- Along any weakly convergent sequence in `V`, a compact operator `J : V →L[𝕜] F` composed with a
map `g : F → α` continuous at `J a` converges to `g (J a)`. -/
theorem tendsto_comp_of_tendsto_toWeakSpace {α : Type*} [TopologicalSpace α]
    (hJ : IsCompactOperator J) {u : ℕ → V} {a : V}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V a)))
    {g : F → α} (hg : ContinuousAt g (J a)) :
    Tendsto (fun n ↦ g (J (u n))) atTop (𝓝 (g (J a))) :=
  hg.tendsto.comp (hJ.tendsto_of_tendsto_toWeakSpace hu)

/-- **Sequential weak closedness of compact constraints.** Over `ℝ` or `ℂ`, for a compact operator
`J : V →L[𝕜] F` and any sequentially closed set `C ⊆ F`, `J ⁻¹' C` is sequentially closed in the
weak topology on `V`, even when `J ⁻¹' C` is unbounded and not weakly closed. -/
theorem isSeqClosed_toWeakSpace_preimage_of_isSeqClosed (hJ : IsCompactOperator J) {C : Set F}
    (hC : IsSeqClosed C) :
    IsSeqClosed (toWeakSpace 𝕜 V '' (J ⁻¹' C)) := by
  rw [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  exact hC.preimage hJ.seqContinuous_toWeakSpace_symm

/-- The preimage of a closed set under a compact operator is weakly sequentially closed. -/
theorem isSeqClosed_toWeakSpace_preimage (hJ : IsCompactOperator J) {C : Set F}
    (hC : IsClosed C) :
    IsSeqClosed (toWeakSpace 𝕜 V '' (J ⁻¹' C)) :=
  hJ.isSeqClosed_toWeakSpace_preimage_of_isSeqClosed hC.isSeqClosed

/-- **Sequential weak lower semicontinuity of a compact perturbation.** Over `ℝ` or `ℂ`, if
`u n → a` weakly in `V` along a sequence in `S`, `E₀` is weakly lower semicontinuous within `S` at
`a`, `J` is compact, and `g` is lower semicontinuous within `J '' S` at `J a`, then every limit `l`
of `E₀ (u n) + g (J (u n))` satisfies `E₀ a + g (J a) ≤ l`. -/
theorem le_of_tendsto_add_comp_of_tendsto_toWeakSpace {β : Type*}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
    (hJ : IsCompactOperator J) {E₀ : V → β} {g : F → β} {S : Set V} {u : ℕ → V} {a : V}
    (huS : ∀ n, u n ∈ S)
    (hE₀ : LowerSemicontinuousWithinAt
      (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) (toWeakSpace 𝕜 V a))
    (hg : LowerSemicontinuousWithinAt g (J '' S) (J a))
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V a)))
    {l : β} (hl : Tendsto (fun n ↦ E₀ (u n) + g (J (u n))) atTop (𝓝 l)) :
    E₀ a + g (J a) ≤ l := by
  -- The weakly convergent sequence has norm-bounded range `B = S ∩ range u`, on which `J` is
  -- weak-to-original continuous and `LowerSemicontinuousWithinAt.add` applies.
  let B : Set V := S ∩ range u
  have hB : IsBounded B := hu.isBounded_range_of_toWeakSpace.subset inter_subset_right
  have hmaps : MapsTo (fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      (toWeakSpace 𝕜 V '' B) (J '' S) := by
    rintro _ ⟨v, hv, rfl⟩
    simpa only [LinearEquiv.symm_apply_apply] using mem_image_of_mem J hv.left
  have hg_at : LowerSemicontinuousWithinAt g (J '' S)
      (J ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V a))) := by
    simpa only [LinearEquiv.symm_apply_apply] using hg
  have hsum := (hE₀.mono (image_mono inter_subset_left)).add
    (LowerSemicontinuousWithinAt.comp
      (g := fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      hg_at (hJ.continuousWithinAt_toWeakSpace_symm hB (toWeakSpace 𝕜 V a)) hmaps)
  have hu_B : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop
      (𝓝[toWeakSpace 𝕜 V '' B] (toWeakSpace 𝕜 V a)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu
      (Eventually.of_forall fun n ↦ mem_image_of_mem _ ⟨huS n, mem_range_self n⟩)
  simpa only [Function.comp_apply, LinearEquiv.symm_apply_apply] using hsum.le_of_tendsto hu_B <| by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hl

end RCLike

section RCLikeNormed

variable {𝕜 V F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {J : V →L[𝕜] F}

/-- For a compact operator `J : V →L[𝕜] F` over `ℝ` or `ℂ`, every level sphere
`{u : V | ‖J u‖ = r}` is sequentially closed in the weak topology. -/
theorem isSeqClosed_toWeakSpace_setOf_norm_eq (hJ : IsCompactOperator J) (r : ℝ) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u : V | ‖J u‖ = r}) := by
  have hsphere : {u : V | ‖J u‖ = r} = J ⁻¹' sphere (0 : F) r := by
    ext u
    simp
  rw [hsphere]
  exact hJ.isSeqClosed_toWeakSpace_preimage isClosed_sphere

end RCLikeNormed

end IsCompactOperator
