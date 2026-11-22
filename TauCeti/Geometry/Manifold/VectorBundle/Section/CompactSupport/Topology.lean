/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
public import TauCeti.Analysis.LocallyConvex.FinalTopology
import TauCeti.Geometry.Manifold.VectorBundle.Section.ScalarTopology
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.WeakWhitney
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The fixed-compact inductive topology on bundle tests

Compactly supported native bundle sections carry the final locally convex topology of their
fixed-compact support stages. Each stage has the subspace topology of the compact derivative
section topology. Linear maps (over `ℝ` or any `ℝ`-algebra) from this space into locally convex
real topological vector spaces are continuous exactly when they are continuous on every stage.
This is the fixed-support presentation of the topology used for bundle-valued tests.

When the vector bundle also carries a compatible structure over a normed `ℝ`-algebra `𝕜'` (in
particular `𝕜' = ℂ`), constant `𝕜'`-scalar multiplication is continuous on compactly supported
sections, and when `𝕜'` is finite-dimensional over `ℝ` the `𝕜'`-scalar action is jointly
continuous.

A native test function on the target of a smooth chart, read in a smooth bundle frame, extends by
zero to a compactly supported section (`Bundle.Trivialization.chartTestSection`), commuting with
any compatible extension-scalar action (`Bundle.Trivialization.chartTestSectionOfNormedAlgebra`).
These chart extensions are continuous from the native LF topology of `TestFunction`
(`Bundle.Trivialization.continuous_chartTestSection`), so precomposing a continuous linear
functional on bundle tests with a chart extension gives a continuous linear functional on the
native test functions of the chart target. In any smooth frame the coefficients of an extended
test are the test function composed with the chart and multiplied by the smooth transition
matrix, and both operations are continuous in the weak Whitney topology on coefficient functions
(`Bundle.Trivialization.continuous_frameCoordinates_chartTestSection_ofSupportedIn`).

Conversely, when `E` is locally compact and `M` is a `C^n` manifold, the chart-reading and
cutoff-reading maps for a chart `c` with `C^n` inverse subordinate to a smooth bundle frame `t` are
continuous from any smooth frame topology whose domains cover `c.source`
(`Bundle.Trivialization.continuous_chartReadSupportedIn`,
`Bundle.Trivialization.continuous_chartReadTestFunction`,
`Bundle.Trivialization.continuous_chartCutoffTestFunction`). When `c` is a two-sided `C^n` chart
with `c.source = univ` on a Hausdorff `C^n` manifold with locally compact model space, extension by
zero is a continuous linear equivalence
`𝓓^{n}(⟨c.target, c.open_target⟩, F) ≃L[ℝ] compactlySupported I F n V` for any covering
`compactlySupportedTopology` (`Bundle.Trivialization.chartTestSectionEquiv`).

The topology is Hausdorff for a covering frame system, is independent of that frame cover,
and on a compact base agrees with the compact derivative topology on all sections. In
particular, taking the final topology does not discard the section values. Convergence in a
single fixed-support stage implies convergence in the test topology.

We reuse `TauCeti.finalLocallyConvexTopology`, rather than the final topology of topological
spaces, so the test topology is a locally convex vector topology. No completeness or strict
inductive-limit assertion is made.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞ω}

variable [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The final locally convex topology of the fixed-compact support stages, each with its
compact derivative subspace topology. It is not defined as a subspace topology on tests. -/
@[instance_reducible]
def compactlySupportedTopology : TopologicalSpace (compactlySupported I F n V) :=
  letI := frameTopology (I := I) (n := n) e U hU
  TauCeti.finalLocallyConvexTopology (ofSupportedIn (I := I) (F := F) (V := V) (n := n))

/-- The test topology is the final locally convex topology of the fixed-compact stages. -/
theorem compactlySupportedTopology_def :
    compactlySupportedTopology (I := I) (n := n) e U hU =
      letI := frameTopology (I := I) (n := n) e U hU
      TauCeti.finalLocallyConvexTopology (ofSupportedIn (I := I) (F := F) (V := V) (n := n)) :=
  (rfl)

/-- The test topology is a group topology. -/
theorem isTopologicalAddGroup_compactlySupportedTopology :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    IsTopologicalAddGroup (compactlySupported I F n V) := by
  rw [compactlySupportedTopology_def]
  infer_instance

/-- Real scalar multiplication is continuous for the test topology. -/
theorem continuousSMul_compactlySupportedTopology :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    ContinuousSMul ℝ (compactlySupported I F n V) := by
  rw [compactlySupportedTopology_def]
  infer_instance

/-- The test topology is locally convex. -/
theorem locallyConvexSpace_compactlySupportedTopology :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    LocallyConvexSpace ℝ (compactlySupported I F n V) := by
  rw [compactlySupportedTopology_def]
  infer_instance

/-- Every fixed-compact support inclusion is continuous. -/
theorem continuous_ofSupportedIn (K : Compacts M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous (ofSupportedIn (I := I) (F := F) (V := V) (n := n) K) := by
  let := frameTopology (I := I) (n := n) e U hU
  exact TauCeti.FinalLocallyConvexTopology.continuous
    (ofSupportedIn (I := I) (F := F) (V := V) (n := n)) K

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]

/-- The linear universal property of compactly supported section tests for maps over an
`ℝ`-algebra into locally convex real topological vector spaces. Continuity is checked on
fixed-compact stages, not just on individual section values. -/
theorem continuous_compactlySupportedTopology_iff {𝕜 : Type*} [Semiring 𝕜] [Algebra ℝ 𝕜]
    [Module 𝕜 (compactlySupported I F n V)] [IsScalarTower ℝ 𝕜 (compactlySupported I F n V)]
    [Module 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    (g : compactlySupported I F n V →ₗ[𝕜] G) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous g ↔ ∀ K : Compacts M, Continuous (g ∘ ofSupportedIn K) := by
  let := frameTopology (I := I) (n := n) e U hU
  exact TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp _ g

/-- Forgetting compact support is continuous into the compact derivative section topology. -/
theorem continuous_val_compactlySupportedTopology :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous (Subtype.val : compactlySupported I F n V → Cₛ^n⟮I; F, V⟯) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  let := continuousSMul_frameTopology (I := I) (n := n) e U hU
  let := locallyConvexSpace_frameTopology (I := I) (n := n) e U hU
  exact (continuous_compactlySupportedTopology_iff e U hU
    (compactlySupported I F n V).subtype).2 fun K => by
      simpa only [Submodule.coe_subtype, val_comp_ofSupportedIn]
        using (continuous_subtypeVal :
          Continuous (Subtype.val : supportedIn I F n V K → Cₛ^n⟮I; F, V⟯))

/-- Each fixed-compact stage retains exactly its compact derivative topology inside the
test space; the final locally convex construction does not collapse a stage. Its
`Topology.IsEmbedding.tendsto_nhds_iff` characterizes convergence within a fixed stage. -/
theorem isEmbedding_ofSupportedIn (K : Compacts M) :
    letI := frameTopology (I := I) (n := n) e U hU
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Topology.IsEmbedding (ofSupportedIn (I := I) (F := F) (V := V) (n := n) K) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  exact Topology.IsEmbedding.of_comp (continuous_ofSupportedIn e U hU K)
    (continuous_val_compactlySupportedTopology e U hU) (by
      simpa only [val_comp_ofSupportedIn]
        using (Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (Subtype.val : supportedIn I F n V K → Cₛ^n⟮I; F, V⟯)))

/-- On a compact base the test topology is the compact derivative topology, transported
through the inclusion of compactly supported sections into all sections. -/
theorem compactlySupportedTopology_eq_induced [CompactSpace M] :
    compactlySupportedTopology (I := I) (n := n) e U hU =
      TopologicalSpace.induced (Subtype.val : compactlySupported I F n V → Cₛ^n⟮I; F, V⟯)
        (frameTopology (I := I) (n := n) e U hU) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  let := continuousSMul_frameTopology (I := I) (n := n) e U hU
  let := locallyConvexSpace_frameTopology (I := I) (n := n) e U hU
  let K : Compacts M := ⟨univ, isCompact_univ⟩
  let r : compactlySupported I F n V →ₗ[ℝ] supportedIn I F n V K :=
    (compactlySupported I F n V).subtype.codRestrict _
      (fun s => mem_supportedIn.2 (subset_univ s.val.tsupport))
  let R : compactlySupported I F n V →L[ℝ] supportedIn I F n V K :=
    ⟨r, continuous_subtypeVal.subtype_mk _⟩
  exact TauCeti.FinalLocallyConvexTopology.eq_of_rightInverse
    (ofSupportedIn (I := I) (F := F) (V := V) (n := n))
    (fun K => continuous_induced_rng.2 (by
      simpa only [val_comp_ofSupportedIn]
        using (continuous_subtypeVal :
          Continuous (Subtype.val : supportedIn I F n V K → Cₛ^n⟮I; F, V⟯)))) K R
    (fun s => Subtype.ext (ofSupportedIn_apply K (R s)))

section ExtensionScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra ℝ 𝕜']
  [NormedSpace 𝕜' F] [IsScalarTower ℝ 𝕜' F]
  [∀ x, Module 𝕜' (V x)] [∀ x, IsScalarTower ℝ 𝕜' (V x)] [VectorBundle 𝕜' F V]

/-- Constant multiplication by an extension scalar `c : 𝕜'` is continuous for the fixed-compact
inductive topology on compactly supported sections. -/
theorem continuousConstSMul_compactlySupportedTopology_ofNormedAlgebra :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    ContinuousConstSMul 𝕜' (compactlySupported I F n V) := by
  let := frameTopology (I := I) (n := n) e U hU
  let (K : Compacts M) :=
    continuousSMul_supportedIn_ofNormedAlgebra (𝕜' := 𝕜') (I := I) (n := n) e U hU (K := K)
  exact TauCeti.FinalLocallyConvexTopology.continuousConstSMul
    (ofSupportedIn (I := I) (F := F) (V := V) (n := n)) fun K c s ↦ by
      simpa only [← coe_ofSupportedInOfNormedAlgebra (𝕜' := 𝕜') (K := K)] using
        (ofSupportedInOfNormedAlgebra (I := I) (F := F) (V := V) (n := n) 𝕜' K).map_smul c s

/-- When the extension field `𝕜'` is finite-dimensional over `ℝ` (in particular `𝕜' = ℂ`), scalar
multiplication by `𝕜'` is jointly continuous on compactly supported sections. -/
theorem continuousSMul_compactlySupportedTopology_ofNormedAlgebra [FiniteDimensional ℝ 𝕜'] :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    ContinuousSMul 𝕜' (compactlySupported I F n V) := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  let := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) e U hU
  let := continuousSMul_compactlySupportedTopology (I := I) (n := n) e U hU
  let := continuousConstSMul_compactlySupportedTopology_ofNormedAlgebra
    (𝕜' := 𝕜') (I := I) (n := n) e U hU
  exact TauCeti.continuousSMul_of_continuousConstSMul_of_finiteDimensional ℝ

end ExtensionScalars

section Cover

variable [LocallyCompactSpace E] (hcover : ∀ x : M, ∃ i, x ∈ U i)

omit [LocallyCompactSpace E] in
include hcover in
/-- The test topology is Hausdorff: the continuous forgetful map separates sections. -/
theorem t2Space_compactlySupportedTopology :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    T2Space (compactlySupported I F n V) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := t2Space_frameTopology (I := I) (n := n) e U hU hcover
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  exact T2Space.of_injective_continuous Subtype.val_injective
    (continuous_val_compactlySupportedTopology e U hU)

include hcover in
/-- Any two covering smooth frame systems give the same test topology, since they give the
same topology on each fixed-support stage. -/
theorem compactlySupportedTopology_eq_of_covers
    {κ : Type*} (e' : κ → Trivialization F (π F V))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ x : M, ∃ j, x ∈ U' j) :
    compactlySupportedTopology (I := I) (n := n) e U hU =
      compactlySupportedTopology (I := I) (n := n) e' U' hU' := by
  unfold compactlySupportedTopology
  rw [frameTopology_eq_of_covers e U hU hcover e' U' hU' hcover']

end Cover

end ContMDiffSection

namespace Bundle.Trivialization

open ContMDiffSection
open scoped Distributions TauCeti.ManifoldWeakWhitney

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hct : c.source ⊆ t.baseSet)

/-- For test functions supported in a fixed compact subset of the chart target, the coefficients
of the extended sections in any smooth frame depend continuously on the test function, in the
weak Whitney topology. Near the chart source the coefficients are the test function composed with
the chart, multiplied by the transition matrix; away from the image of the support they vanish. -/
theorem continuous_frameCoordinates_chartTestSection_ofSupportedIn {K : Compacts E}
    (hK : (K : Set E) ⊆ c.target) (t' : Trivialization F (π F V)) [MemTrivializationAtlas t']
    {U : Opens M} (hU : (U : Set M) ⊆ t'.baseSet) :
    Continuous (fun φ : 𝓓^{n}_{K}(E, F) ↦ t'.frameCoordinates hU
      (t.chartTestSection c hc hct (TestFunction.ofSupportedIn hK φ)).val) := by
  have hL : IsClosed (c.symm '' K) :=
    (K.isCompact.image_of_continuousOn (c.continuousOn_symm.mono hK)).isClosed
  let val : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- Cover `U` by the chart source, where the coefficients are computed in the chart, and by the
  -- complement of the image of `K`, where they vanish.
  let W : Bool → Opens U := fun b ↦
    bif b then Opens.comap val ⟨c.source, c.open_source⟩ else
      Opens.comap val ⟨(c.symm '' K)ᶜ, hL.isOpen_compl⟩
  have hW : ∀ x : U, ∃ b, x ∈ W b := by
    intro x
    by_cases hx : (x : M) ∈ c.source
    · exact ⟨true, hx⟩
    · exact ⟨false, fun ⟨y, hy, hyx⟩ ↦ hx (hyx ▸ c.map_target (hK hy) : val x ∈ c.source)⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    -- Away from the image of `K` every extended test vanishes.
    convert continuous_const (y := (0 : C^n⟮I, W false; 𝓘(ℝ, F), F⟯)) using 1
    funext φ
    ext x
    have hx : ((x : U) : M) ∉
        (t.chartTestSection c hc hct (TestFunction.ofSupportedIn hK φ)).val.tsupport := by
      rw [tsupport_chartTestSection, TestFunction.coe_ofSupportedIn]
      exact fun hmem ↦ x.property (image_mono φ.tsupport_subset hmem)
    rw [ContMDiffMap.restrict_apply, frameCoordinates_apply, eq_zero_of_notMem_tsupport _ hx,
      ← t'.continuousLinearMapAt_apply_of_mem (R := ℝ) (hU (x : U).property), map_zero]
    simp
  | true =>
    -- On the chart source, compose with the chart and apply the transition matrix.
    let j : C^n⟮I, W true; 𝓘(ℝ, E), E⟯ :=
      ⟨fun x ↦ c ((x : U) : M), fun x ↦
        (hc.contMDiffAt (c.open_source.mem_nhds x.property)).comp x
          (contMDiff_subtypeVal.comp contMDiff_subtypeVal).contMDiffAt⟩
    let A : C^n⟮I, W true; 𝓘(ℝ, F →L[ℝ] F), F →L[ℝ] F⟯ :=
      ⟨fun x ↦ (t.coordChangeL ℝ t' ((x : U) : M) : F →L[ℝ] F), fun x ↦
        (contMDiffAt_coordChangeL (e := t) (e' := t') (hct x.property) (hU (x : U).property)).comp x
          (contMDiff_subtypeVal.comp contMDiff_subtypeVal).contMDiffAt⟩
    have hincl : Continuous (ContDiffMapSupportedIn.toContMDiffMap :
        𝓓^{n}_{K}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
      rw [ContMDiffMap.manifoldWeakWhitneyTopology_self]
      exact ContDiffMapSupportedIn.continuous_toContMDiffMap
    have hcomp : Continuous fun φ : 𝓓^{n}_{K}(E, F) ↦
        (ContDiffMapSupportedIn.toContMDiffMap φ).comp j :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (hincl.prodMk continuous_const)
    convert (ContMDiffMap.continuous_clmApplyLinearMap A).comp hcomp using 1
    funext φ
    ext x
    have hx : ((x : U) : M) ∈ c.source := x.property
    rw [ContMDiffMap.restrict_apply, frameCoordinates_apply,
      ← t'.continuousLinearMapAt_apply_of_mem (R := ℝ) (hU (x : U).property),
      t.continuousLinearMapAt_chartTestSection_eq_coordChangeL c hc hct t' _ hx (hU
          (x : U).property)]
    simp only [Function.comp_apply, ContMDiffMap.clmApplyLinearMap_apply,
      ContMDiffMap.comp_apply, TestFunction.coe_ofSupportedIn,
      ContDiffMapSupportedIn.coe_toContMDiffMap]
    -- Both sides are the transition matrix applied to `φ ∘ c`; the right side only unfolds the
    -- local multiplier `A` and chart map `j`.
    rfl

variable {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- **Chart extensions of test functions are continuous.** Extending native test functions on a
chart target by zero, through a smooth bundle frame, is continuous from the LF topology of
`TestFunction` to the fixed-compact inductive topology on compactly supported sections. -/
theorem continuous_chartTestSection :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous (t.chartTestSection c hc hct) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  refine (TestFunction.continuous_iff_continuous_comp (𝕜 := ℝ) _).2 fun K hK ↦ ?_
  -- A test supported in `K` extends to a section supported in the compact set `c.symm '' K`.
  let K' : Compacts M := ⟨c.symm '' K, K.isCompact.image_of_continuousOn
    (c.continuousOn_symm.mono hK)⟩
  have hval : Continuous fun φ : 𝓓^{n}_{K}(E, F) ↦
      (t.chartTestSection c hc hct (TestFunction.ofSupportedIn hK φ)).val :=
    (continuous_frameTopology_iff_frameCoordinates e U hU).2 fun i ↦
      continuous_frameCoordinates_chartTestSection_ofSupportedIn t c hc hct hK (e i) (hU i)
  let g : 𝓓^{n}_{K}(E, F) → supportedIn I F n V K' := fun φ ↦
    ⟨_, t.chartTestSection_mem_supportedIn c hc hct (TestFunction.ofSupportedIn hK φ) (by
      rw [TestFunction.coe_ofSupportedIn]
      exact φ.tsupport_subset)⟩
  refine ((continuous_ofSupportedIn e U hU K').comp (hval.subtype_mk _ : Continuous g)).congr
    fun φ ↦ ?_
  exact Subtype.ext (ofSupportedIn_apply K' (g φ))

end Bundle.Trivialization

namespace Bundle.Trivialization

open ContMDiffSection
open scoped Distributions TauCeti.ManifoldWeakWhitney

section ChartRead

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target)
  (hct : c.source ⊆ t.baseSet)

private def chartTestSectionInv (hc_univ : c.source = univ) :
    compactlySupported I F n V →ₗ[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) where
  toFun s :=
    t.chartReadTestFunction c hc_symm hct
      (K := ⟨s.val.tsupport, mem_compactlySupported.1 s.property⟩)
      ((subset_univ _).trans hc_univ.symm.subset) ⟨s.val, mem_supportedIn.2 Subset.rfl⟩
  map_add' s₁ s₂ := by
    ext y
    by_cases hy : y ∈ c.target
    · simp [t.chartReadTestFunction_apply_of_mem _ _ _ _ _ hy]
    · simp [t.chartReadTestFunction_apply_of_notMem _ _ _ _ _ hy]
  map_smul' a s := by
    ext y
    by_cases hy : y ∈ c.target
    · simp [t.chartReadTestFunction_apply_of_mem _ _ _ _ _ hy]
    · simp [t.chartReadTestFunction_apply_of_notMem _ _ _ _ _ hy]

private theorem chartTestSectionInv_apply (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) :
    t.chartTestSectionInv c hc_symm hct hc_univ s =
      t.chartReadTestFunction c hc_symm hct
        (K := ⟨s.val.tsupport, mem_compactlySupported.1 s.property⟩)
        ((subset_univ _).trans hc_univ.symm.subset) ⟨s.val, mem_supportedIn.2 Subset.rfl⟩ :=
  rfl

variable [LocallyCompactSpace E] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Reading sections supported in a compact subset `K ⊆ c.source` in a chart `c` with `C^n`
inverse subordinate to `t` is continuous from any smooth frame topology whose domains cover
`c.source` into `𝓓^{n}_{c '' K}(E, F)`. -/
theorem continuous_chartReadSupportedIn (hcover : ∀ x ∈ c.source, ∃ i, x ∈ U i)
    {K : Compacts M} (hKc : (K : Set M) ⊆ c.source) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartReadSupportedIn c hc_symm hct hKc) := by
  let := frameTopology (I := I) (n := n) e U hU
  let K' : Compacts E := ⟨c '' (K : Set M), K.isCompact.image_of_continuousOn
    (c.continuousOn.mono hKc)⟩
  refine ContDiffMapSupportedIn.continuous_iff_continuous_toContMDiffMap.2 ?_
  suffices h : Continuous (fun s : supportedIn I F n V K ↦
      ContDiffMapSupportedIn.toContMDiffMap (t.chartReadSupportedIn c hc_symm hct hKc s)) by
    rwa [ContMDiffMap.manifoldWeakWhitneyTopology_self] at h
  let W : Bool → Opens E := fun b ↦
    bif b then ⟨c.target, c.open_target⟩ else ⟨(K' : Set E)ᶜ, K'.isCompact.isClosed.isOpen_compl⟩
  have hW : ∀ y : E, ∃ b, y ∈ W b := fun y ↦ by
    by_cases hy : y ∈ c.target
    · exact ⟨true, hy⟩
    · exact ⟨false, fun ⟨x, hxK, hxy⟩ ↦ hy (hxy ▸ c.map_source (hKc hxK))⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮𝓘(ℝ, E), W false; 𝓘(ℝ, F), F⟯)) using 1
    funext s
    ext y
    rw [ContMDiffMap.restrict_apply, ContDiffMapSupportedIn.coe_toContMDiffMap,
      (t.chartReadSupportedIn c hc_symm hct hKc s).zero_on_compl y.property]
    simp
  | true =>
    let Uc : Opens M := ⟨c.source, c.open_source⟩
    let j : C^n⟮𝓘(ℝ, E), W true; I, Uc⟯ :=
      ⟨fun y ↦ ⟨c.symm y, c.map_target y.property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff Uc _).mp
          (hc_symm.comp_contMDiff contMDiff_subtypeVal fun y ↦ y.property)⟩
    have hcoord : Continuous (fun s : supportedIn I F n V K ↦
        t.frameCoordinates (I := I) (n := n) (U := Uc) hct s.val) :=
      (continuous_frameCoordinates_of_subset_iUnion e U hU t Uc hct
        fun x hx ↦ mem_iUnion.2 (hcover x hx)).comp continuous_subtypeVal
    refine (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      (hcoord.prodMk (continuous_const (y := j)))).congr fun s ↦ ?_
    ext y
    rw [Function.comp_apply, ContMDiffMap.comp_apply]
    simp [j, t.chartReadSupportedIn_apply_of_mem c hc_symm hct hKc s y.property,
      hct (c.map_target y.property)]

/-- Reading sections supported in `K ⊆ c.source` as native test functions on `c.target` is
continuous from any smooth frame topology whose domains cover `c.source`. -/
theorem continuous_chartReadTestFunction (hcover : ∀ x ∈ c.source, ∃ i, x ∈ U i)
    {K : Compacts M} (hKc : (K : Set M) ⊆ c.source) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartReadTestFunction c hc_symm hct hKc) := by
  let := frameTopology (I := I) (n := n) e U hU
  let K' : Compacts E :=
    ⟨c '' (K : Set M), K.isCompact.image_of_continuousOn (c.continuousOn.mono hKc)⟩
  have hK't : (K' : Set E) ⊆ (⟨c.target, c.open_target⟩ : Opens E) :=
    image_subset_iff.2 fun _ hx ↦ c.map_source (hKc hx)
  refine ((TestFunction.ofSupportedInCLM ℝ hK't).continuous.comp
    (t.continuous_chartReadSupportedIn c hc_symm hct e U hU hcover hKc)).congr fun s ↦ ?_
  ext y
  by_cases hy : y ∈ c.target
  · simp [TestFunction.coe_ofSupportedInCLM,
      t.chartReadSupportedIn_apply_of_mem c hc_symm hct hKc s hy,
      t.chartReadTestFunction_apply_of_mem c hc_symm hct hKc s hy]
  · simp [TestFunction.coe_ofSupportedInCLM,
      t.chartReadSupportedIn_apply_of_notMem c hc_symm hct hKc s hy, hy]

/-- Localizing sections by a compactly supported `C^n` cutoff `ρ` with `tsupport ρ ⊆ c.source`
and reading the result in `t` and `c` is continuous from any smooth frame topology whose domains
cover `c.source` into `𝓓^{n}(⟨c.target, c.open_target⟩, F)`. -/
theorem continuous_chartCutoffTestFunction (hcover : ∀ x ∈ c.source, ∃ i, x ∈ U i)
    (ρ : C^n⟮I, M; ℝ⟯) (hρc : HasCompactSupport ρ) (hρs : _root_.tsupport ρ ⊆ c.source) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartCutoffTestFunction c hc_symm hct ρ hρc hρs) := by
  let := frameTopology (I := I) (n := n) e U hU
  let Kρ : Compacts M := ⟨_root_.tsupport ρ, hρc⟩
  refine ((t.continuous_chartReadTestFunction c hc_symm hct e U hU hcover (K := Kρ) hρs).comp
    ((continuous_smulLinearMap e U hU ρ).subtype_mk fun s ↦
      mem_supportedIn.2 ((tsupport_smul_function_subset ρ s).trans inter_subset_left))).congr
    fun s ↦ ?_
  ext y
  by_cases hy : y ∈ c.target
  · simp [t.chartReadTestFunction_apply_of_mem c hc_symm hct (K := Kρ) hρs _ hy,
      t.chartCutoffTestFunction_apply_of_mem c hc_symm hct ρ hρc hρs s hy]
  · simp [hy]

section ChartTestSectionEquiv

variable (hcover : ∀ x : M, ∃ i, x ∈ U i)

include hcover in
private theorem continuous_chartTestSectionInv (hc_univ : c.source = univ) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous (t.chartTestSectionInv c hc_symm hct hc_univ) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  refine (continuous_compactlySupportedTopology_iff e U hU
    (t.chartTestSectionInv c hc_symm hct hc_univ)).2 fun K ↦ ?_
  refine (t.continuous_chartReadTestFunction c hc_symm hct e U hU (fun x _ ↦ hcover x)
    ((subset_univ _).trans hc_univ.symm.subset)).congr fun s ↦ ?_
  ext y
  by_cases hy : y ∈ c.target
  · simp [chartTestSectionInv_apply, t.chartReadTestFunction_apply_of_mem _ _ _ _ _ hy]
  · simp [chartTestSectionInv_apply, t.chartReadTestFunction_apply_of_notMem _ _ _ _ _ hy]

/-- When a two-sided `C^n` chart `c` subordinate to a smooth bundle trivialization `t` has
`c.source = univ`, extending native test functions by `t.chartTestSection` is a continuous linear
equivalence onto `compactlySupported I F n V` with its fixed-compact inductive topology. -/
def chartTestSectionEquiv [T2Space M] (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hc_univ : c.source = univ) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    𝓓^{n}(⟨c.target, c.open_target⟩, F) ≃L[ℝ] compactlySupported I F n V :=
  letI := compactlySupportedTopology (I := I) (n := n) e U hU
  have hright : Function.RightInverse (t.chartTestSectionInv c hc_symm hct hc_univ)
      (t.chartTestSection c hc hct) := fun s ↦ by
    rw [t.chartTestSectionInv_apply, t.chartTestSection_chartReadTestFunction c hc_symm hct hc]
    exact Subtype.ext (ofSupportedIn_apply _ _)
  { toLinearEquiv :=
      { toLinearMap := t.chartTestSection c hc hct
        invFun := t.chartTestSectionInv c hc_symm hct hc_univ
        left_inv φ := t.chartTestSection_injective c hc hct (hright (t.chartTestSection c hc hct φ))
        right_inv := hright }
    continuous_toFun := t.continuous_chartTestSection c hc hct e U hU
    continuous_invFun := t.continuous_chartTestSectionInv c hc_symm hct e U hU hcover hc_univ }

@[simp]
theorem chartTestSectionEquiv_apply [T2Space M] (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    (hc_univ : c.source = univ) (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ φ =
      t.chartTestSection c hc hct φ :=
  (rfl)

/-- On the chart target, the inverse of `chartTestSectionEquiv` reads the section in `t` along
`c.symm`. -/
theorem chartTestSectionEquiv_symm_apply_of_mem [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) {y : E} (hy : y ∈ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  exact t.chartReadTestFunction_apply_of_mem c hc_symm hct _ _ hy

/-- Outside the chart target, the inverse of `chartTestSectionEquiv` vanishes. -/
@[simp]
theorem chartTestSectionEquiv_symm_apply_of_notMem [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source) (hc_univ : c.source = univ)
    (s : compactlySupported I F n V) {y : E} (hy : y ∉ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc_symm hct e U hU hcover hc hc_univ).symm s y = 0 := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  exact t.chartReadTestFunction_apply_of_notMem c hc_symm hct _ _ hy

end ChartTestSectionEquiv

end ChartRead

end Bundle.Trivialization
