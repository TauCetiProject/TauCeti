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
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Analysis.Distribution.TestFunction.WeakWhitney
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# The fixed-compact and chart-generated inductive topologies on bundle tests

Compactly supported native bundle sections carry the final locally convex topology of their
fixed-compact support stages (`ContMDiffSection.compactlySupportedTopology`), where each stage has
the subspace topology of the compact derivative section topology. Linear maps from this space into
locally convex real topological vector spaces are continuous exactly when they are continuous on
every stage. Smooth scalar multiplication is continuous both in the frame topology
(`ContMDiffSection.continuous_smulLinearMap_frameTopology`) and on compactly supported sections
(`ContMDiffSection.continuous_smulLinearMap_compactlySupported`).

A native test function on the target of a smooth chart, read in a smooth bundle frame, extends by
zero to a compactly supported section (`Bundle.Trivialization.chartTestSection`). These chart
extensions are continuous from the native LF topology of `TestFunction`
(`Bundle.Trivialization.continuous_chartTestSection`). Conversely, when the inverse chart is `C^n`,
sections supported in a compact subset of the chart source are read back continuously as supported
test functions (`Bundle.Trivialization.chartTestCoeff`,
`Bundle.Trivialization.continuous_chartTestCoeff`). In particular, on a manifold covered by a
single global chart and frame (such as an open subset of Euclidean space with a trivial bundle),
chart extension is a continuous linear equivalence with Mathlib's `TestFunction`
(`Bundle.Trivialization.chartTestSectionEquiv`).

A family of smooth charts subordinate to smooth frames generates a second final locally convex
topology on compactly supported sections (`ContMDiffSection.chartTestTopology`). It is always
finer than the fixed-compact topology (`chartTestTopology_le_compactlySupportedTopology`) and
Hausdorff (`t2Space_chartTestTopology`). When the model space is finite-dimensional and the charts
have `C^n` inverses and cover the base, finite `C^n` partitions of unity on compact sets identify
the two topologies (`ContMDiffSection.chartTestTopology_eq_compactlySupportedTopology`), yielding
cover independence (`ContMDiffSection.chartTestTopology_eq_of_covers`) and the chart-wise
universal continuity criterion for linear maps out of bundle test sections
(`ContMDiffSection.continuous_compactlySupportedTopology_iff_comp_chartTestSection`, and on any
boundaryless manifold
`ContMDiffSection.continuous_compactlySupportedTopology_iff_forall_chartTestSection`).

The topology is Hausdorff for a covering frame system, is independent of that frame cover, and on
a compact base agrees with the compact derivative topology on all sections. In particular, taking
the final topology does not discard the section values. Convergence in a single fixed-support stage
implies convergence in the test topology. We reuse `TauCeti.finalLocallyConvexTopology`, rather
than the final topology of topological spaces, so the test topology is a locally convex vector
topology. No completeness, σ-compactness, second-countability, or strict inductive-limit
assertion is made.
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

/-- The linear universal property of compactly supported section tests for maps into locally
convex real topological vector spaces. Continuity is checked on fixed-compact stages, not just
on individual section values. -/
theorem continuous_compactlySupportedTopology_iff
    (g : compactlySupported I F n V →ₗ[ℝ] G) :
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

namespace ContMDiffSection

section ScalarMul

open scoped TauCeti.ManifoldWeakWhitney

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Pointwise multiplication by a fixed `C^n` scalar function is continuous in the compact
derivative frame topology. -/
theorem continuous_smulLinearMap_frameTopology (f : C^n⟮I, M; 𝕜⟯) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (smulLinearMap (I := I) (F := F) (V := V) (n := n) f) := by
  let := frameTopology (I := I) (n := n) e U hU
  refine (continuous_frameTopology_iff_frameCoordinates e U hU).2 fun i ↦ ?_
  let A : C^n⟮I, U i; 𝓘(𝕜, F →L[𝕜] F), F →L[𝕜] F⟯ :=
    ⟨fun x ↦ f x • ContinuousLinearMap.id 𝕜 F,
      (f.contMDiff.comp contMDiff_subtypeVal).smul contMDiff_const⟩
  convert (ContMDiffMap.continuous_clmApplyLinearMap A).comp
    (continuous_frameCoordinates e U hU i) using 1
  funext s
  ext x
  simp only [Function.comp_apply, ContMDiffMap.clmApplyLinearMap_apply,
    Trivialization.frameCoordinates_apply, smulLinearMap_eq_smul, smul_apply,
    ← (e i).continuousLinearMapAt_apply_of_mem (R := 𝕜) (hU i x.property), map_smul]
  rfl

end ScalarMul

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- Pointwise multiplication by a fixed `C^n` scalar function is continuous on compactly supported
sections for the fixed-compact inductive topology. -/
theorem continuous_smulLinearMap_compactlySupported (f : C^n⟮I, M; ℝ⟯) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous ((smulLinearMap (I := I) (F := F) (V := V) (n := n) f).restrict
      fun _ hs ↦ smul_function_mem_compactlySupported f hs) := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  refine (continuous_compactlySupportedTopology_iff e U hU _).2 fun K ↦ ?_
  let g : supportedIn I F n V K → supportedIn I F n V K := fun s ↦
    ⟨f • s.val, smul_function_mem_supportedIn f s.property⟩
  have hg : Continuous g :=
    ((continuous_smulLinearMap_frameTopology e U hU f).comp continuous_subtypeVal).subtype_mk _
  exact ((continuous_ofSupportedIn e U hU K).comp hg).congr fun s ↦ Subtype.ext (by simp [g])

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

section ChartCoeff

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
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target) (hct : c.source ⊆ t.baseSet)

private def chartCoeffFun (s : Cₛ^n⟮I; F, V⟯) (y : E) : F := by
  classical
  exact if y ∈ c.target then t.continuousLinearMapAt ℝ (c.symm y) (s (c.symm y)) else 0

omit [ContMDiffVectorBundle n F V I] in
private theorem chartCoeffFun_eq_zero {K : Set M} {s : Cₛ^n⟮I; F, V⟯}
    (hs : s ∈ supportedIn I F n V K) {y : E} (hy : y ∉ c '' K) :
    chartCoeffFun t c s y = 0 := by
  by_cases hyt : y ∈ c.target
  · have hns : c.symm y ∉ s.tsupport :=
      fun h ↦ hy ⟨c.symm y, mem_supportedIn.1 hs h, c.right_inv hyt⟩
    simp [chartCoeffFun, hyt, s.eq_zero_of_notMem_tsupport hns]
  · simp [chartCoeffFun, hyt]

include hc_symm hct in
private theorem contDiff_chartCoeffFun {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    (s : supportedIn I F n V K) :
    ContDiff ℝ n (chartCoeffFun t c s.val) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ c.target
  · have hsec : ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ (t ⟨x, s.val x⟩).2) (c.symm y) :=
      (t.contMDiffAt_section_iff (hct (c.map_target hy))).1 (s.val.contMDiff (c.symm y))
    have hcomp : ContDiffAt ℝ n (fun z ↦ (t ⟨c.symm z, s.val (c.symm z)⟩).2) y :=
      contMDiffAt_iff_contDiffAt.1 <|
        hsec.comp y (hc_symm.contMDiffAt (c.open_target.mem_nhds hy))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [c.open_target.mem_nhds hy] with z hz
    simp only [chartCoeffFun, hz, ↓reduceIte,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target hz))]
  · have hC : IsClosed (c '' (K : Set M)) :=
      (K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)).isClosed
    have hyC : y ∉ c '' (K : Set M) := by
      rintro ⟨x, hx, rfl⟩
      exact hy (c.map_source (hK hx))
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hyC] with z hz
    exact chartCoeffFun_eq_zero t c s.property hz

private def chartCoeff {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) (s : supportedIn I F n V K) :
    𝓓^{n}_{L}(E, F) :=
  ⟨chartCoeffFun t c s.val, contDiff_chartCoeffFun t c hc_symm hct hK s,
    fun _ hy ↦ chartCoeffFun_eq_zero t c s.property fun h ↦ hy (hKL h)⟩

private theorem coe_chartCoeff {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) (s : supportedIn I F n V K) (y : E) :
    chartCoeff t c hc_symm hct hK hKL s y = chartCoeffFun t c s.val y := rfl

/-- Read a `C^n` section supported in a compact subset `K` of a chart source as a supported test
function in `E`, via the inverse chart and the bundle frame. -/
def chartTestCoeff {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) :
    supportedIn I F n V K →ₗ[ℝ] 𝓓^{n}_{L}(E, F) where
  toFun := chartCoeff t c hc_symm hct hK hKL
  map_add' s₁ s₂ := by
    ext y
    by_cases hy : y ∈ c.target <;> simp [coe_chartCoeff, chartCoeffFun, hy]
  map_smul' a s := by
    ext y
    by_cases hy : y ∈ c.target <;> simp [coe_chartCoeff, chartCoeffFun, hy]

/-- On the chart target, `chartTestCoeff` evaluates the bundle frame on the section at the
inverse-chart point. -/
theorem chartTestCoeff_apply_of_mem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L)
    (s : supportedIn I F n V K) {y : E} (hy : y ∈ c.target) :
    t.chartTestCoeff c hc_symm hct hK hKL s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) := by
  simp [chartTestCoeff, coe_chartCoeff, chartCoeffFun, hy]

/-- Outside the chart target, `chartTestCoeff` vanishes. -/
@[simp]
theorem chartTestCoeff_apply_of_notMem {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L)
    (s : supportedIn I F n V K) {y : E} (hy : y ∉ c.target) :
    t.chartTestCoeff c hc_symm hct hK hKL s y = 0 := by
  simp [chartTestCoeff, coe_chartCoeff, chartCoeffFun, hy]

/-- Extending the chart coefficients of a section supported inside the chart source recovers the
original section. -/
theorem chartTestSection_ofSupportedIn_chartTestCoeff [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L) (hL : (L : Set E) ⊆ c.target)
    (s : supportedIn I F n V K) :
    t.chartTestSection c hc hct
      (TestFunction.ofSupportedIn hL (t.chartTestCoeff c hc_symm hct hK hKL s)) =
      ofSupportedIn K s := by
  apply Subtype.ext
  ext x
  by_cases hx : x ∈ c.source
  · rw [chartTestSection_apply_of_mem t c hc hct _ hx, TestFunction.coe_ofSupportedIn,
      chartTestCoeff_apply_of_mem t c hc_symm hct hK hKL s (c.map_source hx), c.left_inv hx,
      t.symmL_continuousLinearMapAt (hct hx), ofSupportedIn_apply]
  · rw [chartTestSection_apply_of_notMem t c hc hct _ hx, ofSupportedIn_apply]
    exact (s.val.eq_zero_of_notMem_tsupport fun h ↦ hx (hK (mem_supportedIn.1 s.property h))).symm

/-- Reading back an extended supported test function recovers it identically. -/
theorem chartTestCoeff_chartTestSection_ofSupportedIn [T2Space M]
    (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
    {L : Compacts E} (hL : (L : Set E) ⊆ c.target)
    {K : Compacts M} (hK : (K : Set M) ⊆ c.source) (hKL : c '' (K : Set M) ⊆ L)
    (hLK : c.symm '' (L : Set E) ⊆ K) (φ : 𝓓^{n}_{L}(E, F)) :
    t.chartTestCoeff c hc_symm hct hK hKL
      ⟨(t.chartTestSection c hc hct (TestFunction.ofSupportedIn hL φ)).val,
        mem_supportedIn.2 ((mem_supportedIn.1 (t.chartTestSection_mem_supportedIn c hc hct
          (TestFunction.ofSupportedIn hL φ) (K := (L : Set E)) (by
            rw [TestFunction.coe_ofSupportedIn]
            exact φ.tsupport_subset))).trans hLK)⟩ = φ := by
  ext y
  by_cases hy : y ∈ c.target
  · rw [chartTestCoeff_apply_of_mem t c hc_symm hct hK hKL _ hy,
      continuousLinearMapAt_chartTestSection t c hc hct _ (c.map_target hy),
      c.right_inv hy, TestFunction.coe_ofSupportedIn]
  · rw [chartTestCoeff_apply_of_notMem t c hc_symm hct hK hKL _ hy]
    exact (φ.zero_on_compl fun h ↦ hy (hL h)).symm

/-- **Chart localization of supported sections is continuous.** On a fixed compact subset of a
chart source, reading sections in the chart and frame depends continuously on the section from the
compact derivative frame topology to `𝓓^{n}_{L}(E, F)`. -/
theorem continuous_chartTestCoeff [LocallyCompactSpace E] [IsManifold I n M]
    {K : Compacts M} (hK : (K : Set M) ⊆ c.source)
    {L : Compacts E} (hKL : c '' (K : Set M) ⊆ L)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (t.chartTestCoeff c hc_symm hct hK hKL) := by
  let := frameTopology (I := I) (n := n) e U hU
  have hind : Topology.IsInducing (ContDiffMapSupportedIn.toContMDiffMap :
      𝓓^{n}_{L}(E, F) → C^n⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) := by
    rw [ContMDiffMap.manifoldWeakWhitneyTopology_self]
    exact ContDiffMapSupportedIn.isInducing_toContMDiffMap
  refine hind.continuous_iff.2 ?_
  have hC : IsClosed (c '' (K : Set M)) :=
    (K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)).isClosed
  -- Cover `E` by the chart target, where the map is the frame coordinates pulled back by `c.symm`,
  -- and by the complement of `c '' K`, where every supported section vanishes.
  let W : Bool → Opens E := fun b ↦
    bif b then ⟨c.target, c.open_target⟩ else ⟨(c '' (K : Set M))ᶜ, hC.isOpen_compl⟩
  have hW : ∀ y : E, ∃ b, y ∈ W b := by
    intro y
    by_cases hy : y ∈ c.target
    · exact ⟨true, hy⟩
    · exact ⟨false, fun ⟨x, hx, hxy⟩ ↦ hy (hxy ▸ c.map_source (hK hx))⟩
  refine ContMDiffMap.continuous_of_forall_continuous_restrict W hW fun b ↦ ?_
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮𝓘(ℝ, E), W false; 𝓘(ℝ, F), F⟯)) using 1
    funext s
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap, ContMDiffMap.coe_zero, Pi.zero_apply]
    exact chartCoeffFun_eq_zero t c s.property y.property
  | true =>
    let j : C^n⟮𝓘(ℝ, E), W true; I, (⟨c.source, c.open_source⟩ : Opens M)⟯ :=
      ⟨fun y ↦ ⟨c.symm y.val, c.map_target y.property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff ⟨c.source, c.open_source⟩ _).1 fun y ↦
          (hc_symm.contMDiffAt (c.open_target.mem_nhds y.property)).comp y
            contMDiff_subtypeVal.contMDiffAt⟩
    have hcoord : Continuous fun s : supportedIn I F n V K ↦
        t.frameCoordinates (I := I) (n := n) (U := ⟨c.source, c.open_source⟩) hct s.val :=
      (continuous_frameCoordinates_of_cover e U hU hcover t ⟨c.source, c.open_source⟩ hct).comp
        continuous_subtypeVal
    have hcomp : Continuous fun s : supportedIn I F n V K ↦
        (t.frameCoordinates (I := I) (n := n)
          (U := ⟨c.source, c.open_source⟩) hct s.val).comp j :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (hcoord.prodMk continuous_const)
    convert hcomp using 1
    funext s
    ext y
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContDiffMapSupportedIn.coe_toContMDiffMap,
      chartTestCoeff_apply_of_mem t c hc_symm hct hK hKL s y.property,
      ContMDiffMap.comp_apply, frameCoordinates_apply,
      t.continuousLinearMapAt_apply_of_mem (R := ℝ) (hct (c.map_target y.property))]
    rfl

end ChartCoeff

section GlobalChart

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
  (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
  (hc_symm : ContMDiffOn 𝓘(ℝ, E) I n c.symm c.target)
  (hct : c.source ⊆ t.baseSet) (hcsource : c.source = univ)
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (hcover : ∀ x : M, ∃ i, x ∈ U i)

/-- **Global-chart equivalence with native test functions.** When a smooth chart with `C^n` inverse
covers the entire manifold inside a smooth bundle frame (for instance, an open subset of a normed
space with a trivial bundle), chart extension is a continuous linear equivalence from Mathlib's
`TestFunction` to compactly supported sections with their fixed-compact inductive topology. -/
def chartTestSectionEquiv :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    𝓓^{n}(⟨c.target, c.open_target⟩, F) ≃L[ℝ] compactlySupported I F n V := by
  let := frameTopology (I := I) (n := n) e U hU
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  let invFun : compactlySupported I F n V → 𝓓^{n}(⟨c.target, c.open_target⟩, F) :=
    fun s ↦
    let K : Compacts M := ⟨s.val.tsupport, mem_compactlySupported.1 s.property⟩
    have hK : (K : Set M) ⊆ c.source := hcsource ▸ subset_univ _
    let L : Compacts E := ⟨c '' K, K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)⟩
    have hL : (L : Set E) ⊆ c.target := image_subset_iff.2 fun x hx ↦ c.map_source (hK hx)
    TestFunction.ofSupportedIn hL
      (t.chartTestCoeff c hc_symm hct hK Subset.rfl ⟨s.val, mem_supportedIn.2 Subset.rfl⟩)
  have hinv_mem (s : compactlySupported I F n V) {y : E} (hy : y ∈ c.target) :
      invFun s y = t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) := by
    simp only [invFun, TestFunction.coe_ofSupportedIn,
      chartTestCoeff_apply_of_mem _ _ _ _ _ _ _ hy]
  have hinv_notMem (s : compactlySupported I F n V) {y : E} (hy : y ∉ c.target) :
      invFun s y = 0 := by
    simp only [invFun, TestFunction.coe_ofSupportedIn,
      chartTestCoeff_apply_of_notMem _ _ _ _ _ _ _ hy]
  refine
    { toLinearMap := t.chartTestSection c hc hct
      invFun := invFun
      left_inv := fun φ ↦ by
        ext y
        by_cases hy : y ∈ c.target
        · rw [LinearMap.toFun_eq_coe, hinv_mem _ hy,
            continuousLinearMapAt_chartTestSection t c hc hct φ (c.map_target hy), c.right_inv hy]
        · rw [LinearMap.toFun_eq_coe, hinv_notMem _ hy]
          exact (φ.zero_on_compl hy).symm
      right_inv := fun s ↦ by
        apply Subtype.ext
        ext x
        have hx : x ∈ c.source := hcsource ▸ mem_univ x
        rw [LinearMap.toFun_eq_coe, chartTestSection_apply_of_mem t c hc hct _ hx,
          hinv_mem _ (c.map_source hx), c.left_inv hx, t.symmL_continuousLinearMapAt (hct hx)]
      continuous_toFun := continuous_chartTestSection t c hc hct e U hU
      continuous_invFun := ?_ }
  let invLM : compactlySupported I F n V →ₗ[ℝ] 𝓓^{n}(⟨c.target, c.open_target⟩, F) :=
    { toFun := invFun
      map_add' := fun s₁ s₂ ↦ by
        ext y
        by_cases hy : y ∈ c.target
        · simp [hinv_mem _ hy]
        · simp [hinv_notMem _ hy]
      map_smul' := fun a s ↦ by
        ext y
        by_cases hy : y ∈ c.target
        · simp [hinv_mem _ hy]
        · simp [hinv_notMem _ hy] }
  refine (continuous_compactlySupportedTopology_iff e U hU invLM).2 fun K ↦ ?_
  have hK : (K : Set M) ⊆ c.source := hcsource ▸ subset_univ _
  let L : Compacts E := ⟨c '' K, K.isCompact.image_of_continuousOn (c.continuousOn.mono hK)⟩
  have hL : (L : Set E) ⊆ c.target := image_subset_iff.2 fun x hx ↦ c.map_source (hK hx)
  refine ((TestFunction.continuous_ofSupportedIn hL).comp
    (continuous_chartTestCoeff t c hc_symm hct hK Subset.rfl e U hU hcover)).congr fun s ↦ ?_
  ext y
  by_cases hy : y ∈ c.target
  · simp [invLM, hinv_mem _ hy, chartTestCoeff_apply_of_mem _ _ _ _ _ _ _ hy]
  · simp [invLM, hinv_notMem _ hy, chartTestCoeff_apply_of_notMem _ _ _ _ _ _ _ hy]

/-- The forward map of `chartTestSectionEquiv` is `chartTestSection`. -/
@[simp]
theorem chartTestSectionEquiv_apply (φ : 𝓓^{n}(⟨c.target, c.open_target⟩, F)) :
    t.chartTestSectionEquiv c hc hc_symm hct hcsource e U hU hcover φ =
      t.chartTestSection c hc hct φ := (rfl)

/-- On the chart target, the inverse of `chartTestSectionEquiv` evaluates the bundle frame on the
section at the inverse-chart point. -/
theorem chartTestSectionEquiv_symm_apply_of_mem (s : compactlySupported I F n V)
    {y : E} (hy : y ∈ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc hc_symm hct hcsource e U hU hcover).symm s y =
      t.continuousLinearMapAt ℝ (c.symm y) (s.val (c.symm y)) := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  have h := congrArg (fun u : compactlySupported I F n V ↦
    t.continuousLinearMapAt ℝ (c.symm y) (u.val (c.symm y)))
    ((t.chartTestSectionEquiv c hc hc_symm hct hcsource e U hU hcover).apply_symm_apply s)
  simpa only [chartTestSectionEquiv_apply,
    continuousLinearMapAt_chartTestSection t c hc hct _ (c.map_target hy), c.right_inv hy] using h

/-- Outside the chart target, the inverse of `chartTestSectionEquiv` vanishes. -/
@[simp]
theorem chartTestSectionEquiv_symm_apply_of_notMem (s : compactlySupported I F n V)
    {y : E} (hy : y ∉ c.target) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    (t.chartTestSectionEquiv c hc hc_symm hct hcsource e U hU hcover).symm s y = 0 := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  exact ((t.chartTestSectionEquiv c hc hc_symm hct hcsource e U hU hcover).symm s).zero_on_compl hy

end GlobalChart

end Bundle.Trivialization

namespace ContMDiffSection

open scoped Distributions

section ChartTestTopology

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]
  {κ : Type*} (t : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (t j)]
  (c : κ → OpenPartialHomeomorph M E)
  (hc : ∀ j, ContMDiffOn I 𝓘(ℝ, E) n (c j) (c j).source)
  (hct : ∀ j, (c j).source ⊆ (t j).baseSet)

/-- The final locally convex topology on compactly supported bundle sections generated by a family
of chart extensions of native test functions. -/
@[instance_reducible]
def chartTestTopology : TopologicalSpace (compactlySupported I F n V) :=
  TauCeti.finalLocallyConvexTopology fun j ↦ (t j).chartTestSection (c j) (hc j) (hct j)

/-- Every generating chart extension is continuous for the chart-generated test topology. -/
theorem continuous_chartTestSection_chartTestTopology (j : κ) :
    letI := chartTestTopology (I := I) (n := n) t c hc hct
    Continuous ((t j).chartTestSection (c j) (hc j) (hct j)) :=
  TauCeti.FinalLocallyConvexTopology.continuous
    (fun j ↦ (t j).chartTestSection (c j) (hc j) (hct j)) j

/-- The universal property of the chart-generated test topology: a linear map over any
`ℝ`-algebra into a locally convex real topological vector space is continuous if and only if its
composition with every generating chart extension is continuous. -/
theorem continuous_chartTestTopology_iff
    {𝕜 : Type*} [Semiring 𝕜] [Algebra ℝ 𝕜]
    [Module 𝕜 (compactlySupported I F n V)] [IsScalarTower ℝ 𝕜 (compactlySupported I F n V)]
    {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]
    [Module 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    (g : compactlySupported I F n V →ₗ[𝕜] G) :
    letI := chartTestTopology (I := I) (n := n) t c hc hct
    Continuous g ↔ ∀ j, Continuous (g ∘ (t j).chartTestSection (c j) (hc j) (hct j)) :=
  TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp _ g

/-- The chart-generated test topology is always finer than the fixed-compact inductive topology
associated with any frame system. -/
theorem chartTestTopology_le_compactlySupportedTopology [LocallyCompactSpace E] [IsManifold I n M]
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet) :
    chartTestTopology (I := I) (n := n) t c hc hct ≤
      compactlySupportedTopology (I := I) (n := n) e U hU := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  exact (TauCeti.FinalLocallyConvexTopology.le_iff _ _).2 fun j ↦
    Bundle.Trivialization.continuous_chartTestSection (t j) (c j) (hc j) (hct j) e U hU

/-- The chart-generated test topology is Hausdorff on every locally compact model space, without
requiring the charts to cover the base. -/
theorem t2Space_chartTestTopology [LocallyCompactSpace E] [IsManifold I n M] :
    letI := chartTestTopology (I := I) (n := n) t c hc hct
    T2Space (compactlySupported I F n V) := by
  let e₀ : M → Trivialization F (π F V) := fun x ↦ trivializationAt F V x
  let U₀ : M → Opens M := fun x ↦ ⟨(e₀ x).baseSet, (e₀ x).open_baseSet⟩
  have hU₀ : ∀ x, (U₀ x : Set M) ⊆ (e₀ x).baseSet := fun _ ↦ Subset.rfl
  have hcover₀ : ∀ x : M, ∃ i, x ∈ U₀ i :=
    fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x⟩
  exact t2Space_antitone
    (chartTestTopology_le_compactlySupportedTopology t c hc hct e₀ U₀ hU₀)
    (t2Space_compactlySupportedTopology e₀ U₀ hU₀ hcover₀)

/-- **Reverse comparison via finite partitions of unity.** When the model space is
finite-dimensional and the charts have `C^n` inverses and cover the manifold, the fixed-compact
inductive topology is finer than the chart-generated test topology. -/
theorem compactlySupportedTopology_le_chartTestTopology [FiniteDimensional ℝ E] [IsManifold I n M]
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover_e : ∀ x : M, ∃ i, x ∈ U i)
    (hc_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c j).symm (c j).target)
    (hcover_c : ∀ x : M, ∃ j, x ∈ (c j).source) :
    compactlySupportedTopology (I := I) (n := n) e U hU ≤
      chartTestTopology (I := I) (n := n) t c hc hct := by
  let := frameTopology (I := I) (n := n) e U hU
  refine TauCeti.FinalLocallyConvexTopology.le_of_sum_factor
    (ofSupportedIn (I := I) (F := F) (V := V) (n := n))
    (fun j ↦ (t j).chartTestSection (c j) (hc j) (hct j)) fun K ↦ ?_
  obtain ⟨s, ρ, hρ_sub, _, _, _, hρ_sum⟩ :=
    K.isCompact.exists_finset_contMDiff_sum_eq_one I (n := (n : ℕ∞ω)) (by simp)
      (fun j ↦ (c j).open_source) fun x _ ↦ hcover_c x
  let K' : κ → Compacts M := fun j ↦
    ⟨(K : Set M) ∩ _root_.tsupport (ρ j),
      K.isCompact.inter_right (_root_.isClosed_tsupport _)⟩
  have hK' (j : κ) : (K' j : Set M) ⊆ (c j).source := inter_subset_right.trans (hρ_sub j)
  let L : κ → Compacts E := fun j ↦
    ⟨(c j) '' (K' j : Set M),
      (K' j).isCompact.image_of_continuousOn ((c j).continuousOn.mono (hK' j))⟩
  have hL (j : κ) : (L j : Set E) ⊆ (c j).target :=
    image_subset_iff.2 fun x hx ↦ (c j).map_source (hK' j hx)
  let loc : ∀ j, supportedIn I F n V K →ₗ[ℝ] supportedIn I F n V (K' j) := fun j ↦
    { toFun := fun sec ↦
        ⟨ρ j • sec.val, mem_supportedIn.2 <| (tsupport_smul_function_subset (ρ j) sec.val).trans
          fun _ ⟨h1, h2⟩ ↦ ⟨mem_supportedIn.1 sec.property h2, h1⟩⟩
      map_add' := fun sec₁ sec₂ ↦
        Subtype.ext (map_add (smulLinearMap (ρ j)) sec₁.val sec₂.val)
      map_smul' := fun r sec ↦ Subtype.ext (map_smul (smulLinearMap (ρ j)) r sec.val) }
  let a (j : κ) :
      supportedIn I F n V K →ₗ[ℝ] 𝓓^{n}(⟨(c j).target, (c j).open_target⟩, F) :=
    ((TestFunction.ofSupportedInCLM ℝ (hL j)).toLinearMap.comp
      ((t j).chartTestCoeff (c j) (hc_symm j) (hct j) (hK' j) Subset.rfl)).comp (loc j)
  refine ⟨s, a, fun j _ ↦ ?_, ?_⟩
  · have hloc : Continuous (loc j) :=
      ((continuous_smulLinearMap_frameTopology e U hU (ρ j)).comp
        continuous_subtypeVal).subtype_mk _
    exact (TestFunction.continuous_ofSupportedIn (hL j)).comp <|
      ((t j).continuous_chartTestCoeff (c j) (hc_symm j) (hct j) (hK' j) Subset.rfl
        e U hU hcover_e).comp hloc
  · ext sec x
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    have hterm (j : κ) :
        ((t j).chartTestSection (c j) (hc j) (hct j) ∘ₗ a j) sec =
          ofSupportedIn (K' j) (loc j sec) :=
      (t j).chartTestSection_ofSupportedIn_chartTestCoeff (c j) (hc_symm j) (hct j) (hc j)
        (hK' j) Subset.rfl (hL j) (loc j sec)
    simp_rw [hterm]
    have hsum_apply : (∑ j ∈ s, (ofSupportedIn (K' j) (loc j sec) : Cₛ^n⟮I; F, V⟯)) x =
        ∑ j ∈ s, ρ j x • sec.val x := by
      have h := congrFun (map_sum (coeAddHom I F (n : ℕ∞ω) V)
        (fun j ↦ (ofSupportedIn (K' j) (loc j sec) : Cₛ^n⟮I; F, V⟯)) s) x
      simpa only [coeAddHom_apply, Finset.sum_apply, ofSupportedIn_apply, loc,
        LinearMap.coe_mk, AddHom.coe_mk, smul_apply] using h
    rw [hsum_apply, ← Finset.sum_smul, ofSupportedIn_apply]
    by_cases hx : x ∈ (K : Set M)
    · rw [hρ_sum x hx, one_smul]
    · rw [sec.val.eq_zero_of_notMem_tsupport fun h ↦ hx (mem_supportedIn.1 sec.property h),
        smul_zero]

/-- **Equivalence of the chart-generated and fixed-compact test topologies.** On a Hausdorff `C^n`
manifold modeled on a finite-dimensional real space, the final locally convex topology generated
by any covering family of smooth charts with `C^n` inverses subordinate to smooth frames coincides
with the fixed-compact inductive topology of any covering frame system. -/
theorem chartTestTopology_eq_compactlySupportedTopology [FiniteDimensional ℝ E] [IsManifold I n M]
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover_e : ∀ x : M, ∃ i, x ∈ U i)
    (hc_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c j).symm (c j).target)
    (hcover_c : ∀ x : M, ∃ j, x ∈ (c j).source) :
    chartTestTopology (I := I) (n := n) t c hc hct =
      compactlySupportedTopology (I := I) (n := n) e U hU :=
  le_antisymm
    (chartTestTopology_le_compactlySupportedTopology t c hc hct e U hU)
    (compactlySupportedTopology_le_chartTestTopology t c hc hct e U hU hcover_e hc_symm hcover_c)

/-- Any two covering families of smooth charts with `C^n` inverses subordinate to smooth frames
generate the same test topology on compactly supported bundle sections. -/
theorem chartTestTopology_eq_of_covers [FiniteDimensional ℝ E] [IsManifold I n M]
    (hc_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c j).symm (c j).target)
    (hcover_c : ∀ x : M, ∃ j, x ∈ (c j).source)
    {κ' : Type*} (t' : κ' → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (t' j)]
    (c' : κ' → OpenPartialHomeomorph M E)
    (hc' : ∀ j, ContMDiffOn I 𝓘(ℝ, E) n (c' j) (c' j).source)
    (hc'_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c' j).symm (c' j).target)
    (hct' : ∀ j, (c' j).source ⊆ (t' j).baseSet)
    (hcover_c' : ∀ x : M, ∃ j, x ∈ (c' j).source) :
    chartTestTopology (I := I) (n := n) t c hc hct =
      chartTestTopology (I := I) (n := n) t' c' hc' hct' := by
  let U : κ → Opens M := fun j ↦ ⟨(c j).source, (c j).open_source⟩
  have h1 := chartTestTopology_eq_compactlySupportedTopology t c hc hct t U hct hcover_c
    hc_symm hcover_c
  have h2 := chartTestTopology_eq_compactlySupportedTopology t' c' hc' hct' t U hct hcover_c
    hc'_symm hcover_c'
  exact h1.trans h2.symm

/-- **Chart-wise continuity criterion for bundle test sections.** For any covering frame system
and any covering family of smooth charts with `C^n` inverses subordinate to smooth frames, a linear
map from compactly supported sections into a locally convex real topological vector space is
continuous if and only if its composition with every chart extension in the cover is continuous
from Mathlib's `TestFunction`. -/
theorem continuous_compactlySupportedTopology_iff_comp_chartTestSection
    [FiniteDimensional ℝ E] [IsManifold I n M]
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover_e : ∀ x : M, ∃ i, x ∈ U i)
    (hc_symm : ∀ j, ContMDiffOn 𝓘(ℝ, E) I n (c j).symm (c j).target)
    (hcover_c : ∀ x : M, ∃ j, x ∈ (c j).source)
    {𝕜 : Type*} [Semiring 𝕜] [Algebra ℝ 𝕜]
    [Module 𝕜 (compactlySupported I F n V)] [IsScalarTower ℝ 𝕜 (compactlySupported I F n V)]
    {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]
    [Module 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    (g : compactlySupported I F n V →ₗ[𝕜] G) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous g ↔ ∀ j, Continuous (g ∘ (t j).chartTestSection (c j) (hc j) (hct j)) := by
  rw [← chartTestTopology_eq_compactlySupportedTopology t c hc hct e U hU hcover_e
    hc_symm hcover_c]
  exact continuous_chartTestTopology_iff t c hc hct g

end ChartTestTopology

section Boundaryless

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n M] [BoundarylessManifold I M]

/-- **All-charts continuity criterion on a boundaryless manifold.** On a Hausdorff boundaryless
`C^n` manifold modeled on a finite-dimensional real space, a linear map from compactly supported
bundle sections (with the fixed-compact inductive topology of any covering frame system) into a
locally convex real topological vector space is continuous if and only if its precomposition with
every smooth chart extension is continuous on Mathlib's `TestFunction`. -/
theorem continuous_compactlySupportedTopology_iff_forall_chartTestSection
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover_e : ∀ x : M, ∃ i, x ∈ U i)
    {𝕜 : Type*} [Semiring 𝕜] [Algebra ℝ 𝕜]
    [Module 𝕜 (compactlySupported I F n V)] [IsScalarTower ℝ 𝕜 (compactlySupported I F n V)]
    {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]
    [Module 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    (g : compactlySupported I F n V →ₗ[𝕜] G) :
    letI := compactlySupportedTopology (I := I) (n := n) e U hU
    Continuous g ↔
      ∀ (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
        (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) n c c.source)
        (hct : c.source ⊆ t.baseSet),
        Continuous (g ∘ t.chartTestSection c hc hct) := by
  let := compactlySupportedTopology (I := I) (n := n) e U hU
  refine ⟨fun hg t _ c hc hct ↦
    hg.comp (Bundle.Trivialization.continuous_chartTestSection t c hc hct e U hU), fun h ↦ ?_⟩
  let t₀ : M → Trivialization F (π F V) := fun x ↦ trivializationAt F V x
  let c₀ : M → OpenPartialHomeomorph M E := fun x ↦
    ((chartAt H x).trans I.interiorChart).restrOpen (t₀ x).baseSet (t₀ x).open_baseSet
  have hct₀ (x : M) : (c₀ x).source ⊆ (t₀ x).baseSet := inter_subset_right
  have hc₀ (x : M) : ContMDiffOn I 𝓘(ℝ, E) n (c₀ x) (c₀ x).source := by
    have hsub : (c₀ x).source ⊆ (chartAt H x).source := by
      intro y hy
      simp only [c₀, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
        mem_inter_iff] at hy
      exact hy.1.1
    refine ((contMDiffOn_extChartAt (I := I) (x := x)).mono hsub).congr fun y _ ↦ ?_
    simp [c₀, extChartAt]
  have hc₀_symm (x : M) : ContMDiffOn 𝓘(ℝ, E) I n (c₀ x).symm (c₀ x).target := by
    have hsub : (c₀ x).target ⊆ (extChartAt I x).target := by
      intro y hy
      have hy1 : y ∈ ((chartAt H x).trans I.interiorChart).target := hy.1
      simp only [OpenPartialHomeomorph.trans_target, ModelWithCorners.interiorChart_target,
        ModelWithCorners.interiorChart_coe_symm, mem_inter_iff, mem_preimage] at hy1
      simp only [extChartAt_target, mem_inter_iff, mem_preimage]
      exact ⟨hy1.2, interior_subset hy1.1⟩
    refine ((contMDiffOn_extChartAt_symm (I := I) (x := x)).mono hsub).congr fun y _ ↦ ?_
    simp [c₀, extChartAt]
  have hcover₀ (x : M) : ∃ y : M, x ∈ (c₀ y).source := by
    refine ⟨x, ?_⟩
    simp only [c₀, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      ModelWithCorners.interiorChart_source, mem_inter_iff, mem_preimage]
    exact ⟨⟨mem_chart_source H x, BoundarylessManifold.isInteriorPoint (I := I)⟩,
      mem_baseSet_trivializationAt F V x⟩
  exact (continuous_compactlySupportedTopology_iff_comp_chartTestSection
    t₀ c₀ hc₀ hct₀ e U hU hcover_e hc₀_symm hcover₀ g).2 fun x ↦
    h (t₀ x) (c₀ x) (hc₀ x) (hct₀ x)

end Boundaryless

end ContMDiffSection
