/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Analysis.LocallyConvex.FinalTopology

/-!
# The fixed-compact inductive topology on bundle tests

Compactly supported native bundle sections carry the final locally convex topology of their
fixed-compact support stages. Each stage has the subspace topology of the compact derivative
section topology. Linear maps from this space into locally convex real topological vector
spaces are continuous exactly when they are continuous on every stage. This is the fixed-support
presentation of the topology used for bundle-valued tests; its comparison with native
test-function chart extensions is not asserted here.

The topology is Hausdorff for a covering frame system, is independent of that frame cover,
and on a compact base agrees with the compact derivative topology on all sections. In
particular, taking the final topology does not discard the section values. Convergence in a
single fixed-support stage implies convergence in the test topology.

We reuse `TauCeti.finalLocallyConvexTopology`, rather than the final topology of topological
spaces. No completeness or strict inductive-limit assertion is made.
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
        using (continuous_subtype_val :
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
    ⟨r, continuous_subtype_val.subtype_mk _⟩
  exact TauCeti.FinalLocallyConvexTopology.eq_of_rightInverse
    (ofSupportedIn (I := I) (F := F) (V := V) (n := n))
    (fun K => continuous_induced_rng.2 (by
      simpa only [val_comp_ofSupportedIn]
        using (continuous_subtype_val :
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
