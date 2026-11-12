/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
public import TauCeti.Topology.MappingSpace.FreeLoop
public import TauCeti.Topology.MappingSpace.NeighborhoodRetract

/-!
# Mapping spaces into manifolds are locally path-connected and semilocally simply connected

Let `M` be a Hausdorff boundaryless smooth manifold modelled on a finite-dimensional real normed
space, and let `K` be a compact space. The mapping space `C(K, M)`, with the compact-open
topology, is locally path-connected (`ContinuousMap.locallyPathConnectedSpace_of_isManifold`) and
semilocally simply connected (`ContinuousMap.semilocallySimplyConnectedSpace_of_isManifold`). No
compactness, second countability or paracompactness is assumed of `M`.

The image of a map `f : K → M` is compact, so it has an open neighbourhood `W` which, as an open
submanifold, smoothly embeds in a Euclidean space
(`IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`), and a tubular neighbourhood of the
image of this embedding retracts onto it (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`).
So `W` is a neighbourhood retract of a Euclidean space, and `C(K, W)` has both properties by
`TauCeti.Topology.MappingSpace.NeighborhoodRetract`. Since `K` is compact, `C(K, W)` is an open
neighbourhood of `f` in `C(K, M)` (`ContinuousMap.isOpenEmbedding_postcomp`), and both properties
are local.

For `K` the circle this applies to the free loop space `𝓛M = C(S¹, M)`. Its subspace `𝓛₀M` of
contractible loops is a union of path components, hence open, and it inherits both properties
(`TauCeti.locallyPathConnectedSpace_contractibleLoops`,
`TauCeti.semilocallySimplyConnectedSpace_contractibleLoops`). These are the hypotheses under which
the connected covering spaces of `𝓛₀M`, such as the covering by capped loops of Hamiltonian Floer
theory, are classified by subgroups of its fundamental group.

## Main results

* `ContinuousMap.locallyPathConnectedSpace_of_isManifold`: `C(K, M)` is locally path-connected.
* `ContinuousMap.semilocallySimplyConnectedSpace_of_isManifold`: `C(K, M)` is semilocally simply
  connected.
* `TauCeti.locallyPathConnectedSpace_contractibleLoops`,
  `TauCeti.semilocallySimplyConnectedSpace_contractibleLoops`: the same for the contractible free
  loops `𝓛₀M`.

## References

* R. S. Palais, *Homotopy theory of infinite dimensional manifolds*, Topology 5 (1966), 1–16.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progr. Math. 133 (1995), 483–524, for the covering of `𝓛₀M` by capped loops.
-/

public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

variable {K M E H : Type*} [TopologicalSpace K] [CompactSpace K] [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ContinuousMap

include I in
/-- A map from a nonempty compact space into a manifold takes values in an open subset `W` such
that `C(K, W)` is locally path-connected and semilocally simply connected: `W` is a neighbourhood
retract of a Euclidean space. -/
private theorem exists_opens_locallyPathConnectedSpace [Nonempty K] (f : C(K, M)) :
    ∃ W : Opens M, (∀ k, f k ∈ W) ∧ LocallyPathConnectedSpace C(K, W) ∧
      TauCeti.SemilocallySimplyConnectedSpace C(K, W) := by
  obtain ⟨W, hfW, -, n, ⟨e⟩⟩ :=
    (isCompact_range f.continuous).exists_opens_nonempty_smoothEmbedding_euclidean (I := I)
  have hf (k : K) : f k ∈ W := hfW (mem_range_self k)
  have : Nonempty W := ⟨⟨f (Classical.arbitrary K), hf _⟩⟩
  obtain ⟨O, hO, heO, -, r, hr, hre⟩ := e.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  have hiO (x : W) : e x ∈ O := heO (mem_range_self x)
  exact ⟨W, hf,
    locallyPathConnectedSpace_of_leftInverse K (map_continuous e) hO hiO hr.continuousOn hre,
    semilocallySimplyConnectedSpace_of_leftInverse K (map_continuous e) hO hiO hr.continuousOn hre⟩

omit [T2Space M] [CompactSpace K] in
/-- A map with values in an open subset `W` lies in the image of `C(K, W)`. -/
private theorem mem_range_postcomp_opens {W : Opens M} {f : C(K, M)} (hf : ∀ k, f k ∈ W) :
    f ∈ range (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ :
      C(K, W) → C(K, M)) :=
  ⟨⟨fun k ↦ ⟨f k, hf k⟩, f.continuous.subtype_mk hf⟩, ext fun _ ↦ rfl⟩

include I in
variable (K M) in
/-- **Mapping spaces into a manifold are locally path-connected.** For a compact space `K` and a
Hausdorff boundaryless smooth manifold `M` modelled on a finite-dimensional real normed space,
the mapping space `C(K, M)` with the compact-open topology is locally path-connected. -/
theorem locallyPathConnectedSpace_of_isManifold : LocallyPathConnectedSpace C(K, M) := by
  rcases isEmpty_or_nonempty K with hK | hK
  · have : Subsingleton C(K, M) := ⟨fun f g ↦ ext fun k ↦ isEmptyElim k⟩
    infer_instance
  refine .of_forall_exists_mem_nhds fun f ↦ ?_
  obtain ⟨W, hf, hW, -⟩ := exists_opens_locallyPathConnectedSpace I f
  have he := isOpenEmbedding_postcomp (X := K) ⟨_, continuous_subtype_val⟩
    W.isOpen.isOpenEmbedding_subtypeVal
  exact ⟨_, he.isOpen_range.mem_nhds (mem_range_postcomp_opens hf),
    he.isEmbedding.toHomeomorph.locallyPathConnectedSpace⟩

include I in
variable (K M) in
/-- **Mapping spaces into a manifold are semilocally simply connected.** For a compact space `K`
and a Hausdorff boundaryless smooth manifold `M` modelled on a finite-dimensional real normed
space, the mapping space `C(K, M)` with the compact-open topology is semilocally simply
connected. -/
theorem semilocallySimplyConnectedSpace_of_isManifold :
    TauCeti.SemilocallySimplyConnectedSpace C(K, M) := by
  rcases isEmpty_or_nonempty K with hK | hK
  · have : Subsingleton C(K, M) := ⟨fun f g ↦ ext fun k ↦ isEmptyElim k⟩
    infer_instance
  refine .of_forall_exists_mem_nhds fun f ↦ ?_
  obtain ⟨W, hf, -, hW⟩ := exists_opens_locallyPathConnectedSpace I f
  have he := isOpenEmbedding_postcomp (X := K) ⟨_, continuous_subtype_val⟩
    W.isOpen.isOpenEmbedding_subtypeVal
  let h := he.isEmbedding.toHomeomorph
  exact ⟨_, he.isOpen_range.mem_nhds (mem_range_postcomp_opens hf),
    (LeftInverse.semilocallySimplyConnectedSpace h.apply_symm_apply h.continuous
      h.symm.continuous)⟩

end ContinuousMap

namespace TauCeti

omit [T2Space M] in
/-- The contractible free loops contain the path component of each of their points. -/
private theorem pathComponent_subset_contractibleLoops {γ : C(Circle, M)}
    (hγ : γ ∈ contractibleLoops M) : pathComponent γ ⊆ contractibleLoops M := by
  obtain ⟨q, hq⟩ := mem_contractibleLoops_iff.1 hγ
  exact fun δ hδ ↦ mem_contractibleLoops_iff.2 ⟨q, (mem_pathComponent_iff.1 hδ).symm.trans hq⟩

include I in
variable (M) in
/-- **The contractible free loops of a manifold are locally path-connected.** The free loop space
`C(S¹, M)` is locally path-connected, so its path components are open, and the contractible free
loops `𝓛₀M` form a union of them. -/
theorem locallyPathConnectedSpace_contractibleLoops :
    LocallyPathConnectedSpace (contractibleLoops M) := by
  have := ContinuousMap.locallyPathConnectedSpace_of_isManifold Circle M I
  refine IsOpen.locallyPathConnectedSpace (isOpen_iff_mem_nhds.2 fun γ hγ ↦ ?_)
  exact Filter.mem_of_superset ((IsOpen.pathComponent γ).mem_nhds (mem_pathComponent_self γ))
    (pathComponent_subset_contractibleLoops hγ)

include I in
variable (M) in
/-- **The contractible free loops of a manifold are semilocally simply connected.** The free loop
space `C(S¹, M)` is semilocally simply connected, and a null-homotopy of a loop of contractible
free loops stays in `𝓛₀M`, a union of path components. -/
theorem semilocallySimplyConnectedSpace_contractibleLoops :
    SemilocallySimplyConnectedSpace (contractibleLoops M) :=
  have := ContinuousMap.semilocallySimplyConnectedSpace_of_isManifold Circle M I
  .subtype_of_pathComponent_subset fun _ ↦ pathComponent_subset_contractibleLoops

end TauCeti
