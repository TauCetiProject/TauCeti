/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Smooth proper exhaustion functions

A finite-dimensional, sigma-compact Hausdorff smooth manifold admits a nonnegative smooth
proper real-valued function. Thus its closed sublevels are compact, and its strict sublevels
exhaust the manifold. No compactness or boundaryless-model hypothesis is needed.

The construction can be controlled by any specified `CompactExhaustion K`: the function
dominates the first index at which a point enters `K`. Consequently its sublevel at height
`n : ℕ` is contained in `K n`. This control is useful when choosing perturbations on successive
compact sets.

The construction uses Mathlib's
`exists_contMDiffMap_forall_mem_convex_of_local_const`, which glues locally constant upper
bounds by a smooth partition of unity. It is the usual compact-exhaustion construction of a
smooth exhaustion function; see J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 2, on smooth partitions of unity and smooth exhaustion functions.
-/

public section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M]

/-- A prescribed compact exhaustion admits a smooth proper real-valued function dominating
its first-entry index. In particular, the function is nonnegative, and its sublevel at any
natural height `n` lies in `K n`. -/
theorem _root_.CompactExhaustion.exists_contMDiffMap_isProperMap (K : CompactExhaustion M)
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsProperMap f ∧ ∀ x, (K.find x : ℝ) ≤ f x := by
  have : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  -- The first-entry index is locally bounded above: a compact stage is a neighbourhood
  -- of each point in the interior of that stage.
  obtain ⟨f, hf⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const I
    (n := (⊤ : ℕ∞)) (t := fun x ↦ Ici (K.find x : ℝ)) (fun _ ↦ convex_Ici _) (fun x ↦ by
      obtain ⟨n, hn⟩ := K.exists_mem_nhds x
      refine ⟨(n : ℝ), ?_⟩
      filter_upwards [hn] with y hy
      exact mem_Ici.mpr (Nat.cast_le.mpr (K.mem_iff_find_le.mp hy)))
  refine ⟨f, isProperMap_iff_isCompact_preimage.mpr ⟨f.contMDiff.continuous, fun A hA ↦ ?_⟩, hf⟩
  -- A compact set of values is bounded above, so its inverse image is a closed subset
  -- of one compact stage. No lower bound on that set of values is required.
  obtain ⟨b, hb⟩ := hA.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_ge b
  refine (K.isCompact n).of_isClosed_subset (hA.isClosed.preimage f.contMDiff.continuous) ?_
  intro x hx
  exact K.mem_iff_find_le.mpr (by exact_mod_cast (hf x).trans ((hb hx).trans hn))

/-- A finite-dimensional sigma-compact Hausdorff smooth manifold has a nonnegative smooth
proper exhaustion function. This also applies to the empty manifold and to manifolds with
boundary or corners. -/
theorem exists_contMDiffMap_isProperMap_nonneg (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [SigmaCompactSpace M] :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsProperMap f ∧ ∀ x, 0 ≤ f x := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨f, hp, hf⟩ := (CompactExhaustion.choice M).exists_contMDiffMap_isProperMap I
  exact ⟨f, hp, fun x ↦ (Nat.cast_nonneg _).trans (hf x)⟩

end TauCeti
