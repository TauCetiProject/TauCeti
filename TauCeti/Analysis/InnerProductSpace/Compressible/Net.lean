/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compressible
public import Mathlib.Topology.MetricSpace.Cover
import TauCeti.Analysis.InnerProductSpace.CoveringNumber
import Mathlib.Data.Finset.Powerset

/-!
# Sparse sphere nets for compressible vectors

A net of the sphere in each coordinate subspace of dimension `k` gives a single net for
compressible vectors, with only a binomial factor for the choice of support. Since the sparse
approximants in `IsCompressibleVector` may have arbitrary norm, normalization costs up to
a second copy of the approximation radius.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 3.3.
-/

public section

noncomputable section

open Finset Metric Set
open scoped NNReal

namespace TauCeti

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

/-- The unit vectors supported on at most `k` coordinates have a net consisting of such
vectors. The cardinality bound counts supports of size exactly `k`, since any smaller
support can be extended to that size. -/
theorem exists_finset_isCover_isCompressibleVector_zero
    {k : ℕ} (hk : k ≤ Fintype.card ι) {η : ℝ≥0} (hη : η ≠ 0) :
    ∃ N : Finset (EuclideanSpace 𝕜 ι),
      (↑N : Set (EuclideanSpace 𝕜 ι)) ⊆ {x : EuclideanSpace 𝕜 ι | IsCompressibleVector k 0 x} ∧
      IsCover η {x : EuclideanSpace 𝕜 ι | IsCompressibleVector k 0 x} N ∧
      (N.card : ℝ) ≤ (Fintype.card ι).choose k *
        (1 + 2 / (η : ℝ)) ^ (Module.finrank ℝ 𝕜 * k) := by
  classical
  choose N hNs hN hcard using
    fun s : Finset ι ↦ exists_finset_isCover_coordinateSphere (𝕜 := 𝕜) s hη
  let supports := (univ : Finset ι).powersetCard k
  refine ⟨supports.biUnion N, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_biUnion.mp hx
    obtain ⟨hn, hzero⟩ := hNs s hxs
    exact isCompressibleVector_zero_right_iff.mpr
      ⟨hn, s, (mem_powersetCard.mp hs).2.le, hzero⟩
  · intro x hx
    obtain ⟨hn, s, hs, hx⟩ := isCompressibleVector_zero_right_iff.mp hx
    obtain ⟨t, hst, htu, ht⟩ := exists_subsuperset_card_eq (subset_univ s) hs (by simpa using hk)
    obtain ⟨y, hy, hxy⟩ := hN t ⟨hn, fun i hi ↦ hx i (fun his ↦ hi (hst his))⟩
    exact ⟨y, mem_biUnion.mpr ⟨t, mem_powersetCard.mpr ⟨htu, ht⟩, hy⟩, hxy⟩
  · calc
      _ ≤ ∑ s ∈ supports, ((N s).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := supports) (t := N))
      _ ≤ ∑ _s ∈ supports, (1 + 2 / (η : ℝ)) ^ (Module.finrank ℝ 𝕜 * k) :=
        sum_le_sum fun s hs ↦ by simpa [(mem_powersetCard.mp hs).2] using hcard s
      _ = _ := by simp [supports]

/-- A radius-`ρ` compressible unit vector is within `2ρ + η` of a point in a sparse
unit-sphere net. The bound includes zero sparsity, when the set to cover is empty. -/
theorem exists_finset_isCover_isCompressibleVector
    {k : ℕ} (hk : k ≤ Fintype.card ι) {ρ η : ℝ≥0} (hρ : ρ < 1) (hη : η ≠ 0) :
    ∃ N : Finset (EuclideanSpace 𝕜 ι),
      (↑N : Set (EuclideanSpace 𝕜 ι)) ⊆ {x : EuclideanSpace 𝕜 ι | IsCompressibleVector k 0 x} ∧
      IsCover (2 * ρ + η) {x : EuclideanSpace 𝕜 ι | IsCompressibleVector k ρ x} N ∧
      (N.card : ℝ) ≤ (Fintype.card ι).choose k *
        (1 + 2 / (η : ℝ)) ^ (Module.finrank ℝ 𝕜 * k) := by
  obtain ⟨N, hNs, hN, hcard⟩ := exists_finset_isCover_isCompressibleVector_zero (𝕜 := 𝕜) hk hη
  refine ⟨N, hNs, ?_, hcard⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hx.exists_isCompressibleVector_zero_dist_le (by exact_mod_cast hρ)
  obtain ⟨z, hz, hyz⟩ := hN hy
  have hyz' : dist y z ≤ (η : ℝ) := edist_le_coe.mp hyz
  have hxz : dist x z ≤ ((2 * ρ + η : ℝ≥0) : ℝ) := by
    push_cast
    linarith [dist_triangle x y z]
  exact ⟨z, hz, edist_le_coe.mpr hxz⟩

end TauCeti
