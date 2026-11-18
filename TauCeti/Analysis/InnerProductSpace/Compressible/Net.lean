/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compressible
public import Mathlib.Topology.MetricSpace.Cover
import TauCeti.Analysis.InnerProductSpace.BasisSpan
import TauCeti.Analysis.Normed.Module.CoveringNumber
import Mathlib.Analysis.Normed.Module.Normalize
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

/-- A compressible vector at radius less than one is within twice that radius of a sparse
unit vector with the same sparsity budget. -/
theorem IsCompressibleVector.exists_isCompressibleVector_zero_dist_le
    {k : ℕ} {ρ : ℝ} {x : EuclideanSpace 𝕜 ι}
    (hx : IsCompressibleVector k ρ x) (hρ : ρ < 1) :
    ∃ y : EuclideanSpace 𝕜 ι, IsCompressibleVector k 0 y ∧ dist x y ≤ 2 * ρ := by
  obtain ⟨hn, s, hs, y, hy, hxy⟩ := isCompressibleVector_iff.mp hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [hn] at hxy
    linarith
  let u := NormedSpace.normalize y
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hy0
  have hyu : dist y u = |‖y‖ - 1| := by
    rw [dist_eq_norm]
    calc
      ‖y - u‖ = ‖(‖y‖ - 1) • u‖ := by
        rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
  refine ⟨u, isCompressibleVector_zero_right_iff.mpr
    ⟨hu, s, hs, fun i hi ↦ by simp [u, NormedSpace.normalize, hy i hi]⟩, ?_⟩
  have hnorm : |‖y‖ - 1| ≤ dist x y := by
    simpa only [hn, dist_eq_norm, Real.norm_eq_abs, norm_sub_rev y x] using
      (dist_norm_norm_le y x)
  rw [← dist_eq_norm] at hxy
  linarith [dist_triangle x y u]

private theorem exists_finset_isCover_coordinateSphere (s : Finset ι) {η : ℝ≥0} (hη : η ≠ 0) :
    ∃ N : Finset (EuclideanSpace 𝕜 ι),
      (↑N : Set (EuclideanSpace 𝕜 ι)) ⊆ {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ s, x i = 0} ∧
      IsCover η {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ s, x i = 0} N ∧
      (N.card : ℝ) ≤ (1 + 2 / (η : ℝ)) ^ (Module.finrank ℝ 𝕜 * s.card) := by
  classical
  let V := (EuclideanSpace.basisFun ι 𝕜).spanIndices (s : Set ι)
  have hV (x : EuclideanSpace 𝕜 ι) : x ∈ V ↔ ∀ i ∉ s, x i = 0 := by
    simp only [V, OrthonormalBasis.mem_spanIndices_iff, EuclideanSpace.basisFun_repr,
      Finset.mem_coe]
  have : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ 𝕜 V
  obtain ⟨N, hNs, hN, hcard⟩ := exists_finset_isCover_sphere (E := V) hη
  let f : V → EuclideanSpace 𝕜 ι := Subtype.val
  have hf : Isometry f := isometry_subtype_coe
  have himage : f '' sphere (0 : V) 1 = {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ s, x i = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_sphere_zero_iff_norm.mp hy, (hV _).mp y.property⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨x, (hV x).mpr hs⟩, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
  have hdim : Module.finrank ℝ V = Module.finrank ℝ 𝕜 * s.card := by
    rw [← Module.finrank_mul_finrank ℝ 𝕜 V, OrthonormalBasis.finrank_spanIndices]
  refine ⟨N.image f, ?_, ?_, ?_⟩
  · rw [Finset.coe_image, ← himage]
    exact Set.image_mono hNs
  · rw [Finset.coe_image, ← himage]
    exact (hf.isCover_image_iff _).mpr hN
  · rw [hdim] at hcard
    exact (Nat.cast_le.mpr Finset.card_image_le).trans hcard

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
    obtain ⟨y, hy, hxy⟩ := hN t (show x ∈ {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ t, x i = 0} from
      ⟨hn, fun i hi ↦ hx i (fun his ↦ hi (hst his))⟩)
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
