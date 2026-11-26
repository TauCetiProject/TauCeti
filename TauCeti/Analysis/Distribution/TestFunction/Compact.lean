/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Compactness.SigmaCompact
import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Compact sets of test functions

Mathlib's test functions `𝓓^{n}(Ω, F)` carry the LF topology, the finest locally convex topology
making the inclusions of the spaces `𝓓^{n}_{K}(E, F)` of the functions supported in a compact
`K ⊆ Ω` continuous. This file proves that a compact set of test functions lives in one of these
spaces: there is a compact `K ⊆ Ω` containing the support of each of its elements
(`TestFunction.exists_compacts_forall_tsupport_subset`). This is the part of the regularity of
the strict inductive limit `𝓓(Ω) = lim 𝓓_K` needed to estimate a distribution, or a family of
distributions, uniformly over a compact set of test functions by estimates on a single space
`𝓓_K`.

## The argument

Suppose the supports of the elements of `S` escape every compact subset of `Ω`. Along a compact
exhaustion `K₀ ⊆ K₁ ⊆ ⋯` of `Ω`, choose `φⱼ ∈ S` and points `xⱼ ∉ Kⱼ` with `φⱼ xⱼ ≠ 0`. Every
compact subset of `Ω` contains only finitely many of the points `xⱼ`, so the linear map

`φ ↦ ((j + 1) ‖φⱼ xⱼ‖⁻¹ φ xⱼ)ⱼ`

takes values in the bounded sequences `ℓ^∞(ℕ, F)`, and on each space `𝓓_K` it is bounded by a
multiple of the sup norm. By the universal property of the LF topology it is continuous on
`𝓓(Ω)`, so it is bounded on the compact set `S`; but its value at `φⱼ` has norm at least
`j + 1`.

## Main declarations

* `TestFunction.exists_compacts_forall_tsupport_subset`: the elements of a compact set of test
  functions on `Ω` are supported in one compact subset of `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.1 (convergence of test functions).
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Chapter 13 (strict inductive
  limits).
-/

public section

noncomputable section

open Filter Set TopologicalSpace
open scoped Distributions ENNReal

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

/-- The weighted evaluations `φ ↦ (c j • φ (x j))ⱼ` at points `x j ∉ K j`, for an increasing
sequence `K j` that eventually contains every compact subset of `Ω`, as a linear map into the
bounded sequences: only finitely many of the points lie in the support of a given test
function. -/
private def evalSeq {K : ℕ → Set E} (hK : ∀ C : Set E, IsCompact C → C ⊆ Ω → ∃ j, C ⊆ K j)
    (hmono : Monotone K) {x : ℕ → E} (hx : ∀ j, x j ∉ K j) (c : ℕ → ℝ) :
    𝓓^{n}(Ω, F) →ₗ[ℝ] lp (fun _ : ℕ ↦ F) ∞ where
  toFun φ := ⟨fun j ↦ c j • φ (x j), by
    obtain ⟨J, hJ⟩ := hK _ φ.hasCompactSupport.isCompact φ.tsupport_subset
    refine memℓp_infty ⟨∑ i ∈ Finset.range J, ‖c i • φ (x i)‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    by_cases hj : j < J
    · exact Finset.single_le_sum (f := fun i ↦ ‖c i • φ (x i)‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_range.2 hj)
    · -- Past `J`, the point `x j` lies outside the support of `φ`.
      have h0 : φ (x j) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
        hx j (hmono (not_lt.1 hj) (hJ h))
      simp only [h0, smul_zero, norm_zero]
      positivity⟩
  map_add' φ ψ := by ext j; simp only [lp.coeFn_add, Pi.add_apply, FunLike.coe_add, smul_add]
  map_smul' a φ := by
    ext j
    simp only [lp.coeFn_smul, Pi.smul_apply, FunLike.coe_smul, RingHom.id_apply, smul_comm a]

private theorem evalSeq_apply {K : ℕ → Set E}
    (hK : ∀ C : Set E, IsCompact C → C ⊆ Ω → ∃ j, C ⊆ K j) (hmono : Monotone K) {x : ℕ → E}
    (hx : ∀ j, x j ∉ K j) (c : ℕ → ℝ) (φ : 𝓓^{n}(Ω, F)) (j : ℕ) :
    (evalSeq (F := F) (n := n) hK hmono hx c φ : ℕ → F) j = c j • φ (x j) :=
  rfl

/-- `evalSeq` is continuous: on the test functions supported in a compact `C ⊆ Ω`, only the
finitely many points `x j` with `j` below the index of a set `K j ⊇ C` contribute. -/
private theorem continuous_evalSeq {K : ℕ → Set E}
    (hK : ∀ C : Set E, IsCompact C → C ⊆ Ω → ∃ j, C ⊆ K j) (hmono : Monotone K) {x : ℕ → E}
    (hx : ∀ j, x j ∉ K j) (c : ℕ → ℝ) :
    Continuous (evalSeq (F := F) (n := n) hK hmono hx c) := by
  refine (TestFunction.continuous_iff_continuous_comp (𝕜 := ℝ) _).2 fun C hCΩ ↦ ?_
  obtain ⟨J, hJ⟩ := hK C C.isCompact hCΩ
  set M : ℝ := ∑ i ∈ Finset.range J, |c i|
  have hbound (f : 𝓓^{n}_{C}(E, F)) : ‖evalSeq hK hmono hx c (ofSupportedIn hCΩ f)‖ ≤
      M * (({0} : Finset ℕ).sup (ContDiffMapSupportedIn.seminorm ℝ E F n C)) f := by
    rw [Finset.sup_singleton]
    refine lp.norm_le_of_forall_le (by positivity) fun j ↦ ?_
    rw [evalSeq_apply, norm_smul, Real.norm_eq_abs]
    by_cases hj : j < J
    · rw [coe_ofSupportedIn]
      refine mul_le_mul ?_ (ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ) (norm_nonneg _)
        (by positivity)
      exact Finset.single_le_sum (f := fun i ↦ |c i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.2 hj)
    · have h0 : f (x j) = 0 := f.zero_on_compl fun h ↦ hx j (hmono (not_lt.1 hj) (hJ h))
      rw [coe_ofSupportedIn, h0, norm_zero, mul_zero]
      positivity
  exact (ContDiffMapSupportedIn.withSeminorms ℝ E F n C).continuous_normedSpace_rng _
    ((evalSeq hK hmono hx c).comp (ofSupportedInCLM ℝ hCΩ).toLinearMap)
    ⟨{0}, ⟨M, by positivity⟩, hbound⟩

/-- **Compact sets of test functions have a common compact support.** If `S` is a compact set of
test functions on `Ω`, there is a compact set `K ⊆ Ω` containing the support of every element of
`S`. -/
theorem exists_compacts_forall_tsupport_subset {S : Set 𝓓^{n}(Ω, F)} (hS : IsCompact S) :
    ∃ K : Compacts E, (K : Set E) ⊆ Ω ∧ ∀ φ ∈ S, tsupport φ ⊆ K := by
  -- On an infinite-dimensional space every test function vanishes.
  by_cases hE : ¬FiniteDimensional ℝ E
  · refine ⟨⊥, by simp, fun φ _ ↦ ?_⟩
    rw [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
    simp
  push Not at hE
  have : LocallyCompactSpace Ω := Ω.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  -- A compact exhaustion `Kⱼ` of `Ω`, read in `E`.
  let X := CompactExhaustion.choice Ω
  set K : ℕ → Set E := fun j ↦ (↑) '' X j
  have hKc (j : ℕ) : IsCompact (K j) := (X.isCompact j).image continuous_subtypeVal
  have hKΩ (j : ℕ) : K j ⊆ Ω := image_subset_iff.2 fun y _ ↦ y.property
  have hmono : Monotone K := fun _ _ h ↦ image_mono (X.subset h)
  have hK (C : Set E) (hC : IsCompact C) (hCΩ : C ⊆ Ω) : ∃ j, C ⊆ K j := by
    obtain ⟨j, hj⟩ := X.exists_superset_of_isCompact (s := (↑) ⁻¹' C)
      (Subtype.isCompact_iff.2 (by
        rwa [image_preimage_eq_of_subset (by rwa [Subtype.range_coe_subtype])]))
    exact ⟨j, fun y hy ↦ ⟨⟨y, hCΩ hy⟩, hj hy, rfl⟩⟩
  by_contra hne
  push Not at hne
  -- For each `j`, an element `φⱼ ∈ S` not vanishing at a point `xⱼ ∉ Kⱼ`.
  have hex (j : ℕ) : ∃ φ ∈ S, ∃ y, y ∉ K j ∧ φ y ≠ 0 := by
    obtain ⟨φ, hφS, hφ⟩ := hne ⟨K j, hKc j⟩ (hKΩ j)
    refine ⟨φ, hφS, ?_⟩
    by_contra h
    push Not at h
    exact hφ (closure_minimal (fun y hy ↦ not_not.1 fun hyK ↦ hy (h y hyK)) (hKc j).isClosed)
  choose φ hφS x hxK hφx using hex
  set c : ℕ → ℝ := fun j ↦ (j + 1) * ‖φ j (x j)‖⁻¹
  set Λ := evalSeq (F := F) (n := n) hK hmono hxK c
  -- `Λ` is bounded on the compact set `S`, but `‖Λ φⱼ‖ ≥ j + 1`.
  obtain ⟨B, hB⟩ := (hS.image (continuous_evalSeq hK hmono hxK c)).isBounded.exists_norm_le
  obtain ⟨j, hj⟩ := exists_nat_gt B
  have hle := (lp.norm_apply_le_norm ENNReal.top_ne_zero (Λ (φ j)) j).trans
    (hB _ ⟨φ j, hφS j, rfl⟩)
  rw [evalSeq_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (hφx j)), mul_one] at hle
  linarith

end TestFunction
