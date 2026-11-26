/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Compact sets of test functions

A compact set `Q` of test functions on an open set `Ω` of a real normed space has its supports in
one compact subset of `Ω`
(`TestFunction.exists_compacts_forall_tsupport_subset_of_isCompact`): the space of test functions
is a *regular* inductive limit of the spaces `𝓓_K` of smooth functions supported in compact sets
`K ⊆ Ω`, as far as compact sets are concerned.

This is what makes the topology of `𝓓'(Ω)`, the uniform convergence on compact sets of test
functions, accessible to estimates in a fixed compact set: to control a distribution uniformly on
`Q`, it is enough to control it on test functions supported in one compact set.

## Implementation notes

If the supports are in no compact subset of `Ω`, choose a compact exhaustion `K₀ ⊆ K₁ ⊆ ⋯` of `Ω`,
and for each `k` a test function `fₖ ∈ Q` and a point `xₖ ∉ Kₖ` with `fₖ xₖ ≠ 0`. A test function
`g` is supported in some `Kₙ`, so `g xₖ = 0` for `k ≥ n`, and the map
`g ↦ (k ↦ (k / ‖fₖ xₖ‖) • g xₖ)` takes values in the bounded sequences. On each `𝓓_K` only finitely
many of its coordinates are nonzero, so it is continuous by the universal property of the topology
of test functions. It is unbounded on `Q`, since the `k`-th coordinate of its value at `fₖ` has
norm `k`, which contradicts the compactness of `Q`.

## References

* L. Schwartz, *Théorie des distributions*, Hermann, 1966, Chapter III, §1, Théorème I.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967,
  Chapter 14 (strict inductive limits) and Proposition 14.6.
-/

public section

open Filter Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- The sequence `k ↦ c k • g (x k)` for a test function `g` and points `x k` that eventually
leave every compact set over which `g` is supported, as a bounded sequence. -/
private noncomputable def evalSeq {x : ℕ → E} (c : ℕ → ℝ)
    (hx : ∀ K : Compacts E, (K : Set E) ⊆ Ω → ∃ N, ∀ k ≥ N, x k ∉ K) (g : 𝓓^{n}(Ω, F)) :
    ℕ →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun k ↦ c k • g (x k))
    (∑ k ∈ Finset.range (hx ⟨tsupport g, g.hasCompactSupport⟩ g.tsupport_subset).choose,
      ‖c k • g (x k)‖) fun k ↦ by
    set N := (hx ⟨tsupport g, g.hasCompactSupport⟩ g.tsupport_subset).choose
    by_cases hk : k < N
    · exact Finset.single_le_sum (f := fun k ↦ ‖c k • g (x k)‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_range.2 hk)
    · have hxk := (hx ⟨tsupport g, g.hasCompactSupport⟩ g.tsupport_subset).choose_spec k
        (not_lt.1 hk)
      rw [image_eq_zero_of_notMem_tsupport hxk, smul_zero, norm_zero]
      exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

private theorem evalSeq_apply {x : ℕ → E} (c : ℕ → ℝ)
    (hx : ∀ K : Compacts E, (K : Set E) ⊆ Ω → ∃ N, ∀ k ≥ N, x k ∉ K) (g : 𝓓^{n}(Ω, F)) (k : ℕ) :
    evalSeq c hx g k = c k • g (x k) :=
  rfl

/-- `TestFunction.evalSeq` as a linear map. -/
private noncomputable def evalSeqLM {x : ℕ → E} (c : ℕ → ℝ)
    (hx : ∀ K : Compacts E, (K : Set E) ⊆ Ω → ∃ N, ∀ k ≥ N, x k ∉ K) :
    𝓓^{n}(Ω, F) →ₗ[ℝ] ℕ →ᵇ F where
  toFun := evalSeq c hx
  map_add' g h := by ext k; simp [evalSeq_apply, smul_add]
  map_smul' a g := by ext k; simp [evalSeq_apply, smul_comm (c k) a]

@[simp]
private theorem evalSeqLM_apply {x : ℕ → E} (c : ℕ → ℝ)
    (hx : ∀ K : Compacts E, (K : Set E) ⊆ Ω → ∃ N, ∀ k ≥ N, x k ∉ K) (g : 𝓓^{n}(Ω, F)) (k : ℕ) :
    evalSeqLM c hx g k = c k • g (x k) :=
  rfl

/-- `TestFunction.evalSeq` is continuous: on test functions supported in a compact set `K`, only
the finitely many coordinates `k` with `x k ∈ K` can be nonzero, and each is a multiple of an
evaluation. -/
private theorem continuous_evalSeqLM {x : ℕ → E} (c : ℕ → ℝ)
    (hx : ∀ K : Compacts E, (K : Set E) ⊆ Ω → ∃ N, ∀ k ≥ N, x k ∉ K) :
    Continuous (evalSeqLM (n := n) (F := F) c hx) := by
  refine (TestFunction.continuous_iff_continuous_comp (𝕜 := ℝ) _).2 fun K hK ↦ ?_
  obtain ⟨N, hN⟩ := hx K hK
  set C : ℝ := ∑ k ∈ Finset.range N, ‖c k‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  -- The composite is bounded by `C` times the sup norm.
  let A : 𝓓^{n}_{K}(E, F) →ₗ[ℝ] ℕ →ᵇ F := evalSeqLM c hx ∘ₗ
    (ofSupportedInCLM ℝ hK : 𝓓^{n}_{K}(E, F) →L[ℝ] 𝓓^{n}(Ω, F)).toLinearMap
  have hA : Continuous A := by
    refine (ContDiffMapSupportedIn.withSeminorms ℝ E F n K).continuous_normedSpace_rng _ A
      ⟨{0}, C.toNNReal, fun g ↦ ?_⟩
    simp only [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, smul_apply,
      NNReal.smul_def, Real.coe_toNNReal _ hC, smul_eq_mul]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun k ↦ ?_
    simp only [A, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      coe_ofSupportedInCLM, evalSeqLM_apply, norm_smul]
    by_cases hk : k < N
    · exact mul_le_mul (Finset.single_le_sum (f := fun k ↦ ‖c k‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_range.2 hk)) (ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ) (norm_nonneg _)
        hC
    · have hg : g (x k) = 0 := g.zero_on_compl (hN k (not_lt.1 hk))
      simp only [coe_ofSupportedIn, hg, norm_zero, mul_zero]
      positivity
  simpa only [A, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, coe_ofSupportedInCLM] using hA

/-- **Compact sets of test functions are supported in a common compact set.** For a compact set
`Q` of test functions on `Ω`, there is a compact set `K ⊆ Ω` containing the support of every
member of `Q`. -/
theorem exists_compacts_forall_tsupport_subset_of_isCompact {Q : Set 𝓓^{n}(Ω, F)}
    (hQ : IsCompact Q) : ∃ K : Compacts E, (K : Set E) ⊆ Ω ∧ ∀ f ∈ Q, tsupport f ⊆ K := by
  -- On an infinite-dimensional space every test function is zero.
  by_cases hE : ¬FiniteDimensional ℝ E
  · exact ⟨⊥, by simp, fun f _ ↦ by simp [eq_zero_of_not_finiteDimensional f hE]⟩
  rw [not_not] at hE
  -- A compact exhaustion of `Ω`, transported to `E`.
  have := Ω.isOpen.locallyCompactSpace
  let C := CompactExhaustion.choice Ω
  let K (k : ℕ) : Compacts E := ⟨(↑) '' C k, (C.isCompact k).image continuous_subtypeVal⟩
  have hKΩ (k : ℕ) : (K k : Set E) ⊆ Ω := by rintro _ ⟨y, -, rfl⟩; exact y.property
  by_contra! hcon
  -- For each `k`, a member `f k` of `Q` with `f k (x k) ≠ 0` at a point `x k ∉ K k`.
  have hsel (k : ℕ) : ∃ f ∈ Q, ∃ y : E, f y ≠ 0 ∧ y ∉ (K k : Set E) := by
    obtain ⟨f, hf, hfK⟩ := hcon (K k) (hKΩ k)
    obtain ⟨y, hy, hyK⟩ := not_subset.1 fun h ↦ hfK <|
      closure_minimal h (K k).isCompact.isClosed
    exact ⟨f, hf, y, hy, hyK⟩
  choose f hf x hfx hxK using hsel
  -- The points `x k` eventually leave every compact subset of `Ω`.
  have hx (L : Compacts E) (hL : (L : Set E) ⊆ Ω) : ∃ N, ∀ k ≥ N, x k ∉ L := by
    have hLc : IsCompact (((↑) : Ω → E) ⁻¹' L) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' L.isCompact (by
        rw [Subtype.range_coe]; exact hL)
    obtain ⟨N, hN⟩ := C.exists_superset_of_isCompact hLc
    refine ⟨N, fun k hk hxL ↦ hxK k ?_⟩
    have hxΩ : x k ∈ Ω := (f k).tsupport_subset (subset_tsupport _ (hfx k))
    exact ⟨⟨x k, hxΩ⟩, C.subset hk (hN hxL), rfl⟩
  -- The map `g ↦ (k ↦ (k / ‖f k (x k)‖) • g (x k))` is continuous, hence bounded on `Q`.
  set c : ℕ → ℝ := fun k ↦ k / ‖f k (x k)‖
  obtain ⟨R, hR⟩ :=
    (hQ.image (continuous_evalSeqLM (n := n) (F := F) c hx)).isBounded.subset_closedBall 0
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hle := hR ⟨f k, hf k, rfl⟩
  rw [mem_closedBall_zero_iff] at hle
  have hnorm : ‖evalSeqLM (n := n) c hx (f k) k‖ = k := by
    simp only [evalSeqLM_apply, norm_smul, c,
      Real.norm_eq_abs, abs_div, Nat.abs_cast, abs_norm]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.2 (hfx k))
  have := (BoundedContinuousFunction.norm_coe_le_norm _ k).trans hle
  rw [hnorm] at this
  linarith

end TestFunction
