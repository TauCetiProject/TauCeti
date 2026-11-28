/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas

/-!
# Splitting operators along cutoffs in common charts

Let `M` be a manifold modelled on a nontrivial finite-dimensional real space `E`, and let `ρ` and
`τ` be cutoffs in two charts of its maximal atlas. This file shows that for every complex-linear
operator `P` on the complex-valued smooth functions on `M`, the operator `ρ P τ` splits as a finite
sum `∑ᵢ φᵢ P ψᵢ`, where for each `i` the cutoffs `φᵢ` and `ψᵢ` are read on `M` through one chart
`eᵢ` of the maximal atlas, with the same charts and cutoffs for every `P`. For a partition of unity
`σᵢ` on the support of `τ`, `ρ P τ = ∑ᵢ ρ P (σᵢ τ)`. The supports of `ρ` and `σᵢ` may be far apart,
but the maximal atlas contains a chart whose source contains both, with disjoint images in `E`
(`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`). Since chart compressions are taken
in every chart of the maximal atlas, each piece `φᵢ P ψᵢ` is then described by a single chart
compression of `P`. No compactness of `M` is needed, since `ρ` and `τ` have compact supports.

On a compact manifold `ρ P` and `P` itself are such finite sums: for cutoffs `ρₖ` in charts whose
pullbacks add up to `1` (`IsCompact.exists_sum_cutoffPullback_eq_one`), every operator is
`ρ P = ∑ₗ ρ P ρₗ` and `P = ∑ₖ ∑ₗ ρₖ P ρₗ`, and each piece splits as above.

## Main results

* `TauCeti.exists_forall_mulLeft_comp_comp_mulLeft_eq_sum_mulLeft_comp_comp_mulLeft`: for cutoffs
  `ρ` and `τ` in charts, finitely many pairs of cutoffs `φᵢ`, `ψᵢ`, each pair in one chart, split
  every operator as `ρ P τ = ∑ᵢ φᵢ P ψᵢ`.
* `TauCeti.exists_forall_mulLeft_comp_eq_sum_mulLeft_comp_comp_mulLeft`: on a compact manifold,
  for a cutoff `ρ` in a chart, finitely many pairs of cutoffs `φᵢ`, `ψᵢ`, each pair in one chart,
  split every operator as `ρ P = ∑ᵢ φᵢ P ψᵢ`.
* `TauCeti.exists_forall_eq_sum_mulLeft_comp_comp_mulLeft`: on a compact manifold, finitely many
  pairs of cutoffs `φᵢ`, `ψᵢ`, each pair in one chart, split every operator as `P = ∑ᵢ φᵢ P ψᵢ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

open Set
open scoped ContDiff Manifold Distributions

universe u

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Splitting `ρ P τ` along cutoffs in common charts.** Let `ρ` and `τ` be cutoffs in charts `e`
and `e'` of a manifold modelled on a nontrivial finite-dimensional real space. There are finitely
many charts `eᵢ` of the maximal atlas and cutoffs `φᵢ`, `ψᵢ` in their targets such that every
complex-linear operator `P` on the complex-valued smooth functions on `M` satisfies
`ρ P τ = ∑ᵢ φᵢ P ψᵢ`, with the cutoffs read on `M` through the charts. -/
theorem exists_forall_mulLeft_comp_comp_mulLeft_eq_sum_mulLeft_comp_comp_mulLeft
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {e' : OpenPartialHomeomorph M E}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (τ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ (ι : Type u) (_ : Fintype ι) (e'' : ι → OpenPartialHomeomorph M E)
      (he'' : ∀ i, e'' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
      (φ ψ : ∀ i, 𝓓(⟨(e'' i).target, (e'' i).open_target⟩, ℝ)),
      ∀ P : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯,
        LinearMap.mulLeft ℂ (e.complexCutoffPullback he ρ 1) ∘ₗ P ∘ₗ
            LinearMap.mulLeft ℂ (e'.complexCutoffPullback he' τ 1) =
          ∑ i, LinearMap.mulLeft ℂ ((e'' i).complexCutoffPullback (he'' i) (φ i) 1) ∘ₗ P ∘ₗ
            LinearMap.mulLeft ℂ ((e'' i).complexCutoffPullback (he'' i) (ψ i) 1) := by
  -- Functions `σᵢ` adding up to `1` on the support of `τ` read on `M`, whose supports lie in charts
  -- `e''ᵢ` agreeing with `e` over the support of `ρ`.
  obtain ⟨ι, _, σ, e'', hσ, he''⟩ :=
    (e'.isCompact_symm_image_tsupport τ).exists_smoothPartition_mem_maximalAtlas_eqOn_symm he
      ρ.hasCompactSupport.isCompact ρ.tsupport_subset
  choose he''a hσc hσe hρe hEq using he''
  -- The product `σᵢ τ` is the pullback of a cutoff `ψᵢ` in `e''ᵢ`.
  set τ' := e'.cutoffPullback he' τ 1
  choose ψ hψ using fun i ↦ OpenPartialHomeomorph.exists_cutoffPullback_one_eq (he''a i)
    (g := σ i * τ') (by rw [ContMDiffMap.coe_mul]; exact HasCompactSupport.mul_right (hσc i))
    (by rw [ContMDiffMap.coe_mul]; exact tsupport_mul_subset_left.trans (hσe i))
  -- The cutoff `ρ`, read in the chart `e''ᵢ`, has the same pullback to `M` as in `e`.
  let ρ' (i : ι) : 𝓓(⟨(e'' i).target, (e'' i).open_target⟩, ℝ) :=
    ⟨ρ, ρ.contDiff, ρ.hasCompactSupport, hρe i⟩
  refine ⟨ι, inferInstance, e'', he''a, ρ', ψ, fun P ↦ ?_⟩
  have hρ' (i : ι) : (e'' i).complexCutoffPullback (he''a i) (ρ' i) =
      e.complexCutoffPullback he ρ :=
    (e.complexCutoffPullback_congr he (he''a i) (ψ' := ρ' i) rfl (hEq i).symm).symm
  -- `τ u = ∑ᵢ σᵢ τ u`, since `∑ᵢ σᵢ = 1` on the support of `τ`.
  have hτ (u : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      ∑ i, (e'' i).complexCutoffPullback (he''a i) (ψ i) 1 * u =
        e'.complexCutoffPullback he' τ 1 * u := by
    rw [← Finset.sum_mul]
    congr 1
    ext q
    simp only [ContMDiffMap.coe_sum, Finset.sum_apply,
      OpenPartialHomeomorph.complexCutoffPullback_one_apply, hψ, ← Complex.ofReal_sum,
      ContMDiffMap.coe_mul, Pi.mul_apply, ← Finset.sum_mul]
    by_cases hq : q ∈ e'.symm '' tsupport τ
    · rw [hσ q hq, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦
        hq (e'.tsupport_cutoffPullback_subset he' τ 1 h), mul_zero]
  ext u p
  simp only [hρ', LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply,
    ← Finset.mul_sum, ← map_sum, hτ]

section Compact

variable [CompactSpace M]

/-- **Splitting `ρ P` along cutoffs in common charts.** Let `ρ` be a cutoff in a chart `e` of a
compact manifold modelled on a nontrivial finite-dimensional real space. There are finitely many
charts `eᵢ` of the maximal atlas and cutoffs `φᵢ`, `ψᵢ` in their targets such that every
complex-linear operator `P` on the complex-valued smooth functions on `M` satisfies
`ρ P = ∑ᵢ φᵢ P ψᵢ`, with the cutoffs read on `M` through the charts. -/
theorem exists_forall_mulLeft_comp_eq_sum_mulLeft_comp_comp_mulLeft
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ (ι : Type u) (_ : Fintype ι) (e' : ι → OpenPartialHomeomorph M E)
      (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
      (φ ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ)),
      ∀ P : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯,
        LinearMap.mulLeft ℂ (e.complexCutoffPullback he ρ 1) ∘ₗ P =
          ∑ i, LinearMap.mulLeft ℂ ((e' i).complexCutoffPullback (he' i) (φ i) 1) ∘ₗ P ∘ₗ
            LinearMap.mulLeft ℂ ((e' i).complexCutoffPullback (he' i) (ψ i) 1) := by
  -- Cutoffs `τₗ` in the charts at finitely many points `cₗ`, with pullbacks adding up to `1`;
  -- each `ρ P τₗ` splits along cutoffs in common charts.
  obtain ⟨N, c, τ, hτ⟩ := isCompact_univ.exists_sum_cutoffPullback_eq_one (E := E) (M := M)
  choose ι _ e' he' φ ψ hP using fun l ↦
    exists_forall_mulLeft_comp_comp_mulLeft_eq_sum_mulLeft_comp_comp_mulLeft he ρ
      (IsManifold.chart_mem_maximalAtlas (c l)) (τ l)
  refine ⟨Σ l, ι l, inferInstance, fun p ↦ e' _ p.2, fun p ↦ he' _ p.2, fun p ↦ φ _ p.2,
    fun p ↦ ψ _ p.2, fun P ↦ ?_⟩
  simp only [Fintype.sum_sigma, ← hP]
  -- `ρ P u = ∑ₗ ρ P (τₗ u)`, since `∑ₗ τₗ = 1`.
  ext u p
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply,
    ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul, sum_complexCutoffPullback_one_eq_one _ τ
      fun q ↦ hτ q (mem_univ q), one_mul]

/-- **Splitting operators along pairs of cutoffs in common charts.** On a compact manifold modelled
on a nontrivial finite-dimensional real space, there are finitely many charts `eᵢ` of the maximal
atlas and cutoffs `φᵢ`, `ψᵢ` with compact supports in their targets such that every complex-linear
operator `P` on the complex-valued smooth functions on `M` is `∑ᵢ φᵢ P ψᵢ`, with the cutoffs read on
`M` through the charts. The supports of `φᵢ` and `ψᵢ` may be far apart on `M`: the maximal atlas
contains charts whose source has two components with disjoint images in the model space. -/
theorem exists_forall_eq_sum_mulLeft_comp_comp_mulLeft :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → OpenPartialHomeomorph M E)
      (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
      (φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)),
      ∀ P : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯,
        P = ∑ i, LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (φ i) 1) ∘ₗ P ∘ₗ
          LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (ψ i) 1) := by
  -- Cutoffs `ρₖ` in the charts at finitely many points `cₖ`, with pullbacks adding up to `1`;
  -- each `ρₖ P` splits along cutoffs in common charts.
  obtain ⟨N, c, ρ, hρ⟩ := isCompact_univ.exists_sum_cutoffPullback_eq_one (E := E) (M := M)
  choose ι _ e he φ ψ hP using fun k ↦ exists_forall_mulLeft_comp_eq_sum_mulLeft_comp_comp_mulLeft
    (IsManifold.chart_mem_maximalAtlas (c k)) (ρ k)
  refine ⟨Σ k, ι k, inferInstance, fun p ↦ e _ p.2, fun p ↦ he _ p.2, fun p ↦ φ _ p.2,
    fun p ↦ ψ _ p.2, fun P ↦ ?_⟩
  simp only [Fintype.sum_sigma, ← hP]
  -- `P u = ∑ₖ ρₖ P u`, since `∑ₖ ρₖ = 1`.
  ext u p
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply,
    ← Finset.sum_mul, sum_complexCutoffPullback_one_eq_one _ ρ fun q ↦ hρ q (mem_univ q),
    one_mul]

end Compact

end TauCeti
