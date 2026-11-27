/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev

/-!
# Elliptic operators on a compact manifold are Fredholm

Let `M` be a compact manifold modelled on `ℝⁿ`, and let `P` be a classical pseudodifferential
operator of order `m` on `M` (`TauCeti.classicalPseudodifferentialOperators`) that is elliptic
(`TauCeti.IsClassicalElliptic`). Read the Sobolev spaces `H^s(M)` through chart partitions: finitely
many cutoffs `ψᵢ` in charts `cᵢ` whose readings `ψᵢ ∘ cᵢ` on `M` add up to `1`, with `H^s(M)` the
closure of the chart readings of smooth functions in `⨁ᵢ H^s(ℝⁿ)` (`TauCeti.chartSobolevSpace`).
This file proves that for every real `s` the extension of `P` to a bounded operator
`H^s(M) → H^{s - m}(M)` (`TauCeti.chartSobolevExtension`) is a **Fredholm operator**
(`TauCeti.IsClassicalElliptic.isFredholm_chartSobolevExtension`): its kernel is finite-dimensional,
its range is closed and of finite codimension.

The proof is Atkinson's criterion
(`ContinuousLinearMap.IsFredholm.of_isCompactOperator_comp_sub_one`) applied to a parametrix. An
elliptic `P` has a classical pseudodifferential operator `Q` of order `-m` with `Q ∘ P - 1` and
`P ∘ Q - 1` of order `-1`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`). The
extension of `Q` to `H^{s - m}(M) → H^s(M)` inverts that of `P` up to the extensions of these
remainders to `H^s(M)` and `H^{s - m}(M)`, and operators of negative order are compact on Sobolev
spaces by Rellich's theorem (`TauCeti.isCompactOperator_chartSobolevExtension_of_mem`).

## Main results

* `TauCeti.IsClassicalElliptic.isFredholm_chartSobolevExtension`: an elliptic classical
  pseudodifferential operator of order `m` on a compact manifold is Fredholm from `H^s(M)` to
  `H^{s - m}(M)`, for every real `s`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §6 (the Fredholm property from a two-sided parametrix).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§4 and 8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Theorem 19.2.1.
-/

public section

noncomputable section

open TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)}

/-- **Elliptic operators are Fredholm.** On a compact manifold, an elliptic classical
pseudodifferential operator `P` of order `m` extends, for every real `s`, to a Fredholm operator
`H^s(M) → H^{s - m}(M)` between the Sobolev spaces of any two chart partitions. -/
theorem IsClassicalElliptic.isFredholm_chartSobolevExtension [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ P s (s - m)).IsFredholm := by
  -- A parametrix `Q` of order `-m`, inverting `P` modulo operators of order `-1`.
  obtain ⟨Q, hQ, hPQ, hQP⟩ := hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators 1
  have hs : s ≤ s - m - -m := by linarith
  have hT := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc') (φ := φ) hP hψ
    (le_refl (s - m))
  have hS := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc) (φ := ψ) hQ hφ hs
  -- The extension of `Q` inverts that of `P` up to the extensions of the remainders.
  have hST : chartSobolevExtension hc' φ hc ψ Q (s - m) s ∘L
      chartSobolevExtension hc ψ hc' φ P s (s - m) - 1 =
        chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s s :=
    (chartSobolevExtension_eq _ fun u ↦ by simp [hT, hS]).symm
  have hTS : chartSobolevExtension hc ψ hc' φ P s (s - m) ∘L
      chartSobolevExtension hc' φ hc ψ Q (s - m) s - 1 =
        chartSobolevExtension hc' φ hc' φ (P ∘ₗ Q - LinearMap.id) (s - m) (s - m) :=
    (chartSobolevExtension_eq _ fun u ↦ by simp [hT, hS]).symm
  -- The remainders have order `-1`, so they are compact.
  refine ContinuousLinearMap.IsFredholm.of_isCompactOperator_comp_sub_one
    (S := chartSobolevExtension hc' φ hc ψ Q (s - m) s) ?_ ?_
  · rw [hST]
    exact isCompactOperator_chartSobolevExtension_of_mem hQP hψ (by push_cast; linarith)
  · rw [hTS]
    exact isCompactOperator_chartSobolevExtension_of_mem hPQ hφ (by push_cast; linarith)

end TauCeti
