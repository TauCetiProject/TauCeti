/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.Fredholm.OrthogonalSplitting
import TauCeti.Geometry.Manifold.Sobolev.Smooth

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

**The kernel is smooth.** The kernel of the extension `H^s(M) → H^{s - m}(M)` consists of the
smooth functions `u` with `P u = 0` (`TauCeti.IsClassicalElliptic.ker_chartSobolevExtension`), so
its dimension is that of the smooth kernel, for every `s`
(`TauCeti.IsClassicalElliptic.finrank_ker_chartSobolevExtension`). For a parametrix `Q` modulo
operators of order `-∞`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`), an
element `x` of the kernel satisfies `x = -(Q P - 1) x`, and `Q P - 1` maps `H^s(M)` into every
`H^t(M)`. An element of every `H^t(M)` is a smooth function
(`TauCeti.mem_range_toChartSobolevSpace_iff`).

**The estimate on the kernel-orthogonal complement.** The elliptic estimate
`‖u‖_{H^s} ≤ C (‖P u‖_{H^{s - m}} + ‖u‖_{H^r})` needs its lower-order term in general: on the
circle the Laplacian kills the constant function `1`. Its kernel is the only obstruction. Fix any
injective continuous linear map `ι` from `H^s(M)` into a Hilbert space and read orthogonality to
the kernel through `ι`: for the identity of `H^s(M)` this is orthogonality in `H^s(M)` itself, and
for an inclusion into `L²` it is the `L²`-orthogonality of the classical statement. On the
elements `ι`-orthogonal to the kernel of `P : H^s(M) → H^{s - m}(M)` the lower-order term can be
dropped: `‖u‖_{H^s} ≤ C ‖P u‖_{H^{s - m}}`
(`TauCeti.IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension`). This holds for
every operator with closed range and finite-dimensional kernel
(`ContinuousLinearMap.exists_norm_le_mul_norm_of_forall_inner_eq_zero`), so it follows from the
Fredholm property.

## Main results

* `TauCeti.IsClassicalElliptic.isFredholm_chartSobolevExtension`: an elliptic classical
  pseudodifferential operator of order `m` on a compact manifold is Fredholm from `H^s(M)` to
  `H^{s - m}(M)`, for every real `s`.
* `TauCeti.IsClassicalElliptic.ker_chartSobolevExtension`,
  `TauCeti.IsClassicalElliptic.finrank_ker_chartSobolevExtension`: its kernel consists of the
  smooth solutions of `P u = 0`.
* `TauCeti.IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension` and
  `TauCeti.IsClassicalElliptic.exists_norm_toChartSobolevSpace_le_mul_norm`: the elliptic estimate
  without lower-order term on the complement of the kernel, on `H^s(M)` and for smooth functions.

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
open scoped ContDiff Manifold Distributions InnerProductSpace

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

/-- **Sobolev solutions of `P u = 0` are smooth.** On a compact manifold, the kernel of the
extension `H^s(M) → H^{s - m}(M)` of an elliptic classical pseudodifferential operator `P` of
order `m` consists of the smooth functions `u` with `P u = 0`, for every real `s`. -/
theorem IsClassicalElliptic.ker_chartSobolevExtension [CompactSpace M]
    (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ P s (s - m)).ker =
      (LinearMap.ker P).map (toChartSobolevSpace hc ψ s) := by
  -- A parametrix `Q` of order `-m`, with `R = Q ∘ P - 1` of order `-∞`.
  have hP := hPe.mem_of_isProperlySupported (isProperlySupported_of_compactSpace P)
  obtain ⟨Q, hQ, -, hQP⟩ := hPe.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators
    (isProperlySupported_of_compactSpace P)
  have hT := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc') (φ := φ) hP hψ
    (le_refl (s - m))
  have hS := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc) (φ := ψ) hQ hφ
    (show s ≤ s - m - -m by linarith)
  have hR : chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s s =
      chartSobolevExtension hc' φ hc ψ Q (s - m) s ∘L
        chartSobolevExtension hc ψ hc' φ P s (s - m) - 1 :=
    chartSobolevExtension_eq _ fun u ↦ by simp [hT, hS]
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    -- `x = -R x`, and `R` maps `H^s(M)` into every `H^t(M)`, so `x` is smooth.
    have hxt (t : ℝ) (ht : s ≤ t) : x ∈ Set.range (chartSobolevInclusion hc ψ ht) := by
      refine ⟨-chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s t x, ?_⟩
      rw [map_neg, ← ContinuousLinearMap.comp_apply,
        chartSobolevInclusion_comp_chartSobolevExtension ht (exists_norm_chartReading_apply_le
          ((mem_smoothingPseudodifferentialOperators_iff.1 hQP) (s - t)) hψ (by linarith)), hR]
      simp [hx]
    obtain ⟨u, rfl⟩ := (mem_range_toChartSobolevSpace_iff hc ψ hψ x).2 hxt
    refine ⟨u, ?_, rfl⟩
    -- The element of `H^{s - m}(M)` of `P u` vanishes, so `P u = 0`.
    refine toChartSobolevSpace_injective hc' φ hφ (s - m) ?_
    rw [← hT, hx, map_zero]
  · rintro _ ⟨u, hu, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT, LinearMap.mem_ker.1 hu, map_zero]

/-- On a compact manifold, the kernel of the extension `H^s(M) → H^{s - m}(M)` of an elliptic
classical pseudodifferential operator `P` of order `m` has the dimension of the space of smooth
solutions of `P u = 0`, for every real `s`. -/
theorem IsClassicalElliptic.finrank_ker_chartSobolevExtension [CompactSpace M]
    (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    Module.finrank ℂ (chartSobolevExtension hc ψ hc' φ P s (s - m)).ker =
      Module.finrank ℂ (LinearMap.ker P) := by
  rw [hPe.ker_chartSobolevExtension hψ hφ s]
  exact (Submodule.equivMapOfInjective _ (toChartSobolevSpace_injective hc ψ hψ s)
    _).finrank_eq.symm

/-- **The elliptic estimate on the kernel-orthogonal complement.** Let `P` be an elliptic classical
pseudodifferential operator of order `m` on a compact manifold, `L : H^s(M) → H^{s - m}(M)` its
extension between the Sobolev spaces of two chart partitions, and `ι` an injective continuous
linear map from `H^s(M)` into a Hilbert space, such as the identity. There is `C > 0` with
`‖u‖_{H^s} ≤ C ‖L u‖_{H^{s - m}}` for every `u ∈ H^s(M)` such that `ι u` is orthogonal to `ι k`
for every `k` in the kernel of `L`. Without the orthogonality the lower-order term of the elliptic
estimate cannot be dropped as soon as the kernel is nonzero. -/
theorem IsClassicalElliptic.exists_norm_le_mul_norm_chartSobolevExtension [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : chartSobolevSpace hc ψ s →L[ℂ] H} (hι : Function.Injective ι) :
    ∃ C > 0, ∀ u, (∀ k ∈ (chartSobolevExtension hc ψ hc' φ P s (s - m)).ker, ⟪ι u, ι k⟫_ℂ = 0) →
      ‖u‖ ≤ C * ‖chartSobolevExtension hc ψ hc' φ P s (s - m) u‖ :=
  have hL := hPe.isFredholm_chartSobolevExtension hP hψ hφ s
  have := hL.finite_ker
  ContinuousLinearMap.exists_norm_le_mul_norm_of_forall_inner_eq_zero hι hL.isClosed_range

/-- **The elliptic estimate on the kernel-orthogonal complement, for smooth functions.** Let `P` be
an elliptic classical pseudodifferential operator of order `m` on a compact manifold and `ι` an
injective continuous linear map from `H^s(M)` into a Hilbert space. There is `C > 0` with
`‖u‖_{H^s} ≤ C ‖P u‖_{H^{s - m}}`, in the norms of the chart readings, for every smooth `u` such
that `ι u` is orthogonal to `ι k` for every `k` in the kernel of the extension
`H^s(M) → H^{s - m}(M)` of `P`. -/
theorem IsClassicalElliptic.exists_norm_toChartSobolevSpace_le_mul_norm [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : chartSobolevSpace hc ψ s →L[ℂ] H} (hι : Function.Injective ι) :
    ∃ C > 0, ∀ u, (∀ k ∈ (chartSobolevExtension hc ψ hc' φ P s (s - m)).ker,
      ⟪ι (toChartSobolevSpace hc ψ s u), ι k⟫_ℂ = 0) →
      ‖toChartSobolevSpace hc ψ s u‖ ≤ C * ‖toChartSobolevSpace hc' φ (s - m) (P u)‖ := by
  obtain ⟨C, hC, h⟩ := hPe.exists_norm_le_mul_norm_chartSobolevExtension (hc' := hc') hP hψ hφ s hι
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  rw [← chartSobolevExtension_toChartSobolevSpace_of_mem hP hψ le_rfl u]
  exact h _ hu

end TauCeti
