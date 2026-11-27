/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.Regularity
public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.Fredholm.OrthogonalSplitting
import TauCeti.Geometry.Manifold.Sobolev.Smooth

/-!
# Elliptic operators on a compact manifold are Fredholm, with index independent of the choices

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
spaces by Rellich's theorem (`TauCeti.isCompactOperator_chartSobolevExtension_of_mem`,
`TauCeti.isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem`).

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

**Independence of the Sobolev order.** Let `s ≤ t`. The same parametrix, now inverting `P` modulo
an operator `R` of order `-N` with `t ≤ s + N`, gives elliptic regularity on the Sobolev scale: if
`u ∈ H^s(M)` and `P u ∈ H^{t - m}(M)`, then `u = Q (P u) - R u ∈ H^t(M)`
(`TauCeti.IsClassicalElliptic.exists_chartSobolevInclusion_eq`). The inclusions
`H^t(M) ⊆ H^s(M)` and `H^{t - m}(M) ⊆ H^{s - m}(M)` are injective with dense range and intertwine
the two extensions of `P`, so the abstract comparison
`ContinuousLinearMap.IsFredholm.index_eq_of_regularity` applies: the inclusion identifies the
kernels, an element of `H^{t - m}(M)` is in the range of `P` on `H^t(M)` exactly when it is in the
range of `P` on `H^s(M)`, and the index of `P : H^s(M) → H^{s - m}(M)` does not depend on `s`.

**Independence of the chart partitions.** The Sobolev spaces of two chart partitions are
isomorphic through `TauCeti.chartSobolevSpaceCongr`, which transports one extension of `P` to the
other, so the index does not depend on the partitions either.

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
* `TauCeti.IsClassicalElliptic.exists_chartSobolevInclusion_eq`: elliptic regularity, if
  `u ∈ H^s(M)` and `P u ∈ H^{t - m}(M)` for `s ≤ t`, then `u ∈ H^t(M)`.
* `TauCeti.IsClassicalElliptic.map_ker_chartSobolevExtension`,
  `TauCeti.IsClassicalElliptic.comap_range_chartSobolevExtension`: the kernel and the range of
  `P` do not depend on the Sobolev order.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_eq`: the index of
  `P : H^s(M) → H^{s - m}(M)` does not depend on `s`.
* `TauCeti.index_chartSobolevExtension_partitions_eq_of_mem`: the index of the extension of a
  classical pseudodifferential operator does not depend on the chart partitions.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §6, pp. 517–519 (the Fredholm property from a two-sided parametrix, and the
  independence of the index from the Sobolev order).
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
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)}

/-- **A parametrix inverts the extension up to a compact operator.** Let `P` and `Q` be classical
pseudodifferential operators of orders `m` and `m'` with `Q ∘ P - 1` of negative order `r`. If
`P` extends to `H^s(M) → H^t(M)` and `Q` to `H^t(M) → H^s(M)`, that is `t ≤ s - m` and
`s ≤ t - m'`, then the composite of the extensions differs from the identity of `H^s(M)` by a
compact operator: it is the extension of `Q ∘ P - 1`, which gains `-r > 0` orders. -/
theorem isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem {m' r : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m')
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators r) (hr : r < 0)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) {s t : ℝ} (ht : t ≤ s - m)
    (hs : s ≤ t - m') :
    IsCompactOperator (chartSobolevExtension hc' φ hc ψ Q t s ∘L
      chartSobolevExtension hc ψ hc' φ P s t - 1 :
        chartSobolevSpace hc ψ s →L[ℂ] chartSobolevSpace hc ψ s) := by
  have hT := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc') (φ := φ) hP hψ ht
  have hS := chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc) (φ := ψ) hQ hφ hs
  have hext : chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s s =
      chartSobolevExtension hc' φ hc ψ Q t s ∘L chartSobolevExtension hc ψ hc' φ P s t - 1 :=
    chartSobolevExtension_eq _ fun u ↦ by simp [hT, hS]
  rw [← hext]
  exact isCompactOperator_chartSobolevExtension_of_mem hQP hψ (by linarith)

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
  have h1 : -((1 : ℕ) : ℝ) < 0 := by norm_num
  exact .of_isCompactOperator_comp_sub_one
    (isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem hP hQ hQP h1 hψ hφ le_rfl
      (by linarith))
    (isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem hQ hP hPQ h1 hφ hψ (by linarith)
      le_rfl)

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

/-! ### Independence of the Sobolev order and of the chart partitions -/

/-- The inclusions `H^t(M) ⊆ H^s(M)` and `H^{t - m}(M) ⊆ H^{s - m}(M)` intertwine the extensions
`H^t(M) → H^{t - m}(M)` and `H^s(M) → H^{s - m}(M)` of a classical pseudodifferential operator `P`
of order `m`. -/
private theorem chartSobolevExtension_chartSobolevInclusion_apply
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) {s t : ℝ} (hst : s ≤ t)
    (x : chartSobolevSpace hc ψ t) :
    chartSobolevExtension hc ψ hc' φ P s (s - m) (chartSobolevInclusion hc ψ hst x) =
      chartSobolevInclusion hc' φ (by linarith : s - m ≤ t - m)
        (chartSobolevExtension hc ψ hc' φ P t (t - m) x) :=
  DFunLike.congr_fun
    (chartSobolevExtension_comp_chartSobolevInclusion_eq_chartSobolevInclusion_comp_of_mem hP hψ
      hst (by linarith) le_rfl le_rfl) x

/-- **Elliptic regularity on the Sobolev scale.** On a compact manifold, let `P` be an elliptic
classical pseudodifferential operator of order `m`, and let `s ≤ t`. If `x ∈ H^s(M)` and the
extension of `P` maps `x` into `H^{t - m}(M) ⊆ H^{s - m}(M)`, then `x` lies in `H^t(M) ⊆ H^s(M)`. -/
theorem IsClassicalElliptic.exists_chartSobolevInclusion_eq [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) {s t : ℝ} (hst : s ≤ t)
    {x : chartSobolevSpace hc ψ s} {y : chartSobolevSpace hc' φ (t - m)}
    (hxy : chartSobolevExtension hc ψ hc' φ P s (s - m) x =
      chartSobolevInclusion hc' φ (by linarith : s - m ≤ t - m) y) :
    ∃ x', chartSobolevInclusion hc ψ hst x' = x := by
  -- A parametrix `Q` of order `-m` with `R = Q ∘ P - 1` of order `-N`, where `t ≤ s + N`.
  obtain ⟨Q, hQ, -, hR⟩ := hPe.exists_comp_sub_id_mem_classicalPseudodifferentialOperators ⌈t - s⌉₊
  have hN : t ≤ s - -(⌈t - s⌉₊ : ℝ) := by linarith [Nat.le_ceil (t - s)]
  -- Then `x = Q (P x) - R x`, where `Q (P x) = Q y` and `R x` both lie in `H^t(M)`.
  refine ⟨chartSobolevExtension hc' φ hc ψ Q (t - m) t y -
    chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s t x, ?_⟩
  have hQs := exists_norm_chartReading_apply_le (hc' := hc) (φ := ψ) hQ hφ
    (show s ≤ s - m - -m by linarith)
  have hQt := exists_norm_chartReading_apply_le (hc' := hc) (φ := ψ) hQ hφ
    (show t ≤ t - m - -m by linarith)
  have hRt := exists_norm_chartReading_apply_le (hc' := hc) (φ := ψ) hR hψ hN
  have hRs : chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s s =
      chartSobolevExtension hc' φ hc ψ Q (s - m) s ∘L chartSobolevExtension hc ψ hc' φ P s (s - m) -
        1 :=
    chartSobolevExtension_eq _ fun u ↦ by
      simp [chartSobolevExtension_toChartSobolevSpace hQs,
        chartSobolevExtension_toChartSobolevSpace_of_mem (hc' := hc') (φ := φ) hP hψ le_rfl]
  -- Included into `H^s(M)`, `Q y` is `Q (P x)` and `R x` is the extension of `R` to `H^s(M)`.
  have hQy : chartSobolevInclusion hc ψ hst (chartSobolevExtension hc' φ hc ψ Q (t - m) t y) =
      chartSobolevExtension hc' φ hc ψ Q (s - m) s
        (chartSobolevExtension hc ψ hc' φ P s (s - m) x) := by
    rw [hxy, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      chartSobolevInclusion_comp_chartSobolevExtension hst hQt,
      chartSobolevExtension_comp_chartSobolevInclusion _ hQs]
  have hRx : chartSobolevInclusion hc ψ hst
      (chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s t x) =
        chartSobolevExtension hc ψ hc ψ (Q ∘ₗ P - LinearMap.id) s s x :=
    DFunLike.congr_fun (chartSobolevInclusion_comp_chartSobolevExtension hst hRt) x
  rw [map_sub, hQy, hRx, hRs]
  simp

/-- **The kernel of an elliptic operator does not depend on the Sobolev order.** On a compact
manifold, let `P` be an elliptic classical pseudodifferential operator of order `m`, and let
`s ≤ t`. The inclusion `H^t(M) ⊆ H^s(M)` maps the kernel of the extension `H^t(M) → H^{t - m}(M)`
of `P` onto the kernel of its extension `H^s(M) → H^{s - m}(M)`. -/
theorem IsClassicalElliptic.map_ker_chartSobolevExtension [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) {s t : ℝ} (hst : s ≤ t) :
    (LinearMap.ker (chartSobolevExtension hc ψ hc' φ P t (t - m)).toLinearMap).map
        (chartSobolevInclusion hc ψ hst).toLinearMap =
      LinearMap.ker (chartSobolevExtension hc ψ hc' φ P s (s - m)).toLinearMap :=
  LinearMap.map_ker_eq_ker_of_regularity
    (chartSobolevExtension_chartSobolevInclusion_apply hP hψ hst)
    (chartSobolevInclusion_injective hc' φ _)
    fun _ _ h ↦ hPe.exists_chartSobolevInclusion_eq hP hψ hφ hst h

/-- **Solvability does not depend on the Sobolev order.** On a compact manifold, let `P` be an
elliptic classical pseudodifferential operator of order `m`, and let `s ≤ t`. An element `y` of
`H^{t - m}(M)` is `P u` for some `u ∈ H^t(M)` exactly when it is `P u` for some `u ∈ H^s(M)`. -/
theorem IsClassicalElliptic.comap_range_chartSobolevExtension [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) {s t : ℝ} (hst : s ≤ t) :
    (LinearMap.range (chartSobolevExtension hc ψ hc' φ P s (s - m)).toLinearMap).comap
        (chartSobolevInclusion hc' φ (by linarith : s - m ≤ t - m)).toLinearMap =
      LinearMap.range (chartSobolevExtension hc ψ hc' φ P t (t - m)).toLinearMap :=
  LinearMap.comap_range_eq_range_of_regularity
    (chartSobolevExtension_chartSobolevInclusion_apply hP hψ hst)
    (chartSobolevInclusion_injective hc' φ _)
    fun _ _ h ↦ hPe.exists_chartSobolevInclusion_eq hP hψ hφ hst h

/-- **The index of an elliptic operator does not depend on the Sobolev order.** On a compact
manifold, the extensions `H^s(M) → H^{s - m}(M)` and `H^t(M) → H^{t - m}(M)` of an elliptic
classical pseudodifferential operator `P` of order `m` have the same index, for all real `s` and
`t`. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_eq [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s t : ℝ) :
    (chartSobolevExtension hc ψ hc' φ P t (t - m)).index =
      (chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  wlog hst : s ≤ t generalizing s t
  · exact (this t s (le_of_not_ge hst)).symm
  exact (hPe.isFredholm_chartSobolevExtension hP hψ hφ s).index_eq_of_regularity
    (chartSobolevExtension_chartSobolevInclusion_apply hP hψ hst)
    (chartSobolevInclusion_injective hc ψ hst) (chartSobolevInclusion_injective hc' φ _)
    (denseRange_chartSobolevInclusion hc' φ _)
    fun _ _ h ↦ hPe.exists_chartSobolevInclusion_eq hP hψ hφ hst h

/-- **The index does not depend on the chart partitions.** Let `P` be a classical pseudodifferential
operator of order `m` and `t ≤ s - m`. The extensions `H^s(M) → H^t(M)` of `P` between the Sobolev
spaces of two pairs of chart partitions have the same index. -/
theorem index_chartSobolevExtension_partitions_eq_of_mem {ι₂ κ₂ : Type*} [Fintype ι₂]
    [Fintype κ₂]
    {c₂ : ι₂ → OpenPartialHomeomorph M (CoordinateSpace n)}
    {hc₂ : ∀ i, c₂ i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {ψ₂ : ∀ i, 𝓓(⟨(c₂ i).target, (c₂ i).open_target⟩, ℝ)}
    {c₂' : κ₂ → OpenPartialHomeomorph M (CoordinateSpace n)}
    {hc₂' : ∀ j, c₂' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {φ₂ : ∀ j, 𝓓(⟨(c₂' j).target, (c₂' j).open_target⟩, ℝ)}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hψ₂ : ∀ x, ∑ i, (c₂ i).cutoffPullback (hc₂ i) (ψ₂ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1)
    (hφ₂ : ∀ x, ∑ j, (c₂' j).cutoffPullback (hc₂' j) (φ₂ j) 1 x = 1) {s t : ℝ}
    (ht : t ≤ s - m) :
    (chartSobolevExtension hc₂ ψ₂ hc₂' φ₂ P s t).index =
      (chartSobolevExtension hc ψ hc' φ P s t).index := by
  rw [chartSobolevExtension_eq_chartSobolevSpaceCongr_comp hψ hψ₂ hφ hφ₂
    (exists_norm_chartReading_apply_le hP hψ ht)]
  simp

end TauCeti
