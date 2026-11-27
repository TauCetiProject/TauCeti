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

**The index.** Write `ind_s(P)` for the Fredholm index of `P : H^s(M) → H^{s - m}(M)`. Since
operators of lower order are compact perturbations, `ind_s(P)` only depends on the principal symbol
`σ_m(P)` (`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_add`,
`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq`). It is
additive under composition, `ind_s(P ∘ Q) = ind_{s - m'}(P) + ind_s(Q)`
(`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp`), and a parametrix has the opposite
index (`TauCeti.index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem`). It is locally constant
along a family `x ↦ ∑ₖ fₖ(x) Aₖ` of elliptic operators of order `m` with continuous coefficients
`fₖ`, whose extensions depend continuously on `x` in operator norm
(`TauCeti.isLocallyConstant_index_chartSobolevExtension_sum_smul`). In particular two elliptic
operators whose principal symbols are joined by the straight-line homotopy
`(1 - t) σ_m(P) + t σ_m(Q)` of symbols invertible off the zero section have the same index
(`TauCeti.index_chartSobolevExtension_eq_of_segment`).

**The kernel is smooth.** The kernel of the extension `H^s(M) → H^{s - m}(M)` consists of the
smooth functions `u` with `P u = 0` (`TauCeti.IsClassicalElliptic.ker_chartSobolevExtension`), so
its dimension is that of the smooth kernel, for every `s`
(`TauCeti.IsClassicalElliptic.finrank_ker_chartSobolevExtension`). For a parametrix `Q` modulo
operators of order `-∞`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`), an
element `x` of the kernel satisfies `x = -(Q P - 1) x`, and `Q P - 1` maps `H^s(M)` into every
`H^t(M)`. An element of every `H^t(M)` is a smooth function
(`TauCeti.mem_range_toChartSobolevSpace_iff`).

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
* `TauCeti.IsClassicalElliptic.exists_chartSobolevInclusion_eq`: elliptic regularity, if
  `u ∈ H^s(M)` and `P u ∈ H^{t - m}(M)` for `s ≤ t`, then `u ∈ H^t(M)`.
* `TauCeti.IsClassicalElliptic.map_ker_chartSobolevExtension`,
  `TauCeti.IsClassicalElliptic.comap_range_chartSobolevExtension`: the kernel and the range of
  `P` do not depend on the Sobolev order.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_eq`: the index of
  `P : H^s(M) → H^{s - m}(M)` does not depend on `s`.
* `TauCeti.index_chartSobolevExtension_partitions_eq_of_mem`: the index of the extension of a
  classical pseudodifferential operator does not depend on the chart partitions.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq`: the
  index only depends on the principal symbol.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp`: the index of a composition is
  the sum of the indices.
* `TauCeti.index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem`: a parametrix has the opposite
  index.
* `TauCeti.isLocallyConstant_index_chartSobolevExtension_sum_smul`,
  `TauCeti.index_chartSobolevExtension_eq_of_segment`: the index is locally constant along
  continuous finite-dimensional families of elliptic operators (so constant over connected
  parameter spaces), in particular along a straight-line homotopy of elliptic principal symbols.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §6, pp. 517–519 (the Fredholm property from a two-sided parametrix, the independence
  of the index from the Sobolev order, and (6.2), the index only depends on the homotopy class of
  the principal symbol).
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
  {P Q R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)}
  {c'' : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc'' : ∀ k, c'' k ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {χ : ∀ k, 𝓓(⟨(c'' k).target, (c'' k).open_target⟩, ℝ)}

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

/-! ### The index -/

/-- **The index ignores lower-order terms.** On a compact manifold, adding an operator `R` of
order `r < m` to an elliptic operator `P` of order `m` does not change the index of its extension
`H^s(M) → H^{s - m}(M)`: the extension of `R` is compact. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_add [CompactSpace M] {r : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hR : R ∈ classicalPseudodifferentialOperators r) (hr : r < m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ (P + R) s (s - m)).index =
      (chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  rw [chartSobolevExtension_add (exists_norm_chartReading_apply_le hP hψ le_rfl)
    (exists_norm_chartReading_apply_le hR hψ (by linarith))]
  exact ContinuousLinearMap.index_add_of_isCompactOperator
    (hPe.isFredholm_chartSobolevExtension hP hψ hφ s)
    (isCompactOperator_chartSobolevExtension_of_mem hR hψ (by linarith))

/-- **The index only depends on the principal symbol.** On a compact manifold, two classical
pseudodifferential operators of order `m` with the same principal symbol, one of them elliptic,
have extensions `H^s(M) → H^{s - m}(M)` of the same index. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq
    [CompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (h : ∀ x ξ, classicalPrincipalSymbol m Q x ξ = classicalPrincipalSymbol m P x ξ)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ Q s (s - m)).index =
      (chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  rw [← add_sub_cancel P Q]
  exact hPe.index_chartSobolevExtension_add hP
    (sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq hQ hP h)
    (by linarith) hψ hφ s

/-- **The index of a composition.** On a compact manifold, let `P` and `Q` be elliptic classical
pseudodifferential operators of orders `m` and `m'`. The index of the extension of `P ∘ Q` to
`H^s(M) → H^{s - m' - m}(M)` is the sum of the indices of the extensions of `Q` to
`H^s(M) → H^{s - m'}(M)` and of `P` to `H^{s - m'}(M) → H^{s - m' - m}(M)`. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_comp [CompactSpace M] {m' : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hQ : Q ∈ classicalPseudodifferentialOperators m') (hQe : IsClassicalElliptic m' Q)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1)
    (hχ : ∀ x, ∑ k, (c'' k).cutoffPullback (hc'' k) (χ k) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc'' χ (P ∘ₗ Q) s (s - m' - m)).index =
      (chartSobolevExtension hc' φ hc'' χ P (s - m') (s - m' - m)).index +
        (chartSobolevExtension hc ψ hc' φ Q s (s - m')).index := by
  rw [← chartSobolevExtension_comp_of_mem hP hQ hψ hφ le_rfl le_rfl]
  exact ContinuousLinearMap.index_comp (hPe.isFredholm_chartSobolevExtension hP hφ hχ _)
    (hQe.isFredholm_chartSobolevExtension hQ hψ hφ s)

/-- **A parametrix has the opposite index.** On a compact manifold, let `P` and `Q` be classical
pseudodifferential operators of orders `m` and `-m` such that `Q ∘ P - 1` and `P ∘ Q - 1` have
negative order `r`. Then the extension of `Q` to `H^{s - m}(M) → H^s(M)` has the opposite index of
the extension of `P` to `H^s(M) → H^{s - m}(M)`. -/
theorem index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem {r : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators r)
    (hPQ : P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators r) (hr : r < 0)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc' φ hc ψ Q (s - m) s).index =
      -(chartSobolevExtension hc ψ hc' φ P s (s - m)).index :=
  ContinuousLinearMap.index_eq_neg_of_isCompactOperator_comp_sub_one
    (isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem hP hQ hQP hr hψ hφ le_rfl
      (by linarith))
    (isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem hQ hP hPQ hr hφ hψ (by linarith)
      le_rfl)

/-- **The index is locally constant in elliptic families.** On a compact manifold, let
`A₁, …, A_N` be classical pseudodifferential operators of order `m` and `f₁, …, f_N` continuous
complex functions on a topological space `X` such that `∑ₖ fₖ(x) Aₖ` is elliptic for every `x`.
Then the index of the extension of `∑ₖ fₖ(x) Aₖ` to `H^s(M) → H^{s - m}(M)` is a locally constant
function of `x`. -/
theorem isLocallyConstant_index_chartSobolevExtension_sum_smul [CompactSpace M] {X : Type*}
    [TopologicalSpace X] {A : ν → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hA : ∀ k, A k ∈ classicalPseudodifferentialOperators m) {f : ν → X → ℂ}
    (hf : ∀ k, Continuous (f k)) (he : ∀ x, IsClassicalElliptic m (∑ k, f k x • A k))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    IsLocallyConstant fun x ↦
      (chartSobolevExtension hc ψ hc' φ (∑ k, f k x • A k) s (s - m)).index := by
  -- The extension of `∑ₖ fₖ(x) Aₖ` is `∑ₖ fₖ(x) • (extension of Aₖ)`, continuous in `x`.
  have hext : ∀ x, chartSobolevExtension hc ψ hc' φ (∑ k, f k x • A k) s (s - m) =
      ∑ k, f k x • chartSobolevExtension hc ψ hc' φ (A k) s (s - m) := fun x ↦
    chartSobolevExtension_eq _ fun u ↦ by
      simp [chartSobolevExtension_toChartSobolevSpace_of_mem (hA _) hψ le_rfl]
  have hmem : ∀ x, ∑ k, f k x • A k ∈ classicalPseudodifferentialOperators m := fun x ↦
    Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hA k)
  simp_rw [hext]
  exact Continuous.isLocallyConstant_index (by fun_prop) fun x ↦
    hext x ▸ (he x).isFredholm_chartSobolevExtension (hmem x) hψ hφ s

/-- **Homotopy invariance of the index.** On a compact manifold, let `P` and `Q` be classical
pseudodifferential operators of order `m` whose principal symbols are joined by a straight-line
homotopy of elliptic symbols: `(1 - t) σ_m(P)(x, ξ) + t σ_m(Q)(x, ξ) ≠ 0` for every `t ∈ [0, 1]`
and every nonzero covector `ξ`. Then the extensions of `P` and `Q` to `H^s(M) → H^{s - m}(M)` have
the same index. -/
theorem index_chartSobolevExtension_eq_of_segment [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ξ, ξ ≠ 0 →
      (1 - t : ℂ) * classicalPrincipalSymbol m P x ξ + t * classicalPrincipalSymbol m Q x ξ ≠ 0)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ P s (s - m)).index =
      (chartSobolevExtension hc ψ hc' φ Q s (s - m)).index := by
  -- The family `t ↦ (1 - t) P + t Q` over the unit interval, written as a sum over `Fin 2`.
  let A : Fin 2 → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ := ![P, Q]
  let f : Fin 2 → unitInterval → ℂ := ![fun t ↦ 1 - ((t : ℝ) : ℂ), fun t ↦ ((t : ℝ) : ℂ)]
  have hA : ∀ k, A k ∈ classicalPseudodifferentialOperators m := Fin.forall_fin_two.2 ⟨hP, hQ⟩
  have hsum : ∀ t, ∑ k, f k t • A k = (1 - ((t : ℝ) : ℂ)) • P + ((t : ℝ) : ℂ) • Q := fun t ↦ by
    simp [Fin.sum_univ_two, f, A]
  have he : ∀ t, IsClassicalElliptic m (∑ k, f k t • A k) := fun t ↦
    isClassicalElliptic_iff.2 fun x ↦ isClassicalEllipticAt_iff.2 fun ξ hξ ↦ by
    rw [hsum, classicalPrincipalSymbol_add (Submodule.smul_mem _ _ hP)
      (Submodule.smul_mem _ _ hQ), classicalPrincipalSymbol_smul hP,
      classicalPrincipalSymbol_smul hQ]
    exact h t t.property x ξ hξ
  have hf : ∀ k, Continuous (f k) := Fin.forall_fin_two.2
    ⟨by simp only [f, Matrix.cons_val_zero]; fun_prop,
      by simp only [f, Matrix.cons_val_one, Matrix.cons_val_fin_one]; fun_prop⟩
  have hconst := (isLocallyConstant_index_chartSobolevExtension_sum_smul hA hf he hψ hφ
    s).apply_eq_of_preconnectedSpace 0 1
  simpa [hsum] using hconst

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
