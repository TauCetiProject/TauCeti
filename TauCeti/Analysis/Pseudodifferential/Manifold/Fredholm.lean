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

## Main results

* `TauCeti.IsClassicalElliptic.isFredholm_chartSobolevExtension`: an elliptic classical
  pseudodifferential operator of order `m` on a compact manifold is Fredholm from `H^s(M)` to
  `H^{s - m}(M)`, for every real `s`.
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
  484–530, §6 (the Fredholm property from a two-sided parametrix, and (6.2), the index only depends
  on the homotopy class of the principal symbol).
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

end TauCeti
