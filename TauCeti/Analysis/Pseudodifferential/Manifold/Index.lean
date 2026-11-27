/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.Pseudodifferential.Manifold.Fredholm

/-!
# The index of an elliptic operator on a compact manifold

Let `M` be a compact manifold modelled on `ℝⁿ`, with the Sobolev spaces `H^s(M)` of chart
partitions (`TauCeti.chartSobolevSpace`). An elliptic classical pseudodifferential operator `P` of
order `m` extends to a Fredholm operator `P_s : H^s(M) → H^{s - m}(M)`
(`TauCeti.IsClassicalElliptic.isFredholm_chartSobolevExtension`), so it has an integer index
`dim ker P_s - dim coker P_s` (`ContinuousLinearMap.index`). This file proves the elementary
rules for this index of Atiyah and Singer, §6:

* **The index ignores lower order terms.** Adding an operator `R` of any order `m' < m` keeps
  `P + R` Fredholm with the same index
  (`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_add_of_mem`): the extension of `R` to
  `H^s(M) → H^{s - m}(M)` gains `m - m' > 0` orders, so it is compact by Rellich's theorem
  (`TauCeti.isCompactOperator_chartSobolevExtension_of_mem`), and compact perturbations keep the
  index (`ContinuousLinearMap.index_add_of_isCompactOperator`). In particular the index depends
  only on the principal symbol
  (`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq`).
* **The index is additive under composition.** For elliptic `P` of order `m` and `Q` of order
  `m'`, the extension of `P ∘ Q` is the composition of those of `P` and `Q`
  (`TauCeti.chartSobolevExtension_comp_of_mem`), so its index is the sum of their indices
  (`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp`). Composing with an operator
  whose extension is bijective changes the order without changing the index
  (`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp_of_bijective`); this is how the
  order of an elliptic operator is normalized by composing with powers of a positive elliptic
  operator.
* **A parametrix has the opposite index.** If `Q` of order `-m` satisfies `P ∘ Q - 1` of order
  `-1`, then the extension of `P ∘ Q` to `H^{s - m}(M)` is the identity plus a compact operator,
  of index `0`, so `index Q = -index P`
  (`TauCeti.index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem`). The same holds for a
  two-sided parametrix modulo any negative order
  (`TauCeti.index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem_of_neg`), since then both
  composites of the extensions are compact perturbations of the identity
  (`TauCeti.isCompactOperator_chartSobolevExtension_comp_sub_one_of_mem`).
* **The index is locally constant in elliptic families.** Along a family `x ↦ ∑ₖ fₖ(x) Aₖ` of
  elliptic operators of order `m` with continuous coefficients `fₖ`, the extensions depend
  continuously on `x` in operator norm, so the index is locally constant
  (`TauCeti.isLocallyConstant_index_chartSobolevExtension_sum_smul`). In particular two elliptic
  operators whose principal symbols are joined by the straight-line homotopy
  `(1 - t) σ_m(P) + t σ_m(Q)` of symbols invertible off the zero section have the same index
  (`TauCeti.index_chartSobolevExtension_eq_of_segment`), which is (6.2) of Atiyah and Singer for
  straight-line homotopies.

## Main results

* `TauCeti.IsClassicalElliptic.isFredholm_chartSobolevExtension_add_of_mem`,
  `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_add_of_mem`: perturbations of lower
  order keep the Fredholm property and the index.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq`:
  elliptic operators with the same principal symbol have the same index.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp`: the index of a composition is
  the sum of the indices.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp_of_bijective`: composing with an
  operator with bijective extension keeps the index.
* `TauCeti.index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem`,
  `TauCeti.index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem_of_neg`: a parametrix has the
  opposite index.
* `TauCeti.isLocallyConstant_index_chartSobolevExtension_sum_smul`,
  `TauCeti.index_chartSobolevExtension_eq_of_segment`: the index is locally constant along
  continuous finite-dimensional families of elliptic operators, in particular along a
  straight-line homotopy of elliptic principal symbols.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §6, pp. 517–519 (the index depends only on the symbol, (6.2) its homotopy invariance,
  and its invariance under change of order).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §19.2.
-/

public section

noncomputable section

open TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M]
  {P Q R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m m' : ℝ}
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

/-! ### Perturbations of lower order -/

section Perturbation

variable (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
  (hR : R ∈ classicalPseudodifferentialOperators m') (hm : m' < m)
  (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
  (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ)

omit [CompactSpace M] in
include hP hR hm hψ in
/-- The extension of `P + R` to `H^s(M) → H^{s - m}(M)` is that of `P` plus that of `R`, which is
compact since `R` has order `m' < m`. -/
private theorem chartSobolevExtension_add_eq_and_isCompactOperator :
    chartSobolevExtension hc ψ hc' φ (P + R) s (s - m) =
        chartSobolevExtension hc ψ hc' φ P s (s - m) +
          chartSobolevExtension hc ψ hc' φ R s (s - m) ∧
      IsCompactOperator (chartSobolevExtension hc ψ hc' φ R s (s - m)) :=
  ⟨chartSobolevExtension_add (exists_norm_chartReading_apply_le hP hψ le_rfl)
      (exists_norm_chartReading_apply_le hR hψ (by linarith)),
    isCompactOperator_chartSobolevExtension_of_mem hR hψ (by linarith)⟩

include hP hPe hR hm hψ hφ

/-- **Perturbations of lower order keep the Fredholm property.** On a compact manifold, if `P` is
an elliptic classical pseudodifferential operator of order `m` and `R` a classical
pseudodifferential operator of order `m' < m`, then `P + R` extends to a Fredholm operator
`H^s(M) → H^{s - m}(M)`. -/
theorem IsClassicalElliptic.isFredholm_chartSobolevExtension_add_of_mem :
    (chartSobolevExtension hc ψ hc' φ (P + R) s (s - m)).IsFredholm := by
  obtain ⟨h, hK⟩ := chartSobolevExtension_add_eq_and_isCompactOperator (hc' := hc') (φ := φ) hP
    hR hm hψ s
  rw [h]
  exact (hPe.isFredholm_chartSobolevExtension hP hψ hφ s).add_of_isCompactOperator hK

/-- **Perturbations of lower order keep the index.** On a compact manifold, if `P` is an elliptic
classical pseudodifferential operator of order `m` and `R` a classical pseudodifferential operator
of order `m' < m`, then the extensions of `P + R` and of `P` to `H^s(M) → H^{s - m}(M)` have the
same index. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_add_of_mem :
    (chartSobolevExtension hc ψ hc' φ (P + R) s (s - m)).index =
      (chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  obtain ⟨h, hK⟩ := chartSobolevExtension_add_eq_and_isCompactOperator (hc' := hc') (φ := φ) hP
    hR hm hψ s
  rw [h]
  exact ContinuousLinearMap.index_add_of_isCompactOperator
    (hPe.isFredholm_chartSobolevExtension hP hψ hφ s) hK

end Perturbation

/-- **The index depends only on the principal symbol.** On a compact manifold, if `P` is an
elliptic classical pseudodifferential operator of order `m` and `Q` a classical pseudodifferential
operator of order `m` with the same principal symbol, then the extensions of `Q` and `P` to
`H^s(M) → H^{s - m}(M)` have the same index: `Q - P` has order `m - 1`. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (h : ∀ x ξ, classicalPrincipalSymbol m Q x ξ = classicalPrincipalSymbol m P x ξ)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ Q s (s - m)).index =
      (chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  simpa using hPe.index_chartSobolevExtension_add_of_mem hP
    (sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq hQ hP h)
    (sub_one_lt m) hψ hφ s

/-! ### Compositions -/

/-- **The index is additive under composition.** On a compact manifold, let `P` and `Q` be
elliptic classical pseudodifferential operators of orders `m` and `m'`. The extension of `P ∘ Q` to
`H^s(M) → H^{s - m' - m}(M)` has index the sum of the indices of the extensions of `P` to
`H^{s - m'}(M) → H^{s - m' - m}(M)` and of `Q` to `H^s(M) → H^{s - m'}(M)`. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_comp
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hQ : Q ∈ classicalPseudodifferentialOperators m') (hQe : IsClassicalElliptic m' Q)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1)
    (hχ : ∀ x, ∑ k, (c'' k).cutoffPullback (hc'' k) (χ k) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc'' χ (P ∘ₗ Q) s (s - m' - m)).index =
      (chartSobolevExtension hc' φ hc'' χ P (s - m') (s - m' - m)).index +
        (chartSobolevExtension hc ψ hc' φ Q s (s - m')).index := by
  rw [← chartSobolevExtension_comp_of_mem hP hQ hψ hφ le_rfl le_rfl]
  exact ContinuousLinearMap.index_comp (hPe.isFredholm_chartSobolevExtension hP hφ hχ (s - m'))
    (hQe.isFredholm_chartSobolevExtension hQ hψ hφ s)

/-- **Changing the order keeps the index.** On a compact manifold, let `P` be an elliptic
classical pseudodifferential operator of order `m` and `Q` a classical pseudodifferential operator
of order `m'` whose extension to `H^s(M) → H^{s - m'}(M)` is bijective. Then the extension of
`P ∘ Q` to `H^s(M) → H^{s - m' - m}(M)` has the same index as that of `P` to
`H^{s - m'}(M) → H^{s - m' - m}(M)`. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_comp_of_bijective
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hQ : Q ∈ classicalPseudodifferentialOperators m')
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1)
    (hχ : ∀ x, ∑ k, (c'' k).cutoffPullback (hc'' k) (χ k) 1 x = 1) (s : ℝ)
    (hQb : Function.Bijective (chartSobolevExtension hc ψ hc' φ Q s (s - m'))) :
    (chartSobolevExtension hc ψ hc'' χ (P ∘ₗ Q) s (s - m' - m)).index =
      (chartSobolevExtension hc' φ hc'' χ P (s - m') (s - m' - m)).index := by
  rw [← chartSobolevExtension_comp_of_mem hP hQ hψ hφ le_rfl le_rfl,
    ContinuousLinearMap.index_comp (hPe.isFredholm_chartSobolevExtension hP hφ hχ (s - m'))
      (.of_bijective hQb), ContinuousLinearMap.index_eq_zero_of_bijective _ hQb, add_zero]

/-! ### Parametrices -/

/-- **A parametrix has the opposite index.** On a compact manifold, let `P` be a classical
pseudodifferential operator of order `m` and `Q` one of order `-m` such that `P ∘ Q - 1` has order
`-1` (so both are elliptic). Then the extension of `Q` to `H^{s - m}(M) → H^s(M)` has the opposite
index of that of `P` to `H^s(M) → H^{s - m}(M)`. -/
theorem index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hPQ : P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc' φ hc ψ Q (s - m) s).index =
      -(chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  have hPe := isClassicalElliptic_left_of_comp_sub_id_mem hP hQ hPQ
  have hQe := isClassicalElliptic_right_of_comp_sub_id_mem hP hQ hPQ
  -- The extension of `Q` is Fredholm, with target `H^{s - m - (-m)}(M) = H^s(M)`.
  have hQF : (chartSobolevExtension hc' φ hc ψ Q (s - m) s).IsFredholm := by
    have key : ∀ t, t = s - m - -m → (chartSobolevExtension hc' φ hc ψ Q (s - m) t).IsFredholm := by
      rintro t rfl
      exact hQe.isFredholm_chartSobolevExtension hQ hφ hψ (s - m)
    exact key s (by ring)
  -- The extension of `P ∘ Q` to `H^{s - m}(M)` is the identity plus a compact operator.
  have hid : (s - m : ℝ) ≤ s - m - 0 := by simp
  have hcomp : chartSobolevExtension hc ψ hc' φ P s (s - m) ∘L
      chartSobolevExtension hc' φ hc ψ Q (s - m) s =
        1 + chartSobolevExtension hc' φ hc' φ (P ∘ₗ Q - LinearMap.id) (s - m) (s - m) := by
    rw [chartSobolevExtension_comp_of_mem hP hQ hφ hψ (by linarith) le_rfl,
      ← chartSobolevExtension_id_self (he := hc') (ψ := φ) (s := s - m),
      ← chartSobolevExtension_add
        (exists_norm_chartReading_apply_le id_mem_classicalPseudodifferentialOperators hφ hid)
        (exists_norm_chartReading_apply_le hPQ hφ (by linarith)),
      add_sub_cancel]
  have h0 := ContinuousLinearMap.index_one_add_eq_zero
    (isCompactOperator_chartSobolevExtension_of_mem (hc' := hc') (φ := φ) (s := s - m)
      (t := s - m) hPQ hφ (by linarith))
  rw [← hcomp, ContinuousLinearMap.index_comp (hPe.isFredholm_chartSobolevExtension hP hψ hφ s)
    hQF] at h0
  omega

omit [CompactSpace M] in
/-- **A two-sided parametrix of any negative order has the opposite index.** Let `P` and `Q` be
classical pseudodifferential operators of orders `m` and `-m` such that `Q ∘ P - 1` and
`P ∘ Q - 1` have negative order `r`, not necessarily `-1`. Then the extension of `Q` to
`H^{s - m}(M) → H^s(M)` has the opposite index of the extension of `P` to
`H^s(M) → H^{s - m}(M)`. -/
theorem index_chartSobolevExtension_eq_neg_of_comp_sub_id_mem_of_neg {r : ℝ}
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

/-! ### Families of elliptic operators -/

/-- **The index is locally constant in elliptic families.** On a compact manifold, let
`A₁, …, A_N` be classical pseudodifferential operators of order `m` and `f₁, …, f_N` continuous
complex functions on a topological space `X` such that `∑ₖ fₖ(x) Aₖ` is elliptic for every `x`.
Then the index of the extension of `∑ₖ fₖ(x) Aₖ` to `H^s(M) → H^{s - m}(M)` is a locally constant
function of `x`. -/
theorem isLocallyConstant_index_chartSobolevExtension_sum_smul {X : Type*}
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
theorem index_chartSobolevExtension_eq_of_segment
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
