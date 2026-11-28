/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.Pseudodifferential.Manifold.Fredholm
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization

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
* **Operators with principal symbol in the slit plane have index zero.** If the principal symbol
  of `P` takes values in the slit plane `ℂ \ (-∞, 0]` at nonzero covectors, for instance if it is
  real and positive, the index of `P` is `0`
  (`TauCeti.index_chartSobolevExtension_eq_zero_of_mem_slitPlane`). The square root of its
  principal symbol, taken in the slit plane, is again a smooth homogeneous function
  (`TauCeti.cpow_mem_homogeneousCotangentSymbols`) and so the principal symbol of an operator `R`
  of order `m / 2` with principal symbol in the slit plane. Then `R ∘ R` and `P` have the same
  principal symbol, so the index of `P` is twice that of `R`. Repeating, the index is divisible by
  every power of `2`, hence `0`.
* **Changing the order keeps the index** (Atiyah and Singer, (6.3)). Composing an elliptic `P` with
  such an operator keeps the index
  (`TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp_of_mem_slitPlane`). On a compact
  manifold there are operators of every real order with positive principal symbol
  (`TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_pos`), so
  every elliptic operator has the index of an elliptic operator of any prescribed order
  (`TauCeti.IsClassicalElliptic.exists_index_chartSobolevExtension_eq`).
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
* `TauCeti.index_chartSobolevExtension_eq_zero_of_mem_slitPlane`: an operator whose principal
  symbol lies in the slit plane at nonzero covectors has index `0`.
* `TauCeti.IsClassicalElliptic.index_chartSobolevExtension_comp_of_mem_slitPlane`: composing with
  such an operator keeps the index.
* `TauCeti.IsClassicalElliptic.exists_index_chartSobolevExtension_eq`: the index of an elliptic
  operator is the index of an elliptic operator of any prescribed real order.

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

/-! ### Principal symbols in the slit plane -/

/-- The index of the extension `H^s(M) → H^{s - m}(M)` of an operator `P` whose principal symbol
takes values in the slit plane at nonzero covectors is divisible by every power of `2`. The square
root of the principal symbol lies again in the slit plane and is the principal symbol of an
operator `R` of order `m / 2`. Then `R ∘ R` has the principal symbol of `P`, so the index of `P` is
twice that of `R`. -/
private theorem two_pow_dvd_index_chartSobolevExtension_of_mem_slitPlane
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (k : ℕ)
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hσ : ∀ x ξ, ξ ≠ 0 → classicalPrincipalSymbol m P x ξ ∈ Complex.slitPlane) (s : ℝ) :
    (2 : ℤ) ^ k ∣ (chartSobolevExtension hc ψ hc ψ P s (s - m)).index := by
  induction k generalizing m P with
  | zero => simp
  | succ k ih =>
    -- The square root of the principal symbol is the principal symbol of some `R`.
    obtain ⟨R, hR, hRσ⟩ :=
      exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq
        (cpow_mem_homogeneousCotangentSymbols
          classicalPrincipalSymbol_mem_homogeneousCotangentSymbols hσ (r := 2⁻¹) (by norm_num))
        isCompact_univ fun x hx ↦ (hx (Set.mem_univ x)).elim
    have hRslit (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
        classicalPrincipalSymbol (m * 2⁻¹) R x ξ ∈ Complex.slitPlane := by
      rw [hRσ]
      exact Complex.mem_slitPlane_iff.2 <| Or.inl <| by
        simpa using (Complex.cpow_one_half_re_pos_iff _).2 (hσ x ξ hξ)
    have hRe := isClassicalElliptic_of_mem_slitPlane hRslit
    -- `R ∘ R` is an operator of order `m` with the principal symbol of `P`.
    have hm : m * 2⁻¹ + m * 2⁻¹ = m := by ring
    have hRR := comp_mem_classicalPseudodifferentialOperators hR hR
    rw [hm] at hRR
    have hRRσ (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
        classicalPrincipalSymbol m (R ∘ₗ R) x ξ = classicalPrincipalSymbol m P x ξ := by
      have h := classicalPrincipalSymbol_comp hR hR x ξ
      rw [hm] at h
      rw [h, hRσ, ← sq]
      simp
    -- So the index of `P` is that of `R ∘ R`, twice that of `R`.
    have hPe := isClassicalElliptic_of_mem_slitPlane hσ
    have hcomp := hRe.index_chartSobolevExtension_comp hR hR hRe hψ hψ hψ s
    rw [hRe.index_chartSobolevExtension_eq hR hψ hψ s (s - m * 2⁻¹),
      show s - m * 2⁻¹ - m * 2⁻¹ = s - m by ring] at hcomp
    rw [← hPe.index_chartSobolevExtension_eq_of_classicalPrincipalSymbol_eq hP hRR hRRσ hψ hψ s,
      hcomp, ← two_mul, pow_succ']
    exact mul_dvd_mul_left 2 (ih hR hRslit)

/-- **Operators with principal symbol in the slit plane have index zero.** On a compact manifold,
let `P` be a classical pseudodifferential operator of order `m` whose principal symbol takes values
in the slit plane `ℂ \ (-∞, 0]` at nonzero covectors, for instance a real positive principal
symbol. Then `P` is elliptic (`TauCeti.isClassicalElliptic_of_mem_slitPlane`), and its extension
`H^s(M) → H^{s - m}(M)` has index `0`, for every real `s`. -/
theorem index_chartSobolevExtension_eq_zero_of_mem_slitPlane
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hσ : ∀ x ξ, ξ ≠ 0 → classicalPrincipalSymbol m P x ξ ∈ Complex.slitPlane)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc' φ P s (s - m)).index = 0 := by
  -- The index is divisible by `2 ^ k` for `k` its absolute value, which exceeds it.
  rw [← index_chartSobolevExtension_partitions_eq_of_mem hP hψ hψ hφ hψ le_rfl]
  set i := (chartSobolevExtension hc ψ hc ψ P s (s - m)).index
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (two_pow_dvd_index_chartSobolevExtension_of_mem_slitPlane hψ i.natAbs hP hσ s)
    (by simpa [Int.natAbs_pow] using Nat.lt_two_pow_self)

/-- **Changing the order keeps the index.** On a compact manifold, let `P` be an elliptic classical
pseudodifferential operator of order `m` and `Q` a classical pseudodifferential operator of order
`m'` whose principal symbol takes values in the slit plane `ℂ \ (-∞, 0]` at nonzero covectors.
Then the extension of `P ∘ Q` to `H^s(M) → H^{s - m' - m}(M)` has the same index as that of `P` to
`H^{s - m'}(M) → H^{s - m' - m}(M)`, since the extension of `Q` has index `0`. -/
theorem IsClassicalElliptic.index_chartSobolevExtension_comp_of_mem_slitPlane
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hQ : Q ∈ classicalPseudodifferentialOperators m')
    (hσ : ∀ x ξ, ξ ≠ 0 → classicalPrincipalSymbol m' Q x ξ ∈ Complex.slitPlane)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1)
    (hχ : ∀ x, ∑ k, (c'' k).cutoffPullback (hc'' k) (χ k) 1 x = 1) (s : ℝ) :
    (chartSobolevExtension hc ψ hc'' χ (P ∘ₗ Q) s (s - m' - m)).index =
      (chartSobolevExtension hc' φ hc'' χ P (s - m') (s - m' - m)).index := by
  rw [hPe.index_chartSobolevExtension_comp hP hQ (isClassicalElliptic_of_mem_slitPlane hσ) hψ hφ
    hχ s, index_chartSobolevExtension_eq_zero_of_mem_slitPlane hQ hσ hψ hφ s, add_zero]

/-- **Every order carries the same indices.** On a compact manifold, let `P` be an elliptic
classical pseudodifferential operator of order `m`. For every real `k` there is an elliptic
classical pseudodifferential operator `P'` of order `k` whose extensions `H^t(M) → H^{t - k}(M)`
have the index of the extensions `H^s(M) → H^{s - m}(M)` of `P`, for all real `s` and `t`. One can
take `P' = P ∘ Q` for an operator `Q` of order `k - m` with positive principal symbol
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_pos`). -/
theorem IsClassicalElliptic.exists_index_chartSobolevExtension_eq
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (k : ℝ) :
    ∃ P' ∈ classicalPseudodifferentialOperators k, IsClassicalElliptic k P' ∧
      ∀ s t, (chartSobolevExtension hc ψ hc' φ P' t (t - k)).index =
        (chartSobolevExtension hc ψ hc' φ P s (s - m)).index := by
  obtain ⟨Q, hQ, hQσ⟩ :=
    exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_pos (n := n) (M := M)
      (k - m)
  have hQslit (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
      classicalPrincipalSymbol (k - m) Q x ξ ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (Complex.pos_iff.1 (hQσ x ξ hξ)).1)
  have hk : m + (k - m) = k := by ring
  have hPQ := comp_mem_classicalPseudodifferentialOperators hP hQ
  have hPQe := hPe.comp hP hQ (isClassicalElliptic_of_mem_slitPlane hQslit)
  rw [hk] at hPQ hPQe
  refine ⟨P ∘ₗ Q, hPQ, hPQe, fun s t ↦ ?_⟩
  -- The extension of `P ∘ Q` to `H^t(M)` has the index of that of `P` to `H^{t - (k - m)}(M)`.
  have h := hPe.index_chartSobolevExtension_comp_of_mem_slitPlane hP hQ hQslit hψ hψ hφ t
  rw [show t - (k - m) - m = t - k by ring] at h
  rw [h, ← hPe.index_chartSobolevExtension_eq hP hψ hφ s (t - (k - m)),
    show t - (k - m) - m = t - k by ring]

end TauCeti
