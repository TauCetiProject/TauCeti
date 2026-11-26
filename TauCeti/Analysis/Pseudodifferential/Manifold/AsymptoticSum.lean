/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.PatchedQuantization
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Analysis.Pseudodifferential.AsymptoticSum

/-!
# Asymptotic summation of classical pseudodifferential operators on a manifold

Let `M` be a σ-compact manifold modelled on `ℝⁿ`, for instance a compact one, and let `Pₖ` be
classical pseudodifferential operators of orders `m - k` on `M`
(`TauCeti.classicalPseudodifferentialOperators`). Although the
series `∑ₖ Pₖ` need not converge, it has an **asymptotic sum**: a classical pseudodifferential
operator `Q` of order `m` such that for every `N` the remainder `Q - ∑_{k < N} Pₖ` has order
`m - N` (`TauCeti.exists_forall_sub_sum_mem_classicalPseudodifferentialOperators`). It is unique
modulo operators of order `-∞`: another operator `Q'` is an asymptotic sum of the `Pₖ` exactly when
`Q' - Q` has order `-∞`
(`TauCeti.forall_sub_sum_mem_classicalPseudodifferentialOperators_iff`).

The construction follows Hörmander (III, Proposition 18.1.3) chart by chart. With a locally
finite family of charts and cutoffs fixed once and for all, every `Pₖ` is a patched quantization
`∑ᵢ Op_{eᵢ}(aₖᵢ)` modulo order `-∞`
(`TauCeti.exists_sub_patchedQuantization_mem_smoothingPseudodifferentialOperators`). In each chart
the classical symbols `aₖᵢ` of orders `m - k` have an asymptotic sum `bᵢ` with classical remainders
(`TauCeti.ClassicalSymbol.exists_asymptoticSum`), and `Q = ∑ᵢ Op_{eᵢ}(bᵢ)`. The patched
quantization only depends on the full symbols, additively
(`TauCeti.patchedQuantization_eq_add`), so `Q - ∑_{k < N} Pₖ` is the patched quantization of the
remainders, of order `m - N`, plus operators of order `-∞`. On a noncompact manifold the family
of charts is infinite but locally finite, and the patched quantizations are properly supported as
locally finite sums.

The main application is the **Neumann series**: if `R` has order `-1`, then `1 - R` has an inverse
modulo operators of order `-∞` on both sides
(`TauCeti.exists_one_sub_mul_sub_one_mem_smoothingPseudodifferentialOperators`), constructed as an
asymptotic sum of the powers `Rᵏ` (`TauCeti.pow_mem_classicalPseudodifferentialOperators`). This
is the step that turns a parametrix modulo order `-1`, obtained by quantizing the inverse of the
principal symbol of an elliptic operator, into a parametrix modulo operators of order `-∞`.

## Main results

* `TauCeti.exists_forall_sub_sum_mem_classicalPseudodifferentialOperators`: on a σ-compact
  manifold, classical pseudodifferential operators of orders `m - k` have an asymptotic sum of
  order `m`.
* `TauCeti.forall_sub_sum_mem_classicalPseudodifferentialOperators_iff`: asymptotic sums are unique
  modulo operators of order `-∞`.
* `TauCeti.exists_one_sub_mul_sub_one_mem_smoothingPseudodifferentialOperators`: on a σ-compact
  manifold, `1 - R` is invertible modulo operators of order `-∞` for every `R` of order `-1`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3
  (asymptotic summation) and §18.1 (operators on manifolds).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§4 and 8.
-/

public section

open Finset
open scoped ContDiff Manifold Distributions SchwartzMap

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {m : ℝ}
  {P : ℕ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {Q Q' R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Uniqueness of asymptotic sums.** If `Q - ∑_{k < N} Pₖ` has order `m - N` for every `N`, then
the same holds for `Q'` exactly when `Q' - Q` has order `-∞`. -/
theorem forall_sub_sum_mem_classicalPseudodifferentialOperators_iff
    (hQ : ∀ N : ℕ, Q - ∑ k ∈ range N, P k ∈ classicalPseudodifferentialOperators (m - N)) :
    (∀ N : ℕ, Q' - ∑ k ∈ range N, P k ∈ classicalPseudodifferentialOperators (m - N)) ↔
      Q' - Q ∈ smoothingPseudodifferentialOperators := by
  rw [mem_smoothingPseudodifferentialOperators_iff_forall_mem m]
  refine forall_congr' fun N ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← sub_sub_sub_cancel_right Q' Q (∑ k ∈ range N, P k)]
    exact sub_mem h (hQ N)
  · rw [← sub_add_sub_cancel Q' Q (∑ k ∈ range N, P k)]
    exact add_mem h (hQ N)

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **Asymptotic summation** (Borel). On a σ-compact manifold, for instance a compact one, let
`Pₖ` be classical pseudodifferential operators of orders `m - k`. Then there is a classical
pseudodifferential operator `Q` of order `m` such that for every `N` the remainder
`Q - ∑_{k < N} Pₖ` is a classical pseudodifferential operator of order `m - N`. -/
theorem exists_forall_sub_sum_mem_classicalPseudodifferentialOperators [SigmaCompactSpace M]
    (hP : ∀ k : ℕ, P k ∈ classicalPseudodifferentialOperators (m - k)) :
    ∃ Q ∈ classicalPseudodifferentialOperators m, ∀ N : ℕ,
      Q - ∑ k ∈ range N, P k ∈ classicalPseudodifferentialOperators (m - N) := by
  -- Fixed locally finite charts, in which every `Pₖ` is `∑ᵢ Op_{eᵢ}(aₖᵢ)` modulo order `-∞`.
  obtain ⟨ι, c, φ, ψ, hS, hs⟩ :=
    exists_sub_patchedQuantization_mem_smoothingPseudodifferentialOperators (n := n) (M := M)
  have he (i : ι) : chartAt (CoordinateSpace n) (c i) ∈
      IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (c i)
  choose a ha using fun k ↦ hs _ _ (hP k)
  -- In each chart, the asymptotic sum `bᵢ ∼ ∑ₖ aₖᵢ` with classical remainders `rᵢ N`.
  choose b r hr using fun i ↦ ClassicalSymbol.exists_asymptoticSum fun k ↦ a k i
  have key (N : ℕ) :
      patchedQuantization he φ ψ b hS =
        patchedQuantization he φ ψ (fun i ↦ r i N) hS +
          ∑ k ∈ range N, patchedQuantization he φ ψ (a k) hS := by
    induction N with
    | zero =>
      rw [sum_range_zero, add_zero]
      exact patchedQuantization_congr he φ ψ b hS fun i ↦ by simp [hr]
    | succ N ih =>
      rw [ih, patchedQuantization_eq_add he φ ψ _ hS (b := fun i ↦ r i (N + 1)) (c := a N)
        fun i ↦ by rw [hr, hr, sum_range_succ]; abel, sum_range_succ]
      abel
  refine ⟨patchedQuantization he φ ψ b hS,
    patchedQuantization_mem_classicalPseudodifferentialOperators he φ ψ b hS, fun N ↦ ?_⟩
  -- The remainder is the patched quantization of the `rᵢ N`, minus operators of order `-∞`.
  rw [key N, add_sub_assoc, ← sum_sub_distrib]
  refine add_mem (patchedQuantization_mem_classicalPseudodifferentialOperators he φ ψ _ hS)
    (Submodule.sum_mem _ fun k _ ↦ ?_)
  have hk := neg_mem
    (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (m - N) (ha k))
  rwa [neg_sub] at hk

/-- **The Neumann series modulo order `-∞`.** On a σ-compact manifold, for instance a compact one,
if `R` is a classical pseudodifferential operator of order `-1`, then `1 - R` is invertible modulo
operators of order `-∞`: there is a classical pseudodifferential operator `S` of order `0` such
that `(1 - R) S - 1` and `S (1 - R) - 1` have order `-∞`. -/
theorem exists_one_sub_mul_sub_one_mem_smoothingPseudodifferentialOperators [SigmaCompactSpace M]
    (hR : R ∈ classicalPseudodifferentialOperators (-1)) :
    ∃ S ∈ classicalPseudodifferentialOperators 0,
      (1 - R) * S - 1 ∈ smoothingPseudodifferentialOperators ∧
        S * (1 - R) - 1 ∈ smoothingPseudodifferentialOperators := by
  have hpow (k : ℕ) : R ^ k ∈ classicalPseudodifferentialOperators (0 - k) := by
    simpa using pow_mem_classicalPseudodifferentialOperators hR k
  obtain ⟨S, hS, hSN⟩ := exists_forall_sub_sum_mem_classicalPseudodifferentialOperators hpow
  have h1R : 1 - R ∈ classicalPseudodifferentialOperators 0 :=
    sub_mem (by simpa [Module.End.one_eq_id] using id_mem_classicalPseudodifferentialOperators)
      (classicalPseudodifferentialOperators_le 1 (by norm_num) hR)
  -- With `S_N = ∑_{k < N} Rᵏ`, `(1 - R) S_N = S_N (1 - R) = 1 - R^N`, so `(1 - R) S - 1` is
  -- `(1 - R) (S - S_N) - R^N` and `S (1 - R) - 1` is `(S - S_N) (1 - R) - R^N`, both of order
  -- `-N`.
  refine ⟨S, hS, (mem_smoothingPseudodifferentialOperators_iff_forall_mem 0).2 fun N ↦ ?_,
    (mem_smoothingPseudodifferentialOperators_iff_forall_mem 0).2 fun N ↦ ?_⟩
  · rw [show (1 - R) * S - 1 = (1 - R) * (S - ∑ k ∈ range N, R ^ k) - R ^ N by
      rw [mul_sub, mul_neg_geom_sum]; abel]
    refine sub_mem ?_ (hpow N)
    simpa [Module.End.mul_eq_comp] using comp_mem_classicalPseudodifferentialOperators h1R (hSN N)
  · rw [show S * (1 - R) - 1 = (S - ∑ k ∈ range N, R ^ k) * (1 - R) - R ^ N by
      rw [sub_mul, geom_sum_mul_neg]; abel]
    refine sub_mem ?_ (hpow N)
    simpa [Module.End.mul_eq_comp] using comp_mem_classicalPseudodifferentialOperators (hSN N) h1R

end TauCeti
