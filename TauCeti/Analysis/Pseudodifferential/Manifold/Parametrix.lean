/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization

/-!
# Parametrices of elliptic operators on a compact manifold

Let `P` be a classical pseudodifferential operator of order `m` on a compact manifold `M` modelled
on `ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`), elliptic in the sense that its principal
symbol `σ_m(P)` vanishes at no nonzero covector (`TauCeti.IsClassicalElliptic`). This file shows
that `P` is invertible modulo operators of arbitrarily low order: for every `N : ℕ` there is a
classical pseudodifferential operator `Q` of order `-m` with

`P ∘ Q - 1 ∈ Ψ^{-N}(M)` and `Q ∘ P - 1 ∈ Ψ^{-N}(M)`

(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`).
Operators of negative order are compact between Sobolev spaces of a compact manifold, so these
parametrices are what makes an elliptic operator Fredholm. A parametrix modulo operators of order
`-∞` is the asymptotic sum of the full Neumann series `Q₀ ∑ R^k` below, whose terms `Q₀ R^k` have
order `-m - k`; this needs asymptotic summation of operators on `M` and is not done here.

The construction has two steps.

* **Inverting the principal symbol.** The inverse `σ_m(P)⁻¹` is a smooth homogeneous function of
  degree `-m` on the cotangent bundle (`TauCeti.inv_mem_homogeneousCotangentSymbols`), so on a
  compact manifold it is the principal symbol of an operator `Q₀` of order `-m`
  (`TauCeti.classicalPrincipalSymbolLinearMap_surjective`). The principal symbol of a composition
  is the product of the principal symbols (`TauCeti.classicalPrincipalSymbol_comp`) and that of the
  identity is `1` (`TauCeti.classicalPrincipalSymbol_id`), so `P Q₀ - 1` and `Q₀ P - 1` have
  vanishing principal symbol of order `0`, that is, order `-1`.
* **The Neumann series.** With `R = 1 - P Q₀` and `L = 1 - Q₀ P`, both of order `-1`, the operator
  `Q = Q₀ (1 + R + ⋯ + R^{N-1})` satisfies `P Q = 1 - R^N`. Since `Q₀ R = L Q₀`, also
  `Q = (1 + L + ⋯ + L^{N-1}) Q₀`, and `Q P = 1 - L^N`. The powers `R^N` and `L^N` have order `-N`
  (`TauCeti.pow_mem_classicalPseudodifferentialOperators`).

## Main results

* `TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`: an
  elliptic classical pseudodifferential operator of order `m` on a compact manifold has, for every
  `N : ℕ`, a two-sided parametrix of order `-m` modulo operators of order `-N`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (elliptic
  operators and their parametrices).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4.
-/

public section

noncomputable section

open Finset
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **The Neumann series.** If `Q` of order `-m` inverts `P` modulo operators of order `-1` on
both sides, then for every `N` the operator `Q (1 + R + ⋯ + R^{N-1})`, with `R = 1 - P Q`, inverts
`P` modulo operators of order `-N` on both sides. -/
private theorem exists_comp_sub_id_mem_of_comp_sub_id_mem_neg_one
    (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hPQ : P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1))
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1)) (N : ℕ) :
    ∃ Q' ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q' - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) ∧
      Q' ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) := by
  simp only [← Module.End.mul_eq_comp, ← Module.End.one_eq_id] at hPQ hQP ⊢
  -- `R = 1 - P Q` and `L = 1 - Q P` have order `-1`, and `Q R = L Q`.
  set R := 1 - P * Q
  set L := 1 - Q * P
  have hR : R ∈ classicalPseudodifferentialOperators (-1) := by simpa [R] using neg_mem hPQ
  have hL : L ∈ classicalPseudodifferentialOperators (-1) := by simpa [L] using neg_mem hQP
  have hQR : SemiconjBy Q R L := by
    simp only [SemiconjBy, R, L, mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
  -- The powers of an operator of order `-1` have order `-k`.
  have hpow {A} (hA : A ∈ classicalPseudodifferentialOperators (n := n) (M := M) (-1)) (k : ℕ) :
      A ^ k ∈ classicalPseudodifferentialOperators (-k) := by
    simpa using pow_mem_classicalPseudodifferentialOperators hA k
  refine ⟨Q * ∑ k ∈ range N, R ^ k, ?_, ?_, ?_⟩
  · rw [mul_sum]
    refine Submodule.sum_mem _ fun k _ ↦ classicalPseudodifferentialOperators_le
      (m' := -m + -k) k (by ring) ?_
    rw [Module.End.mul_eq_comp]
    exact comp_mem_classicalPseudodifferentialOperators hQ
      (hpow hR k)
  · rw [← mul_assoc, show P * Q = 1 - R by simp [R], mul_neg_geom_sum, sub_sub_cancel_left]
    exact neg_mem (hpow hR N)
  · rw [mul_sum, sum_congr rfl fun k _ ↦ (hQR.pow_right k).eq, ← sum_mul, mul_assoc,
      show Q * P = 1 - L by simp [L], geom_sum_mul_neg, sub_sub_cancel_left]
    exact neg_mem (hpow hL N)

/-- **Inverting the principal symbol.** On a compact manifold, an elliptic classical
pseudodifferential operator `P` of order `m` has an inverse modulo operators of order `-1`: an
operator `Q` of order `-m` with principal symbol `σ_m(P)⁻¹`. -/
private theorem IsClassicalElliptic.exists_comp_sub_id_mem_neg_one [CompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) ∧
      Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) := by
  have hPe' (x : M) (ξ) (hξ : ξ ≠ 0) : classicalPrincipalSymbol m P x ξ ≠ 0 :=
    isClassicalEllipticAt_iff.1 (isClassicalElliptic_iff.1 hPe x) ξ hξ
  obtain ⟨⟨Q, hQ⟩, hQs⟩ := classicalPrincipalSymbolLinearMap_surjective (n := n) (M := M)
    ⟨_, inv_mem_homogeneousCotangentSymbols classicalPrincipalSymbol_mem_homogeneousCotangentSymbols
      hPe'⟩
  have hσQ (x : M) (ξ) :
      classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ :=
    by simpa using congrFun (congrFun (congrArg Subtype.val hQs) x) ξ
  -- Both products have principal symbol `σ_m(P) σ_m(P)⁻¹ = 1`, that of the identity.
  have key (A : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (hA : A ∈ classicalPseudodifferentialOperators 0)
      (hσA : ∀ x ξ, classicalPrincipalSymbol 0 A x ξ =
        classicalPrincipalSymbol m P x ξ * (classicalPrincipalSymbol m P x ξ)⁻¹) :
      A - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) := by
    rw [show (-1 : ℝ) = 0 - 1 by norm_num]
    refine sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq hA
      id_mem_classicalPseudodifferentialOperators fun x ξ ↦ ?_
    rw [hσA]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · rw [mul_inv_cancel₀ (hPe' x ξ hξ), classicalPrincipalSymbol_id x hξ]
  refine ⟨Q, hQ, key _ ?_ fun x ξ ↦ ?_, key _ ?_ fun x ξ ↦ ?_⟩
  · simpa using comp_mem_classicalPseudodifferentialOperators hP hQ
  · have h := classicalPrincipalSymbol_comp hP hQ x ξ
    rwa [add_neg_cancel, hσQ] at h
  · simpa using comp_mem_classicalPseudodifferentialOperators hQ hP
  · have h := classicalPrincipalSymbol_comp hQ hP x ξ
    rwa [neg_add_cancel, hσQ, mul_comm] at h

/-- **Parametrices of elliptic operators.** On a compact manifold `M`, let `P` be a classical
pseudodifferential operator of order `m` that is elliptic: its principal symbol vanishes at no
nonzero covector. For every `N : ℕ` there is a classical pseudodifferential operator `Q` of order
`-m` that inverts `P` modulo operators of order `-N` on both sides: `P ∘ Q - 1` and `Q ∘ P - 1`
are classical pseudodifferential operators of order `-N`. -/
theorem IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators
    [CompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) (N : ℕ) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) ∧
      Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) := by
  obtain ⟨Q, hQ, hPQ, hQP⟩ := hPe.exists_comp_sub_id_mem_neg_one hP
  exact exists_comp_sub_id_mem_of_comp_sub_id_mem_neg_one hQ hPQ hQP N

end TauCeti
