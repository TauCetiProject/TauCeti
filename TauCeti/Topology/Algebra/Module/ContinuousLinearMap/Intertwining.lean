/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Intertwining linear maps up to continuous errors

A linear map `T : E →ₗ[R] F` between topological modules, possibly discontinuous, is
intertwined by continuous linear maps `Q` on `F` and `P` on `E` up to a continuous error when
`Q ∘ T - T ∘ P` is continuous. This file shows that such intertwining pairs are closed under
taking products.

## Main results

* `LinearMap.continuous_comp_sub_comp_of_continuous_sub`: products of maps intertwining `T`
  up to continuous errors again intertwine `T` up to a continuous error.
-/

public section

namespace LinearMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- If continuous linear maps `Q n` on `F` intertwine `T` with continuous linear maps `P n` on
`E` up to continuous errors `Q n ∘ T - T ∘ P n`, then so do the products
`V n = Q 0 ∘ ⋯ ∘ Q (n - 1)` and `U n = P 0 ∘ ⋯ ∘ P (n - 1)`. -/
theorem continuous_comp_sub_comp_of_continuous_sub (T : E →ₗ[R] F) (P : ℕ → E →L[R] E)
    (Q : ℕ → F →L[R] F)
    (hPQ : ∀ n, Continuous ((Q n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (P n : E →ₗ[R] E)))
    {U : ℕ → E →L[R] E} (hU0 : U 0 = ContinuousLinearMap.id R E)
    (hU : ∀ n, U (n + 1) = (U n).comp (P n)) {V : ℕ → F →L[R] F}
    (hV0 : V 0 = ContinuousLinearMap.id R F) (hV : ∀ n, V (n + 1) = (V n).comp (Q n)) (n : ℕ) :
    Continuous ((V n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[R] E)) := by
  induction n with
  | zero =>
    have : (V 0 : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U 0 : E →ₗ[R] E) = 0 := by
      ext
      simp [hV0, hU0]
    rw [this]
    exact continuous_zero
  | succ n ih =>
    have : (V (n + 1) : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U (n + 1) : E →ₗ[R] E) =
        (V n : F →ₗ[R] F) ∘ₗ ((Q n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (P n : E →ₗ[R] E)) +
          ((V n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[R] E)) ∘ₗ (P n : E →ₗ[R] E) := by
      ext
      simp [hV, hU]
    have h₁ : Continuous ((V n : F →ₗ[R] F) ∘ₗ
        ((Q n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (P n : E →ₗ[R] E))) :=
      (V n).continuous.comp (hPQ n)
    have h₂ : Continuous (((V n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[R] E)) ∘ₗ
        (P n : E →ₗ[R] E)) :=
      ih.comp (P n).continuous
    rw [this]
    exact h₁.add h₂

end LinearMap
