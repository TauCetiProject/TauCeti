/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Basic

/-!
# Matrix-valued symbols

For the `L^∞` operator norm on real matrices, a matrix-valued map is a symbol of order `ℓ` and
regularity `n` along a filter exactly when each of its entries is
(`TauCeti.isSymbolAlong_matrix_iff`). This reduces the decay of matrix quantities, such as the
inverse of the metric coefficients of an asymptotically Euclidean end, to that of their entries.
-/

public section

open scoped Matrix.Norms.Operator

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : Type*} [Fintype m]
  [Fintype n] {l : Filter E} {r : ℕ∞} {ℓ : ℝ} {A : E → Matrix m n ℝ}

/-- For the `L^∞` operator norm, a matrix-valued map is a symbol of order `ℓ` and regularity `r`
along `l` exactly when each of its entries is. -/
theorem isSymbolAlong_matrix_iff :
    IsSymbolAlong l r ℓ A ↔ ∀ i j, IsSymbolAlong l r ℓ fun x ↦ A x i j := by
  refine ⟨fun hA i j ↦
    (hA.continuousLinearMap_comp (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
      ).congr_of_eventually_nhds (.of_forall fun _ ↦ .of_forall fun x ↦
        (congrFun (LinearMap.coe_toContinuousLinearMap' _) (A x)).trans
          (Matrix.entryLinearMap_apply ..)),
    fun hA ↦ ?_⟩
  classical
  have hsum : A = fun x ↦ ∑ i, ∑ j, A x i j • Matrix.single i j (1 : ℝ) := by
    funext x
    conv_lhs => rw [Matrix.matrix_eq_sum_single (A x)]
    simp [Matrix.smul_single]
  rw [hsum]
  exact IsSymbolAlong.sum fun i _ ↦ IsSymbolAlong.sum fun j _ ↦ by
    simpa using (hA i j).smul (isSymbolAlong_const (Matrix.single i j (1 : ℝ)))

end TauCeti
