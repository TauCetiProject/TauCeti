/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Negative-norm-squared formulas on `L²` products and subsingleton spaces

Records `QuadraticForm.withLpProd_eq_neg_norm_sq`, showing that an orthogonal-sum quadratic form
`Q (v, w) = Q₁ v + Q₂ w` on `WithLp 2 (V × W)` equals `-‖x‖ ^ 2` when `Q₁` and `Q₂` do, and
`QuadraticForm.eq_neg_norm_sq_of_subsingleton`, showing that any quadratic form on a subsingleton
seminormed real module equals `-‖u‖ ^ 2`.

## Main results

* `QuadraticForm.withLpProd_eq_neg_norm_sq`: `L²` negative-norm-squared formula on
  `WithLp 2 (V × W)`.
* `QuadraticForm.eq_neg_norm_sq_of_subsingleton`: any quadratic form on a subsingleton seminormed
  real module satisfies `Q u = -‖u‖ ^ 2`.
-/

public section

namespace QuadraticForm

/-- Any quadratic form on a subsingleton seminormed real module satisfies `Q u = -‖u‖ ^ 2`. -/
theorem eq_neg_norm_sq_of_subsingleton
    {U : Type*} [SeminormedAddCommGroup U] [Module ℝ U] [Subsingleton U]
    (Q : QuadraticForm ℝ U) (u : U) : Q u = -‖u‖ ^ 2 := by
  simp [Subsingleton.elim u 0]

/-- If `Q` on `WithLp 2 (V × W)` decomposes as `Q (v, w) = Q₁ v + Q₂ w` with `Q₁ v = -‖v‖ ^ 2`
and `Q₂ w = -‖w‖ ^ 2`, then `Q x = -‖x‖ ^ 2`. -/
theorem withLpProd_eq_neg_norm_sq
    {V W : Type*} [SeminormedAddCommGroup V] [Module ℝ V]
    [SeminormedAddCommGroup W] [Module ℝ W]
    {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (x : WithLp 2 (V × W)) : Q x = -‖x‖ ^ 2 := by
  rw [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

end QuadraticForm
