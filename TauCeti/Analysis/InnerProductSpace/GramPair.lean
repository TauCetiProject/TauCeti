/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gram determinants of pairs

The Gram determinant of two vectors over an `RCLike` field is
`<u, u> * <v, v> - <u, v> * <v, u>`.  Over the reals this is
`<u, u> * <v, v> - <u, v> ^ 2`, the squared area of the parallelogram spanned by the pair and the
denominator in the definition of sectional curvature.

The results here specialize Mathlib's general Gram-matrix API to a pair, exposing the explicit
formula without introducing a second notion of Gram determinant.  The real Gram determinant
`‖u‖² ‖v‖² - ⟪u, v⟫²` of a pair is also differentiated as a function of the pair
(`TauCeti.hasFDerivAt_sq_sub_inner_sq`); in mechanics it is the squared angular momentum
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` of a phase-space point `(q, p)`.
-/

public section

open scoped InnerProductSpace Matrix

namespace Matrix

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Gram determinant of a pair over an `RCLike` field. -/
theorem det_gram_fin_two (u v : E) :
    (gram 𝕜 ![u, v]).det =
      inner 𝕜 u u * inner 𝕜 v v - inner 𝕜 u v * inner 𝕜 v u := by
  rw [det_fin_two]
  simp [gram_apply]

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant of a pair in a real inner-product space is its squared parallelogram
area. -/
theorem real_det_gram_fin_two (u v : E) :
    (gram ℝ ![u, v]).det = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
  rw [det_gram_fin_two, real_inner_comm v u, pow_two]

end Matrix

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The partial gradients of the real Gram determinant `G(q, p) = ‖q‖² ‖p‖² - ⟪q, p⟫²` of a pair
are `∇_q G = 2 ‖p‖² q - 2 ⟪q, p⟫ p` and `∇_p G = 2 ‖q‖² p - 2 ⟪q, p⟫ q`. -/
theorem hasFDerivAt_sq_sub_inner_sq (x : V × V) :
    HasFDerivAt (fun y : V × V ↦ ‖y.1‖ ^ 2 * ‖y.2‖ ^ 2 - ⟪y.1, y.2⟫_ℝ ^ 2)
      ((innerSL ℝ ((2 * ‖x.2‖ ^ 2) • x.1 - (2 * ⟪x.1, x.2⟫_ℝ) • x.2)).coprod
        (innerSL ℝ ((2 * ‖x.1‖ ^ 2) • x.2 - (2 * ⟪x.1, x.2⟫_ℝ) • x.1))) x := by
  have h12 := (hasFDerivAt_fst (p := x)).inner ℝ (hasFDerivAt_snd (p := x))
  refine ((((hasFDerivAt_fst (p := x)).norm_sq).mul (hasFDerivAt_snd (p := x)).norm_sq).sub
    (h12.mul h12)).congr_of_eventuallyEq (.of_forall fun y ↦ by simp [sq]) |>.congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [real_inner_comm]
  ring

end TauCeti
