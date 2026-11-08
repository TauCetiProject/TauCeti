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

The Gram determinant of two vectors, with inner products valued in a commutative ring, is
`<u, u> * <v, v> - <u, v> * <v, u>`.  Over the reals this is
`<u, u> * <v, v> - <u, v> ^ 2`, the squared area of the parallelogram spanned by the pair and the
denominator in the definition of sectional curvature.

The results here specialize Mathlib's general Gram-matrix API to a pair, exposing the explicit
formula without introducing a second notion of Gram determinant.  The real Gram determinant
`‖u‖² ‖v‖² - ⟪u, v⟫²` of a pair is also differentiated as a function of the pair
(`TauCeti.hasStrictFDerivAt_sq_sub_inner_sq`); in mechanics it is the squared angular momentum
`ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` of a phase-space point `(q, p)`.  Replacing the pair by
`(a q + b p, c q + d p)` multiplies it by `(a d - b c)²`
(`TauCeti.sq_sub_inner_sq_smul_add_smul`), so changes with `a d - b c = ±1` preserve it.
-/

public section

open scoped InnerProductSpace Matrix

namespace Matrix

/-- The Gram determinant of a pair, for inner products valued in a commutative ring. -/
theorem det_gram_fin_two {𝕜 E : Type*} [CommRing 𝕜] [Inner 𝕜 E] (u v : E) :
    (gram 𝕜 ![u, v]).det =
      inner 𝕜 u u * inner 𝕜 v v - inner 𝕜 u v * inner 𝕜 v u := by
  simp [det_fin_two]

/-- The Gram determinant of a pair in a real inner-product space is its squared parallelogram
area. -/
theorem real_det_gram_fin_two {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) :
    (gram ℝ ![u, v]).det = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
  rw [det_gram_fin_two, real_inner_comm v u, pow_two]

end Matrix

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The partial gradients of the real Gram determinant `G(q, p) = ‖q‖² ‖p‖² - ⟪q, p⟫²` of a pair
are `∇_q G = 2 ‖p‖² q - 2 ⟪q, p⟫ p` and `∇_p G = 2 ‖q‖² p - 2 ⟪q, p⟫ q`, as a strict derivative. -/
theorem hasStrictFDerivAt_sq_sub_inner_sq (x : V × V) :
    HasStrictFDerivAt (fun y : V × V ↦ ‖y.1‖ ^ 2 * ‖y.2‖ ^ 2 - ⟪y.1, y.2⟫_ℝ ^ 2)
      ((innerSL ℝ ((2 * ‖x.2‖ ^ 2) • x.1 - (2 * ⟪x.1, x.2⟫_ℝ) • x.2)).coprod
        (innerSL ℝ ((2 * ‖x.1‖ ^ 2) • x.2 - (2 * ⟪x.1, x.2⟫_ℝ) • x.1))) x := by
  have h1 := (hasStrictFDerivAt_norm_sq x.1).comp x (hasStrictFDerivAt_fst (p := x))
  have h2 := (hasStrictFDerivAt_norm_sq x.2).comp x (hasStrictFDerivAt_snd (p := x))
  have h12 := (hasStrictFDerivAt_fst (p := x)).inner ℝ (hasStrictFDerivAt_snd (p := x))
  refine ((h1.mul h2).sub (h12.pow 2)).congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [real_inner_comm]
  ring

/-- Replacing a pair `(q, p)` by `(a q + b p, c q + d p)` multiplies its real Gram determinant
`‖q‖² ‖p‖² - ⟪q, p⟫²` by the square of the determinant `a d - b c` of the change of basis. -/
theorem sq_sub_inner_sq_smul_add_smul (a b c d : ℝ) (q p : V) :
    ‖a • q + b • p‖ ^ 2 * ‖c • q + d • p‖ ^ 2 - ⟪a • q + b • p, c • q + d • p⟫_ℝ ^ 2 =
      (a * d - b * c) ^ 2 * (‖q‖ ^ 2 * ‖p‖ ^ 2 - ⟪q, p⟫_ℝ ^ 2) := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm q p]
  ring

end TauCeti
