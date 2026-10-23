/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gram determinants of pairs

The Gram determinant of two vectors over an `RCLike` field is
`<u, u> * <v, v> - <u, v> * <v, u>`.  Over the reals this is
`<u, u> * <v, v> - <u, v> ^ 2`, the squared area of the parallelogram spanned by the pair and the
denominator in the definition of sectional curvature.

The results here specialize Mathlib's general Gram-matrix API to a pair, exposing the explicit
formula without introducing a second notion of Gram determinant.
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
