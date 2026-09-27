/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gram determinants of pairs

The Gram determinant of two vectors in a real inner-product space is
`<u, u> * <v, v> - <u, v> ^ 2`.  It is strictly positive exactly when the vectors are linearly
independent.  This is the squared area of the parallelogram spanned by the pair, and is the
denominator in the definition of sectional curvature.

The results here specialize Mathlib's general Gram-matrix API to a pair, exposing the explicit
formula and its positivity criterion without introducing a second notion of Gram determinant.
-/

public section

open scoped InnerProductSpace Matrix

namespace Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant of a pair is its squared parallelogram area. -/
theorem det_gram_fin_two (u v : E) :
    (gram ℝ ![u, v]).det = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
  rw [det_fin_two]
  simp only [gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, pow_two]
  rw [real_inner_comm v u]

/-- The Gram determinant of a pair is positive exactly when the pair is linearly independent. -/
theorem det_gram_fin_two_pos_iff_linearIndependent (u v : E) :
    0 < (gram ℝ ![u, v]).det ↔ LinearIndependent ℝ ![u, v] := by
  constructor
  · exact fun h => linearIndependent_of_det_gram_ne_zero h.ne'
  · exact fun h => (posDef_gram_of_linearIndependent h).det_pos

/-- The explicit squared-area expression is positive exactly for a linearly independent pair. -/
theorem inner_mul_inner_sub_sq_pos_iff_linearIndependent (u v : E) :
    0 < inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 ↔
      LinearIndependent ℝ ![u, v] := by
  rw [← det_gram_fin_two, det_gram_fin_two_pos_iff_linearIndependent]

end Matrix
