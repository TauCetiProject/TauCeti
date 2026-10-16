/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic

/-!
# Height bounds for coordinate ratios

The height of a ratio of two coordinates is bounded by the projective height of the tuple.
These bounds control the affine coordinates of a projective point after normalization.
Both multiplicative and logarithmic heights are treated over any field with admissible
absolute values and any finite coordinate type.

Adapted from Ralf Stephan's `ArithmeticHeights/Northcott.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/e443c2479e19f7665b31d8e94e2317c8ced1ca06/ArithmeticHeights/Northcott.lean),
commit `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).
-/

public section

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- The multiplicative height of a ratio of two coordinates is at most the height of the tuple.
The denominator may vanish, with division interpreted as the field's totalized division. -/
lemma mulHeight₁_div_le_mulHeight (x : ι → K) (i j : ι) :
    mulHeight₁ (x i / x j) ≤ mulHeight x := by
  rw [mulHeight₁_div_eq_mulHeight]
  simpa only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq] using mulHeight_comp_le ![i, j] x

/-- The logarithmic height of a ratio of two coordinates is at most the height of the tuple. -/
lemma logHeight₁_div_le_logHeight (x : ι → K) (i j : ι) :
    logHeight₁ (x i / x j) ≤ logHeight x := by
  rw [logHeight₁_div_eq_logHeight]
  simpa only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq] using logHeight_comp_le ![i, j] x

end Height
