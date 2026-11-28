/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard

/-!
# Integral Gram matrices

Whenever an integer matrix `G : Matrix ι ι ℤ` agrees after coercion to `ℝ` with the Gram matrix
`Matrix.gram ℝ v` of a finite family `v` in a real inner product space,
`(G.det : ℝ) = (Matrix.gram ℝ v).det`. Linear independence of `v` therefore yields `1 ≤ G.det`
and Hadamard's logarithmic bound `Real.log (G.det : ℝ) ≤ ∑ i, 2 * Real.log ‖v i‖`.

## Main results

* `Matrix.intCast_det_eq_det_gram`: determinant agreement between an integer matrix `G` and the
  real Gram matrix `Matrix.gram ℝ v` when `G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v`.
* `Matrix.one_le_det_of_map_eq_gram`, `Matrix.log_det_le_of_map_eq_gram`: positivity `1 ≤ G.det`
  and Hadamard's logarithmic upper bound for linearly independent `v`.
-/

public section

open scoped InnerProductSpace

namespace Matrix

/-- If an integer matrix `G` agrees after coercion to `ℝ` with `Matrix.gram ℝ v`, then their
determinants agree in `ℝ`. -/
theorem intCast_det_eq_det_gram {ι E : Type*} [Fintype ι] [DecidableEq ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {G : Matrix ι ι ℤ} {v : ι → E}
    (hG : G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v) :
    (G.det : ℝ) = (Matrix.gram ℝ v).det := by
  rw [← hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]

/-- An integer matrix matching the Gram matrix of a linearly independent real family has
determinant at least `1`. -/
theorem one_le_det_of_map_eq_gram {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {G : Matrix ι ι ℤ} {v : ι → E}
    (hG : G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v) (hv : LinearIndependent ℝ v) :
    1 ≤ G.det := by
  have hpos : (0 : ℝ) < (G.det : ℝ) :=
    intCast_det_eq_det_gram hG ▸ Matrix.det_gram_pos_iff.mpr hv
  exact Int.add_one_le_of_lt (by exact_mod_cast hpos)

/-- Logarithmic Hadamard bound for an integer matrix matching the Gram matrix of a linearly
independent real family. -/
theorem log_det_le_of_map_eq_gram {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {G : Matrix ι ι ℤ} {v : ι → E}
    (hG : G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v) (hv : LinearIndependent ℝ v) :
    Real.log (G.det : ℝ) ≤ ∑ i : ι, 2 * Real.log ‖v i‖ := by
  rw [intCast_det_eq_det_gram hG]
  exact Matrix.log_det_gram_le hv

end Matrix
