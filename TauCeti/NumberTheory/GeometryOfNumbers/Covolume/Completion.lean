/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.Covolume.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Archimedean bounds for completed Gram determinants

A covolume bound for a family in rational coordinates, together with squared-length bounds
for the additional vectors in those coordinates, controls every field conjugate of the
ordinary Gram determinant of the enlarged family. This lets a product-formula argument use
that determinant as a single complex number, without requiring field automorphisms to
commute with complex conjugation.

The completion estimate is the archimedean step of `New.TwistedLattice.covolume_add_index_nonneg`
in `New/Reduction/Lattices/TwistedLattice.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open scoped ComplexOrder InnerProductSpace

namespace Matrix

/-- Complete a family `y` by adjoining `z`. If the coordinates represent the inner product
by a rational positive semidefinite matrix, every field conjugate of the completed Gram
determinant is bounded by `exp (c + ∑ j, b j)`. Here `c` bounds the logarithmic squared covolume
of the first family, and `exp (b j)` bounds the squared length of each additional coordinate
vector after every field automorphism. No independence or spanning assumption is required. -/
theorem norm_map_det_gram_sumElim_le {E m n p : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Fintype m] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    {G : Matrix m m ℚ} (hG : (G.map (algebraMap ℚ ℂ)).PosSemidef) (coord : E → m → ℂ)
    (hcoord : ∀ x y, ⟪x, y⟫_ℂ = star (coord x) ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ coord y))
    {y : n → E} {z : p → E} {c : ℝ} {b : p → ℝ}
    (hy : (Matrix.of fun i j ↦ coord (y j) i).CovolumeLE G c)
    (hz : ∀ (τ : ℂ ≃+* ℂ) j, let v := τ ∘ coord (z j)
      (star v ⬝ᵥ (G.map (algebraMap ℚ ℂ) *ᵥ v)).re ≤ Real.exp (b j)) (σ : ℂ ≃+* ℂ) :
    ‖σ (Matrix.gram ℂ (Sum.elim y z)).det‖ ≤ Real.exp (c + ∑ j, b j) := by
  let A : Matrix m n ℂ := Matrix.of fun i j ↦ coord (y j) i
  let B : Matrix m p ℂ := Matrix.of fun i j ↦ coord (z j) i
  let H := G.map (algebraMap ℚ ℂ)
  have hB : B.CovolumeLE G (∑ j, b j) := by
    apply covolumeLE_sum_of_forall_norm_diag_le hG
    intro τ j
    let v := τ ∘ coord (z j)
    have hv : (B.map τ).col j = v := (rfl)
    have hn : ‖star v ⬝ᵥ (H *ᵥ v)‖ = (star v ⬝ᵥ (H *ᵥ v)).re := by
      simpa only [Complex.ofReal_re] using
        congrArg Complex.re (Complex.norm_of_nonneg' (hG.dotProduct_mulVec_nonneg v))
    rw [conjTranspose_mul_mul_apply (B.map τ) _ (B.map τ) j j, hv, hn]
    exact hz τ j
  have hAB (j : n ⊕ p) : (fromCols A B).col j = coord (Sum.elim y z j) := by
    cases j <;> rfl
  have hgram : Matrix.gram ℂ (Sum.elim y z) = (fromCols A B)ᴴ * H * fromCols A B := by
    ext i j
    rw [Matrix.gram_apply, hcoord, conjTranspose_mul_mul_apply, hAB, hAB]
  rw [hgram]
  exact (hy.fromCols hB hG).norm_map_det_conjTranspose_mul_mul_le hG σ

end Matrix
