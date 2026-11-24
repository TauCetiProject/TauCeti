/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.HalfDiscriminant
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd
import TauCeti.LinearAlgebra.Matrix.Determinant.FromBlocks

/-!
# Nondegeneracy of the standard split forms

The standard split forms `TauCeti.splitEvenForm` and `TauCeti.splitOddForm` are nondegenerate in
the sense of `QuadraticForm.IsDiscrNondegenerate` over every commutative ring, with no
invertibility of `2`. In the basis of `M* × M` given by the dual coordinate functionals and the
coordinate vectors, the polar form of `(f, x) ↦ f x` has Gram matrix `fromBlocks 0 1 1 0`, of
determinant `±1`. The form `((f, x), z) ↦ f x + z²` is `xᵀ A x` for the block-diagonal matrix with
blocks `fromBlocks 0 1 0 0` and `1`, so its half-discriminant is `det (fromBlocks 0 1 1 0) * 1`.

## Main results

* `TauCeti.isDiscrNondegenerate_splitEvenForm`: the standard split even form is nondegenerate.
* `TauCeti.isDiscrNondegenerate_splitOddForm`: the standard split odd form is nondegenerate.

## References

* B. Conrad, *Reductive group schemes*, Appendix C.1.
-/

public section

open Module Matrix QuadraticForm

namespace TauCeti

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The standard split even form is nondegenerate over every commutative ring. -/
theorem isDiscrNondegenerate_splitEvenForm : IsDiscrNondegenerate (splitEvenForm K n) := by
  rw [isDiscrNondegenerate_iff_of_even (splitEvenDualBasis K n) (by simp), polarDiscr_def,
    toMatrix_polarBilin_splitEvenForm]
  simpa using isUnit_neg_one.pow n

/-- The standard split odd form is nondegenerate over every commutative ring. -/
theorem isDiscrNondegenerate_splitOddForm : IsDiscrNondegenerate (splitOddForm K n) := by
  let B : LinearMap.BilinForm K (SplitOddSpace K n) :=
    LinearMap.mk₂ K (fun u v => u.1.1 v.1.2 + u.2 * v.2) (by intros; simp; ring)
      (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
  have hB : B.toQuadraticMap = splitOddForm K n := by ext; simp [B]
  let b := (splitEvenDualBasis K n).prod (Basis.singleton Unit K)
  rw [isDiscrNondegenerate_iff_of_odd b (by simp [Fintype.card_sum, ← two_mul]),
    halfDiscr_eq_halfDet b hB]
  have hM : LinearMap.BilinForm.toMatrix b B =
      fromBlocks (fromBlocks 0 1 0 0) 0 0 (of fun _ _ => 1) := by
    ext ((i | i) | i) ((j | j) | j) <;>
      simp [b, B, LinearMap.BilinForm.toMatrix_apply, Matrix.one_apply, Pi.single_apply]
  rw [hM, halfDet_fromBlocks_zero₁₂_zero₂₁ (by simp), halfDet_unique,
    fromBlocks_transpose, fromBlocks_add]
  simpa using isUnit_neg_one.pow n

end TauCeti
