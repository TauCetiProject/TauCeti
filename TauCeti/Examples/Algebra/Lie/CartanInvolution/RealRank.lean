/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.CartanInvolution.RealRank
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# Real rank zero: `𝔤𝔩_n(ℝ)` and `𝔰𝔬(3)`

* `𝔤𝔩_n(ℝ)` for `n ≥ 1` has real rank `0` because it has no Cartan involution: `ad 1 = 0`, so the
  Killing form pairs `1` with everything to `0`, while a Cartan involution `θ` needs
  `B(1, θ 1) < 0`.
* `𝔰𝔬(3)` has negative definite Killing form `B(X, X) = tr(X X) = -tr(X Xᵀ)`, so it has real
  rank `0`.
-/

public section

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- `𝔤𝔩_n(ℝ)`, `n ≥ 1`, has no Cartan involution: `ad 1 = 0`. -/
theorem not_isCartanInvolution_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (θ : Matrix n n ℝ ≃ₗ⁅ℝ⁆ Matrix n n ℝ) : ¬ θ.IsCartanInvolution := fun hθ ↦ by
  have had : ad ℝ (Matrix n n ℝ) 1 = 0 := LinearMap.ext fun Y ↦ by simp [Ring.lie_def]
  have := hθ.killingForm_apply_apply_neg (x := 1) one_ne_zero
  rw [killingForm_apply_apply, had, LinearMap.zero_comp, map_zero] at this
  exact this.false

/-- `𝔤𝔩_n(ℝ)`, `n ≥ 1`, has real rank `0`, since it has no Cartan involution. -/
theorem realRank_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    realRank (Matrix n n ℝ) = 0 :=
  realRank_eq_zero_of_forall_not_isCartanInvolution not_isCartanInvolution_matrix

/-- The Killing form of `𝔰𝔬(3)` is negative definite: `B(X, X) = tr(X X) = -tr(X Xᵀ)`. -/
theorem killingForm_so_three_neg (X : Orthogonal.so (Fin 3) ℝ) (hX : X ≠ 0) :
    killingForm ℝ (Orthogonal.so (Fin 3) ℝ) X X < 0 := by
  have hX' : (X : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := fun h ↦ hX (Subtype.ext h)
  have hskew : (X : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = -X :=
    (Orthogonal.mem_so _ _ _).mp X.property
  have hpos : 0 < ((X : Matrix (Fin 3) (Fin 3) ℝ) * (X : Matrix (Fin 3) (Fin 3) ℝ)ᴴ).trace :=
    (posSemidef_self_mul_conjTranspose _).trace_nonneg.lt_of_ne
      (Ne.symm (trace_mul_conjTranspose_self_eq_zero_iff.not.2 hX'))
  rw [conjTranspose_eq_transpose_of_trivial, hskew, mul_neg, trace_neg, neg_pos] at hpos
  rw [killingForm_so_apply]
  norm_num
  exact hpos

/-- `𝔰𝔬(3)` has real rank `0`. -/
theorem realRank_so_three : realRank (Orthogonal.so (Fin 3) ℝ) = 0 :=
  realRank_eq_zero_of_killingForm_neg killingForm_so_three_neg

end TauCeti
