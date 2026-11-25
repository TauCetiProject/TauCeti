/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal

/-!
# The Cartan involution of `𝔰𝔩_n(ℝ)`

The special linear Lie algebra `𝔰𝔩_{r+1}(ℝ)` is closed under transpose, which over `ℝ` is the
conjugate transpose, and it has trivial radical. So the matrix Cartan criterion
`LieSubalgebra.isCartanInvolution_restrictNegConjTranspose` makes `θ X = -Xᵀ` a Cartan involution
of `𝔰𝔩_{r+1}(ℝ)` (Knapp, Prop. 6.28). It acts by `-1` on the trace-zero diagonal matrices.

## Main results

* `TauCeti.slNegTranspose`: the involution `X ↦ -Xᵀ` of `𝔰𝔩_{r+1}(ℝ)`.
* `TauCeti.isCartanInvolution_slNegTranspose`: it is a Cartan involution.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2, Proposition 6.28.
-/

public section

open LieAlgebra.SpecialLinear Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (r : ℕ)

/-- The Cartan involution `X ↦ -Xᵀ` of `𝔰𝔩_{r+1}(ℝ)`. -/
noncomputable def slNegTranspose : sl (Fin (r + 1)) ℝ ≃ₗ⁅ℝ⁆ sl (Fin (r + 1)) ℝ :=
  (sl (Fin (r + 1)) ℝ).restrictNegConjTranspose fun _ ↦ conjTranspose_mem_sl

variable {r}

/-- The Cartan involution `slNegTranspose` is `X ↦ -Xᵀ` on the underlying matrices. -/
@[simp]
theorem coe_slNegTranspose_apply (X : sl (Fin (r + 1)) ℝ) :
    ((slNegTranspose r X : sl (Fin (r + 1)) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
      -(X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)ᵀ := by
  rw [slNegTranspose, LieSubalgebra.coe_restrictNegConjTranspose_apply,
    conjTranspose_eq_transpose_of_trivial]

variable (r) in
/-- `X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔩_{r+1}(ℝ)`. -/
theorem isCartanInvolution_slNegTranspose : (slNegTranspose r).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose _ _

/-- The Cartan involution acts on the trace-zero diagonal matrices by `-1`. -/
theorem slNegTranspose_apply_of_mem_specialLinearDiagonal {X : sl (Fin (r + 1)) ℝ}
    (hX : X ∈ specialLinearDiagonal r ℝ) : slNegTranspose r X = -X := by
  ext : 1
  rw [coe_slNegTranspose_apply, ((mem_specialLinearDiagonal_iff r ℝ X).mp hX).isSymm.eq,
    NegMemClass.coe_neg]

end TauCeti
