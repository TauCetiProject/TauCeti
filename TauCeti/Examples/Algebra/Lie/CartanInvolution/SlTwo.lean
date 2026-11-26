/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Matrix
public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose
import TauCeti.Algebra.Lie.GeneralLinear.Radical
import TauCeti.Algebra.Lie.Sl2.Killing

/-!
# Cartan involutions of `𝔰𝔩₂(ℝ)` and of an abelian Lie algebra

Worked examples: the Cartan involution `X ↦ -Xᵀ` of `𝔰𝔩₂(ℝ)`, its `𝔨`/`𝔭` decomposition and
twisted Killing form, and two non-examples.

* On `𝔰𝔩₂(ℝ)` with `θ X = -Xᵀ`: `𝔨` is `𝔰𝔬(2)` (the skew-symmetric matrices), `𝔭` the symmetric
  trace-zero matrices, `B(X, Y) = 4 tr(XY)` (`TauCeti.killingForm_slFinTwo_apply`), and
  `B_θ(X, X) = 4 tr(XXᵀ) > 0` for `X ≠ 0`.
* `θ = 1` is not a Cartan involution of `𝔰𝔩₂(ℝ)`: `B_θ(H, H) = -B(H, H) = -8 < 0` for
  `H = diag(1, -1)`.
* No involution of the abelian Lie algebra `ℝ` is a Cartan involution, because its Killing form
  vanishes (`LieEquiv.IsCartanInvolution.not_isLieAbelian`).
-/

public section

open LieAlgebra LieAlgebra.SpecialLinear Matrix

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Cartan involution `X ↦ -Xᵀ` of `𝔰𝔩₂(ℝ)`. -/
local notation "θ₂" =>
  LieSubalgebra.restrictNegConjTranspose (sl (Fin 2) ℝ) fun _ ↦ conjTranspose_mem_sl

/-- `X ↦ -Xᵀ` is a Cartan involution of `𝔰𝔩₂(ℝ)`. -/
example : (θ₂).IsCartanInvolution :=
  LieSubalgebra.isCartanInvolution_restrictNegConjTranspose _ _

/-- **`𝔨 = 𝔰𝔬(2)`**: the fixed subalgebra of `X ↦ -Xᵀ` on `𝔰𝔩₂(ℝ)` is the skew-symmetric
matrices. -/
theorem mem_fixedSubalgebra_slFinTwo_negTranspose_iff {X : sl (Fin 2) ℝ} :
    X ∈ (θ₂).toLieHom.fixedSubalgebra ↔
      (X : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = -(X : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [LieSubalgebra.mem_fixedSubalgebra_restrictNegConjTranspose_iff,
    conjTranspose_eq_transpose_of_trivial]

/-- **`𝔭` is the symmetric trace-zero matrices**: the `-1`-eigenspace of `X ↦ -Xᵀ` on
`𝔰𝔩₂(ℝ)`. -/
theorem mem_cartanP_slFinTwo_negTranspose_iff {X : sl (Fin 2) ℝ} :
    X ∈ (θ₂).cartanP ↔ (X : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = (X : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff, conjTranspose_eq_transpose_of_trivial]

/-- The Killing form of `𝔰𝔩₂(ℝ)` is `B(X, Y) = 4 tr(XY)`. -/
example (X Y : sl (Fin 2) ℝ) :
    killingForm ℝ (sl (Fin 2) ℝ) X Y =
      4 * ((X : Matrix (Fin 2) (Fin 2) ℝ) * (Y : Matrix (Fin 2) (Fin 2) ℝ)).trace :=
  killingForm_slFinTwo_apply X Y

/-- The twisted Killing form of `X ↦ -Xᵀ` on `𝔰𝔩₂(ℝ)` is `B_θ(X, X) = 4 tr(XXᵀ)`. -/
theorem twistedKillingForm_slFinTwo_negTranspose_apply_self (X : sl (Fin 2) ℝ) :
    (θ₂).twistedKillingForm X X =
      4 * ((X : Matrix (Fin 2) (Fin 2) ℝ) * (X : Matrix (Fin 2) (Fin 2) ℝ)ᵀ).trace := by
  simp [LieEquiv.twistedKillingForm_apply, killingForm_slFinTwo_apply,
    conjTranspose_eq_transpose_of_trivial]

/-- `B_θ(X, X) = 4 tr(XXᵀ) > 0` for nonzero `X ∈ 𝔰𝔩₂(ℝ)`. -/
example {X : sl (Fin 2) ℝ} (hX : X ≠ 0) :
    0 < 4 * ((X : Matrix (Fin 2) (Fin 2) ℝ) * (X : Matrix (Fin 2) (Fin 2) ℝ)ᵀ).trace := by
  rw [← twistedKillingForm_slFinTwo_negTranspose_apply_self]
  exact (LieSubalgebra.isCartanInvolution_restrictNegConjTranspose _ _).posDef_twistedKillingForm
    X hX

/-- **`θ = 1` is not a Cartan involution of `𝔰𝔩₂(ℝ)`**: for `H = diag(1, -1)`,
`B_θ(H, H) = -B(H, H) = -8 < 0`. -/
theorem not_isCartanInvolution_refl_slFinTwo :
    ¬ (LieEquiv.refl : sl (Fin 2) ℝ ≃ₗ⁅ℝ⁆ sl (Fin 2) ℝ).IsCartanInvolution := fun h ↦ by
  have := h.killingForm_apply_apply_neg ((slFinTwoBasis ℝ).ne_zero 2)
  rw [LieEquiv.refl_apply, killingForm_slFinTwoBasis] at this
  norm_num at this

/-- **No involution of the abelian Lie algebra `ℝ` is a Cartan involution**: its Killing form
vanishes. -/
theorem not_isCartanInvolution_real (θ : ℝ ≃ₗ⁅ℝ⁆ ℝ) : ¬ θ.IsCartanInvolution :=
  fun h ↦ h.not_isLieAbelian (isMulCommutative_iff_isLieAbelian.mp inferInstance)

end TauCeti
