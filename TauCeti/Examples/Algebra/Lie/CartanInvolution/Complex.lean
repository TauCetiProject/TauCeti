/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Complex
public import TauCeti.Algebra.Lie.RestrictScalars
public import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Algebra.Lie.Sl2.Killing
import TauCeti.Algebra.Lie.SpecialLinear.ConjTranspose

/-!
# The Cartan involution `X ↦ -X*` of `𝔰𝔩₂(ℂ)` viewed as real

On `𝔰𝔩₂(ℂ)`, viewed as a real Lie algebra, `θ(X) = -X*` (minus the conjugate transpose) is a
conjugate-linear involutive automorphism with `Re B_ℂ(X, θ X) = -4 tr(X X*) < 0` for `X ≠ 0`, so
it is a Cartan involution. Its fixed subalgebra `𝔨` is `𝔰𝔲(2)`, the skew-Hermitian trace-zero
matrices, and its `-1`-eigenspace `𝔭 = i 𝔰𝔲(2)` is the Hermitian trace-zero matrices.
-/

public section

open LieAlgebra Matrix Complex
open scoped ComplexOrder

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The involution `X ↦ -X*` of `𝔰𝔩₂(ℂ)`, as an automorphism of real Lie algebras. -/
noncomputable def slFinTwoNegConjTranspose :
    SpecialLinear.sl (Fin 2) ℂ ≃ₗ⁅ℝ⁆ SpecialLinear.sl (Fin 2) ℂ where
  toFun X := ⟨-(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ,
    neg_mem (SpecialLinear.conjTranspose_mem_sl X.property)⟩
  invFun X := ⟨-(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ,
    neg_mem (SpecialLinear.conjTranspose_mem_sl X.property)⟩
  map_add' X Y := Subtype.ext (by simp [add_comm])
  map_smul' r X := Subtype.ext (by simp [conjTranspose_smul])
  map_lie' {X Y} := Subtype.ext (by simp [Ring.lie_def, conjTranspose_mul])
  left_inv X := Subtype.ext (by simp)
  right_inv X := Subtype.ext (by simp)

/-- `slFinTwoNegConjTranspose` sends `X` to `-X*`. -/
@[simp]
theorem coe_slFinTwoNegConjTranspose_apply (X : SpecialLinear.sl (Fin 2) ℂ) :
    (slFinTwoNegConjTranspose X : Matrix (Fin 2) (Fin 2) ℂ) = -(X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
  (rfl)

/-- `X ↦ -X*` is conjugate-linear. -/
theorem slFinTwoNegConjTranspose_smul (c : ℂ) (X : SpecialLinear.sl (Fin 2) ℂ) :
    slFinTwoNegConjTranspose (c • X) = (starRingEnd ℂ) c • slFinTwoNegConjTranspose X :=
  Subtype.ext (by simp [conjTranspose_smul])

/-- `X ↦ -X*` is a Cartan involution of `𝔰𝔩₂(ℂ)` viewed as a real Lie algebra. -/
theorem isCartanInvolution_slFinTwoNegConjTranspose :
    slFinTwoNegConjTranspose.IsCartanInvolution := by
  refine LieEquiv.isCartanInvolution_of_re_killingForm_neg
    (fun X ↦ Subtype.ext (by simp)) fun X hX ↦ ?_
  have hX' : (X : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := fun h ↦ hX (Subtype.ext h)
  have hpos : 0 < ((X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace :=
    (posSemidef_self_mul_conjTranspose _).trace_nonneg.lt_of_ne
      (Ne.symm (trace_mul_conjTranspose_self_eq_zero_iff.not.2 hX'))
  rw [killingForm_slFinTwo_apply, coe_slFinTwoNegConjTranspose_apply, mul_neg, trace_neg,
    show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, re_ofReal_mul, neg_re]
  linarith [(pos_iff.1 hpos).1]

/-- The fixed subalgebra of `X ↦ -X*` is `𝔰𝔲(2)`: the skew-Hermitian matrices. -/
theorem mem_fixedSubalgebra_slFinTwoNegConjTranspose_iff {X : SpecialLinear.sl (Fin 2) ℂ} :
    X ∈ slFinTwoNegConjTranspose.toLieHom.fixedSubalgebra ↔
      (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = -(X : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, ← Subtype.coe_inj,
    coe_slFinTwoNegConjTranspose_apply, neg_eq_iff_eq_neg]

/-- The `-1`-eigenspace of `X ↦ -X*` is `i 𝔰𝔲(2)`: the Hermitian matrices. -/
theorem mem_cartanP_slFinTwoNegConjTranspose_iff {X : SpecialLinear.sl (Fin 2) ℂ} :
    X ∈ slFinTwoNegConjTranspose.cartanP ↔
      (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (X : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [LieEquiv.mem_cartanP, ← Subtype.coe_inj, coe_slFinTwoNegConjTranspose_apply,
    NegMemClass.coe_neg, neg_inj]

/-- `𝔭 = i 𝔨` for `X ↦ -X*`: `X` is Hermitian exactly when `i X` is skew-Hermitian. -/
example {X : SpecialLinear.sl (Fin 2) ℂ} :
    X ∈ slFinTwoNegConjTranspose.cartanP ↔
      I • X ∈ slFinTwoNegConjTranspose.toLieHom.fixedSubalgebra :=
  LieEquiv.mem_cartanP_iff_I_smul_mem_fixedSubalgebra slFinTwoNegConjTranspose_smul

end TauCeti
