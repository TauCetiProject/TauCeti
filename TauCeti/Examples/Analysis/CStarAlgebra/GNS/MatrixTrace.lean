/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Conjugation.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.ProductRepresentation
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace

/-!
# Checks for the GNS representation of the normalized trace on matrices

For the normalized trace `tr_n` on `M_n(ℂ)` and matrix units `e_ij` with `i ≠ j`:

* the tensor functional is `μ(e_ij ⊗ e_jiᵒᵖ) = tr_n(e_ij e_ji) = 1/n`;
* the right representation acts by right multiplication, `πᵒᵖ(e_ijᵒᵖ)[e_ii] = [e_ij]`, and the
  class `[e_ij]` is nonzero;
* the map `b ↦ J π(b) J` is conjugate linear
  (`PositiveLinearMap.gnsConj_gnsNonUnitalStarAlgHom_smul_gnsConj`) and sends `[e_ii]` to
  `[e_ii e_ij⋆] = 0` at `b = e_ij`. So it is not the right representation `πᵒᵖ` of `M_nᵐᵒᵖ`; the
  two agree only after replacing `b` by `b⋆`.

For `n = 2`, `i = 1`, `j = 2`: `πᵒᵖ(e₁₂ᵒᵖ)ê₁₁ = ê₁₂` while `J π(e₁₂) J ê₁₁ = 0`, so
`b ↦ J π(b) J` differs from `πᵒᵖ`; being conjugate linear
(`PositiveLinearMap.gnsConj_gnsNonUnitalStarAlgHom_smul_gnsConj`), it is not a representation of
`M_nᵐᵒᵖ`.
-/

public section

open MulOpposite CStarMatrix PositiveLinearMap
open scoped ComplexOrder TensorProduct

namespace TauCeti.GNSMatrixTraceExample

variable (n : Type*) [Fintype n]

/-- The normalized trace `tr_n` on `M_n(ℂ)`, as a positive linear functional. -/
noncomputable abbrev tr : CStarMatrix n n ℂ →ₚ[ℂ] ℂ :=
  (normalizedTraceMap n).toPositiveLinearMap

/-- The modular conjugation `J [a] = [a⋆]` of the GNS space of the normalized trace. -/
noncomputable abbrev J : (tr n).GNS ≃ₗᵢ⋆[ℂ] (tr n).GNS :=
  gnsConj (tr n) (normalizedTraceMap_mul_comm (n := n))

variable {n} [DecidableEq n]

/-- **The tensor functional at a pair of matrix units.** `μ(e_ij ⊗ e_jiᵒᵖ) = tr_n(e_ij e_ji) =
1/n`. -/
theorem gnsTensorFunctional_matrixUnit (i j : n) :
    (tr n).gnsTensorFunctional
      (matrixUnit i j ⊗ₜ op (matrixUnit j i)) = (Fintype.card n : ℂ)⁻¹ := by
  simp [matrixUnit_mul_matrixUnit]

/-- The class of a matrix unit in the GNS space of the normalized trace is nonzero. -/
theorem toGNS_matrixUnit_ne_zero (i j : n) :
    (tr n).toGNS (matrixUnit i j) ≠ 0 := by
  have : Nonempty n := ⟨i⟩
  rw [Ne, toGNS_eq_zero_iff]
  simp [Fintype.card_ne_zero]

/-- **The right representation is right multiplication.** `πᵒᵖ(e_ijᵒᵖ)[e_ii] = [e_ij]`. -/
theorem gnsRightNonUnitalStarAlgHom_matrixUnit (i j : n) :
    (tr n).gnsRightNonUnitalStarAlgHom normalizedTraceMap_mul_comm (op (matrixUnit i j))
      ((tr n).toGNS (matrixUnit i i)) = (tr n).toGNS (matrixUnit i j) := by
  rw [gnsRightNonUnitalStarAlgHom_apply_toGNS, matrixUnit_mul_matrixUnit]

/-- **`J π(e_ij) J` kills `[e_ii]`.** For `i ≠ j`, `J π(e_ij) J [e_ii] = [e_ii e_ji] = 0`.
Contrast `gnsRightNonUnitalStarAlgHom_matrixUnit` and `toGNS_matrixUnit_ne_zero`, which give
`πᵒᵖ(e_ijᵒᵖ)[e_ii] = [e_ij] ≠ 0`. -/
theorem gnsConj_gnsNonUnitalStarAlgHom_gnsConj_toGNS_matrixUnit_eq_zero_of_ne {i j : n}
    (h : i ≠ j) :
    J n ((tr n).gnsNonUnitalStarAlgHom
      (matrixUnit i j) (J n ((tr n).toGNS (matrixUnit i i)))) = 0 := by
  rw [gnsConj_gnsNonUnitalStarAlgHom_gnsConj_toGNS, star_matrixUnit,
    matrixUnit_mul_matrixUnit_of_ne i i h, map_zero]

end TauCeti.GNSMatrixTraceExample
