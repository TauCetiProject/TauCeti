/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.FinTwo

/-!
# Checks of the explicit polar decomposition of `SL(2, ℂ)`

* At `g = 1`, `H = 1` and `P = (H + 1) / √(tr H + 2) = 2 / 2 = 1`, and the normalized-segment
  deformation fixes `1` at every time.
* For `g = diag(2, 1/2)`, `H = diag(4, 1/4)`, `√(tr H + 2) = 5/2` and `P = diag(2, 1/2) = g`, with
  `P² = H` and `det P = 1`; the unitary factor of the positive matrix `g` is `1`.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped unitInterval MatrixOrder ComplexOrder

namespace TauCeti.PolarFinTwoExample

/-! ### The identity -/

example : (√(RCLike.re (1 : Matrix (Fin 2) (Fin 2) ℂ).trace + 2))⁻¹ •
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) + 1) = 1 := by
  rw [trace_one, Fintype.card_fin, Nat.cast_ofNat, RCLike.ofNat_re,
    show (2 + 2 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two, ← two_smul ℝ, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

example (s : I) : polarSegmentHomotopy ℂ (s, 1) = 1 :=
  (polarSegmentHomotopy ℂ).eq_fst s ⟨1, map_one _⟩

/-! ### The diagonal matrix `diag(2, 1/2)` -/

/-- The diagonal matrix `diag(2, 1/2)` of `SL(2, ℂ)`. -/
noncomputable def diagTwoHalf : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![2, 0; 0, 1 / 2], by norm_num [det_fin_two_of]⟩

/-- The matrix of `diag(2, 1/2)`. -/
theorem coe_diagTwoHalf :
    (diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ) = !![2, 0; 0, 1 / 2] :=
  (rfl)

/-- `diag(2, 1/2)` is Hermitian. -/
theorem star_diagTwoHalf :
    star (diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ) = !![2, 0; 0, 1 / 2] := by
  rw [coe_diagTwoHalf, star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- For `g = diag(2, 1/2)`, `H = gᴴ g = diag(4, 1/4)`. -/
theorem star_mul_self_diagTwoHalf :
    star (diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ) * (diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ) =
      !![4, 0; 0, 1 / 4] := by
  rw [star_diagTwoHalf, coe_diagTwoHalf, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

example : √(RCLike.re (!![4, 0; 0, 1 / 4] : Matrix (Fin 2) (Fin 2) ℂ).trace + 2) = 5 / 2 := by
  rw [trace_fin_two_of, show RCLike.re (4 + 1 / 4 : ℂ) + 2 = (5 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

example : CFC.sqrt (star (diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ) *
    (diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ)) = !![2, 0; 0, 1 / 2] := by
  rw [sqrt_star_mul_self_fin_two, star_mul_self_diagTwoHalf, trace_fin_two_of,
    show RCLike.re (4 + 1 / 4 : ℂ) + 2 = (5 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

example : (!![2, 0; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℂ) * !![2, 0; 0, 1 / 2] =
    !![4, 0; 0, 1 / 4] ∧ (!![2, 0; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [mul_apply, Fin.sum_univ_two]
  · norm_num [det_fin_two_of]

example : (polarRetraction (Fin 2) ℂ diagTwoHalf : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [coe_polarRetraction_fin_two, mul_assoc, star_mul_self_diagTwoHalf, trace_fin_two_of,
    show RCLike.re (4 + 1 / 4 : ℂ) + 2 = (5 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
    show RCLike.re (4 + 1 / 4 : ℂ) = 17 / 4 by norm_num, coe_diagTwoHalf, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

end TauCeti.PolarFinTwoExample
