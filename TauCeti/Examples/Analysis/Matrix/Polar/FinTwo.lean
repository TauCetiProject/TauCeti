/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.FinTwo

/-!
# Examples of the closed-form polar decomposition of `SL(2, 𝕜)`

Two computations with the explicit polar factors of `TauCeti.Analysis.Matrix.Polar.FinTwo`, where
`√(g gᴴ) = (g gᴴ + 1) / √(tr (g gᴴ) + 2)` and the unitary factor is
`U = (g + (g⁻¹)ᴴ) / √(tr (g gᴴ) + 2)`.

* **A positive diagonal matrix (`sqrt_mul_star_diagTwoHalf`, `coe_polarRetraction_diagTwoHalf`).**
  For `g = diag(2, 1/2)`, `g gᴴ = diag(4, 1/4)` has trace `17/4`, so `√(tr (g gᴴ) + 2) = 5/2`, and
  `√(g gᴴ) = (diag(4, 1/4) + 1) / (5/2) = diag(2, 1/2) = g`, with `(√(g gᴴ)) ^ 2 = g gᴴ` and
  `det √(g gᴴ) = 1`. Accordingly `g + (g⁻¹)ᴴ = diag(5/2, 5/2)` and the unitary factor is `1`.
* **A shear (`coe_polarRetraction_shear`).** For `g = [[1, 1], [0, 1]]`, the trace of `g gᴴ` is `3`
  and `g + (g⁻¹)ᴴ = [[2, 1], [-1, 2]]`, so the unitary factor is the rotation
  `[[2, 1], [-1, 2]] / √5`, not the identity, although `g` is unipotent.
* **The identity and `-g = (-U) P`.** At `g = 1`, `P = (1 + 1) / √(tr 1 + 2) = 1`, and the
  normalized-segment deformation `Matrix.SpecialLinearGroup.polarSegmentHomotopy` fixes `1` at
  every time. The unitary factor changes sign with `g`, so `-g = (-U) P`.
* **The right positive factor of `diag(2, 1/2)`.** `H = gᴴ g = diag(4, 1/4)`, so
  `P = √H = diag(2, 1/2)`, with `P² = H` and `det P = 1`.
-/

public section

noncomputable section

open Matrix
open scoped unitInterval MatrixOrder ComplexOrder

namespace TauCeti.PolarFinTwoExample

variable {𝕜 : Type*} [RCLike 𝕜]

variable (𝕜) in
/-- The positive diagonal matrix `diag(2, 1/2)` of `SL(2, 𝕜)`. -/
def diagTwoHalf : SpecialLinearGroup (Fin 2) 𝕜 :=
  ⟨!![2, 0; 0, 1 / 2], by simp [det_fin_two_of]⟩

@[simp]
theorem coe_diagTwoHalf :
    (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) = !![2, 0; 0, 1 / 2] :=
  (rfl)

variable (𝕜) in
/-- The shear `[[1, 1], [0, 1]]` of `SL(2, 𝕜)`. -/
def shear : SpecialLinearGroup (Fin 2) 𝕜 :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩

@[simp]
theorem coe_shear : (shear 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) = !![1, 1; 0, 1] :=
  (rfl)

/-- `diag(2, 1/2)` times its conjugate transpose is `diag(4, 1/4)`. -/
theorem diagTwoHalf_mul_star :
    (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) * star (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) =
      !![4, 0; 0, 1 / 4] := by
  rw [coe_diagTwoHalf]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

/-- `√(tr (g gᴴ) + 2) = 5/2` for `g = diag(2, 1/2)`. -/
theorem sqrt_trace_diagTwoHalf_add_two :
    √(RCLike.re ((diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) *
      star (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜)).trace + 2) = 5 / 2 := by
  have h : RCLike.re ((4 : 𝕜) + 1 / 4) = 17 / 4 := by
    rw [show (4 : 𝕜) + 1 / 4 = ((17 / 4 : ℝ) : 𝕜) by push_cast; ring, RCLike.ofReal_re]
  rw [diagTwoHalf_mul_star, trace_fin_two_of, h, Real.sqrt_eq_iff_mul_self_eq (by norm_num)
    (by norm_num)]
  norm_num

/-- **The positive factor of `diag(2, 1/2)`** is the matrix itself: `√(g gᴴ) = g`. -/
theorem sqrt_mul_star_diagTwoHalf :
    CFC.sqrt ((diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) *
      star (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜)) = !![2, 0; 0, 1 / 2] := by
  rw [sqrt_mul_star_fin_two_of_norm_det_eq_one (diagTwoHalf 𝕜).norm_det_eq_one,
    sqrt_trace_diagTwoHalf_add_two, diagTwoHalf_mul_star]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [RCLike.real_smul_eq_coe_mul,
    RCLike.algebraMap_eq_ofReal, RCLike.ofReal_ofNat]

/-- **The unitary factor of `diag(2, 1/2)`** is `1`, computed from the explicit formula:
`(g + (g⁻¹)ᴴ) / (5/2) = diag(5/2, 5/2) / (5/2)`. -/
theorem coe_polarRetraction_diagTwoHalf :
    (SpecialLinearGroup.polarRetraction (Fin 2) 𝕜 (diagTwoHalf 𝕜) :
      Matrix (Fin 2) (Fin 2) 𝕜) = 1 := by
  rw [SpecialLinearGroup.coe_polarRetraction_fin_two, sqrt_trace_diagTwoHalf_add_two,
    SpecialLinearGroup.coe_inv, coe_diagTwoHalf, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [RCLike.real_smul_eq_coe_mul,
    RCLike.algebraMap_eq_ofReal, RCLike.ofReal_ofNat]

/-- The shear `[[1, 1], [0, 1]]` times its conjugate transpose is `[[2, 1], [1, 1]]`. -/
theorem shear_mul_star :
    (shear 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) * star (shear 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) =
      !![2, 1; 1, 1] := by
  rw [coe_shear]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

/-- `tr (g gᴴ) + 2 = 5` for the shear `g = [[1, 1], [0, 1]]`. -/
theorem trace_shear_mul_star :
    RCLike.re ((shear 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) *
      star (shear 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜)).trace + 2 = 5 := by
  rw [shear_mul_star, trace_fin_two_of]
  norm_num

/-- **The unitary factor of the shear** `[[1, 1], [0, 1]]` is the rotation `[[2, 1], [-1, 2]] / √5`.
-/
theorem coe_polarRetraction_shear :
    (SpecialLinearGroup.polarRetraction (Fin 2) 𝕜 (shear 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) =
      (√5)⁻¹ • !![2, 1; -1, 2] := by
  rw [SpecialLinearGroup.coe_polarRetraction_fin_two, trace_shear_mul_star,
    SpecialLinearGroup.coe_inv, coe_shear, adjugate_fin_two_of]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-! ### The identity and `-g = (-U) P` -/

example : (√(RCLike.re (1 : Matrix (Fin 2) (Fin 2) ℂ).trace + 2))⁻¹ •
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) + 1) = 1 := by
  rw [show RCLike.re (1 : Matrix (Fin 2) (Fin 2) ℂ).trace + 2 = 2 ^ 2 by simp; norm_num,
    Real.sqrt_sq zero_le_two, ← two_smul ℝ, smul_smul]
  norm_num

example (s : I) : SpecialLinearGroup.polarSegmentHomotopy ℂ (s, 1) = 1 :=
  (SpecialLinearGroup.polarSegmentHomotopy ℂ).eq_fst s ⟨1, map_one _⟩

example (g : SpecialLinearGroup (Fin 2) ℂ) :
    (SpecialLinearGroup.polarRetraction (Fin 2) ℂ (-g) : Matrix (Fin 2) (Fin 2) ℂ) =
      -(SpecialLinearGroup.polarRetraction (Fin 2) ℂ g : Matrix (Fin 2) (Fin 2) ℂ) :=
  SpecialLinearGroup.coe_polarRetraction_neg g

/-! ### The right positive factor of `diag(2, 1/2)` -/

/-- For `g = diag(2, 1/2)`, `H = gᴴ g = diag(4, 1/4)`. -/
theorem star_mul_diagTwoHalf :
    star (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) * (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) =
      !![4, 0; 0, 1 / 4] := by
  rw [coe_diagTwoHalf]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

/-- **The right positive factor of `diag(2, 1/2)`**: `P = √(gᴴ g) = diag(2, 1/2)`. -/
theorem sqrt_star_mul_diagTwoHalf :
    CFC.sqrt (star (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜) *
      (diagTwoHalf 𝕜 : Matrix (Fin 2) (Fin 2) 𝕜)) = !![2, 0; 0, 1 / 2] := by
  rw [← sqrt_mul_star_diagTwoHalf, star_mul_diagTwoHalf, diagTwoHalf_mul_star]

example : (!![2, 0; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) 𝕜) * !![2, 0; 0, 1 / 2] =
    !![4, 0; 0, 1 / 4] ∧ (!![2, 0; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) 𝕜).det = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [mul_apply, Fin.sum_univ_two]
  · norm_num [det_fin_two_of]

end TauCeti.PolarFinTwoExample
