/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Casimir
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Basic.Complex.Basic

/-!
# The compact Cartan basis of `𝔤𝔩₂(ℂ)`

The compact Cartan basis

`H_c = -iJ`, `X_c = (A + iB) / 2`, `Y_c = (A - iB) / 2`, with `J = E₁₂ - E₂₁`, `A = diag(1, -1)`,
`B = E₁₂ + E₂₁`,

of `𝔤𝔩₂(ℂ)`, an `sl₂` triple (`[H_c, X_c] = 2X_c`, `[H_c, Y_c] = -2Y_c`, `[X_c, Y_c] = H_c`) whose
first element spans the complexified Lie algebra of `SO(2)`. Together with the identity matrix it
is a basis of `𝔤𝔩₂(ℂ)`; this file gives the coordinates in that basis, the reflection `A` of
`O(2)`, and the Casimir operator of a `𝔤𝔩₂(ℂ)`-module in this normalization.

## Main definitions

* `TauCeti.compactCartanH`, `TauCeti.compactCartanX`, `TauCeti.compactCartanY`: the compact Cartan
  basis, with `TauCeti.isSl2Triple_compactCartan`.
* `TauCeti.compactCoordH`, `TauCeti.compactCoordX`, `TauCeti.compactCoordY`,
  `TauCeti.compactCoordOne`: the coordinates in the basis `H_c, X_c, Y_c, 1`.
* `TauCeti.gl2RotationGenerator`: `J`, the generator of the rotations `r_θ = exp(θJ)`.
* `TauCeti.compactCartanReflection`: the reflection `A = diag(1, -1)`.
* `TauCeti.gl2Casimir`: the Casimir operator `Ω = (H_c² + 2X_cY_c + 2Y_cX_c) / 4` of a
  `𝔤𝔩₂(ℂ)`-module.

## Main results

* `TauCeti.eq_compactCoord`: every matrix is the combination of `H_c, X_c, Y_c, 1` with its
  coordinates; `TauCeti.compactCoordH_lie` and its siblings compute the coordinates of a bracket.
* `TauCeti.compactCoordX_compactCartanReflection_mul_mul` and its siblings: conjugation by `A`
  exchanges `X_c` and `Y_c` and negates `H_c`.
* `TauCeti.coe_gl2Casimir_lieSubmodule`: the Casimir operator of a Lie submodule is the
  restriction of that of the ambient module.

## Implementation notes

`𝔤𝔩₂(ℂ)` is `Matrix (Fin 2) (Fin 2) ℂ` with the commutator bracket, through the local instance
`LieRing.ofAssociativeRing`, as elsewhere in Tau Ceti.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
* W. Casselman, *Representations of SL₂(ℝ)*, lecture notes, §§2, 5–6, pp. 9–11, 17–20.
-/

public section

noncomputable section

open Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-! ### The compact Cartan basis of `𝔤𝔩₂(ℂ)` -/

/-- The compact Cartan element `H_c = -iJ`, `J = E₁₂ - E₂₁`. -/
def compactCartanH : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The entries of `H_c`. -/
theorem compactCartanH_def : compactCartanH = !![0, -I; I, 0] :=
  (rfl)

/-- The compact raising element `X_c = (A + iB) / 2`, `A = diag(1, -1)`, `B = E₁₂ + E₂₁`. -/
def compactCartanX : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, I / 2; I / 2, -1 / 2]

/-- The entries of `X_c`. -/
theorem compactCartanX_def : compactCartanX = !![1 / 2, I / 2; I / 2, -1 / 2] :=
  (rfl)

/-- The compact lowering element `Y_c = (A - iB) / 2`. -/
def compactCartanY : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, -I / 2; -I / 2, -1 / 2]

/-- The entries of `Y_c`. -/
theorem compactCartanY_def : compactCartanY = !![1 / 2, -I / 2; -I / 2, -1 / 2] :=
  (rfl)

/-- `[X_c, Y_c] = H_c`; explicitly `[X_c, Y_c] = [[0, -i], [i, 0]]`. -/
theorem lie_compactCartanX_compactCartanY :
    ⁅compactCartanX, compactCartanY⁆ = compactCartanH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanX, compactCartanY, compactCartanH, Ring.lie_def] <;> grind [I_sq]

/-- `[H_c, X_c] = 2 X_c`. -/
theorem lie_compactCartanH_compactCartanX :
    ⁅compactCartanH, compactCartanX⁆ = (2 : ℂ) • compactCartanX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanX, compactCartanH, Ring.lie_def] <;> grind [I_sq]

/-- `[H_c, Y_c] = -2 Y_c`. -/
theorem lie_compactCartanH_compactCartanY :
    ⁅compactCartanH, compactCartanY⁆ = -((2 : ℂ) • compactCartanY) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanY, compactCartanH, Ring.lie_def] <;> grind [I_sq]

/-! ### Coordinates in the compact Cartan basis -/

/-- The `H_c`-coordinate `i (m₁₂ - m₂₁) / 2` of a matrix in the basis `H_c, X_c, Y_c, 1`. -/
def compactCoordH : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun M := I * (M 0 1 - M 1 0) / 2
  map_add' M N := by simp only [Matrix.add_apply]; ring
  map_smul' c M := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The `X_c`-coordinate `(m₁₁ - m₂₂ - i (m₁₂ + m₂₁)) / 2`. -/
def compactCoordX : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun M := (M 0 0 - M 1 1 - I * (M 0 1 + M 1 0)) / 2
  map_add' M N := by simp only [Matrix.add_apply]; ring
  map_smul' c M := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The `Y_c`-coordinate `(m₁₁ - m₂₂ + i (m₁₂ + m₂₁)) / 2`. -/
def compactCoordY : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun M := (M 0 0 - M 1 1 + I * (M 0 1 + M 1 0)) / 2
  map_add' M N := by simp only [Matrix.add_apply]; ring
  map_smul' c M := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The coordinate `(m₁₁ + m₂₂) / 2` along the identity matrix. -/
def compactCoordOne : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun M := (M 0 0 + M 1 1) / 2
  map_add' M N := by simp only [Matrix.add_apply]; ring
  map_smul' c M := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The `H_c`-coordinate in matrix entries. Not `@[simp]`, so that the values on the basis below
stay in simp normal form. -/
theorem compactCoordH_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH M = I * (M 0 1 - M 1 0) / 2 :=
  (rfl)

/-- The `X_c`-coordinate in matrix entries. -/
theorem compactCoordX_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX M = (M 0 0 - M 1 1 - I * (M 0 1 + M 1 0)) / 2 :=
  (rfl)

/-- The `Y_c`-coordinate in matrix entries. -/
theorem compactCoordY_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY M = (M 0 0 - M 1 1 + I * (M 0 1 + M 1 0)) / 2 :=
  (rfl)

/-- The coordinate along the identity in matrix entries. -/
theorem compactCoordOne_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne M = (M 0 0 + M 1 1) / 2 :=
  (rfl)

/-- The `H_c`-coordinate of `H_c` is `1`. -/
@[simp]
theorem compactCoordH_compactCartanH : compactCoordH compactCartanH = 1 := by
  simp [compactCoordH_apply, compactCartanH]
  linear_combination -I_sq

/-- The `H_c`-coordinate of `X_c` is `0`. -/
@[simp]
theorem compactCoordH_compactCartanX : compactCoordH compactCartanX = 0 := by
  simp [compactCoordH_apply, compactCartanX]

/-- The `H_c`-coordinate of `Y_c` is `0`. -/
@[simp]
theorem compactCoordH_compactCartanY : compactCoordH compactCartanY = 0 := by
  simp [compactCoordH_apply, compactCartanY]

/-- The `H_c`-coordinate of `1` is `0`. -/
@[simp]
theorem compactCoordH_one : compactCoordH 1 = 0 := by
  simp [compactCoordH_apply]

/-- The `X_c`-coordinate of `H_c` is `0`. -/
@[simp]
theorem compactCoordX_compactCartanH : compactCoordX compactCartanH = 0 := by
  simp [compactCoordX_apply, compactCartanH]

/-- The `X_c`-coordinate of `X_c` is `1`. -/
@[simp]
theorem compactCoordX_compactCartanX : compactCoordX compactCartanX = 1 := by
  simp [compactCoordX_apply, compactCartanX]; ring

/-- The `X_c`-coordinate of `Y_c` is `0`. -/
@[simp]
theorem compactCoordX_compactCartanY : compactCoordX compactCartanY = 0 := by
  norm_num [compactCoordX_apply, compactCartanY]

/-- The `X_c`-coordinate of `1` is `0`. -/
@[simp]
theorem compactCoordX_one : compactCoordX 1 = 0 := by
  simp [compactCoordX_apply]

/-- The `Y_c`-coordinate of `H_c` is `0`. -/
@[simp]
theorem compactCoordY_compactCartanH : compactCoordY compactCartanH = 0 := by
  simp [compactCoordY_apply, compactCartanH]

/-- The `Y_c`-coordinate of `X_c` is `0`. -/
@[simp]
theorem compactCoordY_compactCartanX : compactCoordY compactCartanX = 0 := by
  norm_num [compactCoordY_apply, compactCartanX]

/-- The `Y_c`-coordinate of `Y_c` is `1`. -/
@[simp]
theorem compactCoordY_compactCartanY : compactCoordY compactCartanY = 1 := by
  simp [compactCoordY_apply, compactCartanY]; ring

/-- The `Y_c`-coordinate of `1` is `0`. -/
@[simp]
theorem compactCoordY_one : compactCoordY 1 = 0 := by
  simp [compactCoordY_apply]

/-- The coordinate along the identity of `H_c` is `0`. -/
@[simp]
theorem compactCoordOne_compactCartanH : compactCoordOne compactCartanH = 0 := by
  simp [compactCoordOne_apply, compactCartanH]

/-- The coordinate along the identity of `X_c` is `0`. -/
@[simp]
theorem compactCoordOne_compactCartanX : compactCoordOne compactCartanX = 0 := by
  norm_num [compactCoordOne_apply, compactCartanX]

/-- The coordinate along the identity of `Y_c` is `0`. -/
@[simp]
theorem compactCoordOne_compactCartanY : compactCoordOne compactCartanY = 0 := by
  norm_num [compactCoordOne_apply, compactCartanY]

/-- The coordinate along the identity of `1` is `1`. -/
@[simp]
theorem compactCoordOne_one : compactCoordOne 1 = 1 := by
  simp [compactCoordOne_apply]

/-- The `H_c`-coordinate of a bracket. -/
theorem compactCoordH_lie (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH ⁅M, N⁆ =
      compactCoordX M * compactCoordY N - compactCoordY M * compactCoordX N := by
  simp only [compactCoordH_apply, compactCoordX_apply, compactCoordY_apply, Ring.lie_def,
    Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The `X_c`-coordinate of a bracket. -/
theorem compactCoordX_lie (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX ⁅M, N⁆ =
      2 * (compactCoordH M * compactCoordX N - compactCoordX M * compactCoordH N) := by
  simp only [compactCoordH_apply, compactCoordX_apply, Ring.lie_def, Matrix.sub_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (M 0 1 * N 1 0 - M 1 0 * N 0 1) * I_sq

/-- The `Y_c`-coordinate of a bracket. -/
theorem compactCoordY_lie (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY ⁅M, N⁆ =
      -(2 * (compactCoordH M * compactCoordY N - compactCoordY M * compactCoordH N)) := by
  simp only [compactCoordH_apply, compactCoordY_apply, Ring.lie_def, Matrix.sub_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (M 0 1 * N 1 0 - M 1 0 * N 0 1) * I_sq

/-- A bracket has no component along the identity. -/
theorem compactCoordOne_lie (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne ⁅M, N⁆ = 0 := by
  simp only [compactCoordOne_apply, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

/-- Every matrix is `a H_c + b X_c + c Y_c + d 1` in its compact Cartan coordinates. -/
theorem eq_compactCoord (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = compactCoordH M • compactCartanH + compactCoordX M • compactCartanX +
      compactCoordY M • compactCartanY + compactCoordOne M • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCoordH_apply, compactCoordX_apply, compactCoordY_apply, compactCoordOne_apply,
      compactCartanH, compactCartanX, compactCartanY] <;> grind [I_sq]

/-! ### The compact Cartan triple, the rotation generator and the reflection -/

/-- `(H_c, X_c, Y_c)` is an `sl₂` triple. -/
theorem isSl2Triple_compactCartan : IsSl2Triple compactCartanH compactCartanX compactCartanY where
  h_ne_zero h := by simpa [compactCartanH] using congr_fun (congr_fun h 1) 0
  lie_e_f := lie_compactCartanX_compactCartanY
  lie_h_e_nsmul := by rw [lie_compactCartanH_compactCartanX, ofNat_smul_eq_nsmul]
  lie_h_f_nsmul := by rw [lie_compactCartanH_compactCartanY, ofNat_smul_eq_nsmul]

/-- `J = E₁₂ - E₂₁`, the generator of the rotations `r_θ = exp(θJ)` in `GL₂(ℝ)`. -/
def gl2RotationGenerator : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The entries of `J`. -/
theorem gl2RotationGenerator_def : gl2RotationGenerator = !![0, 1; -1, 0] :=
  (rfl)

/-- `H_c = -iJ`. -/
theorem compactCartanH_eq : compactCartanH = -I • gl2RotationGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanH, gl2RotationGenerator]

/-- The reflection `A = diag(1, -1)` of `O(2)`, which normalizes the compact Cartan subalgebra. -/
def compactCartanReflection : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The entries of `A`. -/
theorem compactCartanReflection_def : compactCartanReflection = !![1, 0; 0, -1] :=
  (rfl)

/-- `A² = 1`, so that `A⁻¹ = A`. -/
@[simp]
theorem compactCartanReflection_mul_self :
    compactCartanReflection * compactCartanReflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanReflection]

/-- `X_c = (A + iB) / 2` with `A = diag(1, -1)` and `B = E₁₂ + E₂₁`. -/
theorem compactCartanX_eq :
    compactCartanX = (1 / 2 : ℂ) • (compactCartanReflection + I • !![0, 1; 1, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanX, compactCartanReflection] <;> ring

/-- `Y_c = (A - iB) / 2` with `A = diag(1, -1)` and `B = E₁₂ + E₂₁`. -/
theorem compactCartanY_eq :
    compactCartanY = (1 / 2 : ℂ) • (compactCartanReflection - I • !![0, 1; 1, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanY, compactCartanReflection] <;> ring

/-! ### The Casimir operator -/

/-- The **Casimir operator** `Ω = (H_c² + 2 X_c Y_c + 2 Y_c X_c) / 4` of a `𝔤𝔩₂(ℂ)`-module: half of
the Casimir operator `TauCeti.sl2Casimir` of the compact triple. -/
def gl2Casimir (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) V] [LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V] :
    Module.End ℂ V :=
  (2⁻¹ : ℂ) • sl2Casimir ℂ compactCartanH compactCartanX compactCartanY V

section GlTwoCasimir

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) V]
  [LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V]

/-- `Ω v = (H_c² v + 2 X_c Y_c v + 2 Y_c X_c v) / 4`. -/
theorem gl2Casimir_apply (v : V) :
    gl2Casimir V v = (4⁻¹ : ℂ) • (⁅compactCartanH, ⁅compactCartanH, v⁆⁆ +
      (2 : ℂ) • ⁅compactCartanX, ⁅compactCartanY, v⁆⁆ +
      (2 : ℂ) • ⁅compactCartanY, ⁅compactCartanX, v⁆⁆) := by
  rw [gl2Casimir, LinearMap.smul_apply, sl2Casimir_apply]
  module

/-- The Casimir operator of a Lie submodule is the restriction of that of the ambient module. -/
theorem coe_gl2Casimir_lieSubmodule {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V}
    (v : N) : (gl2Casimir N v : V) = gl2Casimir V (v : V) := by
  simp [gl2Casimir_apply]

end GlTwoCasimir

/-! ### Conjugation by the reflection -/

/-- Conjugation by `A = diag(1, -1)` negates the off-diagonal entries. -/
theorem compactCartanReflection_mul_mul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCartanReflection * M * compactCartanReflection = !![M 0 0, -M 0 1; -M 1 0, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanReflection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- Conjugation by `A` negates the `H_c`-coordinate. -/
theorem compactCoordH_compactCartanReflection_mul_mul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH (compactCartanReflection * M * compactCartanReflection) = -compactCoordH M := by
  rw [compactCartanReflection_mul_mul]
  simp [compactCoordH_apply]
  ring

/-- Conjugation by `A` moves the `Y_c`-coordinate to `X_c`. -/
theorem compactCoordX_compactCartanReflection_mul_mul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX (compactCartanReflection * M * compactCartanReflection) = compactCoordY M := by
  rw [compactCartanReflection_mul_mul]
  simp [compactCoordX_apply, compactCoordY_apply]
  ring

/-- Conjugation by `A` moves the `X_c`-coordinate to `Y_c`. -/
theorem compactCoordY_compactCartanReflection_mul_mul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY (compactCartanReflection * M * compactCartanReflection) = compactCoordX M := by
  rw [compactCartanReflection_mul_mul]
  simp [compactCoordX_apply, compactCoordY_apply]
  ring

/-- Conjugation by `A` fixes the coordinate along the identity. -/
theorem compactCoordOne_compactCartanReflection_mul_mul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne (compactCartanReflection * M * compactCartanReflection) =
      compactCoordOne M := by
  rw [compactCartanReflection_mul_mul]
  simp [compactCoordOne_apply]

end TauCeti
