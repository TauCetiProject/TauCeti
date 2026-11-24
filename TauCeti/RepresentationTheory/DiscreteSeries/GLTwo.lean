/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Casimir
public import TauCeti.Algebra.Lie.Sl2.Coordinates
public import TauCeti.LinearAlgebra.Finsupp.Supported
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Basic.Complex.Basic

/-!
# The discrete series of `GL₂(ℝ)` as explicit `𝔤𝔩₂(ℂ)`-modules

The discrete series `D_k(μ)` of `GL₂(ℝ)`, `k ≥ 2`, and its limit at `k = 1`, restricted to `SO(2)`,
has the weights `ℓ` with `|ℓ| ≥ k` and `ℓ ≡ k mod 2`, each with multiplicity one: two rays,
interchanged by the reflection `A = diag(1, -1)` of `O(2)`. In the compact Cartan basis

`H_c = -iJ`, `X_c = (A + iB) / 2`, `Y_c = (A - iB) / 2`, with `J = E₁₂ - E₂₁`, `B = E₁₂ + E₂₁`,

of `𝔤𝔩₂(ℂ)` (an `sl₂` triple: `[H_c, X_c] = 2X_c`, `[H_c, Y_c] = -2Y_c`, `[X_c, Y_c] = H_c`), a
weight vector `v_ℓ` is normalized by

`H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`,

and the identity matrix acts by the central scalar `μ`. This file builds these modules
explicitly. The formulas define a `𝔤𝔩₂(ℂ)`-module structure on the finitely supported vectors on
*all* weights `ℓ ∈ ℤ` (`TauCeti.CompactWeightModule k μ`), and `D_k(μ)` is the Lie submodule of the
vectors supported on the two rays (`TauCeti.discreteSeries k μ`): `X_c` leaves the negative ray only
from `v_{-k}`, where its coefficient `(k - k) / 2` vanishes, and `Y_c` leaves the positive ray only
from `v_k`. The rays themselves are Lie submodules `TauCeti.positiveDiscreteSeries k μ` and
`TauCeti.negativeDiscreteSeries k μ`, the lowest and highest weight modules `D_k^±`. The
definitions accept every `k : ℕ`, but only `k ≥ 1` gives a discrete series or its limit: for
`k = 0` the two rays overlap at the weight `0` and the module is the reducible even-weight module.

## Main definitions

* `TauCeti.compactCartanH`, `TauCeti.compactCartanX`, `TauCeti.compactCartanY`: the compact Cartan
  basis, with `TauCeti.isSl2Triple_compactCartan`.
* `TauCeti.compactRep k μ`: the Lie algebra homomorphism `𝔤𝔩₂(ℂ) → End(ℤ →₀ ℂ)` given by the
  formulas above, and `TauCeti.CompactWeightModule k μ`, the resulting module.
* `TauCeti.CompactWeightModule.weightVector k μ ℓ`: the weight vector `v_ℓ`.
* `TauCeti.discreteSeries k μ`: `D_k(μ)`, with the rays `TauCeti.positiveDiscreteSeries k μ` and
  `TauCeti.negativeDiscreteSeries k μ`.
* `TauCeti.CompactWeightModule.reflection k μ`: `v_ℓ ↦ v_{-ℓ}`.
* `TauCeti.compactCasimir`: the Casimir operator `Ω = (H_c² + 2X_cY_c + 2Y_cX_c) / 4` of a
  `𝔤𝔩₂(ℂ)`-module.

## Main results

* `TauCeti.lie_compactCartanH_weightVector`, `TauCeti.lie_compactCartanX_weightVector`,
  `TauCeti.lie_compactCartanY_weightVector`: the normalization above;
  `TauCeti.lie_glTwoRotationGenerator_weightVector`: `J v_ℓ = iℓ v_ℓ`, so that `r_θ = exp(θJ)` acts
  on `v_ℓ` by `e^{iℓθ}`.
* `TauCeti.CompactWeightModule.one_lie_lieSubmodule`, `TauCeti.one_lie_discreteSeries`: the central
  scalar of `D_k(μ)`, and of every Lie submodule of `TauCeti.CompactWeightModule k μ`, is `μ`.
* `TauCeti.CompactWeightModule.compactCasimir_lieSubmodule`,
  `TauCeti.compactCasimir_discreteSeries`: the Casimir operator of `D_k(μ)`, and of every Lie
  submodule of `TauCeti.CompactWeightModule k μ`, is `k (k - 2) / 4`.
* `TauCeti.discreteSeries_eq_sup`: `D_k(μ)` is the sum of its two rays.
* `TauCeti.CompactWeightModule.reflection_lie`: the reflection intertwines the action of `M` with
  that of `A M A⁻¹`; `TauCeti.CompactWeightModule.reflection_mem_negativeDiscreteSeries_iff`: it
  interchanges the two rays.

Explicit checks: `TauCeti.lie_compactCartanY_weightVector_self`,
`TauCeti.lie_compactCartanX_weightVector_self`, `TauCeti.lie_compactCartanY_weightVector_add_two`,
`TauCeti.lie_compactCartanX_weightVector_neg_self`, `TauCeti.compactCasimir_discreteSeries_two`
and `TauCeti.compactCasimir_discreteSeries_one`.

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

/-! ### The operators on weight vectors -/

/-- The weight operator `v_ℓ ↦ ℓ v_ℓ` on `ℤ →₀ ℂ`. -/
def compactWeightOp : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun ℓ : ℤ ↦ (ℓ : ℂ) • Finsupp.single ℓ (1 : ℂ)

/-- The raising operator `v_ℓ ↦ (k + ℓ) / 2 v_{ℓ + 2}` on `ℤ →₀ ℂ`. -/
def compactRaiseOp (k : ℂ) : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun ℓ : ℤ ↦ ((k + ℓ) / 2) • Finsupp.single (ℓ + 2) (1 : ℂ)

/-- The lowering operator `v_ℓ ↦ (k - ℓ) / 2 v_{ℓ - 2}` on `ℤ →₀ ℂ`. -/
def compactLowerOp (k : ℂ) : Module.End ℂ (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun ℓ : ℤ ↦ ((k - ℓ) / 2) • Finsupp.single (ℓ - 2) (1 : ℂ)

/-- `H v_ℓ = ℓ v_ℓ`. -/
@[simp]
theorem compactWeightOp_single (ℓ : ℤ) :
    compactWeightOp (Finsupp.single ℓ 1) = (ℓ : ℂ) • Finsupp.single ℓ 1 := by
  simp [compactWeightOp]

/-- `X v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`. -/
@[simp]
theorem compactRaiseOp_single (k : ℂ) (ℓ : ℤ) :
    compactRaiseOp k (Finsupp.single ℓ 1) = ((k + ℓ) / 2) • Finsupp.single (ℓ + 2) 1 := by
  simp [compactRaiseOp]

/-- `Y v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`. -/
@[simp]
theorem compactLowerOp_single (k : ℂ) (ℓ : ℤ) :
    compactLowerOp k (Finsupp.single ℓ 1) = ((k - ℓ) / 2) • Finsupp.single (ℓ - 2) 1 := by
  simp [compactLowerOp]

/-- The raising and lowering operators satisfy `[X, Y] = H`. -/
theorem lie_compactRaiseOp_compactLowerOp (k : ℂ) :
    ⁅compactRaiseOp k, compactLowerOp k⁆ = compactWeightOp := by
  refine (Ring.lie_def _ _).trans <| Finsupp.lhom_ext' fun ℓ ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, compactRaiseOp_single, compactLowerOp_single, map_smul,
    compactWeightOp_single, sub_add_cancel, add_sub_cancel_right, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-- `[H, X] = 2 X` for the weight and raising operators. -/
theorem lie_compactWeightOp_compactRaiseOp (k : ℂ) :
    ⁅compactWeightOp, compactRaiseOp k⁆ = (2 : ℂ) • compactRaiseOp k := by
  refine (Ring.lie_def _ _).trans <| Finsupp.lhom_ext' fun ℓ ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, compactRaiseOp_single, map_smul, compactWeightOp_single, smul_smul,
    ← sub_smul, LinearMap.smul_apply]
  congr 1
  push_cast
  ring

/-- `[H, Y] = -2 Y` for the weight and lowering operators. -/
theorem lie_compactWeightOp_compactLowerOp (k : ℂ) :
    ⁅compactWeightOp, compactLowerOp k⁆ = -((2 : ℂ) • compactLowerOp k) := by
  refine (Ring.lie_def _ _).trans <| Finsupp.lhom_ext' fun ℓ ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    mul_apply_eq_comp, compactLowerOp_single, map_smul, compactWeightOp_single, smul_smul,
    ← sub_smul, LinearMap.neg_apply, LinearMap.smul_apply, ← neg_smul]
  congr 1
  push_cast
  ring

/-- The weight, raising and lowering operators form an `sl₂` triple. -/
theorem isSl2Triple_compactWeightOp (k : ℂ) :
    IsSl2Triple compactWeightOp (compactRaiseOp k) (compactLowerOp k) where
  h_ne_zero h := by simpa using congr($h (Finsupp.single 1 1))
  lie_e_f := lie_compactRaiseOp_compactLowerOp k
  lie_h_e_nsmul := by rw [lie_compactWeightOp_compactRaiseOp, ofNat_smul_eq_nsmul]
  lie_h_f_nsmul := by rw [lie_compactWeightOp_compactLowerOp, ofNat_smul_eq_nsmul]

/-! ### The representation of `𝔤𝔩₂(ℂ)` on all weights -/

/-- The linear map underlying `TauCeti.compactRep`. -/
private def compactRepLinear (k μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Module.End ℂ (ℤ →₀ ℂ) :=
  compactCoordH.smulRight compactWeightOp + compactCoordX.smulRight (compactRaiseOp k) +
    compactCoordY.smulRight (compactLowerOp k) + (μ • compactCoordOne).smulRight 1

private theorem compactRepLinear_apply (k μ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactRepLinear k μ M =
      compactCoordH M • compactWeightOp + compactCoordX M • compactRaiseOp k +
        compactCoordY M • compactLowerOp k + (μ * compactCoordOne M) • 1 := by
  simp [compactRepLinear]

/-- The action of `𝔤𝔩₂(ℂ)` on `ℤ →₀ ℂ` in which `H_c`, `X_c`, `Y_c` act by
`TauCeti.compactWeightOp`, `TauCeti.compactRaiseOp k`, `TauCeti.compactLowerOp k` and the identity
matrix acts by the scalar `μ`. -/
def compactRep (k μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (ℤ →₀ ℂ) where
  toLinearMap := compactRepLinear k μ
  map_lie' {M N} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, compactRepLinear_apply,
      compactCoordH_lie, compactCoordX_lie, compactCoordY_lie, compactCoordOne_lie, mul_zero,
      zero_smul, add_zero]
    rw [(isSl2Triple_compactWeightOp k).lie_smul_add_smul_add_smul_add_smul
      fun x ↦ (Ring.lie_def _ _).trans (by rw [mul_one, one_mul, sub_self])]

/-- `TauCeti.compactRep k μ M` in the compact Cartan coordinates of `M`. -/
theorem compactRep_apply (k μ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactRep k μ M = compactCoordH M • compactWeightOp + compactCoordX M • compactRaiseOp k +
      compactCoordY M • compactLowerOp k + (μ * compactCoordOne M) • 1 :=
  compactRepLinear_apply k μ M

/-- `H_c` acts by the weight operator. -/
@[simp]
theorem compactRep_compactCartanH (k μ : ℂ) : compactRep k μ compactCartanH = compactWeightOp := by
  simp [compactRep_apply]

/-- `X_c` acts by the raising operator. -/
@[simp]
theorem compactRep_compactCartanX (k μ : ℂ) :
    compactRep k μ compactCartanX = compactRaiseOp k := by
  simp [compactRep_apply]

/-- `Y_c` acts by the lowering operator. -/
@[simp]
theorem compactRep_compactCartanY (k μ : ℂ) :
    compactRep k μ compactCartanY = compactLowerOp k := by
  simp [compactRep_apply]

/-- The identity matrix acts by `μ`. -/
@[simp]
theorem compactRep_one (k μ : ℂ) : compactRep k μ 1 = μ • 1 := by
  simp [compactRep_apply]

/-! ### The module of all compact weights -/

/-- The `𝔤𝔩₂(ℂ)`-module of finitely supported vectors `∑ c_ℓ v_ℓ` on all compact weights `ℓ ∈ ℤ`,
with `H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`, and
the identity matrix acting by `μ`. For `k : ℕ`, the discrete series `D_k(μ)` is its Lie submodule
`TauCeti.discreteSeries k μ` on the weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2`. The type synonym is exposed
because the transported instances need its underlying type. -/
@[expose]
def CompactWeightModule (_k _μ : ℂ) : Type := ℤ →₀ ℂ

namespace CompactWeightModule

variable {k μ : ℂ}

instance instAddCommGroup : AddCommGroup (CompactWeightModule k μ) :=
  inferInstanceAs (AddCommGroup (ℤ →₀ ℂ))

instance instModule : Module ℂ (CompactWeightModule k μ) := inferInstanceAs (Module ℂ (ℤ →₀ ℂ))

instance instLieRingModule :
    LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) :=
  LieRingModule.compLieHom (ℤ →₀ ℂ) (compactRep k μ)

instance instLieModule : LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) :=
  LieModule.compLieHom (ℤ →₀ ℂ) (compactRep k μ)

variable (k μ) in
/-- The coordinates `ℓ ↦ c_ℓ` of a vector `∑ c_ℓ v_ℓ`. -/
def equivFinsupp : CompactWeightModule k μ ≃ₗ[ℂ] (ℤ →₀ ℂ) := LinearEquiv.refl ℂ (ℤ →₀ ℂ)

/-- The bracket of `𝔤𝔩₂(ℂ)` with `TauCeti.CompactWeightModule k μ` is `TauCeti.compactRep k μ`. -/
theorem equivFinsupp_lie (M : Matrix (Fin 2) (Fin 2) ℂ) (v : CompactWeightModule k μ) :
    equivFinsupp k μ ⁅M, v⁆ = compactRep k μ M (equivFinsupp k μ v) :=
  (rfl)

variable (k μ) in
/-- The weight vector `v_ℓ`. -/
def weightVector (ℓ : ℤ) : CompactWeightModule k μ := Finsupp.single ℓ 1

/-- The coordinates of `v_ℓ`. -/
@[simp]
theorem equivFinsupp_weightVector (ℓ : ℤ) :
    equivFinsupp k μ (weightVector k μ ℓ) = Finsupp.single ℓ 1 :=
  (rfl)

variable (k μ) in
/-- The weight vectors form a basis of `TauCeti.CompactWeightModule k μ`. -/
def weightBasis : Module.Basis ℤ ℂ (CompactWeightModule k μ) := Finsupp.basisSingleOne

/-- The basis vectors are the weight vectors. -/
@[simp]
theorem weightBasis_apply (ℓ : ℤ) : weightBasis k μ ℓ = weightVector k μ ℓ :=
  (rfl)

end CompactWeightModule

variable {k μ : ℂ}

open CompactWeightModule (weightVector weightBasis weightBasis_apply)

/-- `H_c v_ℓ = ℓ v_ℓ`. -/
@[simp]
theorem lie_compactCartanH_weightVector (ℓ : ℤ) :
    ⁅compactCartanH, weightVector k μ ℓ⁆ = (ℓ : ℂ) • weightVector k μ ℓ := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, map_smul,
    CompactWeightModule.equivFinsupp_weightVector, compactRep_compactCartanH,
    compactWeightOp_single]

/-- `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`. -/
@[simp]
theorem lie_compactCartanX_weightVector (ℓ : ℤ) :
    ⁅compactCartanX, weightVector k μ ℓ⁆ = ((k + ℓ) / 2) • weightVector k μ (ℓ + 2) := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, map_smul,
    CompactWeightModule.equivFinsupp_weightVector, CompactWeightModule.equivFinsupp_weightVector,
    compactRep_compactCartanX, compactRaiseOp_single]

/-- `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`. -/
@[simp]
theorem lie_compactCartanY_weightVector (ℓ : ℤ) :
    ⁅compactCartanY, weightVector k μ ℓ⁆ = ((k - ℓ) / 2) • weightVector k μ (ℓ - 2) := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, map_smul,
    CompactWeightModule.equivFinsupp_weightVector, CompactWeightModule.equivFinsupp_weightVector,
    compactRep_compactCartanY, compactLowerOp_single]

/-- **The central scalar**: the identity matrix acts by `μ`. -/
@[simp]
theorem one_lie_compactWeightModule (v : CompactWeightModule k μ) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v := by
  apply (CompactWeightModule.equivFinsupp k μ).injective
  rw [CompactWeightModule.equivFinsupp_lie, compactRep_one, map_smul]
  simp

/-- The bracket of a matrix with a weight vector, in the coordinates of the compact Cartan basis. -/
theorem lie_weightVector (M : Matrix (Fin 2) (Fin 2) ℂ) (ℓ : ℤ) :
    ⁅M, weightVector k μ ℓ⁆ = (compactCoordH M * ℓ + μ * compactCoordOne M) • weightVector k μ ℓ +
      (compactCoordX M * ((k + ℓ) / 2)) • weightVector k μ (ℓ + 2) +
      (compactCoordY M * ((k - ℓ) / 2)) • weightVector k μ (ℓ - 2) := by
  conv_lhs => rw [eq_compactCoord M]
  simp only [add_lie, smul_lie, lie_compactCartanH_weightVector, lie_compactCartanX_weightVector,
    lie_compactCartanY_weightVector, one_lie_compactWeightModule, smul_smul]
  module

/-! ### The compact Cartan triple and the Casimir operator -/

/-- `(H_c, X_c, Y_c)` is an `sl₂` triple. -/
theorem isSl2Triple_compactCartan : IsSl2Triple compactCartanH compactCartanX compactCartanY where
  h_ne_zero h := by simpa [compactCartanH] using congr_fun (congr_fun h 1) 0
  lie_e_f := lie_compactCartanX_compactCartanY
  lie_h_e_nsmul := by rw [lie_compactCartanH_compactCartanX, ofNat_smul_eq_nsmul]
  lie_h_f_nsmul := by rw [lie_compactCartanH_compactCartanY, ofNat_smul_eq_nsmul]

/-- `J = E₁₂ - E₂₁`, the generator of the rotations `r_θ = exp(θJ)` in `GL₂(ℝ)`. -/
def glTwoRotationGenerator : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The entries of `J`. -/
theorem glTwoRotationGenerator_def : glTwoRotationGenerator = !![0, 1; -1, 0] :=
  (rfl)

/-- `H_c = -iJ`. -/
theorem compactCartanH_eq : compactCartanH = -I • glTwoRotationGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanH, glTwoRotationGenerator]

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

/-- `J v_ℓ = iℓ v_ℓ`, the derivative of `r_θ v_ℓ = e^{iℓθ} v_ℓ`. -/
theorem lie_glTwoRotationGenerator_weightVector (ℓ : ℤ) :
    ⁅glTwoRotationGenerator, weightVector k μ ℓ⁆ = (I * ℓ) • weightVector k μ ℓ := by
  have hJ : glTwoRotationGenerator = I • compactCartanH := by
    rw [compactCartanH_eq, smul_smul]
    simp
  rw [hJ, smul_lie, lie_compactCartanH_weightVector, smul_smul]

/-- The **Casimir operator** `Ω = (H_c² + 2 X_c Y_c + 2 Y_c X_c) / 4` of a `𝔤𝔩₂(ℂ)`-module: half of
the Casimir operator `TauCeti.sl2Casimir` of the compact triple. -/
def compactCasimir (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) V] [LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V] :
    Module.End ℂ V :=
  (2⁻¹ : ℂ) • sl2Casimir ℂ compactCartanH compactCartanX compactCartanY V

section CompactCasimir

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) V]
  [LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V]

/-- `Ω v = (H_c² v + 2 X_c Y_c v + 2 Y_c X_c v) / 4`. -/
theorem compactCasimir_apply (v : V) :
    compactCasimir V v = (4⁻¹ : ℂ) • (⁅compactCartanH, ⁅compactCartanH, v⁆⁆ +
      (2 : ℂ) • ⁅compactCartanX, ⁅compactCartanY, v⁆⁆ +
      (2 : ℂ) • ⁅compactCartanY, ⁅compactCartanX, v⁆⁆) := by
  rw [compactCasimir, LinearMap.smul_apply, sl2Casimir_apply]
  module

/-- The Casimir operator of a Lie submodule is the restriction of that of the ambient module. -/
theorem coe_compactCasimir_lieSubmodule {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V}
    (v : N) : (compactCasimir N v : V) = compactCasimir V (v : V) := by
  simp [compactCasimir_apply]

end CompactCasimir

/-- **The Casimir operator acts by `k(k - 2)/4`** on every vector of
`TauCeti.CompactWeightModule k μ`. -/
theorem compactCasimir_compactWeightModule :
    compactCasimir (CompactWeightModule k μ) = (k * (k - 2) / 4) • 1 := by
  refine (weightBasis k μ).ext fun ℓ ↦ ?_
  simp only [weightBasis_apply, compactCasimir_apply, LinearMap.smul_apply,
    lie_compactCartanH_weightVector, lie_compactCartanX_weightVector,
    lie_compactCartanY_weightVector, lie_smul, sub_add_cancel, add_sub_cancel_right, smul_smul,
    one_apply_eq_self]
  rw [← add_smul, ← add_smul, smul_smul]
  congr 1
  push_cast
  ring

namespace CompactWeightModule

/-- The Casimir operator acts by `k(k - 2)/4` on every Lie submodule of
`TauCeti.CompactWeightModule k μ`. -/
theorem compactCasimir_lieSubmodule
    (N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)) (v : N) :
    compactCasimir N v = (k * (k - 2) / 4) • v := by
  ext
  rw [coe_compactCasimir_lieSubmodule, compactCasimir_compactWeightModule, LieSubmodule.coe_smul]
  rfl

/-- The identity matrix acts by `μ` on every Lie submodule of `TauCeti.CompactWeightModule k μ`. -/
theorem one_lie_lieSubmodule
    (N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)) (v : N) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v := by
  ext
  simp

/-! ### Lie submodules spanned by weight vectors -/

variable (k μ) in
/-- The Lie submodule of `TauCeti.CompactWeightModule k μ` of the vectors supported on a set `S` of
weights that `X_c` and `Y_c` leave only with coefficient zero. -/
def weightLieSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) where
  toSubmodule := (Finsupp.supported ℂ ℂ S).comap (CompactWeightModule.equivFinsupp k μ).toLinearMap
  lie_mem {M v} hv := by
    replace hv := Submodule.mem_comap.1 hv
    refine Submodule.mem_comap.2 ?_
    rw [LinearEquiv.coe_coe] at hv ⊢
    rw [equivFinsupp_lie, compactRep_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self]
    refine add_mem (add_mem (add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ hv)
    · exact Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ _ (fun ℓ : ℤ ↦ (ℓ : ℂ)) id
        compactWeightOp_single (fun ℓ hℓ h ↦ absurd hℓ h) hv
    · exact Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ _ _ (· + 2)
        (compactRaiseOp_single k) (fun ℓ hℓ h ↦ by rw [hX ℓ hℓ h, zero_div]) hv
    · exact Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ _ _ (· - 2)
        (compactLowerOp_single k) (fun ℓ hℓ h ↦ by rw [hY ℓ hℓ h, zero_div]) hv

/-- The underlying submodule of `TauCeti.CompactWeightModule.weightLieSubmodule`. -/
theorem toSubmodule_weightLieSubmodule {S : Set ℤ} {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0}
    {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0} :
    (weightLieSubmodule k μ S hX hY).toSubmodule =
      (Finsupp.supported ℂ ℂ S).comap (CompactWeightModule.equivFinsupp k μ).toLinearMap :=
  (rfl)

/-- Membership in `TauCeti.CompactWeightModule.weightLieSubmodule`: the coordinates are supported
on `S`. -/
theorem mem_weightLieSubmodule {S : Set ℤ} {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0}
    {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0} {v : CompactWeightModule k μ} :
    v ∈ weightLieSubmodule k μ S hX hY ↔
      CompactWeightModule.equivFinsupp k μ v ∈ Finsupp.supported ℂ ℂ S :=
  Iff.rfl

/-- `v_ℓ` lies in the Lie submodule of a set of weights containing `ℓ`. -/
theorem weightVector_mem_weightLieSubmodule {S : Set ℤ} {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0}
    {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0} {ℓ : ℤ} (hℓ : ℓ ∈ S) :
    weightVector k μ ℓ ∈ weightLieSubmodule k μ S hX hY :=
  mem_weightLieSubmodule.2 (Finsupp.single_mem_supported ℂ _ hℓ)

end CompactWeightModule

open CompactWeightModule (weightLieSubmodule toSubmodule_weightLieSubmodule
  weightVector_mem_weightLieSubmodule)

/-! ### The discrete series `D_k(μ)` -/

/-- The weights of `D_k`: `|ℓ| ≥ k` and `ℓ ≡ k mod 2`, the two rays. For `k = 0` this is the set of
all even integers, and the two rays overlap at `0`. -/
def discreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | (k : ℤ) ≤ |ℓ| ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of the positive ray `D_k^+`: `ℓ ≥ k` and `ℓ ≡ k mod 2`. -/
def positiveDiscreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | (k : ℤ) ≤ ℓ ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of the negative ray `D_k^-`: `ℓ ≤ -k` and `ℓ ≡ k mod 2`. -/
def negativeDiscreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | ℓ ≤ -(k : ℤ) ∧ ℓ % 2 = (k : ℤ) % 2}

/-- Membership in the weights of `D_k`. -/
@[simp]
theorem mem_discreteSeriesWeights {k : ℕ} {ℓ : ℤ} :
    ℓ ∈ discreteSeriesWeights k ↔ (k : ℤ) ≤ |ℓ| ∧ ℓ % 2 = (k : ℤ) % 2 :=
  Iff.rfl

/-- Membership in the weights of the positive ray. -/
@[simp]
theorem mem_positiveDiscreteSeriesWeights {k : ℕ} {ℓ : ℤ} :
    ℓ ∈ positiveDiscreteSeriesWeights k ↔ (k : ℤ) ≤ ℓ ∧ ℓ % 2 = (k : ℤ) % 2 :=
  Iff.rfl

/-- Membership in the weights of the negative ray. -/
@[simp]
theorem mem_negativeDiscreteSeriesWeights {k : ℕ} {ℓ : ℤ} :
    ℓ ∈ negativeDiscreteSeriesWeights k ↔ ℓ ≤ -(k : ℤ) ∧ ℓ % 2 = (k : ℤ) % 2 :=
  Iff.rfl

/-- The weights of `D_k` are those of its two rays. -/
theorem discreteSeriesWeights_eq_union (k : ℕ) :
    discreteSeriesWeights k =
      positiveDiscreteSeriesWeights k ∪ negativeDiscreteSeriesWeights k := by
  ext ℓ
  simp only [mem_discreteSeriesWeights, mem_positiveDiscreteSeriesWeights,
    mem_negativeDiscreteSeriesWeights, Set.mem_union]
  rcases abs_cases ℓ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

private theorem natCast_add_intCast_eq_zero {k : ℕ} {ℓ : ℤ} (h : (k : ℤ) + ℓ = 0) :
    (k : ℂ) + ℓ = 0 :=
  mod_cast h

private theorem natCast_sub_intCast_eq_zero {k : ℕ} {ℓ : ℤ} (h : (k : ℤ) - ℓ = 0) :
    (k : ℂ) - ℓ = 0 :=
  mod_cast h

private theorem positiveDiscreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ positiveDiscreteSeriesWeights k, ℓ + 2 ∉ positiveDiscreteSeriesWeights k →
      (k : ℂ) + ℓ = 0 := fun ℓ hℓ h ↦
  natCast_add_intCast_eq_zero (by rw [mem_positiveDiscreteSeriesWeights] at hℓ h; omega)

private theorem positiveDiscreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ positiveDiscreteSeriesWeights k, ℓ - 2 ∉ positiveDiscreteSeriesWeights k →
      (k : ℂ) - ℓ = 0 := fun ℓ hℓ h ↦
  natCast_sub_intCast_eq_zero (by rw [mem_positiveDiscreteSeriesWeights] at hℓ h; omega)

private theorem negativeDiscreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ negativeDiscreteSeriesWeights k, ℓ + 2 ∉ negativeDiscreteSeriesWeights k →
      (k : ℂ) + ℓ = 0 := fun ℓ hℓ h ↦
  natCast_add_intCast_eq_zero (by rw [mem_negativeDiscreteSeriesWeights] at hℓ h; omega)

private theorem negativeDiscreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ negativeDiscreteSeriesWeights k, ℓ - 2 ∉ negativeDiscreteSeriesWeights k →
      (k : ℂ) - ℓ = 0 := fun ℓ hℓ h ↦
  natCast_sub_intCast_eq_zero (by rw [mem_negativeDiscreteSeriesWeights] at hℓ h; omega)

private theorem discreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ discreteSeriesWeights k, ℓ + 2 ∉ discreteSeriesWeights k → (k : ℂ) + ℓ = 0 := by
  simp only [discreteSeriesWeights_eq_union, Set.mem_union, not_or]
  rintro ℓ (hℓ | hℓ) ⟨hP, hN⟩
  exacts [positiveDiscreteSeriesWeights_raise ℓ hℓ hP, negativeDiscreteSeriesWeights_raise ℓ hℓ hN]

private theorem discreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ discreteSeriesWeights k, ℓ - 2 ∉ discreteSeriesWeights k → (k : ℂ) - ℓ = 0 := by
  simp only [discreteSeriesWeights_eq_union, Set.mem_union, not_or]
  rintro ℓ (hℓ | hℓ) ⟨hP, hN⟩
  exacts [positiveDiscreteSeriesWeights_lower ℓ hℓ hP, negativeDiscreteSeriesWeights_lower ℓ hℓ hN]

/-- **The discrete series `D_k(μ)`** of `GL₂(ℝ)` (`k ≥ 2`), and its limit at `k = 1`, as an explicit
`𝔤𝔩₂(ℂ)`-module: the finitely supported vectors on the weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2`, with
`H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`, central
scalar `μ` and Casimir `k (k - 2) / 4`. Only `k ≥ 1` is meant: for `k = 0` this is the module on all
even weights, which is reducible and not a discrete series: `v_0` spans a one-dimensional submodule
killed by `H_c`, `X_c` and `Y_c`, on which the identity matrix acts by `μ`. -/
def discreteSeries (k : ℕ) (μ : ℂ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (discreteSeriesWeights k) discreteSeriesWeights_raise
    discreteSeriesWeights_lower

/-- The positive ray `D_k^+(μ)`, the lowest weight module of lowest weight `k`, the restriction of
`D_k(μ)` to the identity component of `GL₂(ℝ)` keeping the positive weights. -/
def positiveDiscreteSeries (k : ℕ) (μ : ℂ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (positiveDiscreteSeriesWeights k)
    positiveDiscreteSeriesWeights_raise positiveDiscreteSeriesWeights_lower

/-- The negative ray `D_k^-(μ)`, the highest weight module of highest weight `-k`. -/
def negativeDiscreteSeries (k : ℕ) (μ : ℂ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (negativeDiscreteSeriesWeights k)
    negativeDiscreteSeriesWeights_raise negativeDiscreteSeriesWeights_lower

/-- Membership in `D_k(μ)`: the coordinates are supported on the two rays. -/
theorem mem_discreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    v ∈ discreteSeries k μ ↔
      CompactWeightModule.equivFinsupp (k : ℂ) μ v ∈
        Finsupp.supported ℂ ℂ (discreteSeriesWeights k) :=
  Iff.rfl

/-- Membership in `D_k^+(μ)`: the coordinates are supported on the positive ray. -/
theorem mem_positiveDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    v ∈ positiveDiscreteSeries k μ ↔
      CompactWeightModule.equivFinsupp (k : ℂ) μ v ∈
        Finsupp.supported ℂ ℂ (positiveDiscreteSeriesWeights k) :=
  Iff.rfl

/-- Membership in `D_k^-(μ)`: the coordinates are supported on the negative ray. -/
theorem mem_negativeDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    v ∈ negativeDiscreteSeries k μ ↔
      CompactWeightModule.equivFinsupp (k : ℂ) μ v ∈
        Finsupp.supported ℂ ℂ (negativeDiscreteSeriesWeights k) :=
  Iff.rfl

/-- `D_k(μ)` is the sum of its two rays. -/
theorem discreteSeries_eq_sup (k : ℕ) :
    discreteSeries k μ = positiveDiscreteSeries k μ ⊔ negativeDiscreteSeries k μ := by
  refine LieSubmodule.toSubmodule_injective ?_
  simp only [discreteSeries, positiveDiscreteSeries, negativeDiscreteSeries,
    discreteSeriesWeights_eq_union, LieSubmodule.sup_toSubmodule, toSubmodule_weightLieSubmodule]
  simp [Finsupp.supported_union, Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]

/-- `v_ℓ ∈ D_k(μ)` for every allowed weight. -/
theorem weightVector_mem_discreteSeries {k : ℕ} {ℓ : ℤ} (hℓ : ℓ ∈ discreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ discreteSeries k μ :=
  weightVector_mem_weightLieSubmodule hℓ

/-- `v_ℓ ∈ D_k^+(μ)` for every weight of the positive ray. -/
theorem weightVector_mem_positiveDiscreteSeries {k : ℕ} {ℓ : ℤ}
    (hℓ : ℓ ∈ positiveDiscreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ positiveDiscreteSeries k μ :=
  weightVector_mem_weightLieSubmodule hℓ

/-- `v_ℓ ∈ D_k^-(μ)` for every weight of the negative ray. -/
theorem weightVector_mem_negativeDiscreteSeries {k : ℕ} {ℓ : ℤ}
    (hℓ : ℓ ∈ negativeDiscreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ negativeDiscreteSeries k μ :=
  weightVector_mem_weightLieSubmodule hℓ

/-- **The Casimir operator of `D_k(μ)` is `k (k - 2) / 4`.** -/
theorem compactCasimir_discreteSeries (k : ℕ) (v : discreteSeries k μ) :
    compactCasimir (discreteSeries k μ) v = ((k : ℂ) * (k - 2) / 4) • v :=
  CompactWeightModule.compactCasimir_lieSubmodule _ v

/-- **The central scalar of `D_k(μ)` is `μ`.** -/
theorem one_lie_discreteSeries (k : ℕ) (v : discreteSeries k μ) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v :=
  CompactWeightModule.one_lie_lieSubmodule _ v

/-! ### The reflection -/

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

namespace CompactWeightModule

variable (k μ) in
/-- The **reflection** `v_ℓ ↦ v_{-ℓ}`, the action of `A = diag(1, -1)`, which interchanges the two
rays of `D_k(μ)`. -/
def reflection : CompactWeightModule k μ ≃ₗ[ℂ] CompactWeightModule k μ :=
  Finsupp.domLCongr (Equiv.neg ℤ)

/-- The coordinates of the reflection of `v` are those of `v` at the opposite weights. -/
@[simp]
theorem equivFinsupp_reflection_apply (v : CompactWeightModule k μ) (ℓ : ℤ) :
    equivFinsupp k μ (reflection k μ v) ℓ = equivFinsupp k μ v (-ℓ) :=
  -- `equivFinsupp` is the identity of `ℤ →₀ ℂ` and `reflection` is `Finsupp.domLCongr`, whose
  -- `_apply` lemmas do not fire syntactically on the type synonym, so this unfolds both to cite
  -- `Finsupp.equivMapDomain_apply`.
  Finsupp.equivMapDomain_apply (Equiv.neg ℤ) (equivFinsupp k μ v) ℓ

/-- The reflection sends `v_ℓ` to `v_{-ℓ}`. -/
@[simp]
theorem reflection_weightVector (ℓ : ℤ) :
    reflection k μ (weightVector k μ ℓ) = weightVector k μ (-ℓ) :=
  Finsupp.domLCongr_single _ _ _

/-- The reflection is an involution. -/
@[simp]
theorem reflection_reflection (v : CompactWeightModule k μ) :
    reflection k μ (reflection k μ v) = v :=
  (equivFinsupp k μ).injective <| Finsupp.ext fun ℓ ↦ by simp

/-- The reflection is its own inverse. -/
@[simp]
theorem reflection_symm : (reflection k μ).symm = reflection k μ :=
  LinearEquiv.ext fun v ↦ (reflection k μ).symm_apply_eq.2 (reflection_reflection v).symm

/-- The reflection intertwines the action of `M` with that of `A M A⁻¹ = A M A`, `A = diag(1, -1)`
(`TauCeti.compactCartanReflection_mul_self`): it exchanges `X_c` and `Y_c` and negates `H_c`. -/
theorem reflection_lie (M : Matrix (Fin 2) (Fin 2) ℂ) (v : CompactWeightModule k μ) :
    reflection k μ ⁅M, v⁆ =
      ⁅compactCartanReflection * M * compactCartanReflection, reflection k μ v⁆ := by
  have h : (reflection k μ).toLinearMap ∘ₗ LieModule.toEnd ℂ _ _ M =
      LieModule.toEnd ℂ _ _ (compactCartanReflection * M * compactCartanReflection) ∘ₗ
        (reflection k μ).toLinearMap := by
    refine (weightBasis k μ).ext fun ℓ ↦ ?_
    simp only [weightBasis_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LieModule.toEnd_apply_apply, reflection_weightVector, lie_weightVector, map_add, map_smul,
      compactCoordH_compactCartanReflection_mul_mul, compactCoordX_compactCartanReflection_mul_mul,
      compactCoordY_compactCartanReflection_mul_mul,
      compactCoordOne_compactCartanReflection_mul_mul]
    rw [show -(ℓ + 2) = -ℓ - 2 by ring, show -(ℓ - 2) = -ℓ + 2 by ring]
    push_cast
    module
  simpa using congr($h v)

/-- The reflection maps the vectors supported on `S` onto those supported on `-S`. -/
theorem reflection_mem_weightLieSubmodule_iff {S S' : Set ℤ}
    {hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0} {hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0}
    {hX' : ∀ ℓ ∈ S', ℓ + 2 ∉ S' → k + ℓ = 0} {hY' : ∀ ℓ ∈ S', ℓ - 2 ∉ S' → k - ℓ = 0}
    (hS : ∀ ℓ, -ℓ ∈ S' ↔ ℓ ∈ S) {v : CompactWeightModule k μ} :
    reflection k μ v ∈ weightLieSubmodule k μ S' hX' hY' ↔ v ∈ weightLieSubmodule k μ S hX hY := by
  simp only [mem_weightLieSubmodule, Finsupp.mem_supported', equivFinsupp_reflection_apply]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h _ fun h' ↦ hx (by simpa using (hS (-x)).2 h')⟩
  simpa using h (-x) fun h' ↦ hx ((hS x).1 h')

/-- The reflection preserves `D_k(μ)`. -/
theorem reflection_mem_discreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ discreteSeries k μ ↔ v ∈ discreteSeries k μ :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [mem_discreteSeriesWeights, abs_neg]
    omega

/-- **The reflection interchanges the two rays** `D_k^+(μ)` and `D_k^-(μ)`. -/
theorem reflection_mem_negativeDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ negativeDiscreteSeries k μ ↔ v ∈ positiveDiscreteSeries k μ :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [mem_negativeDiscreteSeriesWeights, mem_positiveDiscreteSeriesWeights]
    omega

/-- The reflection maps the negative ray onto the positive ray. -/
theorem reflection_mem_positiveDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ positiveDiscreteSeries k μ ↔ v ∈ negativeDiscreteSeries k μ :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [mem_negativeDiscreteSeriesWeights, mem_positiveDiscreteSeriesWeights]
    omega

end CompactWeightModule

/-! ### Checks -/

/-- At the lowest positive weight, `Y_c v_k = 0`. -/
theorem lie_compactCartanY_weightVector_self (k : ℕ) :
    ⁅compactCartanY, weightVector (k : ℂ) μ k⁆ = 0 := by
  simp

/-- At the lowest positive weight, `X_c v_k = k v_{k + 2}`. -/
theorem lie_compactCartanX_weightVector_self (k : ℕ) :
    ⁅compactCartanX, weightVector (k : ℂ) μ k⁆ = (k : ℂ) • weightVector (k : ℂ) μ (k + 2) := by
  simp only [lie_compactCartanX_weightVector, Int.cast_natCast]
  congr 1
  ring

/-- `Y_c v_{k + 2} = -v_k`: the minus sign that the bracket and the Casimir need. -/
theorem lie_compactCartanY_weightVector_add_two (k : ℕ) :
    ⁅compactCartanY, weightVector (k : ℂ) μ (k + 2)⁆ = -weightVector (k : ℂ) μ k := by
  simp only [lie_compactCartanY_weightVector, add_sub_cancel_right]
  push_cast
  rw [← neg_one_smul ℂ]
  congr 1
  ring

/-- At the highest negative weight, `X_c v_{-k} = 0`. -/
theorem lie_compactCartanX_weightVector_neg_self (k : ℕ) :
    ⁅compactCartanX, weightVector (k : ℂ) μ (-k)⁆ = 0 := by
  simp

/-- `D₂` has Casimir `0`, the infinitesimal character of the trivial representation; the scalar
`(k² - 1) / 4` would give `3 / 4`. -/
theorem compactCasimir_discreteSeries_two (v : discreteSeries 2 μ) :
    compactCasimir (discreteSeries 2 μ) v = 0 := by
  rw [compactCasimir_discreteSeries]
  norm_num

/-- The limit `D₁` has Casimir `-1/4`. -/
theorem compactCasimir_discreteSeries_one (v : discreteSeries 1 μ) :
    compactCasimir (discreteSeries 1 μ) v = (-1 / 4 : ℂ) • v := by
  rw [compactCasimir_discreteSeries]
  norm_num

end TauCeti
