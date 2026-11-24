/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Casimir
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported

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
vectors supported on the two rays (`TauCeti.discreteSeries μ k`): `X_c` leaves the negative ray only
from `v_{-k}`, where its coefficient `(k - k) / 2` vanishes, and `Y_c` leaves the positive ray only
from `v_k`. The rays themselves are Lie submodules `TauCeti.positiveDiscreteSeries μ k` and
`TauCeti.negativeDiscreteSeries μ k`, the lowest and highest weight modules `D_k^±`.

## Main definitions

* `TauCeti.compactCartanH`, `TauCeti.compactCartanX`, `TauCeti.compactCartanY`: the compact Cartan
  basis, with `TauCeti.isSl2Triple_compactCartan`.
* `TauCeti.compactRep k μ`: the Lie algebra homomorphism `𝔤𝔩₂(ℂ) → End(ℤ →₀ ℂ)` given by the
  formulas above, and `TauCeti.CompactWeightModule k μ`, the resulting module.
* `TauCeti.weightVector k μ ℓ`: the weight vector `v_ℓ`.
* `TauCeti.discreteSeries μ k`: `D_k(μ)`, with the rays `TauCeti.positiveDiscreteSeries μ k` and
  `TauCeti.negativeDiscreteSeries μ k`.
* `TauCeti.reflection k μ`: `v_ℓ ↦ v_{-ℓ}`.
* `TauCeti.compactCasimir`: the Casimir operator `Ω = (H_c² + 2X_cY_c + 2Y_cX_c) / 4` of a
  `𝔤𝔩₂(ℂ)`-module.

## Main results

* `TauCeti.lie_compactCartanH_weightVector`, `TauCeti.lie_compactCartanX_weightVector`,
  `TauCeti.lie_compactCartanY_weightVector`: the normalization above;
  `TauCeti.lie_rotationGenerator_weightVector`: `J v_ℓ = iℓ v_ℓ`, so that `r_θ = exp(θJ)` acts on
  `v_ℓ` by `e^{iℓθ}`.
* `TauCeti.one_lie_discreteSeries`: the central scalar of `D_k(μ)` is `μ`.
* `TauCeti.compactCasimir_discreteSeries`: the Casimir operator of `D_k(μ)` is `k (k - 2) / 4`.
* `TauCeti.discreteSeries_eq_sup`: `D_k(μ)` is the sum of its two rays.
* `TauCeti.reflection_lie`: the reflection intertwines the action of `M` with that of `A M A⁻¹`;
  `TauCeti.reflection_mem_negativeDiscreteSeries_iff`: it interchanges the two rays.

The checks of the roadmap are `TauCeti.lie_compactCartanY_weightVector_self`,
`TauCeti.lie_compactCartanX_weightVector_self`, `TauCeti.lie_compactCartanY_weightVector_add_two`,
`TauCeti.lie_compactCartanX_weightVector_neg_self`, `TauCeti.compactCasimir_discreteSeries_two`
and `TauCeti.compactCasimir_discreteSeries_one`.

## Implementation notes

`𝔤𝔩₂(ℂ)` is `Matrix (Fin 2) (Fin 2) ℂ` with the commutator bracket, through the local instance
`LieRing.ofAssociativeRing`, as elsewhere in Tau Ceti.

## References

The AutomorphicFormsOnReductiveGroups roadmap, §2.6, citing Knapp, §2, pp.398–400, and Casselman,
*Representations of SL₂(ℝ)*, §§2, 5–6.
-/

public section

noncomputable section

open Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-! ### The compact Cartan basis of `𝔤𝔩₂(ℂ)` -/

/-- The compact Cartan element `H_c = -iJ`, `J = E₁₂ - E₂₁`. -/
def compactCartanH : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The compact raising element `X_c = (A + iB) / 2`, `A = diag(1, -1)`, `B = E₁₂ + E₂₁`. -/
def compactCartanX : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, I / 2; I / 2, -1 / 2]

/-- The compact lowering element `Y_c = (A - iB) / 2`. -/
def compactCartanY : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, -I / 2; -I / 2, -1 / 2]

/-- `[X_c, Y_c] = H_c`; explicitly `[X_c, Y_c] = [[0, -i], [i, 0]]`. -/
theorem lie_compactCartanX_compactCartanY :
    ⁅compactCartanX, compactCartanY⁆ = compactCartanH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanX, compactCartanY, compactCartanH, Ring.lie_def] <;> ring_nf

/-- `[H_c, X_c] = 2 X_c`. -/
theorem lie_compactCartanH_compactCartanX :
    ⁅compactCartanH, compactCartanX⁆ = (2 : ℂ) • compactCartanX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanX, compactCartanH, Ring.lie_def] <;> ring_nf <;> simp [I_sq]

/-- `[H_c, Y_c] = -2 Y_c`. -/
theorem lie_compactCartanH_compactCartanY :
    ⁅compactCartanH, compactCartanY⁆ = -((2 : ℂ) • compactCartanY) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCartanY, compactCartanH, Ring.lie_def] <;> ring_nf <;> simp [I_sq]


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

/-- The `H_c`-coordinate of a bracket. -/
theorem compactCoord_lie_H (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH ⁅M, N⁆ =
      compactCoordX M * compactCoordY N - compactCoordY M * compactCoordX N := by
  simp only [compactCoordH, compactCoordX, compactCoordY, LinearMap.coe_mk, AddHom.coe_mk,
    Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

/-- The `X_c`-coordinate of a bracket. -/
theorem compactCoord_lie_X (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX ⁅M, N⁆ =
      2 * (compactCoordH M * compactCoordX N - compactCoordX M * compactCoordH N) := by
  simp only [compactCoordH, compactCoordX, LinearMap.coe_mk, AddHom.coe_mk,
    Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp only [I_sq]
  ring

/-- The `Y_c`-coordinate of a bracket. -/
theorem compactCoord_lie_Y (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY ⁅M, N⁆ =
      -(2 * (compactCoordH M * compactCoordY N - compactCoordY M * compactCoordH N)) := by
  simp only [compactCoordH, compactCoordY, LinearMap.coe_mk, AddHom.coe_mk,
    Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp only [I_sq]
  ring

/-- A bracket has no component along the identity. -/
theorem compactCoord_lie_one (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne ⁅M, N⁆ = 0 := by
  simp only [compactCoordOne, LinearMap.coe_mk, AddHom.coe_mk, Ring.lie_def, Matrix.sub_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Every matrix is `a H_c + b X_c + c Y_c + d 1` in its compact Cartan coordinates. -/
theorem eq_compactCoord (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = compactCoordH M • compactCartanH + compactCoordX M • compactCartanX +
      compactCoordY M • compactCartanY + compactCoordOne M • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCoordH, compactCoordX, compactCoordY, compactCoordOne, compactCartanH,
      compactCartanX, compactCartanY] <;> ring_nf <;> simp [I_sq]

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

/-! ### The representation of `𝔤𝔩₂(ℂ)` on all weights -/

/-- Brackets of combinations `a W + b R + c L + d` of three operators obeying the `sl₂` relations
and the identity. -/
private theorem lie_combination {E : Type*} [AddCommGroup E] [Module ℂ E] {W R L : Module.End ℂ E}
    (hRL : ⁅R, L⁆ = W) (hWR : ⁅W, R⁆ = (2 : ℂ) • R) (hWL : ⁅W, L⁆ = -((2 : ℂ) • L))
    (a b c d a' b' c' d' : ℂ) :
    ⁅a • W + b • R + c • L + d • (1 : Module.End ℂ E),
      a' • W + b' • R + c' • L + d' • (1 : Module.End ℂ E)⁆ =
      (b * c' - c * b') • W + (2 * (a * b' - b * a')) • R +
        (-(2 * (a * c' - c * a'))) • L := by
  have hLR : ⁅L, R⁆ = -W := by rw [← lie_skew, hRL]
  have hRW : ⁅R, W⁆ = -((2 : ℂ) • R) := by rw [← lie_skew, hWR]
  have hLW : ⁅L, W⁆ = (2 : ℂ) • L := by rw [← lie_skew, hWL, neg_neg]
  have h1 : ∀ x : Module.End ℂ E, ⁅x, (1 : Module.End ℂ E)⁆ = 0 := fun x ↦
    (Ring.lie_def _ _).trans (by rw [mul_one, one_mul, sub_self])
  have h1' : ∀ x : Module.End ℂ E, ⁅(1 : Module.End ℂ E), x⁆ = 0 := fun x ↦
    (Ring.lie_def _ _).trans (by rw [mul_one, one_mul, sub_self])
  simp only [lie_add, add_lie, lie_smul, smul_lie, lie_self, hRL, hWR, hWL, hLR, hRW, hLW, h1,
    h1', smul_zero, add_zero, zero_add, smul_neg, smul_smul]
  module

/-- The linear map underlying `TauCeti.compactRep`. -/
def compactRepLinear (k μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Module.End ℂ (ℤ →₀ ℂ) :=
  compactCoordH.smulRight compactWeightOp + compactCoordX.smulRight (compactRaiseOp k) +
    compactCoordY.smulRight (compactLowerOp k) + (μ • compactCoordOne).smulRight 1

/-- The linear map underlying `TauCeti.compactRep`, in coordinates. -/
theorem compactRepLinear_apply (k μ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
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
      compactCoord_lie_H, compactCoord_lie_X, compactCoord_lie_Y, compactCoord_lie_one, mul_zero,
      zero_smul, add_zero]
    rw [lie_combination (lie_compactRaiseOp_compactLowerOp k)
      (lie_compactWeightOp_compactRaiseOp k) (lie_compactWeightOp_compactLowerOp k)]

/-- `TauCeti.compactRep k μ M` in the compact Cartan coordinates of `M`. -/
theorem compactRep_apply (k μ : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactRep k μ M = compactCoordH M • compactWeightOp + compactCoordX M • compactRaiseOp k +
      compactCoordY M • compactLowerOp k + (μ * compactCoordOne M) • 1 :=
  compactRepLinear_apply k μ M

/-- `H_c` acts by the weight operator. -/
theorem compactRep_compactCartanH (k μ : ℂ) : compactRep k μ compactCartanH = compactWeightOp := by
  have h1 : compactCoordH compactCartanH = 1 := by
    simp [compactCoordH, compactCartanH]; ring_nf; simp [I_sq]
  rw [compactRep_apply, h1]
  simp [compactCoordX, compactCoordY, compactCoordOne, compactCartanH]

/-- `X_c` acts by the raising operator. -/
theorem compactRep_compactCartanX (k μ : ℂ) :
    compactRep k μ compactCartanX = compactRaiseOp k := by
  have h1 : compactCoordX compactCartanX = 1 := by
    simp [compactCoordX, compactCartanX]; ring_nf
  have h2 : compactCoordY compactCartanX = 0 := by
    simp [compactCoordY, compactCartanX]; ring_nf
  rw [compactRep_apply, h1, h2]
  simp [compactCoordH, compactCoordOne, compactCartanX]
  norm_num

/-- `Y_c` acts by the lowering operator. -/
theorem compactRep_compactCartanY (k μ : ℂ) :
    compactRep k μ compactCartanY = compactLowerOp k := by
  have h1 : compactCoordY compactCartanY = 1 := by
    simp [compactCoordY, compactCartanY]; ring_nf
  have h2 : compactCoordX compactCartanY = 0 := by
    simp [compactCoordX, compactCartanY]; ring_nf
  rw [compactRep_apply, h1, h2]
  simp [compactCoordH, compactCoordOne, compactCartanY]
  norm_num

/-- The identity matrix acts by `μ`. -/
theorem compactRep_one (k μ : ℂ) : compactRep k μ 1 = μ • 1 := by
  rw [compactRep_apply]
  simp [compactCoordH, compactCoordX, compactCoordY, compactCoordOne]

/-! ### The module of all compact weights -/

/-- The `𝔤𝔩₂(ℂ)`-module of finitely supported vectors `∑ c_ℓ v_ℓ` on all compact weights `ℓ ∈ ℤ`,
with `H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`, and
the identity matrix acting by `μ`. The discrete series `D_k(μ)` is its Lie submodule
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

end CompactWeightModule

variable {k μ : ℂ}

/-- The bracket of `𝔤𝔩₂(ℂ)` with `TauCeti.CompactWeightModule k μ` is `TauCeti.compactRep k μ`. -/
theorem lie_compactWeightModule (M : Matrix (Fin 2) (Fin 2) ℂ) (v : CompactWeightModule k μ) :
    ⁅M, v⁆ = (compactRep k μ M : Module.End ℂ (ℤ →₀ ℂ)) v :=
  (rfl)

variable (k μ) in
/-- The weight vector `v_ℓ`. -/
def weightVector (ℓ : ℤ) : CompactWeightModule k μ := Finsupp.single ℓ 1

variable (k μ) in
/-- The weight vectors form a basis of `TauCeti.CompactWeightModule k μ`. -/
def weightBasis : Module.Basis ℤ ℂ (CompactWeightModule k μ) := Finsupp.basisSingleOne

/-- The basis vectors are the weight vectors. -/
@[simp]
theorem weightBasis_apply (ℓ : ℤ) : weightBasis k μ ℓ = weightVector k μ ℓ :=
  (rfl)

/-- `H_c v_ℓ = ℓ v_ℓ`. -/
@[simp]
theorem lie_compactCartanH_weightVector (ℓ : ℤ) :
    ⁅compactCartanH, weightVector k μ ℓ⁆ = (ℓ : ℂ) • weightVector k μ ℓ := by
  rw [lie_compactWeightModule, compactRep_compactCartanH]
  exact compactWeightOp_single ℓ

/-- `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`. -/
@[simp]
theorem lie_compactCartanX_weightVector (ℓ : ℤ) :
    ⁅compactCartanX, weightVector k μ ℓ⁆ = ((k + ℓ) / 2) • weightVector k μ (ℓ + 2) := by
  rw [lie_compactWeightModule, compactRep_compactCartanX]
  exact compactRaiseOp_single k ℓ

/-- `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`. -/
@[simp]
theorem lie_compactCartanY_weightVector (ℓ : ℤ) :
    ⁅compactCartanY, weightVector k μ ℓ⁆ = ((k - ℓ) / 2) • weightVector k μ (ℓ - 2) := by
  rw [lie_compactWeightModule, compactRep_compactCartanY]
  exact compactLowerOp_single k ℓ

/-- **The central scalar**: the identity matrix acts by `μ`. -/
@[simp]
theorem one_lie_compactWeightModule (v : CompactWeightModule k μ) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v := by
  rw [lie_compactWeightModule, compactRep_one]
  rfl

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

/-- `J = E₁₂ - E₂₁`, the generator of the rotations `r_θ = exp(θJ)`. -/
def rotationGenerator : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `H_c = -iJ`. -/
theorem compactCartanH_eq : compactCartanH = -I • rotationGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanH, rotationGenerator]

/-- `X_c = (A + iB) / 2` with `A = diag(1, -1)` and `B = E₁₂ + E₂₁`. -/
theorem compactCartanX_eq :
    compactCartanX = (1 / 2 : ℂ) • (!![1, 0; 0, -1] + I • !![0, 1; 1, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanX] <;> ring

/-- `Y_c = (A - iB) / 2` with `A = diag(1, -1)` and `B = E₁₂ + E₂₁`. -/
theorem compactCartanY_eq :
    compactCartanY = (1 / 2 : ℂ) • (!![1, 0; 0, -1] - I • !![0, 1; 1, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanY] <;> ring

/-- `J v_ℓ = iℓ v_ℓ`, the derivative of `r_θ v_ℓ = e^{iℓθ} v_ℓ`. -/
theorem lie_rotationGenerator_weightVector (ℓ : ℤ) :
    ⁅rotationGenerator, weightVector k μ ℓ⁆ = (I * ℓ) • weightVector k μ ℓ := by
  have hJ : rotationGenerator = I • compactCartanH := by
    rw [compactCartanH_eq, smul_smul]
    simp
  rw [hJ, smul_lie, lie_compactCartanH_weightVector, smul_smul]

/-- The **Casimir operator** `Ω = (H_c² + 2 X_c Y_c + 2 Y_c X_c) / 4` of a `𝔤𝔩₂(ℂ)`-module: half of
the Casimir operator `TauCeti.sl2Casimir` of the compact triple. -/
def compactCasimir (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) V] [LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) V] :
    Module.End ℂ V :=
  (2⁻¹ : ℂ) • sl2Casimir ℂ compactCartanH compactCartanX compactCartanY V

/-- **The Casimir operator acts by `k(k - 2)/4`** on every vector of
`TauCeti.CompactWeightModule k μ`. -/
theorem compactCasimir_compactWeightModule :
    compactCasimir (CompactWeightModule k μ) = (k * (k - 2) / 4) • 1 := by
  refine (weightBasis k μ).ext fun ℓ ↦ ?_
  simp only [weightBasis_apply, compactCasimir, LinearMap.smul_apply, sl2Casimir_apply,
    lie_compactCartanH_weightVector, lie_compactCartanX_weightVector,
    lie_compactCartanY_weightVector, lie_smul, sub_add_cancel, add_sub_cancel_right, smul_smul,
    one_apply_eq_self]
  rw [← add_smul, ← add_smul, smul_smul]
  congr 1
  push_cast
  ring

/-! ### Lie submodules spanned by weight vectors -/

/-- An endomorphism of `ℤ →₀ ℂ` preserves the vectors supported on `S` as soon as it sends each
`v_ℓ`, `ℓ ∈ S`, to one of them. -/
private theorem mem_supported_of_single {f : Module.End ℂ (ℤ →₀ ℂ)} {S : Set ℤ}
    (h : ∀ ℓ ∈ S, f (Finsupp.single ℓ 1) ∈ Finsupp.supported ℂ ℂ S) {v : ℤ →₀ ℂ}
    (hv : v ∈ Finsupp.supported ℂ ℂ S) : f v ∈ Finsupp.supported ℂ ℂ S := by
  rw [Finsupp.supported_eq_span_single] at hv
  have hle : Submodule.map f (Submodule.span ℂ ((fun i ↦ Finsupp.single i (1 : ℂ)) '' S)) ≤
      Finsupp.supported ℂ ℂ S := by
    rw [Submodule.map_span_le]
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact h ℓ hℓ
  exact hle ⟨v, hv, rfl⟩

variable (k μ) in
/-- The Lie submodule of `TauCeti.CompactWeightModule k μ` of the vectors supported on a set `S` of
weights that `X_c` and `Y_c` leave only with coefficient zero. -/
def weightLieSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ) where
  toSubmodule := (Finsupp.supported ℂ ℂ S).comap (CompactWeightModule.equivFinsupp k μ).toLinearMap
  lie_mem {M v} hv := by
    change (compactRep k μ M) (CompactWeightModule.equivFinsupp k μ v) ∈ Finsupp.supported ℂ ℂ S
    set w := CompactWeightModule.equivFinsupp k μ v
    have hw : w ∈ Finsupp.supported ℂ ℂ S := hv
    have hW : compactWeightOp w ∈ Finsupp.supported ℂ ℂ S := mem_supported_of_single
      (fun ℓ hℓ ↦ by
        rw [compactWeightOp_single]
        exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ hℓ)) hw
    have hR : compactRaiseOp k w ∈ Finsupp.supported ℂ ℂ S := mem_supported_of_single
      (fun ℓ hℓ ↦ by
        rw [compactRaiseOp_single]
        by_cases h : ℓ + 2 ∈ S
        · exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ h)
        · rw [hX ℓ hℓ h, zero_div, zero_smul]
          exact zero_mem _) hw
    have hL : compactLowerOp k w ∈ Finsupp.supported ℂ ℂ S := mem_supported_of_single
      (fun ℓ hℓ ↦ by
        rw [compactLowerOp_single]
        by_cases h : ℓ - 2 ∈ S
        · exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ h)
        · rw [hY ℓ hℓ h, zero_div, zero_smul]
          exact zero_mem _) hw
    rw [compactRep_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self]
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ hW) (Submodule.smul_mem _ _ hR))
      (Submodule.smul_mem _ _ hL)) (Submodule.smul_mem _ _ hw)

/-- Membership in `TauCeti.weightLieSubmodule`: the coordinates are supported on `S`. -/
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

/-! ### The discrete series `D_k(μ)` -/

/-- The weights of `D_k`: `|ℓ| ≥ k` and `ℓ ≡ k mod 2`, the two rays. -/
def discreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | (k : ℤ) ≤ |ℓ| ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of the positive ray `D_k^+`: `ℓ ≥ k` and `ℓ ≡ k mod 2`. -/
def positiveDiscreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | (k : ℤ) ≤ ℓ ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of the negative ray `D_k^-`: `ℓ ≤ -k` and `ℓ ≡ k mod 2`. -/
def negativeDiscreteSeriesWeights (k : ℕ) : Set ℤ := {ℓ | ℓ ≤ -(k : ℤ) ∧ ℓ % 2 = (k : ℤ) % 2}

/-- The weights of `D_k` are those of its two rays. -/
theorem discreteSeriesWeights_eq_union (k : ℕ) :
    discreteSeriesWeights k =
      positiveDiscreteSeriesWeights k ∪ negativeDiscreteSeriesWeights k := by
  ext ℓ
  simp only [discreteSeriesWeights, positiveDiscreteSeriesWeights, negativeDiscreteSeriesWeights,
    Set.mem_ofPred_eq, Set.mem_union]
  rcases abs_cases ℓ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

private theorem discreteSeriesWeights_raise {k : ℕ} :
    ∀ ℓ ∈ discreteSeriesWeights k, ℓ + 2 ∉ discreteSeriesWeights k → (k : ℂ) + ℓ = 0 := by
  intro ℓ hℓ h
  rw [discreteSeriesWeights_eq_union] at hℓ h
  simp only [positiveDiscreteSeriesWeights, negativeDiscreteSeriesWeights, Set.mem_union,
    Set.mem_ofPred_eq] at hℓ h
  have : (k : ℤ) + ℓ = 0 := by omega
  exact_mod_cast this

private theorem discreteSeriesWeights_lower {k : ℕ} :
    ∀ ℓ ∈ discreteSeriesWeights k, ℓ - 2 ∉ discreteSeriesWeights k → (k : ℂ) - ℓ = 0 := by
  intro ℓ hℓ h
  rw [discreteSeriesWeights_eq_union] at hℓ h
  simp only [positiveDiscreteSeriesWeights, negativeDiscreteSeriesWeights, Set.mem_union,
    Set.mem_ofPred_eq] at hℓ h
  have : (k : ℤ) - ℓ = 0 := by omega
  exact_mod_cast this

variable (μ) in
/-- **The discrete series `D_k(μ)`** of `GL₂(ℝ)` (`k ≥ 2`), and its limit at `k = 1`, as an explicit
`𝔤𝔩₂(ℂ)`-module: the finitely supported vectors on the weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2`, with
`H_c v_ℓ = ℓ v_ℓ`, `X_c v_ℓ = (k + ℓ) / 2 v_{ℓ + 2}`, `Y_c v_ℓ = (k - ℓ) / 2 v_{ℓ - 2}`, central
scalar `μ` and Casimir `k (k - 2) / 4`. -/
def discreteSeries (k : ℕ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (discreteSeriesWeights k) discreteSeriesWeights_raise
    discreteSeriesWeights_lower

variable (μ) in
/-- The positive ray `D_k^+(μ)`, the lowest weight module of lowest weight `k`, the restriction of
`D_k(μ)` to the identity component of `GL₂(ℝ)` keeping the positive weights. -/
def positiveDiscreteSeries (k : ℕ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (positiveDiscreteSeriesWeights k)
    (fun ℓ hℓ h ↦ by
      simp only [positiveDiscreteSeriesWeights, Set.mem_ofPred_eq] at hℓ h
      omega)
    (fun ℓ hℓ h ↦ by
      simp only [positiveDiscreteSeriesWeights, Set.mem_ofPred_eq] at hℓ h
      have : (k : ℤ) - ℓ = 0 := by omega
      exact_mod_cast this)

variable (μ) in
/-- The negative ray `D_k^-(μ)`, the highest weight module of highest weight `-k`. -/
def negativeDiscreteSeries (k : ℕ) :
    LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ) :=
  weightLieSubmodule (k : ℂ) μ (negativeDiscreteSeriesWeights k)
    (fun ℓ hℓ h ↦ by
      simp only [negativeDiscreteSeriesWeights, Set.mem_ofPred_eq] at hℓ h
      have : (k : ℤ) + ℓ = 0 := by omega
      exact_mod_cast this)
    (fun ℓ hℓ h ↦ by
      simp only [negativeDiscreteSeriesWeights, Set.mem_ofPred_eq] at hℓ h
      omega)

/-- `D_k(μ)` is the sum of its two rays. -/
theorem discreteSeries_eq_sup (k : ℕ) :
    discreteSeries μ k = positiveDiscreteSeries μ k ⊔ negativeDiscreteSeries μ k := by
  refine LieSubmodule.toSubmodule_injective ?_
  rw [LieSubmodule.sup_toSubmodule]
  change Submodule.comap _ _ = Submodule.comap _ _ ⊔ Submodule.comap _ _
  rw [discreteSeriesWeights_eq_union, Finsupp.supported_union, Submodule.comap_equiv_eq_map_symm,
    Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]

/-- `v_ℓ ∈ D_k(μ)` for every allowed weight. -/
theorem weightVector_mem_discreteSeries {k : ℕ} {ℓ : ℤ} (hℓ : ℓ ∈ discreteSeriesWeights k) :
    weightVector (k : ℂ) μ ℓ ∈ discreteSeries μ k :=
  weightVector_mem_weightLieSubmodule hℓ

/-- **The Casimir operator of `D_k(μ)` is `k (k - 2) / 4`.** -/
theorem compactCasimir_discreteSeries (k : ℕ) (v : discreteSeries μ k) :
    compactCasimir (discreteSeries μ k) v = ((k : ℂ) * (k - 2) / 4) • v := by
  ext
  simp only [compactCasimir, LinearMap.smul_apply, LieSubmodule.coe_smul,
    coe_sl2Casimir_lieSubmodule]
  have := congr($(compactCasimir_compactWeightModule (k := (k : ℂ)) (μ := μ)) (v : _))
  simpa [compactCasimir] using this

/-- **The central scalar of `D_k(μ)` is `μ`.** -/
theorem one_lie_discreteSeries (k : ℕ) (v : discreteSeries μ k) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) ℂ), v⁆ = μ • v := by
  ext
  simp

/-! ### The reflection -/

/-- The reflection `A = diag(1, -1)` of `O(2)`. -/
def reflectionMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Conjugation by `A = diag(1, -1)` negates the off-diagonal entries. -/
theorem reflectionMatrix_mul_mul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    reflectionMatrix * M * reflectionMatrix = !![M 0 0, -M 0 1; -M 1 0, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- Conjugation by `A` negates the `H_c`-coordinate. -/
theorem compactCoordH_reflect (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH (reflectionMatrix * M * reflectionMatrix) = -compactCoordH M := by
  rw [reflectionMatrix_mul_mul]
  simp [compactCoordH]
  ring

/-- Conjugation by `A` moves the `Y_c`-coordinate to `X_c`. -/
theorem compactCoordX_reflect (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX (reflectionMatrix * M * reflectionMatrix) = compactCoordY M := by
  rw [reflectionMatrix_mul_mul]
  simp [compactCoordX, compactCoordY]
  ring

/-- Conjugation by `A` moves the `X_c`-coordinate to `Y_c`. -/
theorem compactCoordY_reflect (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY (reflectionMatrix * M * reflectionMatrix) = compactCoordX M := by
  rw [reflectionMatrix_mul_mul]
  simp [compactCoordX, compactCoordY]
  ring

/-- Conjugation by `A` fixes the coordinate along the identity. -/
theorem compactCoordOne_reflect (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne (reflectionMatrix * M * reflectionMatrix) = compactCoordOne M := by
  rw [reflectionMatrix_mul_mul]
  simp [compactCoordOne]

variable (k μ) in
/-- The **reflection** `v_ℓ ↦ v_{-ℓ}`, the action of `A = diag(1, -1)`, which interchanges the two
rays of `D_k(μ)`. -/
def reflection : CompactWeightModule k μ ≃ₗ[ℂ] CompactWeightModule k μ :=
  Finsupp.domLCongr (Equiv.neg ℤ)

/-- The reflection sends `v_ℓ` to `v_{-ℓ}`. -/
@[simp]
theorem reflection_weightVector (ℓ : ℤ) :
    reflection k μ (weightVector k μ ℓ) = weightVector k μ (-ℓ) :=
  Finsupp.domLCongr_single _ _ _

/-- The reflection intertwines the action of `M` with that of `A M A⁻¹`, `A = diag(1, -1)`: it
exchanges `X_c` and `Y_c` and negates `H_c`. -/
theorem reflection_lie (M : Matrix (Fin 2) (Fin 2) ℂ) (v : CompactWeightModule k μ) :
    reflection k μ ⁅M, v⁆ = ⁅reflectionMatrix * M * reflectionMatrix, reflection k μ v⁆ := by
  have h : (reflection k μ).toLinearMap ∘ₗ LieModule.toEnd ℂ _ _ M =
      LieModule.toEnd ℂ _ _ (reflectionMatrix * M * reflectionMatrix) ∘ₗ
        (reflection k μ).toLinearMap := by
    refine (weightBasis k μ).ext fun ℓ ↦ ?_
    simp only [weightBasis_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LieModule.toEnd_apply_apply, reflection_weightVector, lie_weightVector, map_add, map_smul,
      compactCoordH_reflect, compactCoordX_reflect, compactCoordY_reflect,
      compactCoordOne_reflect]
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
  simp only [mem_weightLieSubmodule, Finsupp.mem_supported']
  change (∀ x ∉ S', Finsupp.equivMapDomain (Equiv.neg ℤ) (CompactWeightModule.equivFinsupp k μ v)
    x = 0) ↔ _
  simp only [Finsupp.equivMapDomain_apply, Equiv.neg_symm, Equiv.neg_apply]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h _ fun h' ↦ hx (by simpa using (hS (-x)).2 h')⟩
  simpa using h (-x) fun h' ↦ hx ((hS x).1 h')

/-- The reflection preserves `D_k(μ)`. -/
theorem reflection_mem_discreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ discreteSeries μ k ↔ v ∈ discreteSeries μ k :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [discreteSeriesWeights, Set.mem_ofPred_eq, abs_neg]
    omega

/-- **The reflection interchanges the two rays** `D_k^+(μ)` and `D_k^-(μ)`. -/
theorem reflection_mem_negativeDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ negativeDiscreteSeries μ k ↔ v ∈ positiveDiscreteSeries μ k :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [negativeDiscreteSeriesWeights, positiveDiscreteSeriesWeights, Set.mem_ofPred_eq]
    omega

/-- The reflection maps the negative ray onto the positive ray. -/
theorem reflection_mem_positiveDiscreteSeries_iff {k : ℕ} {v : CompactWeightModule (k : ℂ) μ} :
    reflection (k : ℂ) μ v ∈ positiveDiscreteSeries μ k ↔ v ∈ negativeDiscreteSeries μ k :=
  reflection_mem_weightLieSubmodule_iff fun ℓ ↦ by
    simp only [negativeDiscreteSeriesWeights, positiveDiscreteSeriesWeights, Set.mem_ofPred_eq]
    omega

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
theorem compactCasimir_discreteSeries_two (v : discreteSeries μ 2) :
    compactCasimir (discreteSeries μ 2) v = 0 := by
  rw [compactCasimir_discreteSeries]
  norm_num

/-- The limit `D₁` has Casimir `-1/4`. -/
theorem compactCasimir_discreteSeries_one (v : discreteSeries μ 1) :
    compactCasimir (discreteSeries μ 1) v = (-1 / 4 : ℂ) • v := by
  rw [compactCasimir_discreteSeries]
  norm_num

end TauCeti
