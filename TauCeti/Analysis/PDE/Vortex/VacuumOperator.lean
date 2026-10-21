/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The gauge-fixed vortex operator at the vacuum

The vortex equations on the plane, for an imaginary connection `a` on the trivial line bundle and
a section `α`, are `∂bar_a α = 0` and `*iF_a = (1 - |α|²) / 8`; the gauge group acts by
`(a, α) ↦ (a - u⁻¹ du, u α)`. Identify the plane with `ℂ`, with coordinates `z = s + i t`, and write
`∂₁ = ∂_{1}` and `∂₂ = ∂_{I}` for the coordinate derivatives. A first-order deformation of the
vacuum `(0, 1)` is written `a = i (b₁ ds + b₂ dt)` and `α = 1 + 2 p + 2 i q`, so that the
coefficient metric `|b|² + |δα|² / 4` becomes the Euclidean metric on `x = (b₁, b₂, p, q) ∈ ℝ⁴`. In
these coordinates the gauge-fixed linearization of the vortex equations at the vacuum is the
first-order operator `L₀ x = (G, C, H₁, H₂)` with

* `G = ∂₁ b₁ + ∂₂ b₂ + q / 2` (the formal adjoint of the infinitesimal gauge action),
* `C = -∂₁ b₂ + ∂₂ b₁ + p / 2` (the linearized curvature equation),
* `H₁ = ∂₁ p - ∂₂ q - b₂ / 2` and `H₂ = ∂₁ q + ∂₂ p + b₁ / 2` (the real and imaginary parts of the
  linearized `∂bar_a α`).

This file defines `L₀` and its formal `L²` adjoint `L₀*` as continuous linear operators on
`ℝ⁴`-valued Schwartz fields on `ℂ`. It proves the Weitzenböck identities
`L₀* L₀ = L₀ L₀* = -Δ + 1 / 4` and the energy identity `‖L₀ x‖₂² = ‖∇x‖₂² + ‖x‖₂² / 4`, together
with their consequences `‖x‖₂ ≤ 2 ‖L₀ x‖₂` and the injectivity of `L₀` on Schwartz fields. These
are the vacuum inputs for the linear analysis of vortices, whose exterior regions are modelled on
the vacuum.

## Main declarations

* `TauCeti.Vortex.vacuumOperator`: the vacuum gauge-fixed operator `L₀`, characterized by the
  component formulas `TauCeti.Vortex.vacuumOperator_apply_zero` through
  `TauCeti.Vortex.vacuumOperator_apply_three`.
* `TauCeti.Vortex.vacuumAdjoint`: its formal adjoint `L₀*`, characterized by
  `TauCeti.Vortex.vacuumAdjoint_apply_zero` through `TauCeti.Vortex.vacuumAdjoint_apply_three`.
* `TauCeti.Vortex.integral_inner_vacuumOperator`: `∫ ⟪L₀ x, y⟫ = ∫ ⟪x, L₀* y⟫`.
* `TauCeti.Vortex.vacuumAdjoint_vacuumOperator` and `TauCeti.Vortex.vacuumOperator_vacuumAdjoint`:
  `L₀* L₀ = -Δ + 1 / 4` and `L₀ L₀* = -Δ + 1 / 4`.
* `TauCeti.Vortex.integral_norm_sq_vacuumOperator`: `‖L₀ x‖₂² = ‖∂₁ x‖₂² + ‖∂₂ x‖₂² + ‖x‖₂² / 4`.
* `TauCeti.Vortex.integral_norm_sq_le_four_mul_integral_norm_sq_vacuumOperator` and
  `TauCeti.Vortex.vacuumOperator_injective`: the resulting lower bound, and triviality of the
  kernel on Schwartz fields.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845--918.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open scoped SchwartzMap LineDeriv Laplacian RealInnerProductSpace
open Complex Matrix MeasureTheory SchwartzMap

/-- The coefficient matrix of `∂₁` in the vacuum operator, in the coordinates `(b₁, b₂, p, q)`. -/
private def coeffOne : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The coefficient matrix of `∂₂` in the vacuum operator. -/
private def coeffI : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- The zeroth-order coefficient matrix of the vacuum operator. -/
private def coeffZero : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 1 / 2; 0, 0, 1 / 2, 0; 0, -1 / 2, 0, 0; 1 / 2, 0, 0, 0]

/-- The constant-coefficient operator `A₁ ∂₁ + A₂ ∂₂ + B` on `ℝ⁴`-valued Schwartz fields. -/
private def firstOrder (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ) :
    𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) →L[ℝ] 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  (postcompCLM (toEuclideanCLM (𝕜 := ℝ) A₁)).comp
      (LineDeriv.lineDerivOpCLM ℝ 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) (1 : ℂ)) +
    (postcompCLM (toEuclideanCLM (𝕜 := ℝ) A₂)).comp
      (LineDeriv.lineDerivOpCLM ℝ 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) I) +
    postcompCLM (toEuclideanCLM (𝕜 := ℝ) B)

private theorem firstOrder_apply (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ)
    (x : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    firstOrder A₁ A₂ B x z = toEuclideanCLM (𝕜 := ℝ) A₁ (∂_{(1 : ℂ)} x z) +
      toEuclideanCLM (𝕜 := ℝ) A₂ (∂_{I} x z) + toEuclideanCLM (𝕜 := ℝ) B (x z) := by
  simp [firstOrder]

/-- The gauge-fixed vortex operator `L₀` at the vacuum, acting on deformations
`x = (b₁, b₂, p, q)` and producing `(G, C, H₁, H₂)`, where `G` is the gauge-fixing condition, `C`
the linearized curvature equation and `(H₁, H₂)` the linearized `∂bar_a α`; see the component
formulas `vacuumOperator_apply_zero` through `vacuumOperator_apply_three`. -/
def vacuumOperator : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) →L[ℝ] 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  firstOrder coeffOne coeffI coeffZero

/-- The formal `L²` adjoint `L₀*` of the vacuum operator, with respect to the Euclidean metrics on
the coordinates `(b₁, b₂, p, q)` and `(G, C, H₁, H₂)`; see `integral_inner_vacuumOperator` and the
component formulas `vacuumAdjoint_apply_zero` through `vacuumAdjoint_apply_three`. -/
def vacuumAdjoint : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) →L[ℝ] 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  firstOrder (-coeffOneᵀ) (-coeffIᵀ) coeffZeroᵀ

variable (x y : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ)

/-- The gauge component `G = ∂₁ b₁ + ∂₂ b₂ + q / 2` of `L₀`. -/
@[simp]
theorem vacuumOperator_apply_zero :
    vacuumOperator x z 0 = ∂_{(1 : ℂ)} x z 0 + ∂_{I} x z 1 + x z 3 / 2 := by
  simp [vacuumOperator, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The curvature component `C = ∂₂ b₁ - ∂₁ b₂ + p / 2` of `L₀`. -/
@[simp]
theorem vacuumOperator_apply_one :
    vacuumOperator x z 1 = ∂_{I} x z 0 - ∂_{(1 : ℂ)} x z 1 + x z 2 / 2 := by
  simp [vacuumOperator, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The first `∂bar` component `H₁ = ∂₁ p - ∂₂ q - b₂ / 2` of `L₀`. -/
@[simp]
theorem vacuumOperator_apply_two :
    vacuumOperator x z 2 = ∂_{(1 : ℂ)} x z 2 - ∂_{I} x z 3 - x z 1 / 2 := by
  simp [vacuumOperator, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The second `∂bar` component `H₂ = ∂₂ p + ∂₁ q + b₁ / 2` of `L₀`. -/
@[simp]
theorem vacuumOperator_apply_three :
    vacuumOperator x z 3 = ∂_{I} x z 2 + ∂_{(1 : ℂ)} x z 3 + x z 0 / 2 := by
  simp [vacuumOperator, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The `b₁` component `-∂₁ G - ∂₂ C + H₂ / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem vacuumAdjoint_apply_zero :
    vacuumAdjoint y z 0 = -∂_{(1 : ℂ)} y z 0 - ∂_{I} y z 1 + y z 3 / 2 := by
  simp [vacuumAdjoint, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The `b₂` component `-∂₂ G + ∂₁ C - H₁ / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem vacuumAdjoint_apply_one :
    vacuumAdjoint y z 1 = -∂_{I} y z 0 + ∂_{(1 : ℂ)} y z 1 - y z 2 / 2 := by
  simp [vacuumAdjoint, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The `p` component `-∂₁ H₁ - ∂₂ H₂ + C / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem vacuumAdjoint_apply_two :
    vacuumAdjoint y z 2 = -∂_{(1 : ℂ)} y z 2 - ∂_{I} y z 3 + y z 1 / 2 := by
  simp [vacuumAdjoint, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The `q` component `∂₂ H₁ - ∂₁ H₂ + G / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem vacuumAdjoint_apply_three :
    vacuumAdjoint y z 3 = ∂_{I} y z 2 - ∂_{(1 : ℂ)} y z 3 + y z 0 / 2 := by
  simp [vacuumAdjoint, firstOrder_apply, coeffOne, coeffI, coeffZero, mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

private theorem lineDerivOp_firstOrder (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ) (v : ℂ)
    (x : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∂_{v} (firstOrder A₁ A₂ B x) = firstOrder A₁ A₂ B (∂_{v} x) := by
  simp only [firstOrder, _root_.add_apply, ContinuousLinearMap.comp_apply,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOp_add, lineDerivOp_postcompCLM]
  rw [x.lineDerivOp_comm v, x.lineDerivOp_comm v]

/-- The vacuum operator has constant coefficients, so it commutes with directional
differentiation. -/
@[simp]
theorem lineDerivOp_vacuumOperator (v : ℂ) :
    ∂_{v} (vacuumOperator x) = vacuumOperator (∂_{v} x) :=
  lineDerivOp_firstOrder _ _ _ v x

/-- The formal adjoint has constant coefficients, so it commutes with directional
differentiation. -/
@[simp]
theorem lineDerivOp_vacuumAdjoint (v : ℂ) :
    ∂_{v} (vacuumAdjoint y) = vacuumAdjoint (∂_{v} y) :=
  lineDerivOp_firstOrder _ _ _ v y

/-- **The Weitzenböck identity at the vacuum**: `L₀* L₀ = -Δ + 1 / 4`. -/
theorem vacuumAdjoint_vacuumOperator :
    vacuumAdjoint (vacuumOperator x) = -Δ x + (1 / 4 : ℝ) • x := by
  have hc := x.lineDerivOp_comm I 1
  ext z i
  fin_cases i <;>
  · simp [lineDerivOp_vacuumOperator, laplacian_eq_lineDerivOp_one_I, hc]
    ring

/-- The reverse Weitzenböck identity at the vacuum: `L₀ L₀* = -Δ + 1 / 4`. -/
theorem vacuumOperator_vacuumAdjoint :
    vacuumOperator (vacuumAdjoint y) = -Δ y + (1 / 4 : ℝ) • y := by
  have hc := y.lineDerivOp_comm I 1
  ext z i
  fin_cases i <;>
  · simp [lineDerivOp_vacuumAdjoint, laplacian_eq_lineDerivOp_one_I, hc]
    ring

private theorem integral_inner_firstOrder (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ) :
    ∫ z, ⟪firstOrder A₁ A₂ B x z, y z⟫ = ∫ z, ⟪x z, firstOrder (-A₁ᵀ) (-A₂ᵀ) Bᵀ y z⟫ := by
  have hT (A : Matrix (Fin 4) (Fin 4) ℝ) (a b : EuclideanSpace ℝ (Fin 4)) :
      ⟪toEuclideanCLM (𝕜 := ℝ) A a, b⟫ = ⟪a, toEuclideanCLM (𝕜 := ℝ) Aᵀ b⟫ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hint (M : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      (f g : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) : Integrable (fun z ↦ ⟪M (f z), g z⟫) := by
    simpa only [postcompCLM_apply] using integrable_inner (postcompCLM M f) g
  have hint' (M : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      (f g : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) : Integrable (fun z ↦ ⟪f z, M (g z)⟫) := by
    simpa only [real_inner_comm (f _)] using hint M g f
  have hD (A : Matrix (Fin 4) (Fin 4) ℝ) (v : ℂ) :
      ∫ z, ⟪toEuclideanCLM (𝕜 := ℝ) A (∂_{v} x z), y z⟫ =
        ∫ z, ⟪x z, toEuclideanCLM (𝕜 := ℝ) (-Aᵀ) (∂_{v} y z)⟫ := by
    have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := volume) y x
      ((innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ _) (toEuclideanCLM (𝕜 := ℝ) A)) v
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply] at h
    calc ∫ z, ⟪toEuclideanCLM (𝕜 := ℝ) A (∂_{v} x z), y z⟫
        = ∫ z, ⟪y z, toEuclideanCLM (𝕜 := ℝ) A (∂_{v} x z)⟫ :=
          integral_congr_ae (.of_forall fun _ ↦ real_inner_comm _ _)
      _ = -∫ z, ⟪∂_{v} y z, toEuclideanCLM (𝕜 := ℝ) A (x z)⟫ := h
      _ = ∫ z, ⟪x z, toEuclideanCLM (𝕜 := ℝ) (-Aᵀ) (∂_{v} y z)⟫ := by
          simp_rw [map_neg, _root_.neg_apply, inner_neg_right, integral_neg, ← hT,
            real_inner_comm (∂_{v} y _)]
  simp only [firstOrder_apply, inner_add_left, inner_add_right]
  rw [integral_add, integral_add, integral_add, integral_add, hD, hD]
  · simp_rw [hT]
  -- the remaining goals are the integrability of the split integrands
  · exact hint' _ _ _
  · exact hint' _ _ _
  · exact (hint' _ _ _).add (hint' _ _ _)
  · exact hint' _ _ _
  · exact hint _ _ _
  · exact hint _ _ _
  · exact (hint _ _ _).add (hint _ _ _)
  · exact hint _ _ _

/-- `vacuumAdjoint` is the formal `L²` adjoint of `vacuumOperator`:
`∫ ⟪L₀ x, y⟫ = ∫ ⟪x, L₀* y⟫` for Schwartz fields `x` and `y`. -/
theorem integral_inner_vacuumOperator :
    ∫ z, ⟪vacuumOperator x z, y z⟫ = ∫ z, ⟪x z, vacuumAdjoint y z⟫ :=
  integral_inner_firstOrder x y _ _ _

/-- **The vacuum energy identity**: `‖L₀ x‖₂² = ‖∇x‖₂² + ‖x‖₂² / 4`, where `‖∇x‖₂²` is the sum of
the squared `L²` norms of the two coordinate derivatives `∂₁ x` and `∂₂ x`. -/
theorem integral_norm_sq_vacuumOperator :
    ∫ z, ‖vacuumOperator x z‖ ^ 2 =
      (∫ z, ‖∂_{(1 : ℂ)} x z‖ ^ 2) + (∫ z, ‖∂_{I} x z‖ ^ 2) + 1 / 4 * ∫ z, ‖x z‖ ^ 2 := by
  have hparts (v : ℂ) : ∫ z, ⟪x z, ∂_{v} (∂_{v} x) z⟫ = -∫ z, ‖∂_{v} x z‖ ^ 2 := by
    have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := volume) x (∂_{v} x)
      ((innerSL ℝ).bilinearComp (.id ℝ _) (.id ℝ _)) v
    simpa only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq] using h
  calc ∫ z, ‖vacuumOperator x z‖ ^ 2
      = ∫ z, ⟪x z, vacuumAdjoint (vacuumOperator x) z⟫ := by
        simp_rw [← real_inner_self_eq_norm_sq]
        exact integral_inner_vacuumOperator x (vacuumOperator x)
    _ = -(∫ z, ⟪x z, ∂_{(1 : ℂ)} (∂_{(1 : ℂ)} x) z⟫) - (∫ z, ⟪x z, ∂_{I} (∂_{I} x) z⟫) +
          1 / 4 * ∫ z, ⟪x z, x z⟫ := by
        simp only [vacuumAdjoint_vacuumOperator, laplacian_eq_lineDerivOp_one_I, _root_.add_apply,
          _root_.neg_apply, _root_.smul_apply, inner_add_right, inner_neg_right, inner_smul_right]
        have h₁ : Integrable (fun z ↦ -(⟪x z, ∂_{(1 : ℂ)} (∂_{(1 : ℂ)} x) z⟫ +
            ⟪x z, ∂_{I} (∂_{I} x) z⟫)) := ((integrable_inner _ _).add (integrable_inner _ _)).neg
        rw [integral_add h₁ ((integrable_inner x x).const_mul _), integral_neg,
          integral_add (integrable_inner _ _) (integrable_inner _ _),
          integral_const_mul]
        ring
    _ = _ := by
        rw [hparts (1 : ℂ), hparts I]
        simp only [real_inner_self_eq_norm_sq]
        ring

/-- **The vacuum lower bound**: `‖x‖₂² ≤ 4 ‖L₀ x‖₂²`, that is, `‖x‖₂ ≤ 2 ‖L₀ x‖₂`. -/
theorem integral_norm_sq_le_four_mul_integral_norm_sq_vacuumOperator :
    ∫ z, ‖x z‖ ^ 2 ≤ 4 * ∫ z, ‖vacuumOperator x z‖ ^ 2 := by
  have h₁ : 0 ≤ ∫ z, ‖∂_{(1 : ℂ)} x z‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  have h₂ : 0 ≤ ∫ z, ‖∂_{I} x z‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  rw [integral_norm_sq_vacuumOperator]
  linarith

/-- The vacuum operator has trivial kernel on Schwartz fields. -/
theorem vacuumOperator_injective : Function.Injective vacuumOperator := by
  refine (injective_iff_map_eq_zero vacuumOperator).2 fun x hx ↦ ?_
  have hle := integral_norm_sq_le_four_mul_integral_norm_sq_vacuumOperator x
  simp only [hx, _root_.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, integral_zero, mul_zero] at hle
  have hae : (fun z ↦ ‖x z‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ ↦ by positivity)
      ((x.memLp 2).integrable_norm_pow two_ne_zero)).1
      (le_antisymm hle (integral_nonneg fun _ ↦ by positivity))
  have heq := (Continuous.ae_eq_iff_eq volume (by fun_prop) (continuous_const (y := (0 : ℝ)))).1 hae
  ext z : 1
  simpa using congrFun heq z

end TauCeti.Vortex
