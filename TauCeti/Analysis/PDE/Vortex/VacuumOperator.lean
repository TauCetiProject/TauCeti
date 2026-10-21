/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The gauge-fixed vortex operator at the vacuum

A vortex on the plane `ℂ` is a pair `(a, α)` of an imaginary-valued connection one-form `a` on
the trivial line bundle and a section `α`, solving

`∂̄_a α = 0`, `*iF_a = (1 - |α|²) / 8`.

At the vacuum `(a, α) = (0, 1)` write `a = i b` with `b = b₁ dx + b₂ dy` real and
`α = 1 + u + i v`, and put `p = u / 2`, `q = v / 2`. In the coordinates `(b₁, b₂, p, q)` the
`L²` metric `|b|² + |δα|² / 4` on the deformations is the Euclidean one. The gauge-fixed
deformation operator at the vacuum is `L₀ = d₀* ⊕ d₁`. Here `d₁` linearizes the two equations,
and `d₀*` is the formal adjoint of the infinitesimal gauge action `ξ ↦ (-dξ, 0, ξ / 2)`. In real
coordinates `L₀` sends `(b₁, b₂, p, q)` to `(G, C, H₁, H₂)`, where

* `G = ∂₁b₁ + ∂₂b₂ + q / 2` is the Coulomb gauge condition,
* `C = -∂₁b₂ + ∂₂b₁ + p / 2` linearizes the curvature equation, and
* `H₁ + i H₂ = (∂₁p - ∂₂q - b₂ / 2) + i (∂₁q + ∂₂p + b₁ / 2)` linearizes `∂̄_a α`.

This file defines `L₀` and its formal `L²` adjoint `L₀*` as continuous linear operators on
Schwartz fields `ℂ → ℝ⁴`. It proves the Weitzenböck identities `L₀* L₀ = L₀ L₀* = -Δ + 1/4` and
the resulting energy identity `‖L₀ x‖₂² = ‖∂₁ x‖₂² + ‖∂₂ x‖₂² + ‖x‖₂² / 4`. In particular `L₀` has
the first-order gap `‖L₀ x‖₂ ≥ ‖x‖₂ / 2`, and `L₀` and `L₀*` are injective. These are the vacuum
inputs to the exterior parametrix and Fredholm theory of the linearized vortex operator.

## Main definitions

* `TauCeti.Vortex.vacuumOperator`: the gauge-fixed vacuum operator `L₀`.
* `TauCeti.Vortex.vacuumAdjoint`: its formal adjoint `L₀*`.

## Main results

* `TauCeti.Vortex.vacuumOperator_apply`, `TauCeti.Vortex.vacuumAdjoint_apply`: the coordinate
  formulas; for instance `(L₀* y)_{b₁} = -∂₁G - ∂₂C + H₂ / 2`.
* `TauCeti.Vortex.integral_inner_vacuumOperator`: `L₀*` is the formal `L²` adjoint of `L₀`.
* `TauCeti.Vortex.vacuumAdjoint_vacuumOperator`, `TauCeti.Vortex.vacuumOperator_vacuumAdjoint`:
  `L₀* L₀ = L₀ L₀* = -Δ + 1/4`.
* `TauCeti.Vortex.integral_norm_vacuumOperator_sq`: the energy identity for `L₀`.
* `TauCeti.Vortex.integral_norm_sq_le_four_mul_integral_norm_vacuumOperator_sq`: the gap
  `‖x‖₂² ≤ 4 ‖L₀ x‖₂²`.
* `TauCeti.Vortex.vacuumOperator_injective`, `TauCeti.Vortex.vacuumAdjoint_injective`.

## References

* A. Jaffe, C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
* C. H. Taubes, *GR ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open scoped SchwartzMap LineDeriv Laplacian Matrix RealInnerProductSpace
open MeasureTheory SchwartzMap LineDeriv

namespace TauCeti.Vortex

/-- The coefficient of `∂₁` in `L₀`. -/
private noncomputable def matOne : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The coefficient of `∂₂` in `L₀`. -/
private noncomputable def matI : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- The zeroth-order coefficient of `L₀`. -/
private noncomputable def matZero : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 1 / 2; 0, 0, 1 / 2, 0; 0, -1 / 2, 0, 0; 1 / 2, 0, 0, 0]

/-- The constant-coefficient first-order operator `A₁ ∂₁ + A₂ ∂₂ + B` on Schwartz fields. -/
private noncomputable def firstOrder (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ) :
    𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) →L[ℝ] 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  (postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A₁)).comp
      (lineDerivOpCLM ℝ 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) (1 : ℂ)) +
    (postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A₂)).comp
      (lineDerivOpCLM ℝ 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) Complex.I) +
    postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) B)

private theorem firstOrder_apply (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ)
    (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    firstOrder A₁ A₂ B f z = Matrix.toEuclideanCLM (𝕜 := ℝ) A₁ ((∂_{(1 : ℂ)} f) z) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) A₂ ((∂_{Complex.I} f) z) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) B (f z) :=
  rfl

private theorem lineDerivOp_firstOrder (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ) (v : ℂ)
    (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∂_{v} (firstOrder A₁ A₂ B f) = firstOrder A₁ A₂ B (∂_{v} f) := by
  simp only [firstOrder, _root_.add_apply, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    LineDeriv.lineDerivOp_add, TauCeti.lineDerivOp_postcompCLM, lineDerivOp_comm f v 1,
    lineDerivOp_comm f v Complex.I]

/-- The gauge-fixed vortex deformation operator `L₀ = d₀* ⊕ d₁` at the vacuum `(a, α) = (0, 1)`,
acting on Schwartz fields `(b₁, b₂, p, q) : ℂ → ℝ⁴`. Its coordinate formula is
`TauCeti.Vortex.vacuumOperator_apply`. -/
noncomputable def vacuumOperator :
    𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) →L[ℝ] 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  firstOrder matOne matI matZero

/-- The formal `L²` adjoint `L₀*` of the vacuum vortex operator (see
`TauCeti.Vortex.integral_inner_vacuumOperator`). Its coordinate formula is
`TauCeti.Vortex.vacuumAdjoint_apply`. -/
noncomputable def vacuumAdjoint :
    𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) →L[ℝ] 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  firstOrder (-matOneᵀ) (-matIᵀ) matZeroᵀ

/-- The coordinates of `L₀ x` for `x = (b₁, b₂, p, q)`: they are
`G = ∂₁b₁ + ∂₂b₂ + q / 2`, `C = -∂₁b₂ + ∂₂b₁ + p / 2`, `H₁ = ∂₁p - ∂₂q - b₂ / 2` and
`H₂ = ∂₁q + ∂₂p + b₁ / 2`, where `∂₁ = ∂_1` and `∂₂ = ∂_I` on `ℂ`. -/
theorem vacuumOperator_apply (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    vacuumOperator f z = !₂[(∂_{(1 : ℂ)} f) z 0 + (∂_{Complex.I} f) z 1 + f z 3 / 2,
      -(∂_{(1 : ℂ)} f) z 1 + (∂_{Complex.I} f) z 0 + f z 2 / 2,
      (∂_{(1 : ℂ)} f) z 2 - (∂_{Complex.I} f) z 3 - f z 1 / 2,
      (∂_{(1 : ℂ)} f) z 3 + (∂_{Complex.I} f) z 2 + f z 0 / 2] := by
  ext i
  fin_cases i <;>
    simp [vacuumOperator, firstOrder_apply, matOne, matI, matZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;>
    ring

/-- The coordinates of `L₀* y` for `y = (G, C, H₁, H₂)`: they are
`-∂₁G - ∂₂C + H₂ / 2`, `∂₁C - ∂₂G - H₁ / 2`, `-∂₁H₁ - ∂₂H₂ + C / 2` and
`-∂₁H₂ + ∂₂H₁ + G / 2`. -/
theorem vacuumAdjoint_apply (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    vacuumAdjoint f z = !₂[-(∂_{(1 : ℂ)} f) z 0 - (∂_{Complex.I} f) z 1 + f z 3 / 2,
      (∂_{(1 : ℂ)} f) z 1 - (∂_{Complex.I} f) z 0 - f z 2 / 2,
      -(∂_{(1 : ℂ)} f) z 2 - (∂_{Complex.I} f) z 3 + f z 1 / 2,
      -(∂_{(1 : ℂ)} f) z 3 + (∂_{Complex.I} f) z 2 + f z 0 / 2] := by
  ext i
  fin_cases i <;>
    simp [vacuumAdjoint, firstOrder_apply, matOne, matI, matZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Matrix.transpose_apply] <;>
    ring

/-- `L₀` has constant coefficients, so it commutes with directional derivatives. -/
@[simp]
theorem lineDerivOp_vacuumOperator (v : ℂ) (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∂_{v} (vacuumOperator f) = vacuumOperator (∂_{v} f) :=
  lineDerivOp_firstOrder _ _ _ v f

/-- `L₀*` has constant coefficients, so it commutes with directional derivatives. -/
@[simp]
theorem lineDerivOp_vacuumAdjoint (v : ℂ) (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∂_{v} (vacuumAdjoint f) = vacuumAdjoint (∂_{v} f) :=
  lineDerivOp_firstOrder _ _ _ v f

private theorem laplacian_apply_eq (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    Δ f z = (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} f)) z + (∂_{Complex.I} (∂_{Complex.I} f)) z := by
  simp [laplacian_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]

/-- **Weitzenböck identity** for the vacuum vortex operator: `L₀* L₀ = -Δ + 1/4`. -/
@[simp]
theorem vacuumAdjoint_vacuumOperator (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    vacuumAdjoint (vacuumOperator f) = -Δ f + (4⁻¹ : ℝ) • f := by
  ext z i
  have hc := DFunLike.congr_fun (lineDerivOp_comm f 1 Complex.I) z
  rw [vacuumAdjoint_apply, lineDerivOp_vacuumOperator, lineDerivOp_vacuumOperator,
    vacuumOperator_apply, vacuumOperator_apply, vacuumOperator_apply]
  fin_cases i <;> simp [laplacian_apply_eq, hc] <;> ring

/-- **Weitzenböck identity** in the other order: `L₀ L₀* = -Δ + 1/4`. -/
@[simp]
theorem vacuumOperator_vacuumAdjoint (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    vacuumOperator (vacuumAdjoint f) = -Δ f + (4⁻¹ : ℝ) • f := by
  ext z i
  have hc := DFunLike.congr_fun (lineDerivOp_comm f 1 Complex.I) z
  rw [vacuumOperator_apply, lineDerivOp_vacuumAdjoint, lineDerivOp_vacuumAdjoint,
    vacuumAdjoint_apply, vacuumAdjoint_apply, vacuumAdjoint_apply]
  fin_cases i <;> simp [laplacian_apply_eq, hc] <;> ring

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

private theorem inner_toEuclideanCLM_left (A : Matrix (Fin 4) (Fin 4) ℝ)
    (u w : EuclideanSpace ℝ (Fin 4)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A u, w⟫ = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Aᵀ w⟫ := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]

private theorem integrable_inner (f g : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    Integrable (fun z => ⟪f z, g z⟫) μ :=
  -- The pairing of `f` and `g` under `innerSL ℝ` is the Schwartz function `z ↦ ⟪f z, g z⟫`.
  (pairing (innerSL ℝ) f g).integrable

/-- Integration by parts for `A₁ ∂₁ + A₂ ∂₂ + B`: its formal adjoint is
`-A₁ᵀ ∂₁ - A₂ᵀ ∂₂ + Bᵀ`. -/
private theorem integral_inner_firstOrder (A₁ A₂ B : Matrix (Fin 4) (Fin 4) ℝ)
    (f g : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ⟪firstOrder A₁ A₂ B f z, g z⟫ ∂μ = ∫ z, ⟪f z, firstOrder (-A₁ᵀ) (-A₂ᵀ) Bᵀ g z⟫ ∂μ := by
  have ibp : ∀ (v : ℂ) (A : Matrix (Fin 4) (Fin 4) ℝ),
      ∫ z, ⟪(∂_{v} f) z, (g.postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) z⟫ ∂μ =
        -∫ z, ⟪f z, ((∂_{v} g).postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) z⟫ ∂μ := by
    intro v A
    have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) f
      (g.postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) (innerSL ℝ) v
    rw [TauCeti.lineDerivOp_postcompCLM] at h
    -- `innerSL ℝ u w` unfolds to `⟪u, w⟫`, so `h` is the claim up to sign.
    exact (neg_eq_iff_eq_neg.mpr h).symm
  have lhs : (fun z => ⟪firstOrder A₁ A₂ B f z, g z⟫) = fun z =>
      ⟪(∂_{(1 : ℂ)} f) z, (g.postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A₁ᵀ)) z⟫ +
        ⟪(∂_{Complex.I} f) z, (g.postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A₂ᵀ)) z⟫ +
        ⟪f z, (g.postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) Bᵀ)) z⟫ := by
    funext z
    simp only [firstOrder_apply, inner_add_left, inner_toEuclideanCLM_left, postcompCLM_apply]
  have rhs : (fun z => ⟪f z, firstOrder (-A₁ᵀ) (-A₂ᵀ) Bᵀ g z⟫) = fun z =>
      -⟪f z, ((∂_{(1 : ℂ)} g).postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A₁ᵀ)) z⟫ +
        -⟪f z, ((∂_{Complex.I} g).postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) A₂ᵀ)) z⟫ +
        ⟪f z, (g.postcompCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) Bᵀ)) z⟫ := by
    funext z
    simp only [firstOrder_apply, inner_add_right, map_neg, _root_.neg_apply, inner_neg_right,
      postcompCLM_apply]
  have hN : ∀ a b : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)), Integrable (fun z => -⟪a z, b z⟫) μ :=
    fun a b => (integrable_inner a b).neg
  have hA : ∀ F G : ℂ → ℝ, Integrable F μ → Integrable G μ →
      Integrable (fun z => F z + G z) μ := fun _ _ hF hG => hF.add hG
  rw [lhs, rhs,
    integral_add (hA _ _ (integrable_inner _ _) (integrable_inner _ _)) (integrable_inner _ _),
    integral_add (integrable_inner _ _) (integrable_inner _ _),
    integral_add (hA _ _ (hN _ _) (hN _ _)) (integrable_inner _ _),
    integral_add (hN _ _) (hN _ _), integral_neg, integral_neg, ibp, ibp]

/-- `L₀*` is the formal `L²` adjoint of `L₀`: `∫ ⟪L₀ x, y⟫ = ∫ ⟪x, L₀* y⟫`. -/
theorem integral_inner_vacuumOperator (f g : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ⟪vacuumOperator f z, g z⟫ ∂μ = ∫ z, ⟪f z, vacuumAdjoint g z⟫ ∂μ :=
  integral_inner_firstOrder _ _ _ f g

/-- `L₀` is the formal `L²` adjoint of `L₀*`: `∫ ⟪L₀* x, y⟫ = ∫ ⟪x, L₀ y⟫`. -/
theorem integral_inner_vacuumAdjoint (f g : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ⟪vacuumAdjoint f z, g z⟫ ∂μ = ∫ z, ⟪f z, vacuumOperator g z⟫ ∂μ := by
  have h₁ : ∀ z, ⟪vacuumAdjoint f z, g z⟫ = ⟪g z, vacuumAdjoint f z⟫ :=
    fun z => real_inner_comm _ _
  have h₂ : ∀ z, ⟪f z, vacuumOperator g z⟫ = ⟪vacuumOperator g z, f z⟫ :=
    fun z => real_inner_comm _ _
  simp_rw [h₁, h₂]
  exact (integral_inner_vacuumOperator g f).symm

/-- The `L²` pairing of `x` with `(-Δ + 1/4) x` is `‖∂₁ x‖₂² + ‖∂₂ x‖₂² + ‖x‖₂² / 4`. -/
private theorem integral_inner_neg_laplacian_add (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ⟪f z, (-Δ f + (4⁻¹ : ℝ) • f) z⟫ ∂μ =
      ∫ z, ‖(∂_{(1 : ℂ)} f) z‖ ^ 2 ∂μ + ∫ z, ‖(∂_{Complex.I} f) z‖ ^ 2 ∂μ +
        4⁻¹ * ∫ z, ‖f z‖ ^ 2 ∂μ := by
  have h : ∫ z, ⟪f z, Δ f z⟫ ∂μ = -∑ i, ∫ z, ⟪(∂_{Complex.orthonormalBasisOneI i} f) z,
      (∂_{Complex.orthonormalBasisOneI i} f) z⟫ ∂μ :=
    -- `innerSL ℝ u w` unfolds to `⟪u, w⟫`.
    integral_bilinear_laplacian_right_eq_neg_sum Complex.orthonormalBasisOneI f f (innerSL ℝ)
  have e : ∀ z, ⟪f z, (-Δ f + (4⁻¹ : ℝ) • f) z⟫ = -⟪f z, Δ f z⟫ + 4⁻¹ * ⟪f z, f z⟫ := by
    intro z
    simp [inner_add_right, inner_neg_right, inner_smul_right]
  simp_rw [e]
  rw [integral_add (by exact (integrable_inner f (Δ f)).neg)
      (by exact (integrable_inner f f).const_mul _), integral_neg, integral_const_mul, h]
  simp [Fin.sum_univ_two]

/-- **Energy identity** for the vacuum vortex operator:
`‖L₀ x‖₂² = ‖∂₁ x‖₂² + ‖∂₂ x‖₂² + ‖x‖₂² / 4`. -/
theorem integral_norm_vacuumOperator_sq (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ‖vacuumOperator f z‖ ^ 2 ∂μ =
      ∫ z, ‖(∂_{(1 : ℂ)} f) z‖ ^ 2 ∂μ + ∫ z, ‖(∂_{Complex.I} f) z‖ ^ 2 ∂μ +
        4⁻¹ * ∫ z, ‖f z‖ ^ 2 ∂μ := by
  simp_rw [← real_inner_self_eq_norm_sq (vacuumOperator f _)]
  rw [integral_inner_vacuumOperator, vacuumAdjoint_vacuumOperator,
    integral_inner_neg_laplacian_add]

/-- **Energy identity** for the adjoint:
`‖L₀* x‖₂² = ‖∂₁ x‖₂² + ‖∂₂ x‖₂² + ‖x‖₂² / 4`. -/
theorem integral_norm_vacuumAdjoint_sq (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ‖vacuumAdjoint f z‖ ^ 2 ∂μ =
      ∫ z, ‖(∂_{(1 : ℂ)} f) z‖ ^ 2 ∂μ + ∫ z, ‖(∂_{Complex.I} f) z‖ ^ 2 ∂μ +
        4⁻¹ * ∫ z, ‖f z‖ ^ 2 ∂μ := by
  simp_rw [← real_inner_self_eq_norm_sq (vacuumAdjoint f _)]
  rw [integral_inner_vacuumAdjoint, vacuumOperator_vacuumAdjoint,
    integral_inner_neg_laplacian_add]

/-- The **first-order gap** of the vacuum vortex operator: `‖x‖₂² ≤ 4 ‖L₀ x‖₂²`. -/
theorem integral_norm_sq_le_four_mul_integral_norm_vacuumOperator_sq
    (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ‖f z‖ ^ 2 ∂μ ≤ 4 * ∫ z, ‖vacuumOperator f z‖ ^ 2 ∂μ := by
  rw [integral_norm_vacuumOperator_sq]
  have h₁ : 0 ≤ ∫ z, ‖(∂_{(1 : ℂ)} f) z‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have h₂ : 0 ≤ ∫ z, ‖(∂_{Complex.I} f) z‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  linarith

/-- The first-order gap of the adjoint: `‖x‖₂² ≤ 4 ‖L₀* x‖₂²`. -/
theorem integral_norm_sq_le_four_mul_integral_norm_vacuumAdjoint_sq
    (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∫ z, ‖f z‖ ^ 2 ∂μ ≤ 4 * ∫ z, ‖vacuumAdjoint f z‖ ^ 2 ∂μ := by
  rw [integral_norm_vacuumAdjoint_sq]
  have h₁ : 0 ≤ ∫ z, ‖(∂_{(1 : ℂ)} f) z‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have h₂ : 0 ≤ ∫ z, ‖(∂_{Complex.I} f) z‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  linarith

/-- A Schwartz field whose squared norm has nonpositive integral vanishes. -/
private theorem eq_zero_of_integral_norm_sq_nonpos (f : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)))
    (h : ∫ z, ‖f z‖ ^ 2 ≤ 0) : f = 0 := by
  have hint : Integrable (fun z => ‖f z‖ ^ 2) :=
    (integrable_inner (μ := volume) f f).congr
      (.of_forall fun z => real_inner_self_eq_norm_sq (f z))
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖f z‖) hint).mp
    (le_antisymm h (integral_nonneg fun _ => sq_nonneg _))
  have hcont : Continuous fun z => ‖f z‖ ^ 2 := by fun_prop
  have := (hcont.ae_eq_iff_eq volume continuous_zero).mp hae
  refine SchwartzMap.ext fun z => ?_
  simpa using congrFun this z

/-- The vacuum vortex operator has no Schwartz kernel. -/
theorem vacuumOperator_injective : Function.Injective vacuumOperator := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => eq_zero_of_integral_norm_sq_nonpos f ?_
  simpa [hf] using integral_norm_sq_le_four_mul_integral_norm_vacuumOperator_sq (μ := volume) f

/-- The adjoint of the vacuum vortex operator has no Schwartz kernel. -/
theorem vacuumAdjoint_injective : Function.Injective vacuumAdjoint := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => eq_zero_of_integral_norm_sq_nonpos f ?_
  simpa [hf] using integral_norm_sq_le_four_mul_integral_norm_vacuumAdjoint_sq (μ := volume) f

end TauCeti.Vortex
