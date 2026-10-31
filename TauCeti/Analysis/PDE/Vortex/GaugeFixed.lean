/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.PDE.Vortex.Deformation
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The gauge-fixed vortex operator at a general field

This file continues `TauCeti.Analysis.PDE.Vortex.Deformation`, in the same coordinates: a field
`x = (A₁, A₂, p, q)` represents `a = i (A₁ ds + A₂ dt)` and `α = 2 (p + i q)`, and the coefficient
metric `|b|² + |δα|² / 4` on variations is the Euclidean metric. The infinitesimal gauge action
`d₀ = gaugeDirection x` sends a real phase `f` to `(-∂₁ f, -∂₂ f, -q f, p f)`, and its formal
`L²` adjoint is

  `d₀* y = ∂₁ y₀ + ∂₂ y₁ + p y₃ - q y₂` (`gaugeAdjoint`).

The gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) puts this gauge-fixing row in
front of the three rows of `linearizedEquation`, and `gaugeFixedAdjoint` is its formal adjoint
`L_x*` for the Euclidean metrics on fields and on `ℝ ⊕ ℝ ⊕ ℂ`. At the vacuum they are the operators
`vacuumOperator` and `vacuumAdjoint` (`gaugeFixedOperator_vacuumField`,
`gaugeFixedAdjoint_vacuumField`).

## Main results

* `gaugeAdjoint_gaugeDirection`: `d₀* d₀ f = -Δ f + (|α|² / 4) f` pointwise, at every field.
* `gaugeFixedOperator_gaugeFixedAdjoint`: the pointwise Weitzenböck formula for `L_x L_x*` at
  every field, with the vortex defects `equation x` appearing explicitly. In complex notation,
  with `φ = α / 2`, `η = (ξ, ζ)`, `∇ = d + a` and the complex defect `E = ∂bar_a α`, it reads
  `L_x L_x* (ξ, ζ) = (-Δ ξ + |φ|² ξ + i (conj ζ) E, -Δ_a ζ + (*iF_a + |φ|²) ζ + i E (conj ξ))`.
* `gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero`: at a point where the vortex
  equation holds, `L_x L_x* = (-Δ + |φ|²) ⊕ (-Δ_a + 1 / 8 + |φ|² / 2)`. Both summands are
  nonnegative Schrödinger operators, which is how the cokernel of `L_x` is shown to vanish at a
  vortex.
* `integral_mul_gaugeAdjoint` and `integral_inner_gaugeFixedOperator`: the integration-by-parts
  identities `∫ f d₀* y = ∫ ⟪d₀ f, y⟫` and `∫ ⟪L_x y, η⟫ = ∫ ⟪y, L_x* η⟫`, for `C¹` data with one
  factor compactly supported and any additive Haar measure.

These are smooth differential expressions; no completed field space, Fredholm property or
cokernel statement is asserted.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277--292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory
open scoped Laplacian RealInnerProductSpace

/-- The formal `L²` adjoint `d₀*` of the infinitesimal gauge action `gaugeDirection x`, applied to
a variation `y`: `d₀* y = ∂₁ y₀ + ∂₂ y₁ + p y₃ - q y₂`. See `integral_mul_gaugeAdjoint`. -/
def gaugeAdjoint (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  fderiv ℝ (fun w ↦ y w 0) z 1 + fderiv ℝ (fun w ↦ y w 1) z I + x z 2 * y z 3 - x z 3 * y z 2

/-- The gauge-fixed linearization `L_x = d₀* ⊕ d₁` of the vortex equation at the field `x`: the
gauge-fixing row `gaugeAdjoint x y` followed by the three rows of `linearizedEquation x y`. -/
def gaugeFixedOperator (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[gaugeAdjoint x y z, linearizedEquation x y z 0, linearizedEquation x y z 1,
    linearizedEquation x y z 2]

/-- The formal `L²` adjoint `L_x*` of `gaugeFixedOperator x`, for the Euclidean metrics on the
coordinates of variations and of `ℝ ⊕ ℝ ⊕ ℂ`. See `integral_inner_gaugeFixedOperator`. -/
def gaugeFixedAdjoint (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ (fun w ↦ η w 0) z 1 - fderiv ℝ (fun w ↦ η w 1) z I +
      x z 2 * η z 3 - x z 3 * η z 2,
    -fderiv ℝ (fun w ↦ η w 0) z I + fderiv ℝ (fun w ↦ η w 1) z 1 -
      x z 2 * η z 2 - x z 3 * η z 3,
    -fderiv ℝ (fun w ↦ η w 2) z 1 - fderiv ℝ (fun w ↦ η w 3) z I -
      x z 1 * η z 2 + x z 0 * η z 3 - x z 3 * η z 0 + x z 2 * η z 1,
    -fderiv ℝ (fun w ↦ η w 3) z 1 + fderiv ℝ (fun w ↦ η w 2) z I -
      x z 0 * η z 2 - x z 1 * η z 3 + x z 2 * η z 0 + x z 3 * η z 1]

/-- The defining formula of `d₀*`. -/
@[simp]
theorem gaugeAdjoint_def (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeAdjoint x y z = fderiv ℝ (fun w ↦ y w 0) z 1 + fderiv ℝ (fun w ↦ y w 1) z I +
      x z 2 * y z 3 - x z 3 * y z 2 := by
  rfl

/-- The gauge-fixing row of `L_x`. -/
@[simp]
theorem gaugeFixedOperator_apply_zero (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedOperator x y z 0 = gaugeAdjoint x y z := by
  rfl

/-- The curvature row of `L_x`. -/
@[simp]
theorem gaugeFixedOperator_apply_one (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedOperator x y z 1 = linearizedEquation x y z 0 := by
  rfl

/-- The real `∂bar` row of `L_x`. -/
@[simp]
theorem gaugeFixedOperator_apply_two (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedOperator x y z 2 = linearizedEquation x y z 1 := by
  rfl

/-- The imaginary `∂bar` row of `L_x`. -/
@[simp]
theorem gaugeFixedOperator_apply_three (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedOperator x y z 3 = linearizedEquation x y z 2 := by
  rfl

/-- The first connection component of `L_x*`. -/
@[simp]
theorem gaugeFixedAdjoint_apply_zero (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedAdjoint x η z 0 = -fderiv ℝ (fun w ↦ η w 0) z 1 - fderiv ℝ (fun w ↦ η w 1) z I +
      x z 2 * η z 3 - x z 3 * η z 2 := by
  rfl

/-- The second connection component of `L_x*`. -/
@[simp]
theorem gaugeFixedAdjoint_apply_one (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedAdjoint x η z 1 = -fderiv ℝ (fun w ↦ η w 0) z I + fderiv ℝ (fun w ↦ η w 1) z 1 -
      x z 2 * η z 2 - x z 3 * η z 3 := by
  rfl

/-- The real section component of `L_x*`. -/
@[simp]
theorem gaugeFixedAdjoint_apply_two (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedAdjoint x η z 2 = -fderiv ℝ (fun w ↦ η w 2) z 1 - fderiv ℝ (fun w ↦ η w 3) z I -
      x z 1 * η z 2 + x z 0 * η z 3 - x z 3 * η z 0 + x z 2 * η z 1 := by
  rfl

/-- The imaginary section component of `L_x*`. -/
@[simp]
theorem gaugeFixedAdjoint_apply_three (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeFixedAdjoint x η z 3 = -fderiv ℝ (fun w ↦ η w 3) z 1 + fderiv ℝ (fun w ↦ η w 2) z I -
      x z 0 * η z 2 - x z 1 * η z 3 + x z 2 * η z 0 + x z 3 * η z 1 := by
  rfl

/-- `d₀*` preserves addition of variations differentiable at the point. -/
theorem gaugeAdjoint_add (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y v : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hy : DifferentiableAt ℝ y z) (hv : DifferentiableAt ℝ v z) :
    gaugeAdjoint x (y + v) z = gaugeAdjoint x y z + gaugeAdjoint x v z := by
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy :)
  have hvi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ v w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hv :)
  simp [fderiv_fun_add, hyi, hvi]
  ring

/-- `d₀*` commutes with real scalar multiplication of variations. -/
theorem gaugeAdjoint_smul (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (t : ℝ) (z : ℂ) :
    gaugeAdjoint x (t • y) z = t * gaugeAdjoint x y z := by
  have hd (i : Fin 4) : fderiv ℝ (fun w ↦ t * y w i) z = t • fderiv ℝ (fun w ↦ y w i) z :=
    congrFun (fderiv_const_smul_field t) z
  simp [hd]
  ring

/-- `L_x` preserves addition of variations differentiable at the point. -/
theorem gaugeFixedOperator_add (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {y v : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ} (hy : DifferentiableAt ℝ y z)
    (hv : DifferentiableAt ℝ v z) :
    gaugeFixedOperator x (y + v) z = gaugeFixedOperator x y z + gaugeFixedOperator x v z := by
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy :)
  have hvi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ v w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hv :)
  have hL := linearizedEquation_add x hyi hvi
  ext i
  fin_cases i
  · simp [-gaugeAdjoint_def, gaugeAdjoint_add x hy hv]
  all_goals simp [hL]

/-- `L_x` commutes with real scalar multiplication of variations. -/
theorem gaugeFixedOperator_smul (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (t : ℝ) (z : ℂ) :
    gaugeFixedOperator x (t • y) z = t • gaugeFixedOperator x y z := by
  have hL := linearizedEquation_smul x y t z
  ext i
  fin_cases i
  · simp [-gaugeAdjoint_def, gaugeAdjoint_smul x y t z]
  all_goals simp [hL]

/-- `L_x*` preserves addition of arguments differentiable at the point. -/
theorem gaugeFixedAdjoint_add (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {η ν : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ} (hη : DifferentiableAt ℝ η z)
    (hν : DifferentiableAt ℝ ν z) :
    gaugeFixedAdjoint x (η + ν) z = gaugeFixedAdjoint x η z + gaugeFixedAdjoint x ν z := by
  have hηi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ η w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hη :)
  have hνi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ ν w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hν :)
  ext i
  fin_cases i <;> simp [fderiv_fun_add, hηi, hνi] <;> ring

/-- `L_x*` commutes with real scalar multiplication. -/
theorem gaugeFixedAdjoint_smul (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (t : ℝ) (z : ℂ) :
    gaugeFixedAdjoint x (t • η) z = t • gaugeFixedAdjoint x η z := by
  have hd (i : Fin 4) : fderiv ℝ (fun w ↦ t * η w i) z = t • fderiv ℝ (fun w ↦ η w i) z :=
    congrFun (fderiv_const_smul_field t) z
  ext i
  fin_cases i <;> simp [hd] <;> ring

/-- **The gauge Laplacian**: at every field, `d₀* d₀ f = -Δ f + (|α|² / 4) f`, where
`|α|² / 4 = p² + q²`. No regularity of the field is needed. -/
theorem gaugeAdjoint_gaugeDirection (x : ℂ → EuclideanSpace ℝ (Fin 4)) {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    gaugeAdjoint x (gaugeDirection x f) z = -Δ f z + (x z 2 ^ 2 + x z 3 ^ 2) * f z := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  simp [laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdf,
    Fin.sum_univ_two, fderiv_fun_neg]
  ring

/-- **The Weitzenböck formula for `L_x L_x*`** at an arbitrary field, with the vortex defects
`E = equation x z` displayed. With `P = p² + q² = |α|² / 4`, the connection part is
`(-Δ + P) η` plus defect couplings, while the section part is `-Δ_a ζ + (E₀ + 1 / 8 + P / 2) ζ`
plus defect couplings, where `-Δ_a` is the covariant Laplacian of `ζ = η₂ + i η₃` for
`∇ = d + a` and `E₀ + 1 / 8 - P / 2 = *iF_a`. In real coordinates
`-Δ_a ζ = -Δ ζ - i (∂₁ A₁ + ∂₂ A₂) ζ - 2 i (A₁ ∂₁ ζ + A₂ ∂₂ ζ) + |A|² ζ`. -/
theorem gaugeFixedOperator_gaugeFixedAdjoint {x η : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z) :
    gaugeFixedOperator x (gaugeFixedAdjoint x η) z =
      !₂[-Δ (fun w ↦ η w 0) z + (x z 2 ^ 2 + x z 3 ^ 2) * η z 0 -
          η z 2 * equation x z 2 + η z 3 * equation x z 1,
        -Δ (fun w ↦ η w 1) z + (x z 2 ^ 2 + x z 3 ^ 2) * η z 1 +
          η z 2 * equation x z 1 + η z 3 * equation x z 2,
        -Δ (fun w ↦ η w 2) z +
          (equation x z 0 + 1 / 8 + (x z 2 ^ 2 + x z 3 ^ 2) / 2 + x z 0 ^ 2 + x z 1 ^ 2) *
            η z 2 +
          (fderiv ℝ (fun w ↦ x w 0) z 1 + fderiv ℝ (fun w ↦ x w 1) z I) * η z 3 +
          2 * (x z 0 * fderiv ℝ (fun w ↦ η w 3) z 1 + x z 1 * fderiv ℝ (fun w ↦ η w 3) z I) -
          equation x z 2 * η z 0 + equation x z 1 * η z 1,
        -Δ (fun w ↦ η w 3) z +
          (equation x z 0 + 1 / 8 + (x z 2 ^ 2 + x z 3 ^ 2) / 2 + x z 0 ^ 2 + x z 1 ^ 2) *
            η z 3 -
          (fderiv ℝ (fun w ↦ x w 0) z 1 + fderiv ℝ (fun w ↦ x w 1) z I) * η z 2 -
          2 * (x z 0 * fderiv ℝ (fun w ↦ η w 2) z 1 + x z 1 * fderiv ℝ (fun w ↦ η w 2) z I) +
          equation x z 1 * η z 0 + equation x z 2 * η z 1] := by
  have hxi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hx :)
  have hηi (i : Fin 4) : ContDiffAt ℝ 2 (fun w ↦ η w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp z hη :)
  have hdη (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ η w i) z :=
    (hηi i).differentiableAt (by norm_num)
  have hdd (i : Fin 4) : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ η w i)) z :=
    ((hηi i).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomm (i : Fin 4) := ((hηi i).isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  ext i
  fin_cases i <;>
    simp (disch := fun_prop) [
      laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI (hdd _), Fin.sum_univ_two,
      fderiv_fun_sub,
      fderiv_fun_add, fderiv_fun_mul, fderiv_fun_neg,
      fderiv_clm_apply (hdd _) (differentiableAt_const _), hcomm] <;>
    ring

/-- **The Weitzenböck formula at a vortex**: where the vortex equation holds,
`L_x L_x* = (-Δ + P) ⊕ (-Δ_a + 1 / 8 + P / 2)` with `P = p² + q² = |α|² / 4`. The section part is
displayed in real coordinates as in `gaugeFixedOperator_gaugeFixedAdjoint`. -/
theorem gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero
    {x η : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z) (hsol : equation x z = 0) :
    gaugeFixedOperator x (gaugeFixedAdjoint x η) z =
      !₂[-Δ (fun w ↦ η w 0) z + (x z 2 ^ 2 + x z 3 ^ 2) * η z 0,
        -Δ (fun w ↦ η w 1) z + (x z 2 ^ 2 + x z 3 ^ 2) * η z 1,
        -Δ (fun w ↦ η w 2) z +
          (1 / 8 + (x z 2 ^ 2 + x z 3 ^ 2) / 2 + x z 0 ^ 2 + x z 1 ^ 2) * η z 2 +
          (fderiv ℝ (fun w ↦ x w 0) z 1 + fderiv ℝ (fun w ↦ x w 1) z I) * η z 3 +
          2 * (x z 0 * fderiv ℝ (fun w ↦ η w 3) z 1 + x z 1 * fderiv ℝ (fun w ↦ η w 3) z I),
        -Δ (fun w ↦ η w 3) z +
          (1 / 8 + (x z 2 ^ 2 + x z 3 ^ 2) / 2 + x z 0 ^ 2 + x z 1 ^ 2) * η z 3 -
          (fderiv ℝ (fun w ↦ x w 0) z 1 + fderiv ℝ (fun w ↦ x w 1) z I) * η z 2 -
          2 * (x z 0 * fderiv ℝ (fun w ↦ η w 2) z 1 + x z 1 * fderiv ℝ (fun w ↦ η w 2) z I)] := by
  rw [gaugeFixedOperator_gaugeFixedAdjoint hx hη]
  ext i
  fin_cases i <;> simp [hsol]

section Vacuum

open scoped SchwartzMap LineDeriv

/-- At the vacuum, the gauge-fixed operator is `vacuumOperator`. -/
theorem gaugeFixedOperator_vacuumField (y : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    gaugeFixedOperator vacuumField y z = vacuumOperator y z := by
  ext i
  fin_cases i <;> simp [SchwartzMap.fderiv_apply_eq_lineDerivOp_apply] <;> ring

/-- At the vacuum, the formal adjoint of the gauge-fixed operator is `vacuumAdjoint`. -/
theorem gaugeFixedAdjoint_vacuumField (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    gaugeFixedAdjoint vacuumField η z = vacuumAdjoint η z := by
  ext i
  fin_cases i <;> simp [SchwartzMap.fderiv_apply_eq_lineDerivOp_apply] <;> ring

end Vacuum

section Continuity

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- `d₀* y` is continuous for a continuous field and a `C¹` variation. -/
theorem continuous_gaugeAdjoint (hx : Continuous x) (hy : ContDiff ℝ 1 y) :
    Continuous (gaugeAdjoint x y) := by
  have (i : Fin 4) (v : ℂ) : Continuous fun z ↦ fderiv ℝ (fun w ↦ y w i) z v :=
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy :).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hyi (i : Fin 4) : Continuous fun z ↦ y z i := by fun_prop
  rw [funext (gaugeAdjoint_def x y)]
  fun_prop

/-- `L_x* y` is continuous for a continuous field and a `C¹` argument. -/
theorem continuous_gaugeFixedAdjoint (hx : Continuous x) (hy : ContDiff ℝ 1 y) :
    Continuous (gaugeFixedAdjoint x y) := by
  have (i : Fin 4) (v : ℂ) : Continuous fun z ↦ fderiv ℝ (fun w ↦ y w i) z v :=
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy :).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hyi (i : Fin 4) : Continuous fun z ↦ y z i := by fun_prop
  have h₀ : Continuous fun z ↦ gaugeFixedAdjoint x y z 0 := by
    simp only [gaugeFixedAdjoint_apply_zero]; fun_prop
  have h₁ : Continuous fun z ↦ gaugeFixedAdjoint x y z 1 := by
    simp only [gaugeFixedAdjoint_apply_one]; fun_prop
  have h₂ : Continuous fun z ↦ gaugeFixedAdjoint x y z 2 := by
    simp only [gaugeFixedAdjoint_apply_two]; fun_prop
  have h₃ : Continuous fun z ↦ gaugeFixedAdjoint x y z 3 := by
    simp only [gaugeFixedAdjoint_apply_three]; fun_prop
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

end Continuity

section Adjoint

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

/-- The pointwise Green identity for `d₀*`: `f d₀* y - ⟪d₀ f, y⟫ = ∂₁ (f y₀) + ∂₂ (f y₁)`. -/
private theorem mul_gaugeAdjoint_eq {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {f : ℂ → ℝ} {z : ℂ}
    (hy : DifferentiableAt ℝ y z) (hf : DifferentiableAt ℝ f z) :
    f z * gaugeAdjoint x y z = ⟪gaugeDirection x f z, y z⟫ +
      fderiv ℝ (fun w ↦ f w * y w 0) z 1 + fderiv ℝ (fun w ↦ f w * y w 1) z I := by
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy :)
  simp (disch := fun_prop) [PiLp.inner_apply, Fin.sum_univ_four, fderiv_fun_mul]
  ring

/-- The pointwise Green identity for `L_x`: `⟪L_x y, η⟫ - ⟪y, L_x* η⟫` is the divergence
`∂₁ V₁ + ∂₂ V₂` of an explicit bilinear current. -/
private theorem inner_gaugeFixedOperator_eq {x y η : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hy : DifferentiableAt ℝ y z) (hη : DifferentiableAt ℝ η z) :
    ⟪gaugeFixedOperator x y z, η z⟫ = ⟪y z, gaugeFixedAdjoint x η z⟫ +
      fderiv ℝ (fun w ↦ y w 0 * η w 0 - y w 1 * η w 1 + y w 2 * η w 2 + y w 3 * η w 3) z 1 +
      fderiv ℝ (fun w ↦ y w 1 * η w 0 + y w 0 * η w 1 - y w 3 * η w 2 + y w 2 * η w 3) z I := by
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy :)
  have hηi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ η w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hη :)
  simp (disch := fun_prop) [PiLp.inner_apply, Fin.sum_univ_four, fderiv_fun_mul,
    fderiv_fun_add, fderiv_fun_sub]
  ring

/-- **`d₀*` is the formal adjoint of the infinitesimal gauge action**: `∫ f d₀* y = ∫ ⟪d₀ f, y⟫`
for a continuous field `x`, a `C¹` variation `y` and a compactly supported `C¹` phase `f`. -/
theorem integral_mul_gaugeAdjoint {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {f : ℂ → ℝ}
    (hx : Continuous x) (hy : ContDiff ℝ 1 y) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∫ z, f z * gaugeAdjoint x y z ∂μ = ∫ z, ⟪gaugeDirection x f z, y z⟫ ∂μ := by
  have hyi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ y w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy :)
  have hg (i : Fin 4) : ContDiff ℝ 1 fun w ↦ f w * y w i := hf.mul (hyi i)
  have hgc (i : Fin 4) : HasCompactSupport fun w ↦ f w * y w i := hfc.mul_right
  have hint (i : Fin 4) (v : ℂ) : Integrable (fun z ↦ fderiv ℝ (fun w ↦ f w * y w i) z v) μ :=
    (((hg i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hgc i).fderiv_apply (𝕜 := ℝ) v)
  have h (z : ℂ) : ⟪gaugeDirection x f z, y z⟫ = f z * gaugeAdjoint x y z -
      fderiv ℝ (fun w ↦ f w * y w 0) z 1 - fderiv ℝ (fun w ↦ f w * y w 1) z I := by
    rw [mul_gaugeAdjoint_eq (hy.differentiable one_ne_zero z) (hf.differentiable one_ne_zero z)]
    ring
  simp_rw [h]
  rw [integral_sub _ (hint 1 I), integral_sub _ (hint 0 1),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (hg 0) (hgc 0),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (hg 1) (hgc 1), sub_zero, sub_zero]
  · exact (hf.continuous.mul (continuous_gaugeAdjoint hx hy)).integrable_of_hasCompactSupport
      hfc.mul_right
  · exact ((hf.continuous.mul (continuous_gaugeAdjoint hx hy)).integrable_of_hasCompactSupport
      hfc.mul_right).sub (hint 0 1)

/-- **`L_x*` is the formal adjoint of the gauge-fixed operator**: `∫ ⟪L_x y, η⟫ = ∫ ⟪y, L_x* η⟫`
for a continuous field `x`, a compactly supported `C¹` variation `y` and a `C¹` field `η`. -/
theorem integral_inner_gaugeFixedOperator {x y η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y)
    (hη : ContDiff ℝ 1 η) :
    ∫ z, ⟪gaugeFixedOperator x y z, η z⟫ ∂μ = ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ := by
  have hyi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ y w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy :)
  have hηi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ η w i :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hη :)
  have hyic (i : Fin 4) : HasCompactSupport fun w ↦ y w i :=
    hyc.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _)
  set V₁ : ℂ → ℝ := fun w ↦ y w 0 * η w 0 - y w 1 * η w 1 + y w 2 * η w 2 + y w 3 * η w 3
  set V₂ : ℂ → ℝ := fun w ↦ y w 1 * η w 0 + y w 0 * η w 1 - y w 3 * η w 2 + y w 2 * η w 3
  have hV₁ : ContDiff ℝ 1 V₁ := by
    have := hyi; have := hηi
    fun_prop
  have hV₂ : ContDiff ℝ 1 V₂ := by
    have := hyi; have := hηi
    fun_prop
  have hV₁c : HasCompactSupport V₁ :=
    ((((hyic 0).mul_right.sub (hyic 1).mul_right).add (hyic 2).mul_right).add (hyic 3).mul_right)
  have hV₂c : HasCompactSupport V₂ :=
    ((((hyic 1).mul_right.add (hyic 0).mul_right).sub (hyic 3).mul_right).add (hyic 2).mul_right)
  have hint (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) (v : ℂ) :
      Integrable (fun z ↦ fderiv ℝ V z v) μ :=
    ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hVc.fderiv_apply (𝕜 := ℝ) v)
  have hmain : Integrable (fun z ↦ ⟪y z, gaugeFixedAdjoint x η z⟫) μ := by
    refine (hy.continuous.inner
      (continuous_gaugeFixedAdjoint hx hη)).integrable_of_hasCompactSupport
        (hyc.mono fun z hz ↦ fun hyz ↦ hz (by simp [hyz]))
  have h (z : ℂ) : ⟪gaugeFixedOperator x y z, η z⟫ = ⟪y z, gaugeFixedAdjoint x η z⟫ +
      fderiv ℝ V₁ z 1 + fderiv ℝ V₂ z I :=
    inner_gaugeFixedOperator_eq (hy.differentiable one_ne_zero z) (hη.differentiable one_ne_zero z)
  simp_rw [h]
  rw [integral_add _ (hint V₂ hV₂ hV₂c I), integral_add hmain (hint V₁ hV₁ hV₁c 1),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hV₁ hV₁c,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hV₂ hV₂c, add_zero, add_zero]
  exact hmain.add (hint V₁ hV₁ hV₁c 1)

end Adjoint

end TauCeti.Vortex
