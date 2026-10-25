/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Basic

/-!
# The smooth plane vortex equation and its deformation complex

Write a field as `x = (b₁, b₂, p, q)`, representing the imaginary connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`. The coefficient metric
`|b|² + |δα|² / 4` is then the Euclidean metric on variations of `x`.
`equation x` has three real components: the defect in
`*iF_a = (1 - |α|²) / 8` and the real and imaginary parts of `∂bar_a α`.
The convention is `∂bar_a α = (∇₁α + i ∇₂α) / 2`, with `∇ = d + a`.
`phaseGauge` realizes the action of `exp (i f)`; its composition law, first variation
and covariance of the equation hold for actual differentiable phases.

`equation_add_smul` gives the exact quadratic expansion, and `hasDerivAt_equation`
identifies `linearizedEquation` as its first variation. For the charge-one infinitesimal
gauge action `gaugeDirection x f`, the off-shell composition is
`(0, -f * (equation x)₂, f * (equation x)₁)`. Consequently it vanishes at every
solution, giving the differential-complex identity without a gauge-fixing assumption.
The vacuum is `(0, 0, 1/2, 0)`; its linearization agrees with the last three rows of
`vacuumOperator`. This is a smooth differential expression; no completed field space,
Fredholm property or quotient construction is asserted.

The normalization follows `TauCeti.Vortex.vacuumOperator` and A. Jaffe and C. H. Taubes,
*Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex

/-- The three real defects of the plane vortex equation in the coordinates
`a = i (x₀ ds + x₁ dt)`, `α = 2 (x₂ + i x₃)`. -/
def equation (x : ℂ → Fin 4 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  ![fderiv ℝ (fun w ↦ x w 0) z I - fderiv ℝ (fun w ↦ x w 1) z 1 +
      (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8,
    fderiv ℝ (fun w ↦ x w 2) z 1 - fderiv ℝ (fun w ↦ x w 3) z I -
      x z 0 * x z 3 - x z 1 * x z 2,
    fderiv ℝ (fun w ↦ x w 3) z 1 + fderiv ℝ (fun w ↦ x w 2) z I +
      x z 0 * x z 2 - x z 1 * x z 3]

/-- The first-order linearization of `equation` at the field `x`, applied to a variation `y`.
The coordinates of `y` represent `δa = i (y₀ ds + y₁ dt)` and `δα = 2 (y₂ + i y₃)`. -/
def linearizedEquation (x y : ℂ → Fin 4 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  ![fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1 +
      x z 2 * y z 2 + x z 3 * y z 3,
    fderiv ℝ (fun w ↦ y w 2) z 1 - fderiv ℝ (fun w ↦ y w 3) z I -
      x z 0 * y z 3 - y z 0 * x z 3 - x z 1 * y z 2 - y z 1 * x z 2,
    fderiv ℝ (fun w ↦ y w 3) z 1 + fderiv ℝ (fun w ↦ y w 2) z I +
      x z 0 * y z 2 + y z 0 * x z 2 - x z 1 * y z 3 - y z 1 * x z 3]

/-- The quadratic remainder of the vortex equation, independent of the base field. -/
def quadraticTerm (y : ℂ → Fin 4 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  ![(y z 2 ^ 2 + y z 3 ^ 2) / 2,
    -y z 0 * y z 3 - y z 1 * y z 2,
    y z 0 * y z 2 - y z 1 * y z 3]

/-- The infinitesimal charge-one gauge action of `i f`: `δa = -i df`, `δα = i f α`. -/
def gaugeDirection (x : ℂ → Fin 4 → ℝ) (f : ℂ → ℝ) (z : ℂ) : Fin 4 → ℝ :=
  ![-fderiv ℝ f z 1, -fderiv ℝ f z I, -f z * x z 3, f z * x z 2]

/-- The gauge transformation with phase `exp (i f)`, in real field coordinates.
Its connection part is `a - i df` and its section part is `exp (i f) α`. -/
def phaseGauge (x : ℂ → Fin 4 → ℝ) (f : ℂ → ℝ) (z : ℂ) : Fin 4 → ℝ :=
  ![x z 0 - fderiv ℝ f z 1, x z 1 - fderiv ℝ f z I,
    Real.cos (f z) * x z 2 - Real.sin (f z) * x z 3,
    Real.sin (f z) * x z 2 + Real.cos (f z) * x z 3]

/-- The normalized vacuum field, with zero connection and section `α = 1`. -/
def vacuumField (_ : ℂ) : Fin 4 → ℝ := ![0, 0, 1 / 2, 0]

/-- The coordinate formula for the three vortex defects. -/
theorem equation_def (x : ℂ → Fin 4 → ℝ) (z : ℂ) :
    equation x z =
      ![fderiv ℝ (fun w ↦ x w 0) z I - fderiv ℝ (fun w ↦ x w 1) z 1 +
          (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8,
        fderiv ℝ (fun w ↦ x w 2) z 1 - fderiv ℝ (fun w ↦ x w 3) z I -
          x z 0 * x z 3 - x z 1 * x z 2,
        fderiv ℝ (fun w ↦ x w 3) z 1 + fderiv ℝ (fun w ↦ x w 2) z I +
          x z 0 * x z 2 - x z 1 * x z 3] := by
  rfl

/-- The coordinate formula for the infinitesimal gauge action. -/
theorem gaugeDirection_def (x : ℂ → Fin 4 → ℝ) (f : ℂ → ℝ) (z : ℂ) :
    gaugeDirection x f z =
      ![-fderiv ℝ f z 1, -fderiv ℝ f z I, -f z * x z 3, f z * x z 2] := by
  rfl

/-- The coordinate formula for the linearized equation. -/
theorem linearizedEquation_def (x y : ℂ → Fin 4 → ℝ) (z : ℂ) :
    linearizedEquation x y z =
      ![fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1 +
          x z 2 * y z 2 + x z 3 * y z 3,
        fderiv ℝ (fun w ↦ y w 2) z 1 - fderiv ℝ (fun w ↦ y w 3) z I -
          x z 0 * y z 3 - y z 0 * x z 3 - x z 1 * y z 2 - y z 1 * x z 2,
        fderiv ℝ (fun w ↦ y w 3) z 1 + fderiv ℝ (fun w ↦ y w 2) z I +
          x z 0 * y z 2 + y z 0 * x z 2 - x z 1 * y z 3 - y z 1 * x z 3] := by
  rfl

/-- The quadratic term contains no derivatives or base-field dependence. -/
theorem quadraticTerm_def (y : ℂ → Fin 4 → ℝ) (z : ℂ) :
    quadraticTerm y z = ![(y z 2 ^ 2 + y z 3 ^ 2) / 2,
      -y z 0 * y z 3 - y z 1 * y z 2, y z 0 * y z 2 - y z 1 * y z 3] := by
  rfl

/-- The coordinate formula for a phase gauge transformation. -/
theorem phaseGauge_def (x : ℂ → Fin 4 → ℝ) (f : ℂ → ℝ) (z : ℂ) :
    phaseGauge x f z =
      ![x z 0 - fderiv ℝ f z 1, x z 1 - fderiv ℝ f z I,
        Real.cos (f z) * x z 2 - Real.sin (f z) * x z 3,
        Real.sin (f z) * x z 2 + Real.cos (f z) * x z 3] := by
  rfl

/-- The coordinates of the vacuum field. -/
@[simp]
theorem vacuumField_apply (z : ℂ) : vacuumField z = ![0, 0, 1 / 2, 0] := by
  rfl

/-- The zero phase acts as the identity. -/
@[simp]
theorem phaseGauge_zero (x : ℂ → Fin 4 → ℝ) : phaseGauge x 0 = x := by
  ext z i
  fin_cases i <;> simp [phaseGauge, fderiv_zero]

/-- Composition of phase gauges corresponds to addition of their real phases. -/
theorem phaseGauge_phaseGauge (x : ℂ → Fin 4 → ℝ) {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    phaseGauge (phaseGauge x f) g z = phaseGauge x (f + g) z := by
  ext i
  fin_cases i <;>
    simp [phaseGauge, fderiv_add hf hg, Real.cos_add, Real.sin_add] <;> ring

/-- The infinitesimal charge-one action is the derivative of the actual phase gauge action. -/
theorem hasDerivAt_phaseGauge (x : ℂ → Fin 4 → ℝ) {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (i : Fin 4) :
    HasDerivAt (fun t : ℝ ↦ phaseGauge x (t • f) z i) (gaugeDirection x f z i) 0 := by
  have hd : ∀ t : ℝ, fderiv ℝ (t • f) z = t • fderiv ℝ f z :=
    fun t ↦ fderiv_const_smul hf t
  have ht := (hasDerivAt_id (0 : ℝ)).mul_const (f z)
  fin_cases i <;> simp only [phaseGauge, gaugeDirection, hd] <;> dsimp
  · simpa [Pi.sub_def] using (hasDerivAt_const (0 : ℝ) (x z 0)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (fderiv ℝ f z 1))
  · simpa [Pi.sub_def] using (hasDerivAt_const (0 : ℝ) (x z 1)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (fderiv ℝ f z I))
  · simpa [Pi.sub_def] using (ht.cos.mul_const (x z 2)).sub (ht.sin.mul_const (x z 3))
  · simpa [Pi.add_def] using (ht.sin.mul_const (x z 2)).add (ht.cos.mul_const (x z 3))

/-- The curvature defect is gauge invariant, and the complex defect transforms by the
same unit phase as the section. This statement includes non-solution fields. -/
theorem equation_phaseGauge {x : ℂ → Fin 4 → ℝ} {f : ℂ → ℝ} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) (hf : ContDiffAt ℝ 2 f z) :
    equation (phaseGauge x f) z =
      ![equation x z 0,
        Real.cos (f z) * equation x z 1 - Real.sin (f z) * equation x z 2,
        Real.sin (f z) * equation x z 1 + Real.cos (f z) * equation x z 2] := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomm := (hf.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  have hf' := hf.differentiableAt (by norm_num)
  have hpartial (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w v) z :=
    hdf.clm_apply (differentiableAt_const _)
  have htrig := Real.sin_sq_add_cos_sq (f z)
  ext i
  fin_cases i <;>
    simp [equation, phaseGauge, fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul,
      hx, hpartial, hf'.cos, hf'.sin, fderiv_cos hf', fderiv_sin hf',
      fderiv_clm_apply hdf (differentiableAt_const _)]
  · linear_combination (x z 2 ^ 2 + x z 3 ^ 2) / 2 * htrig + hcomm
  · ring
  · ring

/-- A phase gauge transformation preserves the solution condition in both directions. -/
@[simp]
theorem equation_phaseGauge_eq_zero_iff {x : ℂ → Fin 4 → ℝ} {f : ℂ → ℝ} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) (hf : ContDiffAt ℝ 2 f z) :
    equation (phaseGauge x f) z = 0 ↔ equation x z = 0 := by
  rw [equation_phaseGauge hx hf]
  refine ⟨fun h ↦ ?_, fun h ↦ by ext i; fin_cases i <;> simp [h]⟩
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h₀ h₁ h₂
  have htrig := Real.sin_sq_add_cos_sq (f z)
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  all_goals simp only [Pi.zero_apply]
  · exact h₀
  · linear_combination Real.cos (f z) * h₁ + Real.sin (f z) * h₂ - equation x z 1 * htrig
  · linear_combination -Real.sin (f z) * h₁ + Real.cos (f z) * h₂ - equation x z 2 * htrig

/-- Exact quadratic expansion of the vortex equation, with no higher remainder. -/
theorem equation_add_smul {x y : ℂ → Fin 4 → ℝ} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z)
    (hy : ∀ i, DifferentiableAt ℝ (fun w ↦ y w i) z) (t : ℝ) :
    equation (x + t • y) z =
      equation x z + t • linearizedEquation x y z + t ^ 2 • quadraticTerm y z := by
  ext i
  fin_cases i <;>
    simp [equation, linearizedEquation, quadraticTerm, fderiv_fun_add,
      fderiv_const_mul, hx, hy] <;> ring

/-- The differential expression `linearizedEquation` is the first variation along every
differentiable field direction, evaluated at any fixed point of the plane. -/
theorem hasDerivAt_equation {x y : ℂ → Fin 4 → ℝ} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z)
    (hy : ∀ i, DifferentiableAt ℝ (fun w ↦ y w i) z) :
    HasDerivAt (fun t : ℝ ↦ equation (x + t • y) z) (linearizedEquation x y z) 0 := by
  simp_rw [equation_add_smul hx hy]
  convert ((hasDerivAt_const (0 : ℝ) (equation x z)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (linearizedEquation x y z))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (quadraticTerm y z)) using 1 <;> simp [Pi.add_def]

/-- Away from solutions, the composition of the linearized equation with the infinitesimal
gauge action is the infinitesimal rotation of the complex equation defect. -/
theorem linearizedEquation_gaugeDirection {x : ℂ → Fin 4 → ℝ} {f : ℂ → ℝ} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (hf : ContDiffAt ℝ 2 f z) :
    linearizedEquation x (gaugeDirection x f) z =
      ![0, -f z * equation x z 2, f z * equation x z 1] := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomm := (hf.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  have hf' := hf.differentiableAt (by norm_num)
  ext i
  fin_cases i <;>
    simp [linearizedEquation, gaugeDirection, equation, fderiv_fun_neg,
      fderiv_fun_mul, hf', hp, hq, fderiv_clm_apply hdf (differentiableAt_const _)] <;>
    nlinarith [hcomm]

/-- At a solution, the infinitesimal gauge action followed by the linearized equation is zero.
This is the differential-complex identity `d₁ d₀ = 0`. -/
theorem linearizedEquation_gaugeDirection_eq_zero {x : ℂ → Fin 4 → ℝ} {f : ℂ → ℝ} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (hf : ContDiffAt ℝ 2 f z)
    (hsol : equation x z = 0) : linearizedEquation x (gaugeDirection x f) z = 0 := by
  rw [linearizedEquation_gaugeDirection hp hq hf, hsol]
  ext i
  fin_cases i <;> simp

/-- The vacuum solves the nonlinear vortex equation. -/
@[simp]
theorem equation_vacuumField (z : ℂ) : equation vacuumField z = 0 := by
  ext i
  fin_cases i <;> norm_num [equation, vacuumField, fderiv_const_apply]

open scoped SchwartzMap LineDeriv

/-- The smooth linearization at the vacuum is exactly the curvature and two complex rows
of the existing gauge-fixed Schwartz operator. -/
theorem linearizedEquation_vacuumField (y : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    linearizedEquation vacuumField (fun w i ↦ y w i) z =
      ![vacuumOperator y z 1, vacuumOperator y z 2, vacuumOperator y z 3] := by
  have hd (i : Fin 4) (v : ℂ) :
      fderiv ℝ (fun w ↦ y w i) z v = (∂_{v} y) z i := by
    have hp := ((EuclideanSpace.proj i).hasFDerivAt.comp z
      y.differentiableAt.hasFDerivAt).fderiv
    simpa [Function.comp_def, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) hp
  ext i
  fin_cases i <;> simp [linearizedEquation, vacuumField, hd] <;> ring

end TauCeti.Vortex
