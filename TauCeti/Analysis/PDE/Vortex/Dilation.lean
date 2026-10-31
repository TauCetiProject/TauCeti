/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Dilation of the plane vortex equation

A field `x = (b₁, b₂, p, q)` represents the connection `i(b₁ ds + b₂ dt)` and the
section `α = 2(p + i q)`. Pullback by `z ↦ t z` multiplies connection components by
`t`, while section components are composed with that map. The curvature equation
with coupling `c` is `*iF_a = c(1 - |α|²)/8`. Dilation changes `c` to `t² c`,
multiplies the curvature defect by `t²`, and multiplies the complex defect by `t`.
In particular, the physical coefficient `r/4` becomes `1/8` in the coordinate
`w = √(2r) z`.

The same laws hold for the linearization and the infinitesimal and finite gauge
actions. For positive coupling the gauge row uses the coefficient metric `|b|² + c |δα|²/4`; its
transformation accounts for the change of that metric. Every-order derivative
and squared `L²` scaling formulas include the change of volume and give the
integer Sobolev factors on smooth fields. These are identities of flat
differential expressions, before Sobolev completion or insertion into a curved
normal tube.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex

/-- Pullback of a connection and section by the real dilation `z ↦ t • z`.
Only the connection components acquire the extra factor `t`. -/
def dilateField (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[t * x (t • z) 0, t * x (t • z) 1, x (t • z) 2, x (t • z) 3]

/-- The component formula for pullback of a vortex field. -/
@[simp]
theorem dilateField_apply (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    dilateField t x z = !₂[t * x (t • z) 0, t * x (t • z) 1,
      x (t • z) 2, x (t • z) 3] :=
  (rfl)

@[simp]
theorem dilateField_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) : dilateField 1 x = x := by
  ext z i
  fin_cases i <;> simp [dilateField]

/-- Successive pullbacks multiply their dilation factors. -/
@[simp]
theorem dilateField_dilateField (s t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField s (dilateField t x) = dilateField (s * t) x := by
  ext z i
  fin_cases i <;> simp [dilateField, mul_comm s t, mul_assoc] <;> ring

/-- A spatial derivative of a pulled-back connection scales by `t²`, while a
spatial derivative of its section scales by `t`. This also holds for the total
Fréchet derivative at nonsmooth fields. -/
theorem fderiv_dilateField_apply (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) (i : Fin 4) :
    fderiv ℝ (fun w ↦ dilateField t x w i) z =
      (if i < 2 then t ^ 2 else t) • fderiv ℝ (fun w ↦ x w i) (t • z) := by
  have hd (j : Fin 4) : fderiv ℝ (fun w ↦ x (t • w) j) z =
      t • fderiv ℝ (fun w ↦ x w j) (t • z) := fderiv_comp_smul (f := fun w ↦ x w j) (x := z) t
  have hm (j : Fin 4) : fderiv ℝ (fun w ↦ t * x (t • w) j) z =
      t • fderiv ℝ (fun w ↦ x (t • w) j) z :=
    congrFun (fderiv_const_smul_field (f := fun w ↦ x (t • w) j) t) z
  fin_cases i <;> simp [dilateField, -Complex.real_smul, hm, hd, pow_two, smul_smul]

/-- Every spatial derivative has its connection or section pullback factor.
This formula keeps the multilinear derivative, before taking norms. -/
theorem iteratedFDeriv_dilateField_apply (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (n : ℕ) (hx : ∀ i, ContDiff ℝ n (fun z ↦ x z i)) (z : ℂ) (i : Fin 4) :
    iteratedFDeriv ℝ n (fun w ↦ dilateField t x w i) z =
      (t ^ n * (if i < 2 then t else 1)) • iteratedFDeriv ℝ n (fun w ↦ x w i) (t • z) := by
  have hd (j : Fin 4) := congrFun (iteratedFDeriv_comp_const_smul t (hx j)) z
  have hm (j : Fin 4) := iteratedFDeriv_const_smul_apply'
    (((hx j).comp (contDiff_id.const_smul t)).contDiffAt) (a := t) (x := z)
  fin_cases i
  · simpa [dilateField, -Complex.real_smul, smul_eq_mul, smul_smul, mul_comm] using
      (hm 0).trans (congrArg (t • ·) (hd 0))
  · simpa [dilateField, -Complex.real_smul, smul_eq_mul, smul_smul, mul_comm] using
      (hm 1).trans (congrArg (t • ·) (hd 1))
  · simpa [dilateField, -Complex.real_smul] using hd 2
  · simpa [dilateField, -Complex.real_smul] using hd 3

open MeasureTheory in
/-- The squared `L²` norm of an order-`n` derivative scales by `t^(2n)` on
connection components and by `t^(2n)/t²` on section components. The latter
factor includes the real two-dimensional change of volume. Summing over
components and derivative orders gives the integer Sobolev pullback factors. -/
theorem integral_norm_iteratedFDeriv_dilateField_apply (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (t : ℝ) (ht : t ≠ 0) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (n : ℕ)
    (hx : ∀ i, ContDiff ℝ n (fun z ↦ x z i)) (i : Fin 4) :
    (∫ z, ‖iteratedFDeriv ℝ n (fun w ↦ dilateField t x w i) z‖ ^ 2 ∂μ) =
      t ^ (2 * n) * (if i < 2 then 1 else (t ^ 2)⁻¹) *
        ∫ z, ‖iteratedFDeriv ℝ n (fun w ↦ x w i) z‖ ^ 2 ∂μ := by
  simp_rw [iteratedFDeriv_dilateField_apply t x n hx, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, Measure.integral_comp_smul μ
    (fun z ↦ ‖iteratedFDeriv ℝ n (fun w ↦ x w i) z‖ ^ 2) t]
  rw [show Module.finrank ℝ ℂ = 2 from Complex.finrank_real_complex,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  split_ifs <;> simp only [mul_one, mul_pow, ← pow_mul] <;> field_simp [ht] <;> ring

/-- The plane vortex defects with curvature coefficient `c/8`. The last two rows
are the real and imaginary parts of `∂bar_a α`, with the existing normalization. -/
def coupledEquation (c : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[equation x z 0 + (c - 1) * (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8,
    equation x z 1, equation x z 2]

/-- The curvature row is `*iF_a - c(1 - |α|²)/8`. -/
@[simp]
theorem coupledEquation_apply_zero (c : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledEquation c x z 0 =
      fderiv ℝ (fun w ↦ x w 0) z I - fderiv ℝ (fun w ↦ x w 1) z 1 +
        c * (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8 := by
  simp [coupledEquation]
  ring

@[simp]
theorem coupledEquation_apply_one (c : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledEquation c x z 1 = equation x z 1 :=
  (rfl)

@[simp]
theorem coupledEquation_apply_two (c : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledEquation c x z 2 = equation x z 2 :=
  (rfl)

/-- Coupling one is the normalized plane vortex equation. -/
@[simp]
theorem coupledEquation_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    coupledEquation 1 x = equation x := by
  ext z i
  fin_cases i <;> simp [coupledEquation]

/-- Dilation multiplies the curvature row by `t²` and the complex rows by `t`,
while changing the coupling from `c` to `t² c`. -/
theorem coupledEquation_dilateField (c t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledEquation (t ^ 2 * c) (dilateField t x) z =
      !₂[t ^ 2 * coupledEquation c x (t • z) 0,
        t * coupledEquation c x (t • z) 1, t * coupledEquation c x (t • z) 2] := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp only [coupledEquation_apply_zero, coupledEquation_apply_one, coupledEquation_apply_two,
      equation_apply_one, equation_apply_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp only [fderiv_dilateField_apply] <;>
    simp [dilateField] <;> ring

/-- A nonzero dilation preserves and reflects the vortex equation at the
correspondingly rescaled coupling and point. -/
theorem coupledEquation_dilateField_eq_zero_iff (c t : ℝ) (ht : t ≠ 0)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledEquation (t ^ 2 * c) (dilateField t x) z = 0 ↔
      coupledEquation c x (t • z) = 0 := by
  rw [coupledEquation_dilateField]
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [ht] using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) h
    · simpa [ht] using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
    · simpa [ht] using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) h
  · intro h
    rw [h]
    ext i
    fin_cases i <;> simp

/-- In the physical coordinate `w = √(2r) z`, the equation with curvature
coefficient `r/4` becomes the normalized coefficient `1/8`, with no sign change. -/
theorem equation_dilateField_inv_sqrt (r : ℝ) (hr : 0 < r)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ) :
    equation (dilateField (√(2 * r))⁻¹ x) w =
      !₂[(2 * r)⁻¹ * coupledEquation (2 * r) x ((√(2 * r))⁻¹ • w) 0,
        (√(2 * r))⁻¹ * coupledEquation (2 * r) x ((√(2 * r))⁻¹ • w) 1,
        (√(2 * r))⁻¹ * coupledEquation (2 * r) x ((√(2 * r))⁻¹ • w) 2] := by
  have hs : (√(2 * r))⁻¹ ^ 2 = (2 * r)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have hc : (√(2 * r))⁻¹ ^ 2 * (2 * r) = 1 := by rw [hs]; field_simp
  simpa only [hc, coupledEquation_one, hs,
    inv_mul_cancel₀ (ne_of_gt (by positivity : 0 < 2 * r))] using
    coupledEquation_dilateField (2 * r) (√(2 * r))⁻¹ x w

/-- The linearization of `coupledEquation c` with gauge row
`div b + c(p δq - q δp)`. For positive `c`, that row is the gauge adjoint for
the coefficient metric `|b|² + c |δα|²/4`. -/
def coupledGaugeFixedOperator (c : ℝ) (x y : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  gaugeFixedOperator x y z +
    !₂[(c - 1) * (x z 2 * y z 3 - x z 3 * y z 2),
      (c - 1) * (x z 2 * y z 2 + x z 3 * y z 3), 0, 0]

/-- The correction to the normalized gauge-fixed operator consists of its two
coupling-dependent zeroth-order rows. -/
@[simp]
theorem coupledGaugeFixedOperator_apply (c : ℝ) (x y : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) :
    coupledGaugeFixedOperator c x y z = gaugeFixedOperator x y z +
      !₂[(c - 1) * (x z 2 * y z 3 - x z 3 * y z 2),
        (c - 1) * (x z 2 * y z 2 + x z 3 * y z 3), 0, 0] :=
  (rfl)

@[simp]
theorem coupledGaugeFixedOperator_one (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    coupledGaugeFixedOperator 1 x y = gaugeFixedOperator x y := by
  ext z i
  fin_cases i <;> simp [coupledGaugeFixedOperator]

/-- The last three rows of the coupled gauge-fixed operator are the actual
first variation of the coupled vortex equation. -/
theorem hasDerivAt_coupledEquation (c : ℝ)
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z)
    (hy : ∀ i, DifferentiableAt ℝ (fun w ↦ y w i) z) (i : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ coupledEquation c (x + t • y) z i)
      (coupledGaugeFixedOperator c x y z i.succ) 0 := by
  have he (j : Fin 3) : HasDerivAt (fun t : ℝ ↦ equation (x + t • y) z j)
      (linearizedEquation x y z j) 0 :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
      0 (hasDerivAt_equation hx hy)
  have hp (j : Fin 4) : HasDerivAt (fun t : ℝ ↦ (x + t • y) z j) (y z j) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, zero_mul, zero_add, one_mul, id_eq] using! (hasDerivAt_const (0 : ℝ) (x z j)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (y z j))
  have hc := ((((hp 2).pow 2).add ((hp 3).pow 2)).const_mul 4).sub_const 1
  fin_cases i
  · convert (he 0).add ((hc.const_mul (c - 1)).div_const 8) using 1
    · rfl
    · simp [coupledGaugeFixedOperator]
      ring
  · simpa [coupledEquation, coupledGaugeFixedOperator] using he 1
  · simpa [coupledEquation, coupledGaugeFixedOperator] using he 2

/-- Both real rows of the gauge-fixed operator scale quadratically, and its
complex rows scale linearly. The input variation is the pulled-back field variation. -/
theorem coupledGaugeFixedOperator_dilateField (c t : ℝ)
    (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    coupledGaugeFixedOperator (t ^ 2 * c) (dilateField t x) (dilateField t y) z =
      !₂[t ^ 2 * coupledGaugeFixedOperator c x y (t • z) 0,
        t ^ 2 * coupledGaugeFixedOperator c x y (t • z) 1,
        t * coupledGaugeFixedOperator c x y (t • z) 2,
        t * coupledGaugeFixedOperator c x y (t • z) 3] := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [coupledGaugeFixedOperator_apply, PiLp.add_apply,
      gaugeFixedOperator_apply_zero, gaugeFixedOperator_apply_one,
      gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three, gaugeAdjoint_def,
      linearizedEquation_apply_zero, linearizedEquation_apply_one, linearizedEquation_apply_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    simp only [fderiv_dilateField_apply] <;>
    simp [dilateField] <;> ring

/-- Pullback commutes with the infinitesimal charge-one gauge action. -/
theorem dilateField_gaugeDirection (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f : ℂ → ℝ) :
    dilateField t (gaugeDirection x f) =
      gaugeDirection (dilateField t x) (fun z ↦ f (t • z)) := by
  ext z i
  fin_cases i <;> simp [dilateField, -Complex.real_smul, fderiv_comp_smul]

/-- Pullback commutes with finite phase gauge transformations. -/
theorem dilateField_phaseGauge (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f : ℂ → ℝ) :
    dilateField t (phaseGauge x f) =
      phaseGauge (dilateField t x) (fun z ↦ f (t • z)) := by
  ext z i
  fin_cases i <;> simp [dilateField, -Complex.real_smul, fderiv_comp_smul] <;> ring

end TauCeti.Vortex
