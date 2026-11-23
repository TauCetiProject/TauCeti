/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Topology.Algebra.ConstMulAction
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Dilation of the plane vortex equation

A field `x = (b₁, b₂, p, q)` represents the connection `i(b₁ ds + b₂ dt)` and the
section `α = 2(p + i q)`. Pullback by `z ↦ t z` multiplies connection components by
`t`, while section components are composed with that map. The curvature equation
with coupling `c` is `*iF_a = c(1 - |α|²)/8`. Dilation changes `c` to `t² c`,
multiplies the curvature defect by `t²`, and multiplies the complex defect by `t`.
In particular, the physical coefficient `r/4` becomes `1/8` in the coordinate
`w = √(2r) z`. The curvature coefficient `∂₁ b₂ - ∂₂ b₁` is multiplied by `t²` and the covariant
derivative `d_a α` by `t`, so for `t = √(2r)` the plane integral of the integrand of Taubes's
scaled energy does not depend on `r`.

The same laws hold for the linearization and the infinitesimal and finite gauge
actions. For positive coupling the gauge row uses the coefficient metric `|b|² + c |δα|²/4`; its
transformation accounts for the change of that metric. The energy density acquires the factors
`t⁴`, `t²` and `1` on its curvature, kinetic and potential terms (`energyDensity_dilateField`).
Every-order derivative and squared `L²` scaling formulas include the change of volume and give the
integer Sobolev factors on smooth fields. These are identities of flat differential expressions;
the action on the Sobolev field spaces and the Sobolev gauge groups is in
`TauCeti.Analysis.PDE.Vortex.Dilation.Sobolev`, and insertion into a curved normal tube is not
treated.

Pullback commutes with the charge-one action of circle-valued gauges, the gauge being pulled
back as well (`dilateField_gaugeTransform`), and the coupled equation is gauge covariant at every
coupling (`coupledEquation_gaugeTransform`). The section of the pulled-back field is the section
composed with the dilation (`sectionValue_dilateField`), so a positive dilation preserves the end
framing `α(z) (z / |z|)⁻ᵐ → a` of degree `m` (`tendsto_sectionValue_dilateField`). Pulling a smooth
framed gauge back by a nonzero dilation is an automorphism `dilateGauge` of the smooth framed gauge
group, through which dilation intertwines the framed gauge actions
(`dilateField_framedGaugeGroup_smul`), so framed gauge orbits go to framed gauge orbits
(`exists_framedGaugeGroup_smul_dilateField_eq_iff`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology

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

@[simp]
theorem dilateField_zero (t : ℝ) : dilateField t 0 = 0 := by
  ext z i
  fin_cases i <;> simp [dilateField]

@[simp]
theorem dilateField_neg (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (-x) = -dilateField t x := by
  ext z i
  fin_cases i <;> simp [dilateField]

/-- The section of a pulled-back field is the section composed with the dilation. -/
@[simp]
theorem sectionValue_dilateField (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (dilateField t x) z = sectionValue x (t • z) := by
  simp [sectionValue_apply]

@[simp]
theorem dilateField_add (t : ℝ) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (x + y) = dilateField t x + dilateField t y := by
  ext z i
  fin_cases i <;> simp [dilateField] <;> ring

@[simp]
theorem dilateField_sub (t : ℝ) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (x - y) = dilateField t x - dilateField t y := by
  ext z i
  fin_cases i <;> simp [dilateField] <;> ring

@[simp]
theorem dilateField_smul (t c : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (c • x) = c • dilateField t x := by
  ext z i
  fin_cases i <;> simp [dilateField] <;> ring

/-- The vacuum is invariant under dilation. -/
@[simp]
theorem dilateField_vacuumField (t : ℝ) : dilateField t vacuumField = vacuumField := by
  ext z i
  fin_cases i <;> simp [dilateField, vacuumField_apply]

/-- Pullback by a dilation preserves the regularity of a field. -/
theorem contDiff_dilateField {n : WithTop ℕ∞} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ n x) (t : ℝ) : ContDiff ℝ n (dilateField t x) := by
  have h (i : Fin 4) : ContDiff ℝ n fun z ↦ x (t • z) i :=
    ((contDiff_piLp 2).1 hx i).comp (contDiff_id.const_smul t)
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  fin_cases i
  · simpa [dilateField] using contDiff_const.mul (h 0)
  · simpa [dilateField] using contDiff_const.mul (h 1)
  · simpa [dilateField] using h 2
  · simpa [dilateField] using h 3

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
  rw [Complex.finrank_real_complex,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  split_ifs <;> simp only [mul_one, mul_pow, ← pow_mul] <;> field_simp [ht] <;> ring

/-- A field differentiable at the dilated point has a differentiable dilation. -/
theorem differentiableAt_dilateField {t : ℝ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : DifferentiableAt ℝ x (t • z)) : DifferentiableAt ℝ (dilateField t x) z := by
  have hc (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x (t • w) i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hx).comp z
      (differentiableAt_id.const_smul t)
  rw [differentiableAt_euclidean]
  intro i
  fin_cases i
  · simpa [dilateField] using (hc 0).const_mul t
  · simpa [dilateField] using (hc 1).const_mul t
  · simpa [dilateField] using hc 2
  · simpa [dilateField] using hc 3

/-- Dilation multiplies the curvature coefficient `∂₁ b₂ - ∂₂ b₁` by `t²`. -/
@[simp]
theorem curvature_dilateField (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    curvature (dilateField t x) z = t ^ 2 * curvature x (t • z) := by
  simp only [curvature_apply, fderiv_dilateField_apply, Fin.isValue, Fin.reduceLT, ↓reduceIte,
    real_smul, smul_apply, smul_eq_mul]
  ring

/-- Dilation multiplies the covariant derivative `d_a α` of the section by `t`. -/
@[simp]
theorem covariantDerivative_dilateField (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) :
    covariantDerivative (dilateField t x) z v = t * covariantDerivative x (t • z) v := by
  have hs : sectionValue (dilateField t x) = fun w ↦ sectionValue x (t • w) :=
    funext fun w ↦ by simp [sectionValue_apply, dilateField]
  rw [covariantDerivative_apply, covariantDerivative_apply, hs, fderiv_comp_smul]
  simp only [dilateField_apply, real_smul, smul_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_add, ofReal_mul]
  ring

open MeasureTheory in
/-- **The scaled vortex energy does not depend on `r`.** For `r > 0` and `t = √(2r)`, the plane
integral of `r⁻¹ |*iF_a|² + |∇₁ α|² + |∇_i α|² + r (1 - |α|²)²` for the dilated field
`dilateField t X` equals `∫ (2 |*iF_a|² + |∇₁ α|² + |∇_i α|² + (1 - |α|²)² / 2)` for `X`, which
does not involve `r`. Pointwise the first integrand is `2r` times the second at `t z`, and the
area factor `t⁻²` of the coordinate `w = t z` cancels `2r`.

The first integrand is the integrand `r⁻¹ |F_a|² + |∇_a α|² + r (1 - |α|²)²` of Taubes's scaled
energy written in plane quantities: for a field pulled back to `ℂ_base × ℂ_normal` along a normal
coordinate, `|F_a|` is `|*iF_a|` and `|∇_a α|²` is `|∇₁ α|² + |∇_i α|²` at that coordinate. -/
theorem integral_inv_mul_curvature_dilateField_sq_add (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    {r : ℝ} (hr : 0 < r) (X : ℂ → EuclideanSpace ℝ (Fin 4)) :
    ∫ z, (r⁻¹ * curvature (dilateField (√(2 * r)) X) z ^ 2 +
        ‖covariantDerivative (dilateField (√(2 * r)) X) z 1‖ ^ 2 +
        ‖covariantDerivative (dilateField (√(2 * r)) X) z I‖ ^ 2 +
        r * (1 - ‖sectionValue (dilateField (√(2 * r)) X) z‖ ^ 2) ^ 2) ∂μ =
      ∫ z, (2 * curvature X z ^ 2 + ‖covariantDerivative X z 1‖ ^ 2 +
        ‖covariantDerivative X z I‖ ^ 2 + (1 - ‖sectionValue X z‖ ^ 2) ^ 2 / 2) ∂μ := by
  set t := √(2 * r)
  have ht : t ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  set g : ℂ → ℝ := fun w ↦ 2 * curvature X w ^ 2 + ‖covariantDerivative X w 1‖ ^ 2 +
    ‖covariantDerivative X w I‖ ^ 2 + (1 - ‖sectionValue X w‖ ^ 2) ^ 2 / 2
  -- Pointwise, the integrand is `2 r g (t z)`.
  have key (z : ℂ) : r⁻¹ * curvature (dilateField t X) z ^ 2 +
      ‖covariantDerivative (dilateField t X) z 1‖ ^ 2 +
      ‖covariantDerivative (dilateField t X) z I‖ ^ 2 +
      r * (1 - ‖sectionValue (dilateField t X) z‖ ^ 2) ^ 2 = (2 * r) * g (t • z) := by
    have hs : sectionValue (dilateField t X) z = sectionValue X (t • z) := by
      simp [sectionValue_apply, dilateField_apply]
    simp only [g, curvature_dilateField, covariantDerivative_dilateField, hs,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg ht₀]
    field_simp
    rw [ht]
    ring
  simp_rw [key]
  rw [integral_const_mul, Measure.integral_comp_smul μ g t, Complex.finrank_real_complex, ht,
    abs_of_nonneg (by positivity), smul_eq_mul]
  field_simp

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

/-- **Dilation of the energy density.** Pullback by `z ↦ t z` multiplies the curvature term of
the energy density by `t⁴` and its kinetic term by `t²`, and leaves the potential term
`(1 - |α|²)²` unchanged. -/
theorem energyDensity_dilateField (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    energyDensity (dilateField t x) z =
      t ^ 4 * curvature x (t • z) ^ 2 +
        t ^ 2 * (‖covariantDerivative x (t • z) 1‖ ^ 2 +
          ‖covariantDerivative x (t • z) I‖ ^ 2) +
        (1 - ‖sectionValue x (t • z)‖ ^ 2) ^ 2 := by
  simp only [energyDensity_apply, curvature_dilateField, covariantDerivative_dilateField,
    sectionValue_dilateField, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- A nonzero dilation carries the solutions of the equation with coupling `c` exactly onto
those of the equation with coupling `t² c`. -/
theorem coupledEquation_dilateField_eq_zero_iff' (c : ℝ) {t : ℝ} (ht : t ≠ 0)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    coupledEquation (t ^ 2 * c) (dilateField t x) = 0 ↔ coupledEquation c x = 0 := by
  simp only [funext_iff, Pi.zero_apply, coupledEquation_dilateField_eq_zero_iff c t ht]
  refine ⟨fun h z ↦ ?_, fun h z ↦ h _⟩
  simpa [smul_smul, ht] using h (t⁻¹ • z)

/-- **The flat scaling.** A field solves the equation `*iF_a = (r / 4) (1 - |α|²)`, with
coupling `2 r`, exactly when its pullback to the coordinate `w = √(2r) z` solves the normalized
plane vortex equation `*iF_a = (1 - |α|²) / 8`. -/
theorem equation_dilateField_inv_sqrt_eq_zero_iff {r : ℝ} (hr : 0 < r)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    equation (dilateField (√(2 * r))⁻¹ x) = 0 ↔ coupledEquation (2 * r) x = 0 := by
  have hc : (√(2 * r))⁻¹ ^ 2 * (2 * r) = 1 := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  simpa only [hc, coupledEquation_one] using
    coupledEquation_dilateField_eq_zero_iff' (2 * r) (t := (√(2 * r))⁻¹)
      (inv_ne_zero (by positivity)) x

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

/-- The logarithmic derivative `Im (u⁻¹ du)` of a pulled-back gauge is the pulled-back
one-form. -/
theorem gaugeForm_comp_smul (u : ℂ → Circle) (t : ℝ) (z : ℂ) :
    gaugeForm (fun w ↦ u (t • w)) z = t • gaugeForm u (t • z) := by
  ext v
  have h : fderiv ℝ (fun w ↦ (u (t • w) : ℂ)) z v =
      t • fderiv ℝ (fun w ↦ (u w : ℂ)) (t • z) v := by
    rw [fderiv_comp_smul (f := fun w ↦ (u w : ℂ)) t, FunLike.coe_smul, Pi.smul_apply]
  simp only [gaugeForm_apply, h, FunLike.coe_smul, Pi.smul_apply, mul_smul_comm, Complex.smul_im,
    smul_eq_mul]

/-- Pullback commutes with finite charge-one gauge transformations by circle-valued maps. -/
theorem dilateField_gaugeTransform (t : ℝ) (u : ℂ → Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (gaugeTransform u x) =
      gaugeTransform (fun w ↦ u (t • w)) (dilateField t x) := by
  ext z i
  fin_cases i <;> simp [dilateField, gaugeTransform_apply, gaugeForm_comp_smul, -gaugeForm_apply,
    -Complex.real_smul] <;> ring

/-- Pullback commutes with the linear gauge action on field variations. -/
theorem dilateField_gaugeLinearAction (t : ℝ) (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (gaugeLinearAction u y) =
      gaugeLinearAction (fun z ↦ u (t • z)) (dilateField t y) := by
  ext z i
  fin_cases i <;> simp [dilateField, gaugeLinearAction_apply]

/-- Off-shell gauge covariance of the coupled equation: the curvature row is unchanged and the
complex row is multiplied by the same circle element as the section. -/
theorem coupledEquation_gaugeTransform (c : ℝ) {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) :
    coupledEquation c (gaugeTransform u x) z =
      !₂[coupledEquation c x z 0,
        (u z : ℂ).re * coupledEquation c x z 1 - (u z : ℂ).im * coupledEquation c x z 2,
        (u z : ℂ).im * coupledEquation c x z 1 + (u z : ℂ).re * coupledEquation c x z 2] := by
  have he := equation_gaugeTransform hu hx
  have hn := Circle.re_sq_add_im_sq (u z)
  have h₀ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) he
  have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) he
  have h₂ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h₀ h₁ h₂
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · simp only [coupledEquation, Matrix.cons_val_zero, h₀]
    simp only [gaugeTransform_apply, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination (c - 1) * (x z 2 ^ 2 + x z 3 ^ 2) / 2 * hn
  · simpa [coupledEquation] using h₁
  · simpa [coupledEquation] using h₂

/-- A gauge transformation preserves the coupled vortex equation in both directions. -/
@[simp]
theorem coupledEquation_gaugeTransform_eq_zero_iff (c : ℝ) {u : ℂ → Circle}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z)
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) :
    coupledEquation c (gaugeTransform u x) z = 0 ↔ coupledEquation c x z = 0 := by
  rw [coupledEquation_gaugeTransform c hu hx, circle_rotate_tail_eq_zero_iff]

/-- A positive dilation preserves the limit `a` of the end framing `α(z) (z / |z|)^(-m)` of
degree `m`. -/
theorem tendsto_sectionValue_dilateField {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ} {a : ℂ}
    (hx : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 a))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun z ↦ sectionValue (dilateField t x) z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹)
      (cocompact ℂ) (𝓝 a) := by
  have hdil : Tendsto (fun z : ℂ ↦ t • z) (cocompact ℂ) (cocompact ℂ) :=
    (Homeomorph.smulOfNeZero t ht.ne').map_cocompact.le
  refine (hx.comp hdil).congr fun z ↦ ?_
  simp only [Function.comp_apply, sectionValue_dilateField, smul_div_norm_smul ht]

/-! ### Dilation of framed gauges -/

/-- Pulling a smooth framed gauge back by a nonzero dilation gives a smooth framed gauge. -/
theorem comp_smul_mem_framedGaugeGroup {u : ℂ → Circle} (hu : u ∈ framedGaugeGroup) {t : ℝ}
    (ht : t ≠ 0) : (fun w ↦ u (t • w)) ∈ framedGaugeGroup := by
  obtain ⟨hs, hlim⟩ := (mem_framedGaugeGroup u).1 hu
  exact (mem_framedGaugeGroup _).2 ⟨hs.comp (contDiff_id.const_smul t),
    hlim.comp (Homeomorph.smulOfNeZero t ht).map_cocompact.le⟩

/-- **Dilation of framed gauges**: the automorphism `u ↦ u (t • ·)` of the smooth framed gauge
group, for `t ≠ 0`. -/
def dilateGauge {t : ℝ} (ht : t ≠ 0) : framedGaugeGroup ≃* framedGaugeGroup where
  toFun u := ⟨fun w ↦ u.val (t • w), comp_smul_mem_framedGaugeGroup u.property ht⟩
  invFun u := ⟨fun w ↦ u.val (t⁻¹ • w), comp_smul_mem_framedGaugeGroup u.property (inv_ne_zero ht)⟩
  left_inv u := by
    ext w
    simp [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 ht)]
  right_inv u := by
    ext w
    simp [inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.2 ht)]
  map_mul' _ _ := rfl

@[simp]
theorem coe_dilateGauge_apply {t : ℝ} (ht : t ≠ 0) (u : framedGaugeGroup) (w : ℂ) :
    (dilateGauge ht u : ℂ → Circle) w = (u : ℂ → Circle) (t • w) :=
  (rfl)

@[simp]
theorem coe_dilateGauge_symm_apply {t : ℝ} (ht : t ≠ 0) (u : framedGaugeGroup) (w : ℂ) :
    ((dilateGauge ht).symm u : ℂ → Circle) w = (u : ℂ → Circle) (t⁻¹ • w) :=
  (rfl)

/-- Dilation intertwines the actions of the smooth framed gauge group. -/
theorem dilateField_framedGaugeGroup_smul {t : ℝ} (ht : t ≠ 0) (u : framedGaugeGroup)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    dilateField t (u • x) = dilateGauge ht u • dilateField t x := by
  have hu : ((dilateGauge ht u : framedGaugeGroup) : ℂ → Circle) = fun w ↦ u.val (t • w) :=
    funext (coe_dilateGauge_apply ht u)
  rw [framedGaugeGroup_smul, framedGaugeGroup_smul, hu]
  exact dilateField_gaugeTransform t u x

/-- A gauge lies in the smooth framed gauge group exactly when its pullback by a nonzero
dilation does. -/
theorem comp_smul_mem_framedGaugeGroup_iff {t : ℝ} (ht : t ≠ 0) {u : ℂ → Circle} :
    (fun w ↦ u (t • w)) ∈ framedGaugeGroup ↔ u ∈ framedGaugeGroup := by
  refine ⟨fun h ↦ ?_, fun h ↦ comp_smul_mem_framedGaugeGroup h ht⟩
  simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using
    comp_smul_mem_framedGaugeGroup h (inv_ne_zero ht)

/-- **Dilation preserves framed gauge orbits.** For `t ≠ 0`, the fields `x` and `y` are related
by a smooth framed gauge transformation exactly when their pullbacks by `z ↦ t z` are. -/
theorem exists_framedGaugeGroup_smul_dilateField_eq_iff {t : ℝ} (ht : t ≠ 0)
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    (∃ u : framedGaugeGroup, u • dilateField t y = dilateField t x) ↔
      ∃ u : framedGaugeGroup, u • y = x := by
  -- Pulling back a relating gauge by `t` relates the pulled-back fields; pulling back by `t⁻¹`
  -- undoes the dilation.
  have key {s : ℝ} (hs : s ≠ 0) {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
      (h : ∃ u : framedGaugeGroup, u • y = x) :
      ∃ u : framedGaugeGroup, u • dilateField s y = dilateField s x := by
    obtain ⟨u, rfl⟩ := h
    exact ⟨dilateGauge hs u, (dilateField_framedGaugeGroup_smul hs u y).symm⟩
  refine ⟨fun h ↦ ?_, key ht⟩
  simpa [inv_mul_cancel₀ ht] using key (inv_ne_zero ht) h

end TauCeti.Vortex
