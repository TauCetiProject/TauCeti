/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Topology.Algebra.Field
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Translations and rotations of plane vortex fields

A field `x = (b₁, b₂, p, q)` represents the connection `a = i(b₁ ds + b₂ dt)` and the section
`α = 2(p + i q)`. The orientation-preserving isometries of the plane act on fields by pullback.

* `translateField a x` is the pullback by `z ↦ z + a`; all components are composed with the
  translation.
* `rotateField u x` is the pullback by `z ↦ u z` for `u` on the unit circle. The section is
  composed with the rotation, and the connection coefficient `b₁ + i b₂` is composed with the
  rotation and multiplied by `u⁻¹`, since the pullback of `b₁ ds + b₂ dt` is
  `v ↦ Re(conj (b₁ + i b₂) · u v)`.

Both actions commute with the charge-one gauge action and fix the vacuum. The curvature,
the energy density and the gauge-fixing row are scalars and are simply transported. The
complex defect `∂bar_a α` is a `(0,1)`-form coefficient, so under rotation it is transported and
multiplied by `u⁻¹`; `rotateTarget` records this action on the target `ℝ ⊕ ℝ ⊕ ℂ` of the
gauge-fixed operator `L_x`, and `L_x` intertwines the two actions, as does its formal adjoint.
In particular translations and rotations map vortices to vortices.

For the framing at infinity, `α(z) (z / |z|)^(-m) → 1`, translations preserve the condition,
while a rotation multiplies the limit by `u^m`. The constant line-frame gauge `u^(-m)` restores
it, so a rotation followed by this constant gauge preserves framed degree-`m` vortices.

These are identities of smooth differential expressions; their Sobolev completions, and the
induced action on the divisor of a vortex, are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology

/-! ### Translations -/

/-- Pullback of a vortex field by the translation `z ↦ z + a`. -/
def translateField (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  x (z + a)

@[simp]
theorem translateField_apply (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    translateField a x z = x (z + a) := (rfl)

@[simp]
theorem translateField_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) : translateField 0 x = x := by
  funext z
  simp

/-- Successive translations add. -/
@[simp]
theorem translateField_translateField (a b : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    translateField a (translateField b x) = translateField (a + b) x := by
  funext z
  simp [add_assoc]

/-- A spatial derivative of a translated component is the translated derivative. No
differentiability is needed. -/
theorem fderiv_translateField_apply (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ)
    (i : Fin 4) :
    fderiv ℝ (fun w ↦ translateField a x w i) z = fderiv ℝ (fun w ↦ x w i) (z + a) :=
  fderiv_comp_add_right (f := fun w ↦ x w i) a

@[simp]
theorem sectionValue_translateField (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (translateField a x) z = sectionValue x (z + a) := by
  simp [sectionValue_apply]

@[simp]
theorem covariantDerivative_translateField (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (z v : ℂ) :
    covariantDerivative (translateField a x) z v = covariantDerivative x (z + a) v := by
  have h : sectionValue (translateField a x) = fun w ↦ sectionValue x (w + a) :=
    funext (sectionValue_translateField a x)
  simp only [covariantDerivative_apply, h, fderiv_comp_add_right (f := sectionValue x) a,
    translateField_apply]

@[simp]
theorem curvature_translateField (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    curvature (translateField a x) z = curvature x (z + a) := by
  simp only [curvature_apply, fderiv_translateField_apply]

@[simp]
theorem energyDensity_translateField (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    energyDensity (translateField a x) z = energyDensity x (z + a) := by
  simp [energyDensity_apply]

/-- Translation transports the vortex defects. -/
@[simp]
theorem equation_translateField (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    equation (translateField a x) z = equation x (z + a) := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp only [equation_apply_zero, equation_apply_one, equation_apply_two,
      fderiv_translateField_apply] <;>
    simp only [translateField_apply]

/-- Translation transports the linearized equation, translating base field and variation. -/
@[simp]
theorem linearizedEquation_translateField (a : ℂ) (x y : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) :
    linearizedEquation (translateField a x) (translateField a y) z =
      linearizedEquation x y (z + a) := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp only [linearizedEquation_apply_zero, linearizedEquation_apply_one,
      linearizedEquation_apply_two, fderiv_translateField_apply] <;>
    simp only [translateField_apply]

/-- The gauge-fixing row `d₀*` commutes with translations. -/
theorem gaugeAdjoint_translateField (a : ℂ) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeAdjoint (translateField a x) (translateField a y) z = gaugeAdjoint x y (z + a) := by
  simp only [gaugeAdjoint_def, fderiv_translateField_apply]
  simp only [translateField_apply]

/-- The gauge-fixed operator `L_x` commutes with translations. -/
@[simp]
theorem gaugeFixedOperator_translateField (a : ℂ) (x y : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) :
    gaugeFixedOperator (translateField a x) (translateField a y) z =
      gaugeFixedOperator x y (z + a) := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [gaugeFixedOperator_apply_zero, gaugeFixedOperator_apply_one,
      gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three,
      gaugeAdjoint_translateField, linearizedEquation_translateField]

/-- The formal adjoint `L_x*` commutes with translations. -/
@[simp]
theorem gaugeFixedAdjoint_translateField (a : ℂ) (x η : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) :
    gaugeFixedAdjoint (translateField a x) (translateField a η) z =
      gaugeFixedAdjoint x η (z + a) := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [gaugeFixedAdjoint_apply_zero, gaugeFixedAdjoint_apply_one,
      gaugeFixedAdjoint_apply_two, gaugeFixedAdjoint_apply_three,
      fderiv_translateField_apply] <;>
    simp only [translateField_apply]

/-- Translation commutes with the infinitesimal gauge action, translating the phase. -/
theorem translateField_gaugeDirection (a : ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f : ℂ → ℝ) :
    translateField a (gaugeDirection x f) =
      gaugeDirection (translateField a x) (fun w ↦ f (w + a)) := by
  ext z i
  fin_cases i <;> simp [fderiv_comp_add_right]

/-- Translation commutes with the charge-one gauge action, translating the gauge. -/
theorem translateField_gaugeTransform (a : ℂ) (g : ℂ → Circle)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    translateField a (gaugeTransform g x) =
      gaugeTransform (fun w ↦ g (w + a)) (translateField a x) := by
  funext z
  simp only [translateField_apply, gaugeTransform_apply, gaugeForm_apply,
    fderiv_comp_add_right (f := fun w ↦ (g w : ℂ)) a]

@[simp]
theorem translateField_vacuumField (a : ℂ) : translateField a vacuumField = vacuumField := by
  funext z
  simp [vacuumField_apply]

/-- The unit phase `z / |z|` changes by a factor tending to one under a fixed translation. -/
private theorem tendsto_phase_add_div_phase (a : ℂ) :
    Tendsto (fun z : ℂ ↦ (z + a) / ((‖z + a‖ : ℝ) : ℂ) / (z / ((‖z‖ : ℝ) : ℂ)))
      (cocompact ℂ) (𝓝 1) := by
  -- The ratio is `g / |g|` for `g z = (z + a) / z = 1 + a z⁻¹`, which tends to one.
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ Filter.tendsto_inv₀_cobounded
  have hg : Tendsto (fun z : ℂ ↦ 1 + a * z⁻¹) (cocompact ℂ) (𝓝 1) := by
    simpa using (hinv.const_mul a).const_add 1
  have hcont : ContinuousAt (fun w : ℂ ↦ w / ((‖w‖ : ℝ) : ℂ)) 1 :=
    continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt (by simp)
  have hlim := (hcont.tendsto.comp hg)
  simp only [norm_one, ofReal_one, div_one, Function.comp_def] at hlim
  refine hlim.congr' ?_
  filter_upwards [(isCompact_singleton : IsCompact ({0} : Set ℂ)).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz0
  have hsum : 1 + a * z⁻¹ = (z + a) / z := by field_simp
  rw [hsum, norm_div, ofReal_div]
  field_simp

/-- Translations preserve the end framing `α(z) (z / |z|)^(-m) → 1` of degree `m`. -/
theorem tendsto_sectionValue_translateField {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}
    (hx : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (a : ℂ) :
    Tendsto (fun z ↦ sectionValue (translateField a x) z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹)
      (cocompact ℂ) (𝓝 1) := by
  have hshift : Tendsto (fun z : ℂ ↦ z + a) (cocompact ℂ) (cocompact ℂ) :=
    (Homeomorph.addRight a).map_cocompact.le
  have h := (hx.comp hshift).mul ((tendsto_phase_add_div_phase a).pow m)
  simp only [one_mul, one_pow, Function.comp_def] at h
  refine h.congr' ?_
  filter_upwards [(isCompact_singleton : IsCompact ({0} : Set ℂ)).compl_mem_cocompact,
    (isCompact_singleton : IsCompact ({-a} : Set ℂ)).compl_mem_cocompact] with z hz hza
  have hz0 : z ≠ 0 := by simpa using hz
  have hza0 : z + a ≠ 0 := fun h ↦ hza (by simpa using eq_neg_of_add_eq_zero_left h)
  have h₁ : z / (‖z‖ : ℂ) ≠ 0 := by simp [hz0]
  have h₂ : (z + a) / (‖z + a‖ : ℂ) ≠ 0 := by simp [hza0]
  have h₃ : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz0
  have h₄ : ((‖z + a‖ : ℝ) : ℂ) ≠ 0 := by simpa using hza0
  rw [sectionValue_translateField, mul_assoc, ← inv_pow, ← inv_pow, ← mul_pow]
  congr 2
  field_simp

/-! ### Rotations -/

/-- Pullback of a vortex field by the rotation `z ↦ u z`. The section is composed with the
rotation; the connection coefficient `b₁ + i b₂` is composed with the rotation and multiplied
by `u⁻¹`, which is the pullback of the one-form `b₁ ds + b₂ dt`. -/
def rotateField (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[(u : ℂ).re * x (u * z) 0 + (u : ℂ).im * x (u * z) 1,
    (u : ℂ).re * x (u * z) 1 - (u : ℂ).im * x (u * z) 0, x (u * z) 2, x (u * z) 3]

@[simp]
theorem rotateField_apply (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    rotateField u x z =
      !₂[(u : ℂ).re * x (u * z) 0 + (u : ℂ).im * x (u * z) 1,
        (u : ℂ).re * x (u * z) 1 - (u : ℂ).im * x (u * z) 0, x (u * z) 2, x (u * z) 3] :=
  (rfl)

@[simp]
theorem rotateField_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) : rotateField 1 x = x := by
  ext z i
  fin_cases i <;> simp

/-- Successive rotations multiply. -/
@[simp]
theorem rotateField_rotateField (u v : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateField u (rotateField v x) = rotateField (u * v) x := by
  ext z i
  fin_cases i <;> simp [mul_comm (v : ℂ), mul_assoc] <;> ring

/-- The action of a rotation on the target `ℝ ⊕ ℝ ⊕ ℂ` of the gauge-fixed operator: the
gauge-fixing and curvature rows are transported, and the complex `∂bar` row is transported
and multiplied by `u⁻¹`. -/
def rotateTarget (u : Circle) (η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[η (u * z) 0, η (u * z) 1, (u : ℂ).re * η (u * z) 2 + (u : ℂ).im * η (u * z) 3,
    (u : ℂ).re * η (u * z) 3 - (u : ℂ).im * η (u * z) 2]

@[simp]
theorem rotateTarget_apply (u : Circle) (η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    rotateTarget u η z =
      !₂[η (u * z) 0, η (u * z) 1, (u : ℂ).re * η (u * z) 2 + (u : ℂ).im * η (u * z) 3,
        (u : ℂ).re * η (u * z) 3 - (u : ℂ).im * η (u * z) 2] :=
  (rfl)

@[simp]
theorem rotateTarget_one (η : ℂ → EuclideanSpace ℝ (Fin 4)) : rotateTarget 1 η = η := by
  ext z i
  fin_cases i <;> simp

/-- Successive rotations of the target multiply. -/
@[simp]
theorem rotateTarget_rotateTarget (u v : Circle) (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateTarget u (rotateTarget v η) = rotateTarget (u * v) η := by
  ext z i
  fin_cases i <;> simp [mul_comm (v : ℂ), mul_assoc] <;> ring

/-- The chain rule for precomposition with the rotation `w ↦ u w`. -/
private theorem fderiv_comp_mul_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Circle) (g : ℂ → F) (z v : ℂ) :
    fderiv ℝ (fun w ↦ g (u * w)) z v = fderiv ℝ g (u * z) (u * v) := by
  have h := (rotation u).toContinuousLinearEquiv.comp_right_fderiv (f := g) (x := z)
  simpa [Function.comp_def, rotation_apply] using congrArg (fun L ↦ L v) h

/-- Evaluation of a real-linear functional at `u`, in the basis `(1, I)`. -/
private theorem clm_apply_coe (L : ℂ →L[ℝ] ℝ) (u : Circle) :
    L u = (u : ℂ).re * L 1 + (u : ℂ).im * L I := by
  simpa using LinearMap.apply_eq_re_smul_one_add_im_smul_I (L : ℂ →ₗ[ℝ] ℝ) u

/-- Evaluation of a real-linear functional at `u I`, in the basis `(1, I)`. -/
private theorem clm_apply_coe_mul_I (L : ℂ →L[ℝ] ℝ) (u : Circle) :
    L (u * I) = -(u : ℂ).im * L 1 + (u : ℂ).re * L I := by
  simpa using LinearMap.apply_eq_re_smul_one_add_im_smul_I (L : ℂ →ₗ[ℝ] ℝ) (u * I)

/-- The coordinate derivatives of a rotated field component. -/
private theorem fderiv_comp_mul_apply_one (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (i : Fin 4) (z : ℂ) :
    fderiv ℝ (fun w ↦ x (u * w) i) z 1 = (u : ℂ).re * fderiv ℝ (fun w ↦ x w i) (u * z) 1 +
      (u : ℂ).im * fderiv ℝ (fun w ↦ x w i) (u * z) I := by
  rw [fderiv_comp_mul_apply u (fun w ↦ x w i), mul_one, clm_apply_coe]

private theorem fderiv_comp_mul_apply_I (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (i : Fin 4) (z : ℂ) :
    fderiv ℝ (fun w ↦ x (u * w) i) z I = -(u : ℂ).im * fderiv ℝ (fun w ↦ x w i) (u * z) 1 +
      (u : ℂ).re * fderiv ℝ (fun w ↦ x w i) (u * z) I := by
  rw [fderiv_comp_mul_apply u (fun w ↦ x w i), clm_apply_coe_mul_I]

private theorem differentiableAt_comp_mul {u : Circle} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {i : Fin 4} {z : ℂ} (hx : DifferentiableAt ℝ (fun w ↦ x w i) (u * z)) :
    DifferentiableAt ℝ (fun w ↦ x (u * w) i) z :=
  hx.comp z (differentiableAt_id.const_mul _)

@[simp]
theorem sectionValue_rotateField (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (rotateField u x) z = sectionValue x (u * z) := by
  simp [sectionValue_apply]

/-- The covariant derivative of the pullback is the pulled-back covariant derivative. No
differentiability is needed. -/
@[simp]
theorem covariantDerivative_rotateField (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (z v : ℂ) :
    covariantDerivative (rotateField u x) z v = covariantDerivative x (u * z) (u * v) := by
  have h : sectionValue (rotateField u x) = fun w ↦ sectionValue x (u * w) :=
    funext (sectionValue_rotateField u x)
  simp only [covariantDerivative_apply, h, fderiv_comp_mul_apply, sectionValue_rotateField]
  congr 2
  simp only [rotateField_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_re, mul_im]
  push_cast
  ring

/-- Curvature is a two-form coefficient, and rotations preserve the area form. -/
@[simp]
theorem curvature_rotateField {u : Circle} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hb₀ : DifferentiableAt ℝ (fun w ↦ x w 0) (u * z))
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 1) (u * z)) :
    curvature (rotateField u x) z = curvature x (u * z) := by
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  have h₀ := differentiableAt_comp_mul hb₀
  have h₁ := differentiableAt_comp_mul hb₁
  simp only [curvature_apply, rotateField_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [fderiv_fun_sub (h₁.const_mul _) (h₀.const_mul _),
    fderiv_fun_add (h₀.const_mul _) (h₁.const_mul _)]
  simp only [fderiv_const_mul h₀, fderiv_const_mul h₁, sub_apply, add_apply, smul_apply,
    smul_eq_mul, fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
  linear_combination (fderiv ℝ (fun w ↦ x w 1) (u * z) 1 -
    fderiv ℝ (fun w ↦ x w 0) (u * z) I) * hn

/-- The covariant derivative is real-linear in the tangent vector. -/
private theorem covariantDerivative_eq (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) :
    covariantDerivative x z v =
      v.re * covariantDerivative x z 1 + v.im * covariantDerivative x z I := by
  have h := LinearMap.apply_eq_re_smul_one_add_im_smul_I
    (fderiv ℝ (sectionValue x) z : ℂ →ₗ[ℝ] ℂ) v
  simp only [ContinuousLinearMap.coe_coe, Complex.real_smul] at h
  simp only [covariantDerivative_apply, h, one_re, one_im, I_re, I_im]
  push_cast
  ring

/-- Rotation transports the physical energy density. -/
@[simp]
theorem energyDensity_rotateField {u : Circle} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hb₀ : DifferentiableAt ℝ (fun w ↦ x w 0) (u * z))
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 1) (u * z)) :
    energyDensity (rotateField u x) z = energyDensity x (u * z) := by
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  simp only [energyDensity_apply, curvature_rotateField hb₀ hb₁, covariantDerivative_rotateField,
    sectionValue_rotateField, mul_one]
  rw [covariantDerivative_eq x _ (u : ℂ), covariantDerivative_eq x _ ((u : ℂ) * I)]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, add_re, add_im, mul_re,
    mul_im, ofReal_re, ofReal_im, I_re, I_im]
  linear_combination ((covariantDerivative x (u * z) 1).re ^ 2 +
    (covariantDerivative x (u * z) 1).im ^ 2 + (covariantDerivative x (u * z) I).re ^ 2 +
    (covariantDerivative x (u * z) I).im ^ 2) * hn

/-- Rotation transports the curvature defect and multiplies the complex defect `∂bar_a α` by
`u⁻¹`. -/
theorem equation_rotateField {u : Circle} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hb₀ : DifferentiableAt ℝ (fun w ↦ x w 0) (u * z))
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 1) (u * z)) :
    equation (rotateField u x) z =
      !₂[equation x (u * z) 0,
        (u : ℂ).re * equation x (u * z) 1 + (u : ℂ).im * equation x (u * z) 2,
        (u : ℂ).re * equation x (u * z) 2 - (u : ℂ).im * equation x (u * z) 1] := by
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · have hc := curvature_rotateField hb₀ hb₁
    simp only [curvature_apply] at hc
    simp only [equation_apply_zero, Matrix.cons_val_zero]
    simp only [rotateField_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hc ⊢
    linear_combination -hc
  all_goals
    simp only [equation_apply_one, equation_apply_two, rotateField_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, fderiv_comp_mul_apply_one,
      fderiv_comp_mul_apply_I]
    ring

/-- Rotations preserve and reflect the vortex equation. -/
theorem equation_rotateField_eq_zero_iff {u : Circle} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hb₀ : DifferentiableAt ℝ (fun w ↦ x w 0) (u * z))
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 1) (u * z)) :
    equation (rotateField u x) z = 0 ↔ equation x (u * z) = 0 := by
  rw [equation_rotateField hb₀ hb₁]
  refine ⟨fun h ↦ ?_, fun h ↦ by ext i; fin_cases i <;> simp [h]⟩
  have h₀ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) h
  have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  have h₂ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply] at h₀ h₁ h₂
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  all_goals simp only [PiLp.zero_apply]
  · exact h₀
  · linear_combination (u : ℂ).re * h₁ - (u : ℂ).im * h₂ - equation x (u * z) 1 * hn
  · linear_combination (u : ℂ).im * h₁ + (u : ℂ).re * h₂ - equation x (u * z) 2 * hn

/-- Rotation transports the curvature row of the linearized equation and multiplies its
complex rows by `u⁻¹`, rotating base field and variation. -/
theorem linearizedEquation_rotateField {u : Circle} {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) (u * z))
    (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) (u * z)) :
    linearizedEquation (rotateField u x) (rotateField u y) z =
      !₂[linearizedEquation x y (u * z) 0,
        (u : ℂ).re * linearizedEquation x y (u * z) 1 +
          (u : ℂ).im * linearizedEquation x y (u * z) 2,
        (u : ℂ).re * linearizedEquation x y (u * z) 2 -
          (u : ℂ).im * linearizedEquation x y (u * z) 1] := by
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  have h₀ := differentiableAt_comp_mul hy₀
  have h₁ := differentiableAt_comp_mul hy₁
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · simp only [linearizedEquation_apply_zero, rotateField_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rw [fderiv_fun_sub (h₁.const_mul _) (h₀.const_mul _),
      fderiv_fun_add (h₀.const_mul _) (h₁.const_mul _)]
    simp only [fderiv_const_mul h₀, fderiv_const_mul h₁, sub_apply, add_apply, smul_apply,
      smul_eq_mul, fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
    linear_combination (fderiv ℝ (fun w ↦ y w 0) (u * z) I -
      fderiv ℝ (fun w ↦ y w 1) (u * z) 1) * hn
  all_goals
    simp only [linearizedEquation_apply_one, linearizedEquation_apply_two, rotateField_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, fderiv_comp_mul_apply_one,
      fderiv_comp_mul_apply_I]
    ring

/-- The gauge-fixing row `d₀*` is a divergence, and is transported by rotations. -/
theorem gaugeAdjoint_rotateField {u : Circle} {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) (u * z))
    (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) (u * z)) :
    gaugeAdjoint (rotateField u x) (rotateField u y) z = gaugeAdjoint x y (u * z) := by
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  have h₀ := differentiableAt_comp_mul hy₀
  have h₁ := differentiableAt_comp_mul hy₁
  simp only [gaugeAdjoint_def, rotateField_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  rw [fderiv_fun_sub (h₁.const_mul _) (h₀.const_mul _),
    fderiv_fun_add (h₀.const_mul _) (h₁.const_mul _)]
  simp only [fderiv_const_mul h₀, fderiv_const_mul h₁, sub_apply, add_apply, smul_apply,
    smul_eq_mul, fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
  linear_combination (fderiv ℝ (fun w ↦ y w 0) (u * z) 1 +
    fderiv ℝ (fun w ↦ y w 1) (u * z) I) * hn

/-- The gauge-fixed operator intertwines the rotation of fields with `rotateTarget`. -/
theorem gaugeFixedOperator_rotateField {u : Circle} {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) (u * z))
    (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) (u * z)) :
    gaugeFixedOperator (rotateField u x) (rotateField u y) z =
      rotateTarget u (gaugeFixedOperator x y) z := by
  have hl := linearizedEquation_rotateField (x := x) hy₀ hy₁
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [gaugeAdjoint_rotateField hy₀ hy₁, hl, -gaugeAdjoint_def]

/-- The formal adjoint `L_x*` intertwines `rotateTarget` with the rotation of fields. -/
theorem gaugeFixedAdjoint_rotateField {u : Circle} {x η : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hη₂ : DifferentiableAt ℝ (fun w ↦ η w 2) (u * z))
    (hη₃ : DifferentiableAt ℝ (fun w ↦ η w 3) (u * z)) :
    gaugeFixedAdjoint (rotateField u x) (rotateTarget u η) z =
      rotateField u (gaugeFixedAdjoint x η) z := by
  have hn := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hn
  have h₂ := differentiableAt_comp_mul hη₂
  have h₃ := differentiableAt_comp_mul hη₃
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [gaugeFixedAdjoint_apply_zero, gaugeFixedAdjoint_apply_one, rotateField_apply,
      rotateTarget_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
    ring
  · simp only [gaugeFixedAdjoint_apply_zero, gaugeFixedAdjoint_apply_one, rotateField_apply,
      rotateTarget_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
    ring
  · simp only [gaugeFixedAdjoint_apply_two, rotateField_apply, rotateTarget_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [fderiv_fun_add (h₂.const_mul _) (h₃.const_mul _),
      fderiv_fun_sub (h₃.const_mul _) (h₂.const_mul _)]
    simp only [fderiv_const_mul h₂, fderiv_const_mul h₃, sub_apply, add_apply, smul_apply,
      smul_eq_mul, fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
    linear_combination (-fderiv ℝ (fun w ↦ η w 2) (u * z) 1 -
      fderiv ℝ (fun w ↦ η w 3) (u * z) I - x (u * z) 1 * η (u * z) 2 +
      x (u * z) 0 * η (u * z) 3) * hn
  · simp only [gaugeFixedAdjoint_apply_three, rotateField_apply, rotateTarget_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [fderiv_fun_add (h₂.const_mul _) (h₃.const_mul _),
      fderiv_fun_sub (h₃.const_mul _) (h₂.const_mul _)]
    simp only [fderiv_const_mul h₂, fderiv_const_mul h₃, sub_apply, add_apply, smul_apply,
      smul_eq_mul, fderiv_comp_mul_apply_one, fderiv_comp_mul_apply_I]
    linear_combination (-fderiv ℝ (fun w ↦ η w 3) (u * z) 1 +
      fderiv ℝ (fun w ↦ η w 2) (u * z) I - x (u * z) 0 * η (u * z) 2 -
      x (u * z) 1 * η (u * z) 3) * hn

/-- Rotation commutes with the infinitesimal gauge action, rotating the phase. -/
theorem rotateField_gaugeDirection (u : Circle) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f : ℂ → ℝ) :
    rotateField u (gaugeDirection x f) =
      gaugeDirection (rotateField u x) (fun w ↦ f (u * w)) := by
  ext z i
  fin_cases i <;>
    simp [fderiv_comp_mul_apply, clm_apply_coe, clm_apply_coe_mul_I, add_comm]

/-- The logarithmic derivative of a rotated gauge is the pulled-back logarithmic derivative. -/
private theorem gaugeForm_comp_mul (u : Circle) (g : ℂ → Circle) (z v : ℂ) :
    gaugeForm (fun w ↦ g (u * w)) z v = gaugeForm g (u * z) (u * v) := by
  simp only [gaugeForm_apply]
  rw [fderiv_comp_mul_apply u (fun w ↦ (g w : ℂ))]

/-- Rotation commutes with the charge-one gauge action, rotating the gauge. -/
theorem rotateField_gaugeTransform (u : Circle) (g : ℂ → Circle)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateField u (gaugeTransform g x) =
      gaugeTransform (fun w ↦ g (u * w)) (rotateField u x) := by
  ext z i
  fin_cases i <;>
    simp [gaugeTransform_apply, gaugeForm_comp_mul, clm_apply_coe, clm_apply_coe_mul_I,
      -gaugeForm_apply] <;> ring

@[simp]
theorem rotateField_vacuumField (u : Circle) : rotateField u vacuumField = vacuumField := by
  ext z i
  fin_cases i <;> simp [vacuumField_apply]

/-- A rotation multiplies the limit of the end framing `α(z) (z / |z|)^(-m)` by `u^m`. -/
theorem tendsto_sectionValue_rotateField {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}
    (hx : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (u : Circle) :
    Tendsto (fun z ↦ sectionValue (rotateField u x) z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹)
      (cocompact ℂ) (𝓝 ((u : ℂ) ^ m)) := by
  have hrot : Tendsto (fun z : ℂ ↦ (u : ℂ) * z) (cocompact ℂ) (cocompact ℂ) :=
    Filter.tendsto_cocompact_mul_left₀ (Circle.coe_ne_zero u)
  have h := (hx.comp hrot).mul_const ((u : ℂ) ^ m)
  rw [one_mul] at h
  refine h.congr fun z ↦ ?_
  have hu : (u : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero u)
  simp only [Function.comp_apply, sectionValue_rotateField, norm_mul, Circle.norm_coe, one_mul,
    mul_div_assoc, mul_pow, mul_inv]
  field_simp

/-- **Line-frame law.** After a rotation by `u`, the constant gauge `u^(-m)` restores the end
framing of degree `m`. -/
theorem tendsto_sectionValue_gaugeTransform_rotateField {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {m : ℕ}
    (hx : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (u : Circle) :
    Tendsto (fun z ↦ sectionValue (gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x)) z *
      ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) := by
  have h := (tendsto_sectionValue_rotateField hx u).const_mul (((u⁻¹ ^ m : Circle)) : ℂ)
  have hu : (u : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Circle.coe_ne_zero u)
  simp only [Circle.coe_pow, Circle.coe_inv, inv_pow, inv_mul_cancel₀ hu] at h
  simpa only [sectionValue_gaugeTransform, Circle.coe_pow, Circle.coe_inv, inv_pow, mul_assoc]
    using h

end TauCeti.Vortex
