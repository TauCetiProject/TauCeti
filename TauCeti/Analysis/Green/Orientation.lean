/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Affine.Basic
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Geometry.Manifold.Boundary.Orientation
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The outward-first planar orientation and flux

Mathlib's complex orientation is the orientation of `(1,I)`. For a nonzero positive boundary
velocity `v`, the outward-first pair `(-I*v,v)` has this orientation. The flux form evaluates
to the real inner product with the rotated velocity, or with its unit normalization times speed.
The canonical complex-to-Euclidean isometry also identifies this normal with the actual outward
half-space convention, whose constrained coordinate is slot zero.
-/

public section

noncomputable section

open Complex
open scoped Manifold InnerProductSpace

namespace TauCeti.Green

/-- The determinant of the outward-first pair is the squared speed. -/
theorem det_outwardFirst (v : ℂ) : Complex.basisOneI.det ![-I * v, v] = ‖v‖ ^ 2 := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, neg_re, neg_im, I_mul_re, I_mul_im]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Every nonzero boundary velocity gives a positive outward-first determinant. -/
theorem det_outwardFirst_pos {v : ℂ} (hv : v ≠ 0) :
    0 < Complex.basisOneI.det ![-I * v, v] := by
  rw [det_outwardFirst]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

/-- The actual outward-first basis, obtained by complex multiplication from `(1,I)`. -/
def outwardFirstBasis (v : ℂ) (hv : v ≠ 0) : Module.Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.map
    ((LinearEquiv.smulOfNeZero ℂ ℂ (-I * v) (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hv) :
      ℂ ≃ₗ[ℂ] ℂ).restrictScalars ℝ)

/-- The vectors of the outward-first basis are the rotated velocity and the velocity. -/
@[simp]
theorem outwardFirstBasis_apply (v : ℂ) (hv : v ≠ 0) :
    ⇑(outwardFirstBasis v hv) = ![-I * v, v] := by
  ext i
  fin_cases i
  · simp [outwardFirstBasis, Complex.coe_basisOneI, smul_eq_mul]
  · simp [outwardFirstBasis, Complex.coe_basisOneI, smul_eq_mul]
    ring_nf
    simp

/-- The actual outward-first basis agrees with Mathlib's standard complex orientation. -/
@[simp]
theorem orientation_outwardFirstBasis (v : ℂ) (hv : v ≠ 0) :
    (outwardFirstBasis v hv).orientation = Complex.orientation := by
  -- Complex.orientation is the orientation of basisOneI; expose that basis for the determinant
  -- test.
  change (outwardFirstBasis v hv).orientation = Complex.basisOneI.orientation
  apply Eq.symm
  apply (Complex.basisOneI.orientation_eq_iff_det_pos _).mpr
  rw [outwardFirstBasis_apply]
  exact det_outwardFirst_pos hv

/-- The existing horizontal/vertical coordinate interchange reverses the actual complex
orientation. -/
theorem orientation_coordinateSwap :
    Orientation.map (Fin 2) Complex.coordinateSwapCLE.toLinearEquiv Complex.orientation =
      -Complex.orientation := by
  apply (Orientation.map_eq_neg_iff_det_neg _ _ (by simp)).mpr
  rw [Complex.det_coordinateSwapCLE]
  norm_num

/-- The planar flux form `X dy - Y dx` is the inner product with the outward rotated velocity. -/
theorem oneForm_flux_eq_inner (X Y : ℂ → ℝ) (z v : ℂ) :
    oneForm (fun z ↦ -Y z) X z v = ⟪(⟨X z, Y z⟩ : ℂ), -I * v⟫_ℝ := by
  simp only [oneForm_apply, Complex.inner, mul_re, mul_im, conj_re, conj_im,
    neg_re, neg_mul, I_re, I_im]
  ring

/-- Flux is inner product with the unit outward normal, multiplied by speed. -/
theorem oneForm_flux_eq_inner_unitNormal_mul_speed (X Y : ℂ → ℝ) (z : ℂ)
    {v : ℂ} (hv : v ≠ 0) :
    oneForm (fun z ↦ -Y z) X z v =
      ⟪(⟨X z, Y z⟩ : ℂ), (‖v‖⁻¹ : ℝ) • (-I * v)⟫_ℝ * ‖v‖ := by
  rw [oneForm_flux_eq_inner, real_inner_smul_right]
  field_simp [norm_ne_zero_iff.mpr hv]

/-- The raw flux integrand is the usual inner product with the rotated actual velocity. -/
theorem circulationFun_flux_eq_inner (X Y : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) :
    circulationFun (fun z ↦ -Y z) X γ t =
      ⟪(⟨X (γ t), Y (γ t)⟩ : ℂ), -I * deriv γ t⟫_ℝ := by
  rw [circulationFun_eq_oneForm, oneForm_flux_eq_inner]

/-- In the canonical Euclidean half-space chart, the rotated complex velocity is actually
outward exactly when its imaginary component is negative. This is Mathlib's slot-zero convention. -/
theorem isOutwardPointing_complex_halfSpace
    {x : EuclideanHalfSpace 2}
    (hx : x ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2)) (v : ℂ) :
    TauCeti.IsOutwardPointing (n := 1) x (Complex.orthonormalBasisOneI.repr (-I * v)) ↔
      v.im < 0 := by
  constructor
  · intro h
    have hh := h.coordinate_deriv_neg
    rw [mfderiv_extChartAt_self] at hh
    -- After the chart derivative is the identity, read the half-space test in coordinate zero.
    change (Complex.orthonormalBasisOneI.repr (-I * v)) 0 < 0 at hh
    simpa using hh
  · intro hv
    apply TauCeti.isOutwardPointing_iff.mpr
    refine ⟨hx, ?_⟩
    rw [mfderiv_extChartAt_self]
    -- After the chart derivative is the identity, read the half-space test in coordinate zero.
    change (Complex.orthonormalBasisOneI.repr (-I * v)) 0 < 0
    simpa using hv

/-- The positively oriented tangent to the standard complex half-space is `-I`, and its
outward rotated vector is the actual negative first Euclidean coordinate vector. -/
theorem outwardFirst_standard_halfSpace :
    Complex.orthonormalBasisOneI.repr (-I * (-I)) =
      -EuclideanSpace.single (𝕜 := ℝ) 0 1 := by
  ext i
  fin_cases i <;> simp

end TauCeti.Green
