/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Basic
import TauCeti.LinearAlgebra.Complex.Module

/-!
# The smooth plane vortex equation and its deformation complex

Write a field as `x = (b₁, b₂, p, q)`, representing the imaginary connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`. The coefficient metric
`|b|² + |δα|² / 4` is then the Euclidean metric on variations of `x`.
Fields take values in `EuclideanSpace ℝ (Fin 4)` and equation defects in
`EuclideanSpace ℝ (Fin 3)`, with these Euclidean coefficient norms.
`equation x` has three real components: the defect in
`*iF_a = (1 - |α|²) / 8` and the real and imaginary parts of `∂bar_a α`.
The convention is `∂bar_a α = (∇₁α + i ∇₂α) / 2`, with `∇ = d + a`.
`phaseGauge` realizes the action of `exp (i f)`; its composition law holds for
differentiable phases, and its first variation requires no phase regularity.
Covariance of the equation requires `C²` phases. Where the section does not vanish,
`∂bar_a α = 0` determines the connection from the section (`eq_of_forall_section_eq`).
Where `∂bar_a α = 0`, the covariant derivative is complex linear,
`d_a α (v) = v · d_a α (1)` (`covariantDerivative_eq_mul_of_equation_eq_zero`), and it controls
the gradient of `|α|²` through `(∂_s |α|²)² + (∂_t |α|²)² = 4 |α|² |d_a α (1)|²`
(`fderiv_normSq_apply_one_sq_add_apply_I_sq`), so `|d_a α (1)| ≤ |∇ |α|²|` where `|α|² ≥ 1 / 2`
(`norm_covariantDerivative_one_le_norm_fderiv_normSq`).

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
def equation (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[fderiv ℝ (fun w ↦ x w 0) z I - fderiv ℝ (fun w ↦ x w 1) z 1 +
      (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8,
    fderiv ℝ (fun w ↦ x w 2) z 1 - fderiv ℝ (fun w ↦ x w 3) z I -
      x z 0 * x z 3 - x z 1 * x z 2,
    fderiv ℝ (fun w ↦ x w 3) z 1 + fderiv ℝ (fun w ↦ x w 2) z I +
      x z 0 * x z 2 - x z 1 * x z 3]

/-- The actual section `α = 2(p + i q)` represented by a real vortex field. -/
def sectionValue (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℂ :=
  2 * ((x z 2 : ℂ) + (x z 3 : ℂ) * I)

/-- The section in the real field coordinates. -/
theorem sectionValue_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue x z = 2 * ((x z 2 : ℂ) + (x z 3 : ℂ) * I) := (rfl)

/-- The section of a difference of fields is the difference of their sections. -/
theorem sectionValue_sub (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (x - y) z = sectionValue x z - sectionValue y z := by
  simp only [sectionValue_apply, Pi.sub_apply, PiLp.sub_apply, ofReal_sub]
  ring

/-- The squared modulus `|α|² = 4 (p² + q²)` of the section in the real field coordinates. -/
theorem sq_norm_sectionValue (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ‖sectionValue x z‖ ^ 2 = 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
  rw [sectionValue_apply, ← normSq_eq_norm_sq, normSq_apply]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
  ring

/-- If a field tends to zero along a filter, then so does its section. -/
theorem tendsto_sectionValue_zero {l : Filter ℂ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Filter.Tendsto x l (nhds 0)) : Filter.Tendsto (sectionValue x) l (nhds 0) := by
  have h : Continuous fun v : EuclideanSpace ℝ (Fin 4) ↦ 2 * ((v 2 : ℂ) + (v 3 : ℂ) * I) := by
    fun_prop
  have := (h.tendsto 0).comp hx
  simp only [PiLp.zero_apply, ofReal_zero, zero_mul, add_zero, mul_zero] at this
  exact this.congr fun z ↦ (sectionValue_apply x z).symm

/-- The section with its real coordinates composed with `ofRealCLM`, the form used to compute its
regularity and derivative. -/
private theorem sectionValue_eq_ofRealCLM (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    sectionValue x = fun w ↦ 2 * ((ofRealCLM ∘ fun w ↦ x w 2) w +
      (ofRealCLM ∘ fun w ↦ x w 3) w * I) := by
  funext w
  simp only [sectionValue_apply, Function.comp_apply, ofRealCLM_apply]

/-- The squared modulus `|α|² = 4 (p² + q²)` is as regular as the real coordinates of the
section. -/
theorem contDiff_normSq {x : ℂ → EuclideanSpace ℝ (Fin 4)} {n : WithTop ℕ∞}
    (hp : ContDiff ℝ n (fun w ↦ x w 2)) (hq : ContDiff ℝ n (fun w ↦ x w 3)) :
    ContDiff ℝ n (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) :=
  contDiff_const.mul ((hp.pow 2).add (hq.pow 2))

/-- The derivative of the squared modulus `|α|² = 4 (p² + q²)` in terms of those of the real
coordinates of the section: `d |α|² (v) = 8 (p ∂_v p + q ∂_v q)`. -/
theorem fderiv_normSq_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (v : ℂ) :
    fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z v =
      8 * (x z 2 * fderiv ℝ (fun w ↦ x w 2) z v + x z 3 * fderiv ℝ (fun w ↦ x w 3) z v) := by
  have hd := ((hp.hasFDerivAt.pow 2).fun_add (hq.hasFDerivAt.pow 2)).const_mul (4 : ℝ)
  rw [hd.fderiv]
  simp only [smul_add, add_apply, smul_apply, smul_eq_mul, Nat.add_one_sub_one, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The section `α = 2 (p + i q)` is as regular as its real coordinates. -/
theorem contDiff_sectionValue {x : ℂ → EuclideanSpace ℝ (Fin 4)} {n : WithTop ℕ∞}
    (hp : ContDiff ℝ n (fun w ↦ x w 2)) (hq : ContDiff ℝ n (fun w ↦ x w 3)) :
    ContDiff ℝ n (sectionValue x) := by
  rw [sectionValue_eq_ofRealCLM]
  exact contDiff_const.mul ((ofRealCLM.contDiff.comp hp).add
    ((ofRealCLM.contDiff.comp hq).mul contDiff_const))

/-- The derivative of the section `α = 2 (p + i q)` in terms of those of its real coordinates. -/
theorem fderiv_sectionValue_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (v : ℂ) :
    fderiv ℝ (sectionValue x) z v =
      2 * ((fderiv ℝ (fun w ↦ x w 2) z v : ℂ) + (fderiv ℝ (fun w ↦ x w 3) z v : ℂ) * I) := by
  have hcp := ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt
  have hcq := ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt
  have h := (hcp.fun_add (hcq.mul_const I)).const_mul (2 : ℂ)
  rw [sectionValue_eq_ofRealCLM, h.fderiv]
  simp only [Fin.isValue, smul_add, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, smul_eq_mul]
  ring

/-- A field whose section has the degree-`m` end framing `α(z) (z / |z|)^(-m) → 1` has squared
modulus `|α|² = 4 (p² + q²)` tending to one at infinity. -/
theorem tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hframe : Filter.Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹)
      (Filter.cocompact ℂ) (nhds 1)) :
    Filter.Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (Filter.cocompact ℂ) (nhds 1) := by
  have h := hframe.norm.pow 2
  rw [norm_one, one_pow] at h
  refine h.congr' ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
  rw [norm_mul, norm_inv, norm_pow, norm_div]
  simp only [norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz), one_pow, inv_one, mul_one]
  exact sq_norm_sectionValue x z

/-- The covariant derivative `d_a α`, with the charge-one connection `a = i(b₁ ds + b₂ dt)`.
The argument `v` is an actual real tangent vector to the plane. -/
def covariantDerivative (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) : ℂ :=
  fderiv ℝ (sectionValue x) z v +
    I * ((x z 0 * v.re + x z 1 * v.im : ℝ) : ℂ) * sectionValue x z

/-- Coordinate evaluation of the covariant derivative of the actual section. -/
theorem covariantDerivative_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) :
    covariantDerivative x z v = fderiv ℝ (sectionValue x) z v +
      I * ((x z 0 * v.re + x z 1 * v.im : ℝ) : ℂ) * sectionValue x z := (rfl)

/-- The covariant derivative is real-linear in the tangent vector, so it is determined by its
values on the coordinate frame `(1, i)`. -/
theorem covariantDerivative_eq_re_mul_add_im_mul (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z v : ℂ) :
    covariantDerivative x z v =
      v.re * covariantDerivative x z 1 + v.im * covariantDerivative x z I := by
  have h := LinearMap.apply_eq_re_smul_one_add_im_smul_I
    (fderiv ℝ (sectionValue x) z : ℂ →ₗ[ℝ] ℂ) v
  simp only [ContinuousLinearMap.coe_coe, Complex.real_smul] at h
  simp only [covariantDerivative_apply, h, one_re, one_im, I_re, I_im]
  push_cast
  ring

/-- The real curvature coefficient: `F_a = i curvature ds ∧ dt`. -/
def curvature (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I

/-- The curvature coefficient in the oriented coordinate frame `(1, i)`. -/
theorem curvature_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    curvature x z = fderiv ℝ (fun w ↦ x w 1) z 1 -
      fderiv ℝ (fun w ↦ x w 0) z I := (rfl)

/-- The physical energy density `|F_a|² + |d_a α|² + (1 - |α|²)²` in the Euclidean plane.
No finite-energy condition is built into a field's type. -/
def energyDensity (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ℝ :=
  curvature x z ^ 2 + ‖covariantDerivative x z 1‖ ^ 2 +
    ‖covariantDerivative x z I‖ ^ 2 + (1 - ‖sectionValue x z‖ ^ 2) ^ 2

/-- The physical energy density as a sum of curvature, kinetic and potential terms. -/
theorem energyDensity_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    energyDensity x z = curvature x z ^ 2 + ‖covariantDerivative x z 1‖ ^ 2 +
      ‖covariantDerivative x z I‖ ^ 2 + (1 - ‖sectionValue x z‖ ^ 2) ^ 2 := (rfl)

/-- The first-order linearization of `equation` at the field `x`, applied to a variation `y`.
The coordinates of `y` represent `δa = i (y₀ ds + y₁ dt)` and `δα = 2 (y₂ + i y₃)`. -/
def linearizedEquation (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1 +
      x z 2 * y z 2 + x z 3 * y z 3,
    fderiv ℝ (fun w ↦ y w 2) z 1 - fderiv ℝ (fun w ↦ y w 3) z I -
      x z 0 * y z 3 - y z 0 * x z 3 - x z 1 * y z 2 - y z 1 * x z 2,
    fderiv ℝ (fun w ↦ y w 3) z 1 + fderiv ℝ (fun w ↦ y w 2) z I +
      x z 0 * y z 2 + y z 0 * x z 2 - x z 1 * y z 3 - y z 1 * x z 3]

/-- The quadratic remainder of the vortex equation, independent of the base field. -/
def quadraticTerm (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(y z 2 ^ 2 + y z 3 ^ 2) / 2,
    -y z 0 * y z 3 - y z 1 * y z 2,
    y z 0 * y z 2 - y z 1 * y z 3]

/-- The infinitesimal charge-one gauge action of `i f`: `δa = -i df`, `δα = i f α`. -/
def gaugeDirection (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ f z 1, -fderiv ℝ f z I, -f z * x z 3, f z * x z 2]

/-- The gauge transformation with phase `exp (i f)`, in real field coordinates.
Its connection part is `a - i df` and its section part is `exp (i f) α`. -/
def phaseGauge (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[x z 0 - fderiv ℝ f z 1, x z 1 - fderiv ℝ f z I,
    Real.cos (f z) * x z 2 - Real.sin (f z) * x z 3,
    Real.sin (f z) * x z 2 + Real.cos (f z) * x z 3]

/-- The normalized vacuum field, with zero connection and section `α = 1`. -/
def vacuumField (_ : ℂ) : EuclideanSpace ℝ (Fin 4) := !₂[0, 0, 1 / 2, 0]

/-- The curvature defect of the vortex equation. -/
@[simp]
theorem equation_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    equation x z 0 = fderiv ℝ (fun w ↦ x w 0) z I - fderiv ℝ (fun w ↦ x w 1) z 1 +
      (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8 := by
  rfl

/-- The real complex-equation defect. -/
@[simp]
theorem equation_apply_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    equation x z 1 = fderiv ℝ (fun w ↦ x w 2) z 1 - fderiv ℝ (fun w ↦ x w 3) z I -
      x z 0 * x z 3 - x z 1 * x z 2 := by
  rfl

/-- The imaginary complex-equation defect. -/
@[simp]
theorem equation_apply_two (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    equation x z 2 = fderiv ℝ (fun w ↦ x w 3) z 1 + fderiv ℝ (fun w ↦ x w 2) z I +
      x z 0 * x z 2 - x z 1 * x z 3 := by
  rfl

/-- At a solution of the vortex equation the curvature coefficient `∂₁ b₂ - ∂₂ b₁` of
`F_a = i (∂₁ b₂ - ∂₂ b₁) ds ∧ dt` is `-(1 - |α|²) / 8`. -/
theorem curvature_eq_of_equation_eq_zero {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hsol : equation x z = 0) :
    fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I =
      -((1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 8) := by
  have h := congrArg (· 0) hsol
  simp only [equation_apply_zero, PiLp.zero_apply] at h
  linarith

/-- Where the holomorphicity rows `∂bar_a α = 0` hold, the covariant derivative is complex linear
in the tangent vector: `d_a α (v) = v · d_a α (1)`. -/
theorem covariantDerivative_eq_mul_of_equation_eq_zero {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) (v : ℂ) :
    covariantDerivative x z v = v * covariantDerivative x z 1 := by
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  have hI : covariantDerivative x z I = I * covariantDerivative x z 1 := by
    apply Complex.ext <;>
      simp [covariantDerivative_apply, fderiv_sectionValue_apply hp hq, sectionValue_apply] <;>
      linarith
  rw [covariantDerivative_eq_re_mul_add_im_mul, hI]
  calc (v.re : ℂ) * covariantDerivative x z 1 + v.im * (I * covariantDerivative x z 1) =
      (v.re + v.im * I) * covariantDerivative x z 1 := by ring
    _ = v * covariantDerivative x z 1 := by rw [re_add_im]

/-- The squared modulus of `d_a α (1) = 2 ((∂_s p - b₁ q) + i (∂_s q + b₁ p))`. -/
theorem sq_norm_covariantDerivative_one {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) :
    ‖covariantDerivative x z 1‖ ^ 2 =
      4 * ((fderiv ℝ (fun w ↦ x w 2) z 1 - x z 0 * x z 3) ^ 2 +
        (fderiv ℝ (fun w ↦ x w 3) z 1 + x z 0 * x z 2) ^ 2) := by
  rw [covariantDerivative_apply, fderiv_sectionValue_apply hp hq, sectionValue_apply,
    Complex.sq_norm, Complex.normSq_apply]
  simp only [one_re, one_im, mul_one, mul_zero, add_zero, mul_re, mul_im, add_re, add_im,
    ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
  ring

/-- Where the holomorphicity rows `∂bar_a α = 0` hold, the gradient of `|α|²` and the covariant
derivative of `α` satisfy `(∂_s |α|²)² + (∂_t |α|²)² = 4 |α|² |d_a α (1)|²`. -/
theorem fderiv_normSq_apply_one_sq_add_apply_I_sq {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z 1 ^ 2 +
        fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z I ^ 2 =
      4 * (4 * (x z 2 ^ 2 + x z 3 ^ 2)) * ‖covariantDerivative x z 1‖ ^ 2 := by
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  rw [fderiv_normSq_apply hp hq, fderiv_normSq_apply hp hq, sq_norm_covariantDerivative_one hp hq]
  -- With `A + i B = d_a α (1) / 2`, the rows give `p ∂_t p + q ∂_t q = q A - p B`, while
  -- `p ∂_s p + q ∂_s q = p A + q B`.
  linear_combination (64 * (x z 2 * fderiv ℝ (fun w ↦ x w 2) z I +
      x z 3 * fderiv ℝ (fun w ↦ x w 3) z I) +
    64 * (x z 3 * (fderiv ℝ (fun w ↦ x w 2) z 1 - x z 0 * x z 3) -
      x z 2 * (fderiv ℝ (fun w ↦ x w 3) z 1 + x z 0 * x z 2))) *
    (x z 2 * h₂ - x z 3 * h₁)

/-- Where the holomorphicity rows `∂bar_a α = 0` hold and `|α|² ≥ 1 / 2`, the covariant derivative
is bounded by the gradient of `|α|²`: `|d_a α (1)| ≤ |∇ |α|²|`. -/
theorem norm_covariantDerivative_one_le_norm_fderiv_normSq {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (h₁ : equation x z 1 = 0)
    (h₂ : equation x z 2 = 0) (hhalf : 1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ‖covariantDerivative x z 1‖ ≤ ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ := by
  set f := fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z
  have hid := fderiv_normSq_apply_one_sq_add_apply_I_sq hp hq h₁ h₂
  -- Both coordinate derivatives are bounded by the operator norm.
  have hf₁ : f 1 ^ 2 ≤ ‖f‖ ^ 2 := by
    have h := f.le_opNorm 1
    rw [norm_one, mul_one, Real.norm_eq_abs] at h
    exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  have hfI : f I ^ 2 ≤ ‖f‖ ^ 2 := by
    have h := f.le_opNorm I
    rw [norm_I, mul_one, Real.norm_eq_abs] at h
    exact sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  -- So `2 |d_a α (1)|² ≤ 4 |α|² |d_a α (1)|² ≤ 2 |∇ |α|²|²`.
  have hsq : ‖covariantDerivative x z 1‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    nlinarith [sq_nonneg ‖covariantDerivative x z 1‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- The curvature component of the linearized equation. -/
@[simp]
theorem linearizedEquation_apply_zero (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    linearizedEquation x y z 0 =
      fderiv ℝ (fun w ↦ y w 0) z I - fderiv ℝ (fun w ↦ y w 1) z 1 +
        x z 2 * y z 2 + x z 3 * y z 3 := by
  rfl

/-- The real complex component of the linearized equation. -/
@[simp]
theorem linearizedEquation_apply_one (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    linearizedEquation x y z 1 =
      fderiv ℝ (fun w ↦ y w 2) z 1 - fderiv ℝ (fun w ↦ y w 3) z I -
        x z 0 * y z 3 - y z 0 * x z 3 - x z 1 * y z 2 - y z 1 * x z 2 := by
  rfl

/-- The imaginary complex component of the linearized equation. -/
@[simp]
theorem linearizedEquation_apply_two (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    linearizedEquation x y z 2 =
      fderiv ℝ (fun w ↦ y w 3) z 1 + fderiv ℝ (fun w ↦ y w 2) z I +
        x z 0 * y z 2 + y z 0 * x z 2 - x z 1 * y z 3 - y z 1 * x z 3 := by
  rfl

/-- The curvature component of the quadratic remainder. -/
@[simp]
theorem quadraticTerm_apply_zero (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    quadraticTerm y z 0 = (y z 2 ^ 2 + y z 3 ^ 2) / 2 := by
  rfl

/-- The real complex component of the quadratic remainder. -/
@[simp]
theorem quadraticTerm_apply_one (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    quadraticTerm y z 1 = -y z 0 * y z 3 - y z 1 * y z 2 := by
  rfl

/-- The imaginary complex component of the quadratic remainder. -/
@[simp]
theorem quadraticTerm_apply_two (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    quadraticTerm y z 2 = y z 0 * y z 2 - y z 1 * y z 3 := by
  rfl

/-- The first connection component of the infinitesimal gauge action. -/
@[simp]
theorem gaugeDirection_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    gaugeDirection x f z 0 = -fderiv ℝ f z 1 := by
  rfl

/-- The second connection component of the infinitesimal gauge action. -/
@[simp]
theorem gaugeDirection_apply_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    gaugeDirection x f z 1 = -fderiv ℝ f z I := by
  rfl

/-- The real section component of the infinitesimal gauge action. -/
@[simp]
theorem gaugeDirection_apply_two (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    gaugeDirection x f z 2 = -f z * x z 3 := by
  rfl

/-- The imaginary section component of the infinitesimal gauge action. -/
@[simp]
theorem gaugeDirection_apply_three (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    gaugeDirection x f z 3 = f z * x z 2 := by
  rfl

/-- The first connection component of a phase gauge transformation. -/
@[simp]
theorem phaseGauge_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    phaseGauge x f z 0 = x z 0 - fderiv ℝ f z 1 := by
  rfl

/-- The second connection component of a phase gauge transformation. -/
@[simp]
theorem phaseGauge_apply_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    phaseGauge x f z 1 = x z 1 - fderiv ℝ f z I := by
  rfl

/-- The real section component of a phase gauge transformation. -/
@[simp]
theorem phaseGauge_apply_two (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    phaseGauge x f z 2 = Real.cos (f z) * x z 2 - Real.sin (f z) * x z 3 := by
  rfl

/-- The imaginary section component of a phase gauge transformation. -/
@[simp]
theorem phaseGauge_apply_three (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ) :
    phaseGauge x f z 3 = Real.sin (f z) * x z 2 + Real.cos (f z) * x z 3 := by
  rfl

/-- The linearized equation preserves addition of variations differentiable at the point. -/
theorem linearizedEquation_add (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {y v : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hy : ∀ i, DifferentiableAt ℝ (fun w ↦ y w i) z)
    (hv : ∀ i, DifferentiableAt ℝ (fun w ↦ v w i) z) :
    linearizedEquation x (y + v) z = linearizedEquation x y z + linearizedEquation x v z := by
  ext i
  fin_cases i <;>
    simp [fderiv_fun_add, hy, hv] <;> ring

/-- The linearized equation commutes with real scalar multiplication of variations. -/
theorem linearizedEquation_smul (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (t : ℝ) (z : ℂ) :
    linearizedEquation x (t • y) z = t • linearizedEquation x y z := by
  have hd (i : Fin 4) : fderiv ℝ (fun w ↦ t * y w i) z =
      t • fderiv ℝ (fun w ↦ y w i) z :=
    congrFun (fderiv_const_smul_field t) z
  ext i
  fin_cases i <;> simp [hd] <;> ring

/-- The zero variation has zero linearized equation. -/
@[simp]
theorem linearizedEquation_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    linearizedEquation x 0 = 0 := by
  ext z i
  fin_cases i <;> simp

/-- The infinitesimal gauge action preserves addition of phases differentiable at the point. -/
theorem gaugeDirection_add (x : ℂ → EuclideanSpace ℝ (Fin 4)) {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gaugeDirection x (f + g) z = gaugeDirection x f z + gaugeDirection x g z := by
  ext i
  fin_cases i <;> simp [fderiv_add hf hg] <;> ring

/-- The infinitesimal gauge action commutes with real scalar multiplication of phases. -/
theorem gaugeDirection_smul (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (t : ℝ) (z : ℂ) :
    gaugeDirection x (t • f) z = t • gaugeDirection x f z := by
  ext i
  fin_cases i <;> simp [fderiv_const_smul_field] <;> ring

/-- The zero phase has zero infinitesimal gauge action. -/
@[simp]
theorem gaugeDirection_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) : gaugeDirection x 0 = 0 := by
  ext z i
  fin_cases i <;> simp [fderiv_zero]

/-- The coordinates of the vacuum field. -/
@[simp]
theorem vacuumField_apply (z : ℂ) : vacuumField z = !₂[0, 0, 1 / 2, 0] := by
  rfl

/-- The zero phase acts as the identity. -/
@[simp]
theorem phaseGauge_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) : phaseGauge x 0 = x := by
  ext z i
  fin_cases i <;> simp [fderiv_zero]

/-- Composition of phase gauges corresponds to addition of their real phases. -/
theorem phaseGauge_phaseGauge (x : ℂ → EuclideanSpace ℝ (Fin 4)) {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    phaseGauge (phaseGauge x f) g z = phaseGauge x (f + g) z := by
  ext i
  fin_cases i <;>
    simp [fderiv_add hf hg, Real.cos_add, Real.sin_add] <;> ring

/-- The infinitesimal charge-one action is the derivative of the actual phase gauge action. -/
theorem hasDerivAt_phaseGauge (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) (z : ℂ)
    (i : Fin 4) :
    HasDerivAt (fun t : ℝ ↦ phaseGauge x (t • f) z i) (gaugeDirection x f z i) 0 := by
  have hd : ∀ t : ℝ, fderiv ℝ (t • f) z = t • fderiv ℝ f z :=
    fun t ↦ congrFun (fderiv_const_smul_field t) z
  have ht := (hasDerivAt_id (0 : ℝ)).mul_const (f z)
  fin_cases i
  · simpa [hd, Pi.sub_def] using (hasDerivAt_const (0 : ℝ) (x z 0)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (fderiv ℝ f z 1))
  · simpa [hd, Pi.sub_def] using (hasDerivAt_const (0 : ℝ) (x z 1)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (fderiv ℝ f z I))
  · simpa [Pi.sub_def] using (ht.cos.mul_const (x z 2)).sub (ht.sin.mul_const (x z 3))
  · simpa [Pi.add_def] using (ht.sin.mul_const (x z 2)).add (ht.cos.mul_const (x z 3))

/-- The curvature defect is gauge invariant, and the complex defect transforms by the
same unit phase as the section. This statement includes non-solution fields. -/
theorem equation_phaseGauge {x : ℂ → EuclideanSpace ℝ (Fin 4)} {f : ℂ → ℝ} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) (hf : ContDiffAt ℝ 2 f z) :
    equation (phaseGauge x f) z =
      !₂[equation x z 0,
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
    simp [fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul,
      hx, hpartial, hf'.cos, hf'.sin, fderiv_cos hf', fderiv_sin hf',
      fderiv_clm_apply hdf (differentiableAt_const _)]
  · linear_combination (x z 2 ^ 2 + x z 3 ^ 2) / 2 * htrig + hcomm
  · ring
  · ring

/-- A phase gauge transformation preserves the solution condition in both directions. -/
@[simp]
theorem equation_phaseGauge_eq_zero_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {f : ℂ → ℝ} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z) (hf : ContDiffAt ℝ 2 f z) :
    equation (phaseGauge x f) z = 0 ↔ equation x z = 0 := by
  rw [equation_phaseGauge hx hf]
  refine ⟨fun h ↦ ?_, fun h ↦ by ext i; fin_cases i <;> simp [h]⟩
  have h₀ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 0) h
  have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  have h₂ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply] at h₀ h₁ h₂
  have htrig := Real.sin_sq_add_cos_sq (f z)
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  all_goals simp only [PiLp.zero_apply]
  · exact h₀
  · linear_combination Real.cos (f z) * h₁ + Real.sin (f z) * h₂ - equation x z 1 * htrig
  · linear_combination -Real.sin (f z) * h₁ + Real.cos (f z) * h₂ - equation x z 2 * htrig

/-- **The section of a vortex determines its connection where it does not vanish.** If two fields
satisfy the holomorphicity equation `∂bar_a α = 0`, have continuous connection components and the
same section, and the zero set of that section has empty interior, then the fields are equal. -/
theorem eq_of_forall_section_eq {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : Continuous fun z ↦ x z 0) (hx₁ : Continuous fun z ↦ x z 1)
    (hy₀ : Continuous fun z ↦ y z 0) (hy₁ : Continuous fun z ↦ y z 1)
    (hxsol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hysol : ∀ z, equation y z 1 = 0 ∧ equation y z 2 = 0)
    (h₂ : ∀ z, x z 2 = y z 2) (h₃ : ∀ z, x z 3 = y z 3)
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) : x = y := by
  -- Off the zeros of the section, the two holomorphicity equations are a nondegenerate linear
  -- system for the difference of the connections.
  have hb (z : ℂ) (hz : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0) : x z 0 = y z 0 ∧ x z 1 = y z 1 := by
    obtain ⟨hx₁, hx₂⟩ := hxsol z
    obtain ⟨hy₁, hy₂⟩ := hysol z
    simp only [equation_apply_one, equation_apply_two, h₂, h₃] at hx₁ hx₂ hy₁ hy₂
    have e₀ : (x z 0 - y z 0) * (y z 2 ^ 2 + y z 3 ^ 2) = 0 := by
      linear_combination -y z 3 * (hx₁ - hy₁) + y z 2 * (hx₂ - hy₂)
    have e₁ : (x z 1 - y z 1) * (y z 2 ^ 2 + y z 3 ^ 2) = 0 := by
      linear_combination -y z 2 * (hx₁ - hy₁) - y z 3 * (hx₂ - hy₂)
    exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 e₀).resolve_right hz),
      sub_eq_zero.1 ((mul_eq_zero.1 e₁).resolve_right hz)⟩
  have h₀ := hx₀.ext_on hdense hy₀ fun z hz ↦ (hb z hz).1
  have h₁ := hx₁.ext_on hdense hy₁ fun z hz ↦ (hb z hz).2
  ext z i
  fin_cases i
  exacts [congrFun h₀ z, congrFun h₁ z, h₂ z, h₃ z]

/-- Exact quadratic expansion of the vortex equation, with no higher remainder. -/
theorem equation_add_smul {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z)
    (hy : ∀ i, DifferentiableAt ℝ (fun w ↦ y w i) z) (t : ℝ) :
    equation (x + t • y) z =
      equation x z + t • linearizedEquation x y z + t ^ 2 • quadraticTerm y z := by
  ext i
  fin_cases i <;>
    simp [fderiv_fun_add, fderiv_const_mul, hx, hy] <;> ring

/-- The differential expression `linearizedEquation` is the first variation along every
differentiable field direction, evaluated at any fixed point of the plane. -/
theorem hasDerivAt_equation {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : ∀ i, DifferentiableAt ℝ (fun w ↦ x w i) z)
    (hy : ∀ i, DifferentiableAt ℝ (fun w ↦ y w i) z) :
    HasDerivAt (fun t : ℝ ↦ equation (x + t • y) z) (linearizedEquation x y z) 0 := by
  simp_rw [equation_add_smul hx hy]
  convert ((hasDerivAt_const (0 : ℝ) (equation x z)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (linearizedEquation x y z))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (quadraticTerm y z)) using 1 <;> simp [Pi.add_def]

/-- At every field (off-shell), the composition of the linearized equation with the
infinitesimal gauge action is the infinitesimal rotation of the complex equation defect. -/
theorem linearizedEquation_gaugeDirection {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {f : ℂ → ℝ} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (hf : ContDiffAt ℝ 2 f z) :
    linearizedEquation x (gaugeDirection x f) z =
      !₂[0, -f z * equation x z 2, f z * equation x z 1] := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomm := (hf.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  have hf' := hf.differentiableAt (by norm_num)
  ext i
  fin_cases i <;>
    simp [fderiv_fun_neg, fderiv_fun_mul, hf', hp, hq,
      fderiv_clm_apply hdf (differentiableAt_const _)]
  · linear_combination hcomm
  · ring
  · ring

/-- At a solution, the infinitesimal gauge action followed by the linearized equation is zero.
This is the differential-complex identity `d₁ d₀ = 0`. -/
theorem linearizedEquation_gaugeDirection_eq_zero {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {f : ℂ → ℝ} {z : ℂ}
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
  fin_cases i <;> norm_num [vacuumField, fderiv_const_apply]

open scoped SchwartzMap LineDeriv

/-- The smooth linearization at the vacuum is exactly the curvature and two complex rows
of the existing gauge-fixed Schwartz operator. -/
theorem linearizedEquation_vacuumField (y : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (z : ℂ) :
    linearizedEquation vacuumField y z =
      !₂[vacuumOperator y z 1, vacuumOperator y z 2, vacuumOperator y z 3] := by
  have hd (i : Fin 4) (v : ℂ) :
      fderiv ℝ (fun w ↦ y w i) z v = (∂_{v} y) z i := by
    have hp := ((EuclideanSpace.proj i).hasFDerivAt.comp z
      y.differentiableAt.hasFDerivAt).fderiv
    simpa [Function.comp_def, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) hp
  ext i
  fin_cases i <;> simp [vacuumField, hd] <;> ring

end TauCeti.Vortex
