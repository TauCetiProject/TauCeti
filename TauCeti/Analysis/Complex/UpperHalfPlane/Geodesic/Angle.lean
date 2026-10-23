/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv

/-!
# Velocities of geodesic lines and the angle between two geodesics

The velocity `velocity g t` of the geodesic line `geodesicLine g` at parameter `t` is the
derivative of `t ↦ (geodesicLine g t : ℂ)`; it is the derivative of the Möbius map of `g`
applied to the vertical velocity `I * exp t` (`hasDerivAt_coe_geodesicLine`, `velocity_mul`).
The angle `geodesicAngle g₁ g₂` between two geodesic lines starting at the same point is the
Euclidean angle between their velocities at parameter `0`. Since Möbius transformations act on
velocities by multiplication by the nonzero complex number `smulDeriv`, the angle is invariant
under the action (`geodesicAngle_mul`): this is the conformality of `PSL(2, ℝ)`.

Source: Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 10 (2010): the definition of
the angle between geodesics as the angle between tangent vectors, §2 p. 7; Theorem 5.1 and
Corollary 5.2 (Möbius transformations preserve the norm on tangent spaces, hence angles), p. 17–18.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups Real

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation dilation)

/-! ### Velocities -/

/-- The velocity of the geodesic line `geodesicLine g` at parameter `t`: the derivative of
`t ↦ (geodesicLine g t : ℂ)`, see `hasDerivAt_coe_geodesicLine`. -/
def velocity (g : PSL(2, ℝ)) (t : ℝ) : ℂ :=
  smulDeriv g (geodesicLine 1 t) * (Complex.I * Real.exp t)

-- The body of `velocity` is not `@[expose]`d, so downstream modules rewrite with this equation.
/-- `velocity` is the derivative of the Möbius map applied to the vertical velocity `I * exp t`. -/
theorem velocity_def (g : PSL(2, ℝ)) (t : ℝ) :
    velocity g t = smulDeriv g (geodesicLine 1 t) * (Complex.I * Real.exp t) := by rfl

/-- `velocity g t` is the derivative of the geodesic line `geodesicLine g`, as a curve in `ℂ`. -/
theorem hasDerivAt_coe_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (geodesicLine g s : ℂ)) (velocity g t) t := by
  -- the vertical axis `s ↦ I * exp s`, then the Möbius map of `g`
  have hax : HasDerivAt (fun s : ℝ ↦ ((geodesicLine 1 s : ℍ) : ℂ)) (Complex.I * Real.exp t) t := by
    have h : (fun s : ℝ ↦ ((geodesicLine 1 s : ℍ) : ℂ)) =
        fun s : ℝ ↦ Complex.I * (Real.exp s : ℂ) := by
      funext s
      rw [geodesicLine_one_apply, UpperHalfPlane.coe_mk]
      simp [Complex.ext_iff, Complex.exp_ofReal_re]
    rw [h]
    exact (Real.hasDerivAt_exp t).ofReal_comp.const_mul Complex.I
  have hfun : (fun s : ℝ ↦ (geodesicLine g s : ℂ)) =
      (fun w : ℂ ↦ ((g • ofComplex w : ℍ) : ℂ)) ∘ fun s : ℝ ↦ ((geodesicLine 1 s : ℍ) : ℂ) := by
    funext s
    simp only [Function.comp_apply, ofComplex_apply, smul_geodesicLine, mul_one]
  rw [hfun, velocity, mul_comm]
  exact (hasStrictDerivAt_coe_smul g (geodesicLine 1 t)).hasDerivAt.scomp t hax

/-- Geodesic lines are regular curves: their velocity never vanishes. -/
@[simp]
theorem velocity_ne_zero (g : PSL(2, ℝ)) (t : ℝ) : velocity g t ≠ 0 :=
  mul_ne_zero (smulDeriv_ne_zero g _)
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'))

/-- The velocity of the upward imaginary axis `t ↦ i exp t`. -/
@[simp]
theorem velocity_one (t : ℝ) : velocity 1 t = Complex.I * Real.exp t := by
  rw [velocity, smulDeriv_one, one_mul]

/-- The chain rule: translating a geodesic line by `h` multiplies its velocity by the derivative
of the Möbius map of `h` at the point. -/
theorem velocity_mul (h g : PSL(2, ℝ)) (t : ℝ) :
    velocity (h * g) t = smulDeriv h (geodesicLine g t) * velocity g t := by
  have hg : geodesicLine g t = g • geodesicLine 1 t := by rw [smul_geodesicLine, mul_one]
  rw [velocity, velocity, smulDeriv_mul, hg, mul_assoc]

/-- Reversing a geodesic line negates its velocity. -/
theorem velocity_mul_pslS (g : PSL(2, ℝ)) (t : ℝ) : velocity (g * pslS) t = -velocity g (-t) := by
  have h1 := hasDerivAt_coe_geodesicLine (g * pslS) t
  have h2 : HasDerivAt (fun s : ℝ ↦ (geodesicLine (g * pslS) s : ℂ)) (-velocity g (-t)) t := by
    have h : (fun s : ℝ ↦ (geodesicLine (g * pslS) s : ℂ)) =
        (fun s : ℝ ↦ (geodesicLine g s : ℂ)) ∘ Neg.neg := by
      funext s
      simp [geodesicLine_mul_pslS]
    rw [h]
    simpa using (hasDerivAt_coe_geodesicLine g (-t)).scomp t (hasDerivAt_neg t)
  exact h1.unique h2

/-- Shifting the parameter of a geodesic line shifts its velocity. -/
theorem velocity_mul_dilation (g : PSL(2, ℝ)) (s t : ℝ) :
    velocity (g * ↑(dilation s)) t = velocity g (s + t) := by
  have h1 := hasDerivAt_coe_geodesicLine (g * ↑(dilation s)) t
  have h2 : HasDerivAt (fun u : ℝ ↦ (geodesicLine (g * ↑(dilation s)) u : ℂ))
      (velocity g (s + t)) t := by
    have h : (fun u : ℝ ↦ (geodesicLine (g * ↑(dilation s)) u : ℂ)) =
        (fun u : ℝ ↦ (geodesicLine g u : ℂ)) ∘ (s + ·) := by
      funext u
      simp [geodesicLine_mul_dilation]
    rw [h]
    simpa using (hasDerivAt_coe_geodesicLine g (s + t)).scomp t ((hasDerivAt_id' t).const_add s)
  exact h1.unique h2

/-- The velocity of the rotated imaginary axis. -/
theorem velocity_rotation (θ t : ℝ) :
    velocity (↑(rotation θ)) t =
      Complex.I * Real.exp t / (Real.cos θ - Complex.I * Real.exp t * Real.sin θ) ^ 2 := by
  have h : ((UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t) : ℍ) : ℂ) =
      Complex.I * Real.exp t := by
    rw [UpperHalfPlane.coe_mk]
    simp [Complex.ext_iff, Complex.exp_ofReal_re]
  rw [velocity, Matrix.SpecialLinearGroup.smulDeriv_coe, geodesicLine_one_apply, h]
  simp only [denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.algebraMap_self_apply, Matrix.SpecialLinearGroup.coe_rotation, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [inv_mul_eq_div]
  congr 2
  push_cast
  ring

/-- At `I`, the rotation by `θ` turns the vertical velocity `I` by the angle `2θ`. -/
theorem velocity_rotation_zero (θ : ℝ) :
    velocity (↑(rotation θ)) 0 = Complex.I * Complex.exp (2 * θ * Complex.I) := by
  rw [velocity_rotation, Real.exp_zero, Complex.ofReal_one, mul_one]
  have h : (Real.cos θ - Complex.I * Real.sin θ : ℂ) = Complex.exp (-θ * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  rw [h, ← Complex.exp_nat_mul, div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  push_cast
  ring

/-! ### The angle between two geodesic lines -/

/-- The angle between the geodesic lines of `g₁` and `g₂` at their common starting point
`geodesicLine g₁ 0 = geodesicLine g₂ 0`: the Euclidean angle between their velocities. -/
def geodesicAngle (g₁ g₂ : PSL(2, ℝ)) : ℝ :=
  InnerProductGeometry.angle (velocity g₁ 0) (velocity g₂ 0)

-- The body of `geodesicAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- `geodesicAngle` is the Euclidean angle between the velocities at parameter `0`. -/
theorem geodesicAngle_def (g₁ g₂ : PSL(2, ℝ)) :
    geodesicAngle g₁ g₂ = InnerProductGeometry.angle (velocity g₁ 0) (velocity g₂ 0) := by rfl

/-- The angle between two geodesic lines is symmetric. -/
theorem geodesicAngle_comm (g₁ g₂ : PSL(2, ℝ)) : geodesicAngle g₁ g₂ = geodesicAngle g₂ g₁ :=
  InnerProductGeometry.angle_comm _ _

/-- Angles between geodesic lines are nonnegative. -/
theorem geodesicAngle_nonneg (g₁ g₂ : PSL(2, ℝ)) : 0 ≤ geodesicAngle g₁ g₂ :=
  InnerProductGeometry.angle_nonneg _ _

/-- Angles between geodesic lines are at most `π`. -/
theorem geodesicAngle_le_pi (g₁ g₂ : PSL(2, ℝ)) : geodesicAngle g₁ g₂ ≤ π :=
  InnerProductGeometry.angle_le_pi _ _

/-- The angle of a geodesic line with itself is `0`. -/
@[simp]
theorem geodesicAngle_self (g : PSL(2, ℝ)) : geodesicAngle g g = 0 :=
  InnerProductGeometry.angle_self (velocity_ne_zero g 0)

/-- The angle between two geodesic lines is the absolute value of the argument of the quotient
of their velocities. -/
theorem geodesicAngle_eq_abs_arg (g₁ g₂ : PSL(2, ℝ)) :
    geodesicAngle g₁ g₂ = |(velocity g₁ 0 / velocity g₂ 0).arg| :=
  Complex.angle_eq_abs_arg (velocity_ne_zero _ _) (velocity_ne_zero _ _)

/-- **Möbius transformations preserve angles**: the angle between two geodesic lines through a
common point is unchanged by translating both by `h`. -/
theorem geodesicAngle_mul (h g₁ g₂ : PSL(2, ℝ)) (h0 : geodesicLine g₁ 0 = geodesicLine g₂ 0) :
    geodesicAngle (h * g₁) (h * g₂) = geodesicAngle g₁ g₂ := by
  rw [geodesicAngle_eq_abs_arg, geodesicAngle_eq_abs_arg, velocity_mul, velocity_mul, h0,
    mul_div_mul_left _ _ (smulDeriv_ne_zero h _)]

/-- Reversing the first line replaces the angle by its supplement. -/
theorem geodesicAngle_mul_pslS_left (g₁ g₂ : PSL(2, ℝ)) :
    geodesicAngle (g₁ * pslS) g₂ = π - geodesicAngle g₁ g₂ := by
  rw [geodesicAngle, geodesicAngle, velocity_mul_pslS, neg_zero,
    InnerProductGeometry.angle_neg_left]

/-- The angle at `I` between the imaginary axis and its rotation by `θ` is `2 |θ|`, for
`|θ| ≤ π / 2`. -/
theorem geodesicAngle_one_rotation {θ : ℝ} (hθ : |θ| ≤ π / 2) :
    geodesicAngle 1 (↑(rotation θ)) = 2 * |θ| := by
  rw [geodesicAngle_eq_abs_arg, velocity_one, velocity_rotation_zero, Real.exp_zero,
    Complex.ofReal_one, mul_one, div_mul_cancel_left₀ Complex.I_ne_zero, ← Complex.exp_neg]
  have h : -(2 * (θ : ℂ) * Complex.I) = ((-(2 * θ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_mul_I]
  obtain ⟨h1, h2⟩ := abs_le.1 hθ
  rcases lt_or_eq_of_le h2 with h2 | h2
  · have harg := Complex.arg_mul_cos_add_sin_mul_I one_pos
      (θ := -(2 * θ)) ⟨by linarith, by linarith⟩
    rw [Complex.ofReal_one, one_mul] at harg
    rw [harg, abs_neg, abs_mul, abs_two]
  · subst h2
    have h3 : -(2 * (π / 2)) = -π := by ring
    rw [h3, abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
    simp [abs_of_pos Real.pi_pos]
    ring

/-- The angle at `I` between the rotations of the imaginary axis by `θ` and by `φ`. -/
theorem geodesicAngle_rotation_rotation {θ φ : ℝ} (h : |θ - φ| ≤ π / 2) :
    geodesicAngle (↑(rotation θ)) (↑(rotation φ)) = 2 * |θ - φ| := by
  have hθ : (↑(rotation θ) : PSL(2, ℝ)) = ↑(rotation φ) * ↑(rotation (θ - φ)) := by
    rw [← QuotientGroup.mk_mul, ← Matrix.SpecialLinearGroup.rotation_add, add_sub_cancel]
  calc geodesicAngle (↑(rotation θ)) (↑(rotation φ))
      = geodesicAngle (↑(rotation φ) * ↑(rotation (θ - φ))) (↑(rotation φ) * 1) := by
        rw [mul_one, ← hθ]
    _ = geodesicAngle (↑(rotation (θ - φ))) 1 :=
        geodesicAngle_mul _ _ _ (by
          rw [geodesicLine_zero, geodesicLine_zero, UpperHalfPlane.pslMk_smul, rotation_smul_I,
            one_smul])
    _ = 2 * |θ - φ| := by rw [geodesicAngle_comm, geodesicAngle_one_rotation h]

end TauCeti.UpperHalfPlane
