/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Basic

/-!
# Helicoids with arbitrary pitch

The parametrization `(u,v) ↦ (v cos u, v sin u, a u)` has first fundamental form
`(a²+v²)du²+dv²`. The differential is injective exactly when the pitch or the signed radial
parameter is nonzero. At zero pitch on the axis, the angular coordinate vector lies in its kernel.

Based on Yangyang Li's formalization of the arbitrary-pitch helicoid.

## References

* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Chapter 3.
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Helicoid

local notation "P" => ℝ × ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The helicoid of pitch `a`, obtained from planar polar coordinates by adding height `au`. -/
def parametrization (a : ℝ) (p : P) : E₃ :=
  SurfaceOfRevolution.parametrization id (fun _ ↦ 0) p +
    (a * p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The three Euclidean coordinates of the helicoid. -/
theorem parametrization_def (a : ℝ) (p : P) :
    parametrization a p =
      (p.2 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (p.2 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      (a * p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  simp only [parametrization, SurfaceOfRevolution.parametrization_def, id_eq,
    zero_smul, add_zero]

/-- The helicoid parametrization is smooth for every pitch. -/
theorem contDiff_parametrization (a : ℝ) : ContDiff ℝ ∞ (parametrization a) := by
  unfold parametrization
  exact (SurfaceOfRevolution.contDiff_parametrization contDiff_id contDiff_const).add
    ((contDiff_const.mul contDiff_fst).smul contDiff_const)

/-- The differential in the angular and signed radial parameter. -/
theorem fderiv_parametrization (a : ℝ) (p w : P) :
    fderiv ℝ (parametrization a) p w =
      (w.2 * Real.cos p.1 - p.2 * Real.sin p.1 * w.1) •
        EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (w.2 * Real.sin p.1 + p.2 * Real.cos p.1 * w.1) •
        EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      (a * w.1) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  have hb := (SurfaceOfRevolution.contDiff_parametrization
    (f := id) (g := fun _ ↦ 0) (n := ∞) contDiff_id contDiff_const).differentiable (by simp) p
  have hh := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul a).smul_const
    (EuclideanSpace.basisFun (Fin 3) ℝ 2)
  have h := (hb.hasFDerivAt.add hh).congr_of_eventuallyEq
    (f₁ := parametrization a) (.of_forall fun _ ↦ rfl)
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.coe_fst', smul_eq_mul,
    SurfaceOfRevolution.fderiv_parametrization differentiableAt_id (differentiableAt_const 0),
    deriv_id, deriv_const, id_eq, zero_mul, zero_smul, add_zero, one_mul]

/-- The first fundamental form of the helicoid is diagonal with coefficients `a²+v²,1`. -/
theorem inner_fderiv_parametrization (a : ℝ) (p w z : P) :
    inner ℝ (fderiv ℝ (parametrization a) p w) (fderiv ℝ (parametrization a) p z) =
      (a ^ 2 + p.2 ^ 2) * w.1 * z.1 + w.2 * z.2 := by
  rw [fderiv_parametrization, fderiv_parametrization]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num
  linear_combination (p.2 ^ 2 * w.1 * z.1 + w.2 * z.2) * Real.sin_sq_add_cos_sq p.1

/-- The metric is positive on a tangent vector exactly when its radial component is nonzero
or its angular component is nonzero at a regular parameter point. -/
theorem firstFundamentalForm_pos_iff (a : ℝ) (p w : P) :
    0 < (a ^ 2 + p.2 ^ 2) * w.1 ^ 2 + w.2 ^ 2 ↔
      ((a ≠ 0 ∨ p.2 ≠ 0) ∧ w.1 ≠ 0) ∨ w.2 ≠ 0 := by
  have h : 0 ≤ (a ^ 2 + p.2 ^ 2) * w.1 ^ 2 := by positivity
  rw [lt_iff_le_and_ne, and_iff_right (add_nonneg h (sq_nonneg _)), ne_comm, ne_eq,
    add_eq_zero_iff_of_nonneg h (sq_nonneg _), mul_eq_zero, sq_add_sq_eq_zero,
    sq_eq_zero_iff, sq_eq_zero_iff]
  tauto

/-- The helicoid differential is injective exactly where the pitch or signed radius is nonzero. -/
theorem injective_fderiv_parametrization_iff (a : ℝ) (p : P) :
    Function.Injective (fderiv ℝ (parametrization a) p) ↔ a ≠ 0 ∨ p.2 ≠ 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro hi
    by_contra! h
    have he := hi (1, 0) (by simp [fderiv_parametrization, h.1, h.2])
    simpa using congrArg Prod.fst he
  · intro h w hw
    by_contra hn
    have hpos := (firstFundamentalForm_pos_iff a p w).2 (by
      by_cases h₂ : w.2 = 0
      · exact Or.inl ⟨h, fun h₁ ↦ hn (Prod.ext h₁ h₂)⟩
      · exact Or.inr h₂)
    have hm := inner_fderiv_parametrization a p w w
    rw [hw, inner_zero_left] at hm
    nlinarith

end TauCeti.Helicoid
