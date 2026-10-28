/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Period-one cylindrical coordinates on the punctured disc

The punctured unit disc is a half-cylinder, with longitudinal coordinate `s > 0` and
angular coordinate in `ℝ / ℤ`. The coordinate is `exp (-2π(s + it))` on real lifts.
The construction uses Mathlib's polar homeomorphism `homeomorphUnitSphereProd` and
`AddCircle.homeomorphCircle`, so the angular coordinate has period one.
-/

public noncomputable section

open Set

namespace TauCeti.Complex.UnitDisc

/-- Exponential radial coordinate: positive cylinder length corresponds to radius in `(0,1)`.
The normalization makes the angular period equal to one. -/
def cylinderRadius : Ioi (0 : ℝ) ≃ₜ Ioo (0 : ℝ) 1 where
  toFun s := ⟨Real.exp (-(2 * Real.pi) * s), Real.exp_pos _,
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) s.2)⟩
  invFun r := ⟨-Real.log r / (2 * Real.pi),
    div_pos (neg_pos.mpr ((Real.log_neg_iff r.2.1).mpr r.2.2)) (by positivity)⟩
  left_inv s := by
    ext
    simp only [Real.log_exp]
    field_simp
  right_inv r := by
    ext
    have h : -(2 * Real.pi) * (-Real.log r / (2 * Real.pi)) = Real.log r := by
      field_simp
    dsimp only
    rw [h, Real.exp_log r.2.1]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((Real.continuousOn_log.comp_continuous continuous_subtype_val
      (fun r ↦ r.2.1.ne')).neg).div_const _

/-- The radial coordinate is the normalized decreasing exponential. -/
@[simp] theorem cylinderRadius_apply (s : Ioi (0 : ℝ)) :
    (cylinderRadius s : ℝ) = Real.exp (-(2 * Real.pi) * s) := (rfl)

/-- The inverse radial coordinate is normalized negative logarithmic radius. -/
@[simp] theorem cylinderRadius_symm_apply (r : Ioo (0 : ℝ) 1) :
    (cylinderRadius.symm r : ℝ) = -Real.log r / (2 * Real.pi) := (rfl)

/-- Polar coordinates on the punctured unit disc, with radius constrained to `(0,1)`.
This is the restriction of Mathlib's `homeomorphUnitSphereProd`. -/
def puncturedPolar : ↥(Metric.ball (0 : ℂ) 1 \ {0}) ≃ₜ Circle × Ioo (0 : ℝ) 1 where
  toFun z :=
    let p := homeomorphUnitSphereProd ℂ ⟨z, z.2.2⟩
    (p.1, ⟨p.2, p.2.2, by
      dsimp only [p]
      simpa only [homeomorphUnitSphereProd_apply_snd_coe, Metric.mem_ball,
        dist_zero_right] using z.2.1⟩)
  invFun p := ⟨(homeomorphUnitSphereProd ℂ).symm (p.1, ⟨p.2, p.2.2.1⟩), by
    constructor
    · simp [homeomorphUnitSphereProd_symm_apply_coe,
        abs_of_pos p.2.2.1, Circle.norm_coe, p.2.2.2]
    · exact ((homeomorphUnitSphereProd ℂ).symm (p.1, ⟨p.2, p.2.2.1⟩)).2⟩
  left_inv z := by
    dsimp only
    apply Subtype.ext
    exact congrArg (fun x : ({0}ᶜ : Set ℂ) ↦ (x : ℂ))
      ((homeomorphUnitSphereProd ℂ).symm_apply_apply ⟨z, z.2.2⟩)
  right_inv p := by
    dsimp only
    have h := (homeomorphUnitSphereProd ℂ).apply_symm_apply (p.1, ⟨p.2, p.2.2.1⟩)
    apply Prod.ext
    · exact congrArg (fun x : Circle × Ioi (0 : ℝ) ↦ x.1) h
    · apply Subtype.ext
      exact congrArg (fun x : Circle × Ioi (0 : ℝ) ↦ (x.2 : ℝ)) h
  continuous_toFun := by
    apply Continuous.prodMk
    · exact ((homeomorphUnitSphereProd ℂ).continuous.comp
        (continuous_subtype_val.subtype_mk _)).fst
    · apply Continuous.subtype_mk
      simpa only [homeomorphUnitSphereProd_apply_snd_coe] using
        (continuous_subtype_val.norm :
          Continuous (fun z : ↥(Metric.ball (0 : ℂ) 1 \ {0}) ↦ ‖(z : ℂ)‖))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp ((homeomorphUnitSphereProd ℂ).symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.subtype_val.subtype_mk _)))

/-- The direction of the punctured polar coordinate is the normalized complex vector. -/
@[simp] theorem puncturedPolar_apply_fst (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    ((puncturedPolar z).1 : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) :=
  homeomorphUnitSphereProd_apply_fst_coe _ _

/-- The radial component of the punctured polar coordinate is its norm. -/
@[simp] theorem puncturedPolar_apply_snd (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    ((puncturedPolar z).2 : ℝ) = ‖(z : ℂ)‖ :=
  homeomorphUnitSphereProd_apply_snd_coe _ _

/-- The inverse polar map multiplies the unit direction by its positive radius. -/
@[simp] theorem puncturedPolar_symm_apply (p : Circle × Ioo (0 : ℝ) 1) :
    (puncturedPolar.symm p : ℂ) = (p.2 : ℝ) • (p.1 : ℂ) :=
  homeomorphUnitSphereProd_symm_apply_coe _ _

/-- The period-one cylindrical parameterization of the punctured unit disc.
Its real lift is `exp (-2π(s + it))`. -/
def puncturedCylinder : Ioi (0 : ℝ) × AddCircle (1 : ℝ) ≃ₜ
    ↥(Metric.ball (0 : ℂ) 1 \ {0}) :=
  ((cylinderRadius.prodCongr
    ((Homeomorph.neg _).trans (AddCircle.homeomorphCircle one_ne_zero))).trans
      (Homeomorph.prodComm _ _)).trans puncturedPolar.symm

/-- The inverse cylindrical coordinates recover logarithmic radius and angular phase. -/
theorem puncturedCylinder_symm_apply (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    puncturedCylinder.symm z =
      (cylinderRadius.symm (puncturedPolar z).2,
        -(AddCircle.homeomorphCircle one_ne_zero).symm (puncturedPolar z).1) := (rfl)

/-- Evaluation of cylindrical coordinates by radius and the period-one angular coordinate. -/
theorem puncturedCylinder_apply (s : Ioi (0 : ℝ)) (t : AddCircle (1 : ℝ)) :
    (puncturedCylinder (s, t) : ℂ) =
      Real.exp (-(2 * Real.pi) * s) • (AddCircle.toCircle (-t) : ℂ) := by
  simp [puncturedCylinder, puncturedPolar_symm_apply, cylinderRadius_apply,
    AddCircle.homeomorphCircle_apply]

/-- On real angular lifts the cylinder coordinate is the holomorphic exponential. -/
theorem puncturedCylinder_apply_mk (s : Ioi (0 : ℝ)) (t : ℝ) :
    (puncturedCylinder (s, (t : AddCircle (1 : ℝ))) : ℂ) =
      Complex.exp (-(2 * (Real.pi : ℂ)) * ((s : ℝ) + t * Complex.I)) := by
  rw [puncturedCylinder_apply, ← AddCircle.coe_neg, AddCircle.toCircle_apply_mk,
    Circle.coe_exp, Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end TauCeti.Complex.UnitDisc
