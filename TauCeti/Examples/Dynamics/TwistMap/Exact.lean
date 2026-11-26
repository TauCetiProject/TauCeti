/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.Exact
public import TauCeti.Dynamics.TwistMap.OpenStrip
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Examples.Dynamics.TwistMap.OpenStrip

/-!
# Checks for exact maps of the strip

For the primitive `λ = y dx` of the area form on the plane, with period `1`:

* the shear `(x, y) ↦ (x + y, y)` is exact, with `S = y²/2`: `F*(y dx) − y dx = y dy`;
* the shifted shear `(x, y) ↦ (x + y, y + c)` with `c ≠ 0` is a monotone twist map preserving
  Lebesgue measure, and it is not exact: `F*(y dx) − y dx = (y + c)(dx + dy) − y dx` has
  `dx`-coefficient `c` along `y = 0`, the flux of `F`. Area preservation alone does not imply
  exactness on the open strip.
* the standard map `(x, y) ↦ (x + y + ε sin 2πx, y + ε sin 2πx)` is exact for every `ε`: with
  `Y = y + ε sin 2πx`, `F*(y dx) − y dx = ε sin(2πx) dx + d(Y²/2)`, and since
  `∫₀¹ ε sin 2πx dx = 0` this is `dS` for the periodic `S = −ε cos(2πx)/(2π) + Y²/2`
  (`isExactForPrimitive_standardMap`).
-/

open Set MeasureTheory

public noncomputable section

namespace TauCeti.Examples.ExactTwistMap

/-- The shifted shear `(x, y) ↦ (x + y, y + c)` of the plane, with inverse
`(x, y) ↦ (x − y + c, y − c)`. -/
def shiftedShear (c : ℝ) : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (p.1 + p.2, p.2 + c)
  invFun p := (p.1 - p.2 + c, p.2 - c)
  left_inv p := by ext <;> dsimp only <;> ring
  right_inv p := by ext <;> dsimp only <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem shiftedShear_apply (c : ℝ) (p : ℝ × ℝ) : shiftedShear c p = (p.1 + p.2, p.2 + c) :=
  (rfl)

@[simp]
theorem shiftedShear_symm_apply (c : ℝ) (p : ℝ × ℝ) :
    (shiftedShear c).symm p = (p.1 - p.2 + c, p.2 - c) :=
  (rfl)

/-- The shifted shear as an explicit function. -/
theorem coe_shiftedShear (c : ℝ) : ⇑(shiftedShear c) = fun p => (p.1 + p.2, p.2 + c) :=
  funext (shiftedShear_apply c)

/-- The inverse of the shifted shear as an explicit function. -/
theorem coe_shiftedShear_symm (c : ℝ) :
    ⇑(shiftedShear c).symm = fun p => (p.1 - p.2 + c, p.2 - c) :=
  funext (shiftedShear_symm_apply c)

/-- The derivative of the shifted shear is `(u, v) ↦ (u + v, v)`. -/
theorem hasFDerivAt_shiftedShear (c : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (shiftedShear c) ((ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have hfst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  rw [coe_shiftedShear]
  exact (hfst.add hsnd).prodMk (hsnd.add_const c)

/-- The first component of the derivative of the shifted shear is `dx + dy`. -/
theorem fst_comp_fderiv_shiftedShear (c : ℝ) (p : ℝ × ℝ) :
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ (shiftedShear c) p) =
      ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ := by
  rw [(hasFDerivAt_shiftedShear c p).fderiv]
  exact ContinuousLinearMap.fst_comp_prod _ _

/-- The shifted shear is a monotone twist map of the plane with period `1`. -/
theorem isMonotoneTwistMap_shiftedShear (c : ℝ) :
    IsMonotoneTwistMap 1 univ (shiftedShear c).toOpenPartialHomeomorph := by
  have hs : ContDiff ℝ 1 (shiftedShear c) := by
    rw [coe_shiftedShear]
    fun_prop
  have hsymm : ContDiff ℝ 1 (shiftedShear c).symm := by
    rw [coe_shiftedShear_symm]
    fun_prop
  refine
    { period_pos := one_pos
      nonempty := univ_nonempty
      isOpen := isOpen_univ
      ordConnected := ordConnected_univ
      source_eq := by rw [Homeomorph.toOpenPartialHomeomorph_source, univ_prod_univ]
      target_eq := by rw [Homeomorph.toOpenPartialHomeomorph_target, univ_prod_univ]
      apply_add_period := fun x y _ => ?_
      strictMonoOn_fst := fun x y₁ _ y₂ _ h => ?_
      lower_end := fun d _ => ⟨d - c, mem_univ _, fun x y _ hy => ?_⟩
      upper_end := fun d _ => ⟨d - c, mem_univ _, fun x y _ hy => ?_⟩
      contDiffOn := by
        rw [Homeomorph.toOpenPartialHomeomorph_apply]
        exact hs.contDiffOn
      contDiffOn_symm := by
        rw [Homeomorph.toOpenPartialHomeomorph_symm_apply]
        exact hsymm.contDiffOn
      fderiv_fst_pos := fun p _ => ?_ }
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, shiftedShear_apply, Prod.mk_add_mk,
      add_zero]
    ext <;> ring
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, shiftedShear_apply]
    linarith
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, shiftedShear_apply]
    linarith
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, shiftedShear_apply]
    linarith
  · have h := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (0, 1)) (fst_comp_fderiv_shiftedShear c p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] at h
    rw [Homeomorph.toOpenPartialHomeomorph_apply, h]
    simp

/-- The shifted shear preserves Lebesgue measure on the plane. -/
theorem measurePreserving_shiftedShear (c : ℝ) :
    MeasurePreserving (shiftedShear c) volume volume := by
  rw [coe_shiftedShear]
  convert ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) c)).comp
    (measurePreserving_add_prod (volume : Measure ℝ) volume) using 1
  funext p
  simp

/-- For the shear `F(x, y) = (x + y, y)`, `S = y²/2` is a primitive of `F*(y dx) − y dx = y dy`:
`dS_p = (F p)₂ (dF_p)₁ − p₂ dx`. -/
theorem hasFDerivAt_primitive_shiftedShear_zero (p : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2 / 2) ((shiftedShear 0 p).2 •
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ (shiftedShear 0) p) -
        p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) p.2 p.2 :=
    (HasDerivAt.div_const (hasDerivAt_pow 2 p.2) 2).congr_deriv (by norm_num)
  have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have h : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2 / 2)
      (p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hsq.comp_hasFDerivAt p hsnd
  convert h using 1
  rw [fst_comp_fderiv_shiftedShear]
  ext <;> simp [shiftedShear_apply]

/-- The shear `(x, y) ↦ (x + y, y)` is exact for `λ = y dx`, with `S = y²/2`. -/
example : IsExactForPrimitive 1 univ (shiftedShear 0) fun p => p.2 :=
  isExactForPrimitive_iff.2
    ⟨_, by fun_prop, fun _ _ _ => rfl, fun p _ => hasFDerivAt_primitive_shiftedShear_zero p⟩

/-- For `c ≠ 0` the shifted shear is not exact for `λ = y dx`: its flux is `c`. -/
example {c : ℝ} (hc : c ≠ 0) :
    ¬ IsExactForPrimitive 1 univ (shiftedShear c) fun p => p.2 := by
  intro h
  refine hc (h.eq_zero_of_flux one_ne_zero (mem_univ 0) fun x => ?_)
  have h1 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) (fst_comp_fderiv_shiftedShear c (x, 0))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] at h1
  rw [h1, shiftedShear_apply]
  simp

/-- The standard map is exact for `λ = y dx` for every `ε`, with
`S = −ε cos(2πx)/(2π) + (y + ε sin 2πx)²/2`. -/
theorem isExactForPrimitive_standardMap (ε : ℝ) :
    IsExactForPrimitive 1 univ (standardMap ε) fun p => p.2 := by
  refine isExactForPrimitive_iff.2 ⟨fun p => -ε * Real.cos (2 * Real.pi * p.1) * (2 * Real.pi)⁻¹ +
    (p.2 + ε * Real.sin (2 * Real.pi * p.1)) ^ 2 * 2⁻¹, by fun_prop, fun x _ _ => ?_,
    fun p _ => ?_⟩
  · simp only [mul_add, mul_one, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hfst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hsin := (hfst.const_mul (2 * Real.pi)).sin
  have hcos := (hfst.const_mul (2 * Real.pi)).cos
  have hY := hsnd.add (hsin.const_mul ε)
  have hS := ((hcos.const_mul (-ε)).mul_const (2 * Real.pi)⁻¹).add ((hY.pow 2).mul_const 2⁻¹)
  refine hS.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [fst_comp_fderiv_standardMap]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp [standardMap_apply, Pi.add_apply]
  field_simp
  ring

end TauCeti.Examples.ExactTwistMap
