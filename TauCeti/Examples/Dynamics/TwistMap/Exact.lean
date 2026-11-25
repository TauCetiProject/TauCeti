/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.Exact
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Checks for exact maps of the strip

For the primitive `λ = y dx` of the area form on the plane, with period `1`:

* the shear `(x, y) ↦ (x + y, y)` is exact, with `S = y²/2`: `F*(y dx) − y dx = y dy`;
* the shifted shear `(x, y) ↦ (x + y, y + c)` with `c ≠ 0` is a monotone twist map preserving
  Lebesgue measure, and it is not exact: `F*(y dx) − y dx = (y + c)(dx + dy) − y dx` has
  `dx`-coefficient `c` along `y = 0`, the flux of `F`. Area preservation alone does not imply
  exactness on the open strip.
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

/-- The derivative of the shifted shear is `(u, v) ↦ (u + v, v)`. -/
theorem hasFDerivAt_shiftedShear (c : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (shiftedShear c) ((ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have hfst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have h := (hfst.add hsnd).prodMk (hsnd.add_const c)
  rw [show ⇑(shiftedShear c) = _ from funext (shiftedShear_apply c)]
  exact h

/-- The first component of the derivative of the shifted shear is `dx + dy`. -/
theorem fst_comp_fderiv_shiftedShear (c : ℝ) (p : ℝ × ℝ) :
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (fderiv ℝ (shiftedShear c).toOpenPartialHomeomorph p) =
      ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ := by
  have : ⇑(shiftedShear c).toOpenPartialHomeomorph = ⇑(shiftedShear c) := rfl
  rw [this, (hasFDerivAt_shiftedShear c p).fderiv]
  rfl

/-- The shifted shear is a monotone twist map of the plane with period `1`. -/
theorem isMonotoneTwistMap_shiftedShear (c : ℝ) :
    IsMonotoneTwistMap 1 univ (shiftedShear c).toOpenPartialHomeomorph := by
  have hs : ContDiff ℝ 1 (shiftedShear c) := by
    rw [show ⇑(shiftedShear c) = _ from funext (shiftedShear_apply c)]
    fun_prop
  have hsymm : ContDiff ℝ 1 (shiftedShear c).symm := by
    rw [show ⇑(shiftedShear c).symm = _ from funext (shiftedShear_symm_apply c)]
    fun_prop
  refine
    { period_pos := one_pos
      nonempty := univ_nonempty
      isOpen := isOpen_univ
      ordConnected := ordConnected_univ
      source_eq := univ_prod_univ.symm
      target_eq := univ_prod_univ.symm
      apply_add_period := fun x y _ => ?_
      strictMonoOn_fst := fun x y₁ _ y₂ _ h => ?_
      lower_end := fun d _ => ⟨d - c, mem_univ _, fun x y _ hy => ?_⟩
      upper_end := fun d _ => ⟨d - c, mem_univ _, fun x y _ hy => ?_⟩
      contDiffOn := hs.contDiffOn
      contDiffOn_symm := hsymm.contDiffOn
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
    rw [h]
    simp

/-- The shifted shear preserves Lebesgue measure on the plane. -/
theorem measurePreserving_shiftedShear (c : ℝ) :
    MeasurePreserving (shiftedShear c) volume volume := by
  have h₁ : MeasurePreserving (fun z : ℝ × ℝ => (z.2, z.2 + z.1)) volume volume :=
    measurePreserving_prod_add_swap volume volume
  have h₂ := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) c)).comp
    (Measure.measurePreserving_swap.comp h₁)
  convert h₂ using 1
  funext p
  simp only [shiftedShear_apply, Function.comp_apply, Prod.swap_prod_mk, Prod.map_apply, id]
  ext <;> simp [add_comm]

/-- The shear `(x, y) ↦ (x + y, y)` is exact for `λ = y dx`, with `S = y²/2`. -/
example : IsExactForPrimitive 1 univ (shiftedShear 0).toOpenPartialHomeomorph
    fun p => p.2 := by
  refine isExactForPrimitive_iff.2
    ⟨fun p => p.2 ^ 2 / 2, by fun_prop, fun _ _ _ => rfl, fun p _ => ?_⟩
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

/-- For `c ≠ 0` the shifted shear is not exact for `λ = y dx`: its flux is `c`. -/
example {c : ℝ} (hc : c ≠ 0) :
    ¬ IsExactForPrimitive 1 univ (shiftedShear c).toOpenPartialHomeomorph fun p => p.2 := by
  intro h
  refine hc (h.eq_zero_of_flux one_ne_zero (mem_univ 0) fun x => ?_)
  have h1 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) (fst_comp_fderiv_shiftedShear c (x, 0))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] at h1
  rw [h1, Homeomorph.toOpenPartialHomeomorph_apply, shiftedShear_apply]
  simp

end TauCeti.Examples.ExactTwistMap
