/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Maps of the complex plane in real coordinates

A map `f : ℂ → ℂ` of the plane, read in the real coordinates `ℝ × ℝ ≃ ℂ` given by
`Complex.equivRealProdCLM`, is `TauCeti.Complex.realChart f`. When `f` has complex derivative
`f'`, the real derivative of its real chart is multiplication by `f'`
(`TauCeti.Complex.hasFDerivAt_realChart`, `TauCeti.Complex.fderiv_realChart_apply`), whose real
determinant is `|f'|²`, so the Jacobian determinant of the real chart is nonnegative
(`TauCeti.Complex.det_fderiv_realChart`, `TauCeti.Complex.det_fderiv_realChart_nonneg`), and a map
that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates (`TauCeti.Complex.contDiff_realChart`).
The real chart of an injective map is injective (`TauCeti.Complex.realChart_injective`), and the
real chart maps the real coordinates of a set onto those of its image
(`TauCeti.Complex.image_realChart_preimage`). For instance an affine map `w ↦ c + a w` with
`a ≠ 0` is injective and orientation-preserving in real coordinates
(`TauCeti.Complex.realChart_affine_injective`,
`TauCeti.Complex.det_fderiv_realChart_affine_nonneg`), and it maps closed and open discs about
`w`, and closed annuli about `w`, onto those about `c + a w`
(`TauCeti.Complex.image_realChart_affine_closedBall`,
`TauCeti.Complex.image_realChart_affine_ball`,
`TauCeti.Complex.image_realChart_affine_closedBall_sdiff_ball`). A closed annulus is compact in
real coordinates (`TauCeti.Complex.isCompact_preimage_closedBall_sdiff_ball`).
-/

public section

namespace TauCeti.Complex

/-- A map `f : ℂ → ℂ` of the plane, written in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def realChart (f : ℂ → ℂ) : ℝ × ℝ → ℝ × ℝ :=
  Complex.equivRealProdCLM ∘ f ∘ Complex.equivRealProdCLM.symm

theorem realChart_apply (f : ℂ → ℂ) (z : ℝ × ℝ) :
    realChart f z = Complex.equivRealProdCLM (f (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- In complex coordinates, the real chart of `f` is `f`. -/
@[simp]
theorem equivRealProdCLM_symm_realChart (f : ℂ → ℂ) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (realChart f z) = f (Complex.equivRealProdCLM.symm z) :=
  Complex.equivRealProdCLM.symm_apply_apply _

/-- The real chart of `f` at the real coordinates of `w` is the real coordinates of `f w`. -/
theorem realChart_equivRealProdCLM (f : ℂ → ℂ) (w : ℂ) :
    realChart f (Complex.equivRealProdCLM w) = Complex.equivRealProdCLM (f w) := by
  rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- In real coordinates, the derivative of a map with complex derivative `f'` is multiplication
by `f'`. -/
theorem hasFDerivAt_realChart {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) :
    HasFDerivAt (realChart f)
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ).comp
          (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) w :=
  Complex.equivRealProdCLM.hasFDerivAt.comp w
    ((hf.hasFDerivAt.restrictScalars ℝ).comp w Complex.equivRealProdCLM.symm.hasFDerivAt)

theorem fderiv_realChart_apply {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) (v : ℝ × ℝ) :
    fderiv ℝ (realChart f) w v =
      Complex.equivRealProdCLM (f' * Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_realChart hf).fderiv]
  simp [mul_comm]

/-- In real coordinates, the Jacobian determinant of a map with complex derivative `f'` is
`|f'|²`. -/
theorem det_fderiv_realChart {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) :
    (fderiv ℝ (realChart f) w).det = Complex.normSq f' := by
  rw [(hasFDerivAt_realChart hf).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- In real coordinates, the Jacobian determinant of a map with a complex derivative is
nonnegative. -/
theorem det_fderiv_realChart_nonneg {f : ℂ → ℂ} {f' : ℂ} {w : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) :
    0 ≤ (fderiv ℝ (realChart f) w).det := by
  rw [det_fderiv_realChart hf]
  exact Complex.normSq_nonneg f'

/-- A map that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates. -/
theorem contDiff_realChart {f : ℂ → ℂ} {n : WithTop ℕ∞} (hf : ContDiff ℂ n f) :
    ContDiff ℝ n (realChart f) :=
  Complex.equivRealProdCLM.contDiff.comp
    ((hf.restrict_scalars ℝ).comp Complex.equivRealProdCLM.symm.contDiff)

/-- The real chart of an injective map is injective. -/
theorem realChart_injective {f : ℂ → ℂ} (hf : Function.Injective f) :
    Function.Injective (realChart f) :=
  Complex.equivRealProdCLM.injective.comp (hf.comp Complex.equivRealProdCLM.symm.injective)

/-- The real chart of `f` maps the real coordinates of a set `s` onto the real coordinates of
`f '' s`. -/
theorem image_realChart_preimage (f : ℂ → ℂ) (s : Set ℂ) :
    realChart f '' (Complex.equivRealProdCLM.symm ⁻¹' s) =
      Complex.equivRealProdCLM.symm ⁻¹' (f '' s) := by
  rw [realChart, Set.image_comp, Set.image_comp,
    Set.image_preimage_eq _ Complex.equivRealProdCLM.symm.surjective,
    Complex.equivRealProdCLM.image_eq_preimage_symm]

/-- In real coordinates, the affine map `w ↦ c + a w`, for `a ≠ 0`, is injective. -/
theorem realChart_affine_injective {c a : ℂ} (ha : a ≠ 0) :
    Function.Injective (realChart (c + a * ·)) :=
  realChart_injective fun _ _ h ↦ mul_left_cancel₀ ha (add_left_cancel h)

/-- In real coordinates, the affine map `w ↦ c + a w` preserves orientation. -/
theorem det_fderiv_realChart_affine_nonneg (c a : ℂ) (w : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (realChart (c + a * ·)) w).det :=
  det_fderiv_realChart_nonneg (f' := a) (by simpa using ((hasDerivAt_id _).const_mul a).const_add c)

/-- In real coordinates, the affine map `w ↦ c + a w`, for `a ≠ 0`, maps the closed disc about `w`
of radius `r` onto the closed disc about `c + a w` of radius `‖a‖ r`. -/
theorem image_realChart_affine_closedBall {c a : ℂ} (ha : a ≠ 0) (w : ℂ) (r : ℝ) :
    realChart (c + a * ·) '' (Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall w r) =
      Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall (c + a * w) (‖a‖ * r) := by
  have h : (c + a * ·) = (c +ᵥ ·) ∘ (a • ·) := rfl
  rw [image_realChart_preimage, h, Set.image_comp, Set.image_smul, smul_closedBall' ha,
    Set.image_vadd, Metric.vadd_closedBall]
  rfl

/-- In real coordinates, the affine map `w ↦ c + a w`, for `a ≠ 0`, maps the open disc about `w`
of radius `r` onto the open disc about `c + a w` of radius `‖a‖ r`. -/
theorem image_realChart_affine_ball {c a : ℂ} (ha : a ≠ 0) (w : ℂ) (r : ℝ) :
    realChart (c + a * ·) '' (Complex.equivRealProdCLM.symm ⁻¹' Metric.ball w r) =
      Complex.equivRealProdCLM.symm ⁻¹' Metric.ball (c + a * w) (‖a‖ * r) := by
  have h : (c + a * ·) = (c +ᵥ ·) ∘ (a • ·) := rfl
  rw [image_realChart_preimage, h, Set.image_comp, Set.image_smul, smul_ball ha, Set.image_vadd,
    Metric.vadd_ball]
  rfl

/-- In real coordinates, the affine map `w ↦ c + a w`, for `a ≠ 0`, maps the closed annulus about
`w` with radii `r₁` and `r₂` onto the closed annulus about `c + a w` with radii `‖a‖ r₁` and
`‖a‖ r₂`. -/
theorem image_realChart_affine_closedBall_sdiff_ball {c a : ℂ} (ha : a ≠ 0) (w : ℂ) (r₁ r₂ : ℝ) :
    realChart (c + a * ·) '' (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall w r₂ \ Metric.ball w r₁)) =
      Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall (c + a * w) (‖a‖ * r₂) \ Metric.ball (c + a * w) (‖a‖ * r₁)) := by
  rw [Set.preimage_sdiff, Set.image_sdiff (realChart_affine_injective ha),
    image_realChart_affine_closedBall ha, image_realChart_affine_ball ha, Set.preimage_sdiff]

/-- A closed annulus of `ℂ` is compact in real coordinates. -/
theorem isCompact_preimage_closedBall_sdiff_ball (w : ℂ) (r₁ r₂ : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' (Metric.closedBall w r₂ \ Metric.ball w r₁)) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    ((isCompact_closedBall _ _).diff Metric.isOpen_ball)

end TauCeti.Complex
