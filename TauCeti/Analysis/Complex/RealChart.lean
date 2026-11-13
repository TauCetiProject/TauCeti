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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

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
(`TauCeti.Complex.image_realChart_preimage`); for instance an affine map `w ↦ c + a w` maps closed
annuli about `0` onto closed annuli about `c` (`TauCeti.Complex.image_realChart_affine_annulus`).
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
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, (equivRealProdCLM_symm_realChart f y).symm⟩
  · rintro ⟨w, hw, hwz⟩
    refine ⟨Complex.equivRealProdCLM w,
      by rwa [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply], ?_⟩
    rw [realChart_equivRealProdCLM, hwz, ContinuousLinearEquiv.apply_symm_apply]

/-- In real coordinates, the affine map `w ↦ c + a w`, for `a ≠ 0`, maps the closed annulus about
`0` with radii `r₁` and `r₂` onto the closed annulus about `c` with radii `‖a‖ r₁` and `‖a‖ r₂`. -/
theorem image_realChart_affine_annulus {c a : ℂ} (ha : a ≠ 0) (r₁ r₂ : ℝ) :
    realChart (c + a * ·) '' (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall 0 r₂ \ Metric.ball 0 r₁)) =
      Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall c (‖a‖ * r₂) \ Metric.ball c (‖a‖ * r₁)) := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [image_realChart_preimage]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm,
    not_lt, sub_zero]
  constructor
  · rintro ⟨y, ⟨h₂, h₁⟩, rfl⟩
    rw [add_sub_cancel_left, norm_mul]
    exact ⟨by gcongr, by gcongr⟩
  · rintro ⟨h₂, h₁⟩
    refine ⟨(w - c) / a, ⟨?_, ?_⟩, by rw [mul_div_cancel₀ _ ha, add_sub_cancel]⟩
    · rw [norm_div, div_le_iff₀ ha']
      linarith
    · rw [norm_div, le_div_iff₀ ha']
      linarith

end TauCeti.Complex
