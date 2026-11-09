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
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# Maps of the complex plane in real coordinates

A map `f : ℂ → ℂ` of the plane, read in the real coordinates `ℝ × ℝ ≃ ℂ` given by
`Complex.equivRealProdCLM`, is `TauCeti.Complex.realChart f`. When `f` has complex derivative
`f'`, the real derivative of its real chart is multiplication by `f'`
(`TauCeti.Complex.hasFDerivAt_realChart`, `TauCeti.Complex.fderiv_realChart_apply`), and a map
that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates (`TauCeti.Complex.contDiff_realChart`).
The real chart of an injective map is injective (`TauCeti.Complex.realChart_injective`), and the
real chart of a complex differentiable map preserves orientation: its Jacobian determinant is
nonnegative (`TauCeti.Complex.det_fderiv_realChart_nonneg`).
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
    Complex.equivRealProdCLM.symm (realChart f z) = f (Complex.equivRealProdCLM.symm z) := by
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

/-- **A holomorphic map preserves orientation.** In real coordinates, the Jacobian determinant of
a map that is complex differentiable at a point is nonnegative there. -/
theorem det_fderiv_realChart_nonneg {f : ℂ → ℂ} {w : ℝ × ℝ}
    (hf : DifferentiableAt ℂ f (Complex.equivRealProdCLM.symm w)) :
    0 ≤ (fderiv ℝ (realChart f) w).det := by
  rw [(hasFDerivAt_realChart hf.hasDerivAt).fderiv]
  simpa [ContinuousLinearMap.det] using LinearMap.det_restrictScalars_nonneg (E := ℂ)
    (LinearMap.toSpanSingleton ℂ ℂ (deriv f (Complex.equivRealProdCLM.symm w)))

/-- A map that is `C^n` over `ℂ` is `C^n` over `ℝ` in real coordinates. -/
theorem contDiff_realChart {f : ℂ → ℂ} {n : WithTop ℕ∞} (hf : ContDiff ℂ n f) :
    ContDiff ℝ n (realChart f) :=
  Complex.equivRealProdCLM.contDiff.comp
    ((hf.restrict_scalars ℝ).comp Complex.equivRealProdCLM.symm.contDiff)

/-- The real chart of an injective map is injective. -/
theorem realChart_injective {f : ℂ → ℂ} (hf : Function.Injective f) :
    Function.Injective (realChart f) :=
  Complex.equivRealProdCLM.injective.comp (hf.comp Complex.equivRealProdCLM.symm.injective)

end TauCeti.Complex
