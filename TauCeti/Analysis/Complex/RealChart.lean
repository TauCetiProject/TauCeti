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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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
The real chart of an injective map is injective (`TauCeti.Complex.realChart_injective`).

When `f` is periodic of period one in the direction of `i`, the integral of a period-one function
along the image of a vertical side `s = s₀` of a rectangle may be taken over `[0, 1]` instead of
`[-1/2, 1/2]` (`TauCeti.Complex.intervalIntegral_realChart_eq_of_periodic`). The complement of
finitely many points of `ℂ`, read in real coordinates, is open
(`TauCeti.Complex.isOpen_setOf_forall_equivRealProdCLM_symm_ne`).
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

/-- If `f` is periodic of period one in the direction of `i`, the integral of a period-one
function `G` along the image under the real chart of `f` of a vertical side `s = s₀` of a
rectangle may be taken over `[0, 1]` instead of `[-1/2, 1/2]`. -/
theorem intervalIntegral_realChart_eq_of_periodic {X E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → ℂ} (hf : ∀ s : ℝ, Function.Periodic
      (fun t : ℝ => f (s + t * Complex.I)) 1) {G : ℝ → X → E}
    (hG : Function.Periodic G 1) (u : ℝ × ℝ → X) (s : ℝ) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (s, t))) =
      ∫ t in (0 : ℝ)..1, G t (u (Complex.equivRealProdCLM (f (s + t * Complex.I)))) := by
  have hper : Function.Periodic
      (fun t : ℝ => G t (u (Complex.equivRealProdCLM (f (s + t * Complex.I))))) 1 := fun t => by
    have h' : f (s + ((t + 1 : ℝ) : ℂ) * Complex.I) = f (s + t * Complex.I) := hf s t
    simp only [hG t, h']
  have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
  norm_num at h
  simp only [realChart_apply, Complex.equivRealProdCLM_symm_apply]
  convert h using 1 <;> norm_num

/-- The complement of finitely many points `c i` of `ℂ`, in real coordinates, is open. -/
theorem isOpen_setOf_forall_equivRealProdCLM_symm_ne {ι : Type*} [Finite ι] (c : ι → ℂ) :
    IsOpen {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const

end TauCeti.Complex
