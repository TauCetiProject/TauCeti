/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smoothness of the logarithm and real powers of the continuous functional calculus

In a Banach algebra `A` with an isometric continuous functional calculus, `CFC.log` inverts the
exponential: `log (exp a) = a` for self-adjoint `a` and `exp (log b) = b` for strictly positive
`b`. If the derivative `TauCeti.expFDeriv 𝕂 a` of the exponential is invertible at a self-adjoint
`a`, the inverse function theorem gives an analytic local inverse of `exp` near `exp a`, and the
continuity of `CFC.log` identifies it with `CFC.log` on the strictly positive elements. Hence
`CFC.log` is `C^n` on the strictly positive elements for every `n : ℕ∞ω`, including the analytic
case `n = ω`: near each strictly positive element it agrees on them with a function that is
analytic on a whole neighbourhood in `A`. The real powers `a ^ s = exp (s • log a)` and the square
root inherit this smoothness.

The hypothesis on the derivative holds for matrices; see
`TauCeti/Analysis/Matrix/Exponential/Log.lean`.

## Main results

* `CFC.rpow_eq_exp_smul_log`: `a ^ s = exp (s • log a)` for strictly positive `a`.
* `CFC.contDiffWithinAt_log_exp`: if `expFDeriv 𝕂 a` is invertible at a self-adjoint `a`, then
  `CFC.log` is `C^n` at `exp a` within the strictly positive elements, for every `n`.
* `CFC.contDiffOn_log`, `CFC.contDiffOn_rpow`, `CFC.contDiffOn_sqrt`: if `expFDeriv 𝕂 a` is
  invertible at every self-adjoint `a`, then `CFC.log`, every real power and the square root are
  `C^n` on the strictly positive elements.
-/

public section

open NormedSpace Filter Topology
open scoped ContDiff

namespace CFC

section RpowExpLog

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- A real power of a strictly positive element is the exponential of the rescaled logarithm. -/
theorem rpow_eq_exp_smul_log (a : A) (s : ℝ) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ s = exp (s • log a) := by
  have hpos : ∀ x ∈ spectrum ℝ a, 0 < x := fun x hx ↦ ha.spectrum_pos hx
  have hlog : ContinuousOn Real.log (spectrum ℝ a) :=
    Real.continuousOn_log.mono fun x hx ↦ (hpos x hx).ne'
  calc
    a ^ s = cfc (fun x : ℝ ↦ x ^ s) a := rpow_eq_cfc_real ha.nonneg
    _ = cfc (fun x ↦ Real.exp (s * Real.log x)) a :=
      cfc_congr fun x hx ↦ by rw [Real.rpow_def_of_pos (hpos x hx), mul_comm]
    _ = cfc Real.exp (cfc (fun x ↦ s * Real.log x) a) :=
      cfc_comp' Real.exp (fun x ↦ s * Real.log x) a
    _ = exp (cfc (fun x ↦ s * Real.log x) a) := real_exp_eq_normedSpace_exp (cfc_predicate _ a)
    _ = exp (s • log a) := by rw [cfc_const_mul s Real.log a hlog, log]

end RpowExpLog

section Smooth

variable {𝕂 A : Type*} [RCLike 𝕂] [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [NormedAlgebra 𝕂 A] [CompleteSpace A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [ContinuousStar A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

/-- If the derivative of the exponential is invertible at a self-adjoint `a`, then `CFC.log` is
`C^n` at `exp a` within the strictly positive elements: near `exp a` it agrees on them with the
analytic local inverse of `exp`. -/
theorem contDiffWithinAt_log_exp {a : A} (ha : IsSelfAdjoint a)
    (hda : IsUnit (TauCeti.expFDeriv 𝕂 a)) {n : ℕ∞ω} :
    ContDiffWithinAt 𝕂 n log {b : A | IsStrictlyPositive b} (exp a) := by
  obtain ⟨e, he⟩ := hda
  let e' : A ≃L[𝕂] A := ContinuousLinearEquiv.unitsEquiv 𝕂 A e
  have hcoe : (e' : A →L[𝕂] A) = TauCeti.expFDeriv 𝕂 a := by
    rw [← he]
    ext x
    exact ContinuousLinearEquiv.unitsEquiv_apply 𝕂 A e x
  have hderiv : HasFDerivAt exp (e' : A →L[𝕂] A) a := hcoe ▸ TauCeti.hasFDerivAt_exp a
  have hexp : ContDiffAt 𝕂 ω exp a := (exp_analytic (𝕂 := 𝕂) a).contDiffAt
  have hω : (ω : ℕ∞ω) ≠ 0 := by simp
  -- The analytic local inverse `g` of `exp` near `exp a`.
  let g := hexp.localInverse hderiv hω
  have hg : ContDiffAt 𝕂 ω g (exp a) := hexp.to_localInverse hderiv hω
  have hleft : ∀ᶠ x in 𝓝 a, g (exp x) = x :=
    (hexp.hasStrictFDerivAt' hderiv hω).eventually_left_inverse
  -- `log` is continuous at `exp a` on the strictly positive elements, with value `a` there.
  have hlog : Tendsto log (𝓝[{b : A | IsStrictlyPositive b}] (exp a)) (𝓝 a) := by
    have hcont : ContinuousWithinAt log {b : A | IsSelfAdjoint b ∧ IsUnit b} (exp a) :=
      continuousOn_log _ ⟨ha.exp, isUnit_exp_of_mem_ball (𝕂 := 𝕂)
        ((expSeries_radius_eq_top 𝕂 A).symm ▸ edist_lt_top _ _)⟩
    rw [ContinuousWithinAt, log_exp a ha] at hcont
    exact hcont.mono_left (nhdsWithin_mono _ fun b hb ↦ ⟨hb.isSelfAdjoint, hb.isUnit⟩)
  refine (hg.of_le le_top).contDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hlog hleft] with b hb hgb
    rw [← hgb, exp_log b hb]
  · rw [log_exp a ha]
    exact (hexp.localInverse_apply_image hderiv hω).symm

/-- If the derivative of the exponential is invertible at every self-adjoint element, then
`CFC.log` is `C^n` on the strictly positive elements. -/
theorem contDiffOn_log (hda : ∀ a : A, IsSelfAdjoint a → IsUnit (TauCeti.expFDeriv 𝕂 a))
    {n : ℕ∞ω} : ContDiffOn 𝕂 n log {b : A | IsStrictlyPositive b} := fun b hb ↦ by
  have h := contDiffWithinAt_log_exp (n := n) (IsSelfAdjoint.log (a := b)) (hda _ .log)
  rwa [exp_log b hb] at h

variable [SMulCommClass 𝕂 ℝ A]

/-- If the derivative of the exponential is invertible at every self-adjoint element, then every
real power `a ↦ a ^ s` is `C^n` on the strictly positive elements. -/
theorem contDiffOn_rpow (hda : ∀ a : A, IsSelfAdjoint a → IsUnit (TauCeti.expFDeriv 𝕂 a))
    (s : ℝ) {n : ℕ∞ω} : ContDiffOn 𝕂 n (fun a : A ↦ a ^ s) {b : A | IsStrictlyPositive b} := by
  have hexp : ContDiff 𝕂 n (exp : A → A) :=
    contDiff_iff_contDiffAt.2 fun x ↦ ((exp_analytic (𝕂 := 𝕂) x).contDiffAt).of_le le_top
  exact (hexp.comp_contDiffOn ((contDiffOn_log hda).const_smul s)).congr fun b hb ↦
    rpow_eq_exp_smul_log b s hb

/-- If the derivative of the exponential is invertible at every self-adjoint element, then the
square root is `C^n` on the strictly positive elements. -/
theorem contDiffOn_sqrt (hda : ∀ a : A, IsSelfAdjoint a → IsUnit (TauCeti.expFDeriv 𝕂 a))
    {n : ℕ∞ω} : ContDiffOn 𝕂 n (sqrt : A → A) {b : A | IsStrictlyPositive b} :=
  (contDiffOn_rpow hda (1 / 2)).congr fun _ _ ↦ sqrt_eq_rpow

end Smooth

end CFC
