/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Holder.OpenSet.Basic
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# The Cauchy–Riemann operator on `C^{1,α}(Ω)`

For an open set `Ω` of the plane and a complex normed space `W`, the conjugate Wirtinger
derivative `∂u/∂(conj z) = (∂ₛu + i ∂ₜu) / 2` maps `C^{1,α}(Ω, W)` continuously to the bounded
Hölder space `C^α(Ω, W)`: it is a fixed continuous real-linear map applied to the first
derivative field, whose `C^α(Ω)` norm is bounded by the `C^{1,α}(Ω)` norm. This is the operator of
boundary value problems for the Cauchy–Riemann equation in Hölder spaces.

## Main declarations

* `TauCeti.conjWirtingerDerivHolderL`: the operator `u ↦ ∂u/∂(conj z)` from `C^{1,α}(Ω, W)` to
  `C^α(Ω, W)`.
* `TauCeti.conjWirtingerDerivHolderL_apply`: its value at a point of `Ω` is the conjugate
  Wirtinger derivative `conjWirtingerDeriv g z 1` of any function `g` agreeing with the element on
  `Ω`.
-/

public noncomputable section

open TopologicalSpace
open scoped NNReal

namespace TauCeti

variable {α : ℝ≥0} {Ω : Opens ℂ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The real-linear map sending the first derivative `Du` at a point, as a `1`-multilinear map, to
the conjugate Wirtinger derivative `(Du 1 + i • Du i) / 2`. -/
private def conjWirtingerOfFin1L : (ℂ [×1]→L[ℝ] W) →L[ℝ] W :=
  (ContinuousLinearMap.apply ℝ W (1 : ℂ)).comp
    (ContinuousLinearMap.complexAntilinearPartL.comp
      (continuousMultilinearCurryFin1 ℝ ℂ W).toContinuousLinearEquiv.toContinuousLinearMap)

private theorem conjWirtingerOfFin1L_iteratedFDeriv (g : ℂ → W) (z : ℂ) :
    conjWirtingerOfFin1L (iteratedFDeriv ℝ 1 g z) = conjWirtingerDeriv g z 1 := by
  have h : continuousMultilinearCurryFin1 ℝ ℂ W (iteratedFDeriv ℝ 1 g z) = fderiv ℝ g z := by
    ext v
    simp
  simp [conjWirtingerOfFin1L, h, conjWirtingerDeriv_apply_eq_complexAntilinearPartL]

/-- The Cauchy–Riemann operator `u ↦ ∂u/∂(conj z)` from `C^{1,α}(Ω, W)` to the bounded Hölder space
`C^α(Ω, W)`, for an open set `Ω` of the plane. -/
def conjWirtingerDerivHolderL : CkHolderSpaceOn 1 α Ω W →L[ℝ] HolderSpace α Ω W :=
  (HolderSpace.compLeftL conjWirtingerOfFin1L).comp CkHolderSpaceOn.iteratedFDerivHolderL

/-- The value of `∂u/∂(conj z)` at a point of `Ω` is the conjugate Wirtinger derivative, in the
direction `1`, of any function on the plane agreeing with `u` on `Ω`. -/
theorem conjWirtingerDerivHolderL_apply (u : CkHolderSpaceOn 1 α Ω W) {g : ℂ → W}
    (hg : ∀ x : Ω, g x = u x) (z : Ω) :
    conjWirtingerDerivHolderL u z = conjWirtingerDeriv g z 1 := by
  simpa [conjWirtingerDerivHolderL, conjWirtingerOfFin1L_iteratedFDeriv] using
    congrArg conjWirtingerOfFin1L (u.iteratedFDeriv_eq hg (Fin.last 1) z).symm

/-- The value of `∂u/∂(conj z)` at a point of `Ω` is the conjugate Wirtinger derivative of the
extension by zero of `u`. -/
@[simp]
theorem conjWirtingerDerivHolderL_apply_extend (u : CkHolderSpaceOn 1 α Ω W) (z : Ω) :
    conjWirtingerDerivHolderL u z = conjWirtingerDeriv u.extend z 1 :=
  conjWirtingerDerivHolderL_apply u u.extend_apply z

end TauCeti
