/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Operator
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.TimeReversal
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace

/-!
# The backward parabolic operator at every order

For coefficient fields `A`, `B`, `C` in the bounded parabolic Hölder space `C_{par,b}^{k+α}` on the
slab `E × [a, b]`, this file defines the backward operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u`
as a bounded linear map `C_{par,b}^{k+2+α} → C_{par,b}^{k+α}`, and the terminal-data operator
`u ↦ (P_back u, u(·, b))` into `C_{par,b}^{k+α} × C_b^{k+2,α}`.

The time reversal `R (x, s) = (x, T - s)` turns the backward operator into a forward one:
`P_R (u ∘ R) = -(P_back u) ∘ R`, where `P_R` has the reversed coefficients
(`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_timeReverseLIE`). This reduces terminal-value
problems to Cauchy problems.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.backwardParabolicOperatorL`: the backward operator.
* `TauCeti.ParabolicCkHolderSpace.terminalDataL`: the operator `u ↦ (P_back u, u(·, b))`.
* `TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_timeReverseLIE`: its time reversal.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4
  (backward equations and time reversal).
-/

public section

noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal

namespace ParabolicCkHolderSpace

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- **The backward parabolic operator** `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` with coefficient
fields in `C_{par,b}^{k+α}`, as a continuous linear map from `C_{par,b}^{(k+2)+α}` to
`C_{par,b}^{k+α}`. -/
def backwardParabolicOperatorL (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  timeDerivL k α E F hab + spatialOperatorL hα A B C

theorem backwardParabolicOperatorL_def (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    backwardParabolicOperatorL hα A B C = timeDerivL k α E F hab + spatialOperatorL hα A B C :=
  (rfl)

/-- The values of the backward operator, in terms of the fields of `u`. -/
@[simp]
theorem backwardParabolicOperatorL_apply (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) (p : slab (E := E) a b) :
    backwardParabolicOperatorL hα A B C u p =
      mixedDerivL 1 0 u p 0 + (A p (continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 u p)) +
        B p (spatialFDerivBCF u p) + C p (u p)) := by
  simp [backwardParabolicOperatorL]

/-- The values of the backward operator at `(x, t)`, in terms of the time derivative within
`[a, b]` and the spatial Fréchet derivatives of `u`: the equation `∂ₜu + A·D_x²u + B·D_xu + C·u`
read classically. -/
theorem backwardParabolicOperatorL_slabMk (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) (x : E) (t : Icc a b) :
    backwardParabolicOperatorL hα A B C u (slabMk x t) =
      derivWithin (ParabolicC2HolderSpace.timeExtension hab.le u x) (Icc a b) t +
        (A (slabMk x t) (fderiv ℝ (fderiv ℝ fun y ↦ u (slabMk y t)) x) +
          B (slabMk x t) (fderiv ℝ (fun y ↦ u (slabMk y t)) x) +
          C (slabMk x t) (u (slabMk x t))) := by
  rw [backwardParabolicOperatorL_def, _root_.add_apply, coe_add, Pi.add_apply,
    timeDerivL_slabMk, spatialOperatorL_slabMk]

/-- **The operator bound for the backward operator.**
`‖P_back‖ ≤ 1 + 21 (k + 1)² 2ᵏ (‖A‖ + 8 (k + 1)² ‖B‖ + 64 (k + 1)² (k + 2)² ‖C‖)`, uniformly over
the spaces and the slab. -/
theorem norm_backwardParabolicOperatorL_le (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    ‖backwardParabolicOperatorL hα A B C‖ ≤ 1 + 21 * (k + 1) ^ 2 * 2 ^ k *
      (‖A‖ + 8 * (k + 1) ^ 2 * ‖B‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C‖) :=
  (norm_add_le _ _).trans (add_le_add norm_timeDerivL_le_one (norm_spatialOperatorL_le hα A B C))

/-- The terminal-data operator `u ↦ (P_back u, u(·, b))` from `C_{par,b}^{(k+2)+α}` to
`C_{par,b}^{k+α} × C_b^{k+2,α}`. -/
def terminalDataL (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ]
      ParabolicCkHolderSpace k α E F hab × CkHolderSpace (k + 2) α E F :=
  (backwardParabolicOperatorL hα A B C).prod (spatialTraceL ⟨b, right_mem_Icc.2 hab.le⟩)

/-- The first data component is the backward operator. -/
@[simp]
theorem terminalDataL_fst (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (terminalDataL hα A B C u).1 = backwardParabolicOperatorL hα A B C u := by
  simp [terminalDataL]

/-- The second data component is the terminal spatial trace. -/
@[simp]
theorem terminalDataL_snd (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (terminalDataL hα A B C u).2 = u.spatialTrace ⟨b, right_mem_Icc.2 hab.le⟩ := by
  simp [terminalDataL]

/-- **Time reversal of the backward operator.** With `R (x, s) = (x, T - s)`, the forward operator
with the reversed coefficients satisfies `P_R (u ∘ R) = -(P_back u) ∘ R`. -/
theorem parabolicOperatorL_timeReverseLIE {a' b' T : ℝ} {ha : a' = T - b} {hb : b' = T - a}
    (hα : α ≤ 1) (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    parabolicOperatorL hα (timeReverseLIE T ha hb A) (timeReverseLIE T ha hb B)
        (timeReverseLIE T ha hb C) (timeReverseLIE T ha hb u) =
      -timeReverseLIE T ha hb (backwardParabolicOperatorL hα A B C u) := by
  refine ext fun p ↦ ?_
  simp [parabolicOperatorL_apply]
  abel

end ParabolicCkHolderSpace

end TauCeti
