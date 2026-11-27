/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Operator
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.TimeReversal
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The backward parabolic operator at every order

For `0 ≤ α ≤ 1` and coefficient fields `A`, `B`, `C` in the bounded parabolic Hölder space
`C_{par,b}^{k+α}` on the slab `E × [a, b]`, `a < b`, this file defines the backward operator
`P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` as a bounded linear map
`C_{par,b}^{k+2+α} → C_{par,b}^{k+α}`, and the terminal-data operator `u ↦ (P_back u, u(·, b))`
into `C_{par,b}^{k+α} × C_b^{k+2,α}`.

The time reversal `R (x, s) = (x, T - s)` turns the backward operator into a forward one:
`P_R (u ∘ R) = -(P_back u) ∘ R`, where `P_R` has the reversed coefficients
(`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_timeReverseLIE`). So the initial data of
`u ∘ R` are the terminal data `(f, g)` of `u` transported to `(-f ∘ R, g)`, and the terminal-data
operator is bijective exactly when the initial-data operator of the reversed forward problem is.
This reduces terminal-value problems to Cauchy problems.

These are the order-`k` forms of the order-two declarations
`TauCeti.ParabolicC2HolderSpace.backwardParabolicOperatorL`,
`TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_timeReverseLIE` and
`TauCeti.ParabolicC2HolderSpace.bijective_backwardParabolicOperatorL_prod_spatialTraceL_iff`,
and follow their proofs.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.backwardParabolicOperatorL`: the backward operator.
* `TauCeti.ParabolicCkHolderSpace.terminalDataL`: the operator `u ↦ (P_back u, u(·, b))`.
* `TauCeti.ParabolicCkHolderSpace.backwardParabolicOperatorL_sub_backwardParabolicOperatorL`,
  `terminalDataL_sub_terminalDataL` and `norm_terminalDataL_sub`: differences of backward and
  terminal-data operators in terms of the differences of the coefficients.
* `TauCeti.ParabolicCkHolderSpace.norm_backwardParabolicOperatorL_sub_le` and
  `norm_terminalDataL_sub_le`: their Lipschitz dependence on the coefficients.
* `TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_timeReverseLIE`: its time reversal.
* `TauCeti.ParabolicCkHolderSpace.initialDataL_timeReverseLIE`: the initial data of `u ∘ R` are the
  reversed terminal data of `u`.
* `TauCeti.ParabolicCkHolderSpace.bijective_terminalDataL_iff`: the terminal-data operator is
  bijective iff the reversed initial-data operator is.
* `TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_backwardParabolicOperatorL`: the backward operator
  commutes with the inclusions between orders, and so do the terminal data
  (`TauCeti.ParabolicCkHolderSpace.terminalDataL_inclusionOfLEL_fst` and
  `TauCeti.ParabolicCkHolderSpace.coe_terminalDataL_inclusionOfLEL_snd`).
* `TauCeti.ParabolicCkHolderSpace.timeReverseLIE_euclideanSecondOrderCoeff` and its first- and
  zeroth-order companions: time reversal of the coordinate coefficient fields on `ℝⁿ`.

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
fields in `C_{par,b}^{k+α}`, `α ≤ 1`, as a continuous linear map from `C_{par,b}^{(k+2)+α}` to
`C_{par,b}^{k+α}`. The time derivative is taken within `[a, b]`, so one-sided at the endpoints. -/
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
  simp only [backwardParabolicOperatorL_def, _root_.add_apply, coe_add, Pi.add_apply,
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
`C_{par,b}^{k+α} × C_b^{k+2,α}`, for `α ≤ 1`: the forcing and the terminal spatial trace of `u`. -/
def terminalDataL (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ]
      ParabolicCkHolderSpace k α E F hab × CkHolderSpace (k + 2) α E F :=
  (backwardParabolicOperatorL hα A B C).prod (spatialTraceL ⟨b, right_mem_Icc.2 hab.le⟩)

theorem terminalDataL_def (hα : α ≤ 1)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    terminalDataL hα A B C =
      (backwardParabolicOperatorL hα A B C).prod (spatialTraceL ⟨b, right_mem_Icc.2 hab.le⟩) :=
  (rfl)

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

section Coefficients

variable (hα : α ≤ 1)
  (A A' : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
  (B B' : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
  (C C' : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)

/-- The difference of two backward operators is the spatial operator of the difference of their
coefficients. This is the backward form of
`TauCeti.ParabolicCkHolderSpace.parabolicOperatorL_sub_parabolicOperatorL`. -/
theorem backwardParabolicOperatorL_sub_backwardParabolicOperatorL :
    backwardParabolicOperatorL hα A B C - backwardParabolicOperatorL hα A' B' C' =
      spatialOperatorL hα (A - A') (B - B') (C - C') := by
  rw [spatialOperatorL_sub, backwardParabolicOperatorL_def, backwardParabolicOperatorL_def]
  abel

/-- **Lipschitz dependence on the coefficients.** In operator norm,
`‖P_back - P_back'‖ ≤
  21 (k + 1)² 2ᵏ (‖A - A'‖ + 8 (k + 1)² ‖B - B'‖ + 64 (k + 1)² (k + 2)² ‖C - C'‖)`. This is the
backward form of `TauCeti.ParabolicCkHolderSpace.norm_parabolicOperatorL_sub_le`. -/
theorem norm_backwardParabolicOperatorL_sub_le :
    ‖backwardParabolicOperatorL hα A B C - backwardParabolicOperatorL hα A' B' C'‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k *
        (‖A - A'‖ + 8 * (k + 1) ^ 2 * ‖B - B'‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C - C'‖) := by
  rw [backwardParabolicOperatorL_sub_backwardParabolicOperatorL]
  exact norm_spatialOperatorL_le hα _ _ _

/-- Terminal traces cancel in the difference of two terminal-data operators. -/
theorem terminalDataL_sub_terminalDataL :
    terminalDataL hα A B C - terminalDataL hα A' B' C' =
      (backwardParabolicOperatorL hα A B C - backwardParabolicOperatorL hα A' B' C').prod 0 := by
  ext u <;> simp

/-- Terminal traces cancel in a difference of terminal-data operators, so the perturbation norm
is that of the backward operators. -/
theorem norm_terminalDataL_sub :
    ‖terminalDataL hα A B C - terminalDataL hα A' B' C'‖ =
      ‖backwardParabolicOperatorL hα A B C - backwardParabolicOperatorL hα A' B' C'‖ := by
  rw [terminalDataL_sub_terminalDataL, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)]

/-- A coefficient perturbation has the same explicit bound for the full terminal-data operator as
for its backward component:
`‖(P_back, ·(b)) - (P_back', ·(b))‖ ≤
  21 (k + 1)² 2ᵏ (‖A - A'‖ + 8 (k + 1)² ‖B - B'‖ + 64 (k + 1)² (k + 2)² ‖C - C'‖)`. This is the
terminal-data form of `TauCeti.ParabolicCkHolderSpace.norm_initialDataL_sub_le`. -/
theorem norm_terminalDataL_sub_le :
    ‖terminalDataL hα A B C - terminalDataL hα A' B' C'‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k *
        (‖A - A'‖ + 8 * (k + 1) ^ 2 * ‖B - B'‖ + 64 * (k + 1) ^ 2 * (k + 2) ^ 2 * ‖C - C'‖) := by
  rw [norm_terminalDataL_sub]
  exact norm_backwardParabolicOperatorL_sub_le hα A A' B B' C C'

end Coefficients

/-! ### Time reversal -/

section TimeReversal

variable {a' b' T : ℝ} {ha : a' = T - b} {hb : b' = T - a}

/-- **Time reversal of the backward operator.** With `R (x, s) = (x, T - s)`, the forward operator
with the reversed coefficients satisfies `P_R (u ∘ R) = -(P_back u) ∘ R`. -/
theorem parabolicOperatorL_timeReverseLIE
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

/-- **The reversed initial data are the transported terminal data.** With `R (x, s) = (x, T - s)`,
the initial data of `u ∘ R` for the forward operator with the reversed coefficients are
`(-f ∘ R, g)`, where `(f, g)` are the terminal data of `u` for the backward operator. -/
theorem initialDataL_timeReverseLIE
    (hα : α ≤ 1) (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    initialDataL hα (timeReverseLIE T ha hb A) (timeReverseLIE T ha hb B)
        (timeReverseLIE T ha hb C) (timeReverseLIE T ha hb u) =
      (-timeReverseLIE T ha hb (terminalDataL hα A B C u).1, (terminalDataL hα A B C u).2) := by
  rw [initialDataL_apply, terminalDataL_fst, terminalDataL_snd, parabolicOperatorL_timeReverseLIE,
    spatialTrace_timeReverseLIE_left]

/-- **Solvability of the terminal-value problem by time reversal.** With
`R (x, s) = (x, T - s)`, the terminal-data operator `u ↦ (P_back u, u(·, b))` on `E × [a, b]` is
bijective if and only if the initial-data operator `v ↦ (P_R v, v(·, T - b))` on
`E × [T - b, T - a]` with the reversed coefficients is. -/
theorem bijective_terminalDataL_iff
    (hα : α ≤ 1) (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab) :
    Function.Bijective (terminalDataL hα A B C) ↔
      Function.Bijective (initialDataL hα (timeReverseLIE T ha hb A) (timeReverseLIE T ha hb B)
        (timeReverseLIE T ha hb C)) := by
  -- The data transport `(f, g) ↦ (-f ∘ R, g)`.
  let Φ := ((timeReverseLIE T ha hb (k := k) (α := α) (E := E) (F := F) (hab := hab)
      ).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.neg ℝ)).prodCongr
    (ContinuousLinearEquiv.refl ℝ (CkHolderSpace (k + 2) α E F))
  have hcomp : ⇑(initialDataL hα (timeReverseLIE T ha hb A) (timeReverseLIE T ha hb B)
      (timeReverseLIE T ha hb C)) ∘ timeReverseLIE T ha hb = Φ ∘ terminalDataL hα A B C :=
    funext fun u ↦ by simp [Φ, initialDataL_timeReverseLIE]
  rw [← Function.Bijective.of_comp_iff' Φ.bijective, ← hcomp,
    Function.Bijective.of_comp_iff _ (timeReverseLIE T ha hb).bijective]

end TimeReversal

/-! ### Reading the operator at a lower order -/

/-- The backward operator commutes with the inclusions between orders: reading `P_back u` at a
lower order `m` is applying the operator with the coefficients and `u` read at that order. -/
theorem inclusionOfLEL_backwardParabolicOperatorL (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    inclusionOfLEL hα h (backwardParabolicOperatorL hα A B C u) =
      backwardParabolicOperatorL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B)
        (inclusionOfLEL hα h C) (inclusionOfLEL hα (Nat.add_le_add_right h 2) u) := by
  rw [backwardParabolicOperatorL_def, backwardParabolicOperatorL_def, _root_.add_apply, map_add,
    _root_.add_apply, inclusionOfLEL_timeDerivL, inclusionOfLEL_spatialOperatorL]

/-- Reading `u` and the coefficients at a lower order `m` reads the forcing of the terminal data at
that order. -/
theorem terminalDataL_inclusionOfLEL_fst (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    (terminalDataL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B) (inclusionOfLEL hα h C)
        (inclusionOfLEL hα (Nat.add_le_add_right h 2) u)).1 =
      inclusionOfLEL hα h (terminalDataL hα A B C u).1 := by
  rw [terminalDataL_fst, terminalDataL_fst, inclusionOfLEL_backwardParabolicOperatorL]

/-- Reading `u` and the coefficients at a lower order keeps the terminal trace. -/
theorem coe_terminalDataL_inclusionOfLEL_snd (hα : α ≤ 1) {m : ℕ} (h : m ≤ k)
    (A : ParabolicCkHolderSpace k α E ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) hab)
    (B : ParabolicCkHolderSpace k α E ((E →L[ℝ] F) →L[ℝ] F) hab)
    (C : ParabolicCkHolderSpace k α E (F →L[ℝ] F) hab)
    (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ⇑(terminalDataL hα (inclusionOfLEL hα h A) (inclusionOfLEL hα h B) (inclusionOfLEL hα h C)
        (inclusionOfLEL hα (Nat.add_le_add_right h 2) u)).2 =
      ⇑(terminalDataL hα A B C u).2 := by
  rw [terminalDataL_snd, terminalDataL_snd, coe_spatialTrace_inclusionOfLEL]

/-! ### Time reversal of the coordinate coefficients on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] {a' b' T : ℝ} {ha : a' = T - b} {hb : b' = T - a}

attribute [local instance] instNormedAddCommGroupEuclideanCovector
  instNormedSpaceEuclideanCovector instNormedAddCommGroupEuclideanHessian
  instNormedSpaceEuclideanHessian

/-- Reversing the second-order coefficient field in time reverses its scalar coefficients. -/
@[simp]
theorem timeReverseLIE_euclideanSecondOrderCoeff [DecidableEq ι]
    (c : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hab) :
    timeReverseLIE T ha hb (euclideanSecondOrderCoeff c) =
      euclideanSecondOrderCoeff fun i j ↦ timeReverseLIE T ha hb (c i j) :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

/-- Reversing the first-order coefficient field in time reverses its scalar coefficients. -/
@[simp]
theorem timeReverseLIE_euclideanFirstOrderCoeff [DecidableEq ι]
    (c : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hab) :
    timeReverseLIE T ha hb (euclideanFirstOrderCoeff c) =
      euclideanFirstOrderCoeff fun i ↦ timeReverseLIE T ha hb (c i) :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

/-- Reversing the zeroth-order coefficient field in time reverses its scalar coefficient. -/
@[simp]
theorem timeReverseLIE_euclideanZerothOrderCoeff
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hab) :
    timeReverseLIE T ha hb (euclideanZerothOrderCoeff c) =
      euclideanZerothOrderCoeff (timeReverseLIE T ha hb c) :=
  ext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

/-- Reversing the second-order scalar coefficients in time preserves uniform ellipticity, with the
same constant. -/
theorem ellipticity_timeReverseLIE [DecidableEq ι]
    {c : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hab}
    (hc : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ c i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤
        (Matrix.of fun i j ↦ timeReverseLIE T ha hb (c i j) p).toQuadraticForm' ξ :=
  hc.imp fun _ h ↦ ⟨h.1, fun p ξ ↦ by
    simpa only [timeReverseLIE_apply] using h.2 (slabTimeReverse T ha hb p) ξ⟩

end Euclidean

end ParabolicCkHolderSpace

end TauCeti
