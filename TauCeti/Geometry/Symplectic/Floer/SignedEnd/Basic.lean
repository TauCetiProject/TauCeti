/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Signed-end Hamiltonians under time reflection

On a punctured Riemann surface or a PSS plane, a cylindrical end carries an orientation sign
`ε ∈ {1, -1}` (`ε * ε = 1`): `ε = 1` on a positive (input) end, where `s → +∞`, and `ε = -1` on a
negative (output) end, where `s → -∞`. Reading a negative end as a positive end via the holomorphic
reflection `(s, t) ↦ (ε s, ε t)` pulls a cylindrical perturbation `H(t) dt` back to `H'(t) dt` for
the signed-end Hamiltonian `H'(t, x) = ε H(ε t, x)` (`TauCeti.Floer.signedHamiltonian`).

This file defines `TauCeti.Floer.signedHamiltonian` for any sign `ε : ℝ` with `ε * ε = 1` and
records its algebraic and regularity properties (involution, periodicity, `C^n` smoothness, and
target differentiability), instantiated for pair-of-pants ends in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart` and for PSS planes in
`TauCeti.Geometry.Symplectic.Floer.Plane.Basic`.
-/

public section

open Function

namespace TauCeti.Floer

/-- Given a sign `ε : ℝ` with `ε * ε = 1`, either `ε = 1` or `ε = -1`. -/
theorem eq_one_or_eq_neg_one_of_mul_self_eq_one {ε : ℝ} (hε : ε * ε = 1) : ε = 1 ∨ ε = -1 :=
  sq_eq_one_iff.1 (by rwa [sq])

/-- Given a sign `ε : ℝ` with `ε * ε = 1`, `|ε| = 1`. -/
theorem abs_eq_one_of_mul_self_eq_one {ε : ℝ} (hε : ε * ε = 1) : |ε| = 1 := by
  rcases eq_one_or_eq_neg_one_of_mul_self_eq_one hε with rfl | rfl <;> norm_num

/-- A `c`-periodic map on `ℝ` composed with `t ↦ ε * t` for `ε * ε = 1` remains `c`-periodic. -/
theorem periodic_comp_mul_of_mul_self_eq_one {α : Type*} {ε c : ℝ} (hε : ε * ε = 1) {x : ℝ → α}
    (hx : Periodic x c) : Periodic (fun t ↦ x (ε * t)) c := by
  rcases eq_one_or_eq_neg_one_of_mul_self_eq_one hε with rfl | rfl
  · simpa using hx
  · simpa using hx.comp_neg

/-- The Hamiltonian `H'(t, x) = ε H(ε t, x)` obtained by reading an end of sign `ε` in positive
end coordinates `(s, t) ↦ (ε s, ε t)`. For `ε = 1` it is `H`; for `ε = -1` it is the
time-reversed Hamiltonian `(t, x) ↦ -H(-t, x)`. -/
def signedHamiltonian (ε : ℝ) {X : Type*} (H : ℝ → X → ℝ) (t : ℝ) (x : X) : ℝ :=
  ε * H (ε * t) x

theorem signedHamiltonian_apply (ε : ℝ) {X : Type*} (H : ℝ → X → ℝ) (t : ℝ) (x : X) :
    signedHamiltonian ε H t x = ε * H (ε * t) x :=
  (rfl)

@[simp]
theorem signedHamiltonian_one {X : Type*} (H : ℝ → X → ℝ) : signedHamiltonian 1 H = H := by
  funext t x
  simp [signedHamiltonian_apply]

theorem signedHamiltonian_neg_one {X : Type*} (H : ℝ → X → ℝ) :
    signedHamiltonian (-1) H = fun t x ↦ -H (-t) x := by
  funext t x
  simp [signedHamiltonian_apply]

/-- Applying `signedHamiltonian ε` twice gives back `H` whenever `ε * ε = 1`. -/
theorem signedHamiltonian_signedHamiltonian {ε : ℝ} (hε : ε * ε = 1) {X : Type*} (H : ℝ → X → ℝ) :
    signedHamiltonian ε (signedHamiltonian ε H) = H := by
  funext t x
  simp [signedHamiltonian_apply, ← mul_assoc, hε]

/-- If `H` has period `c` in `t` and `ε * ε = 1`, then `signedHamiltonian ε H` has period `c`. -/
theorem periodic_signedHamiltonian {ε c : ℝ} (hε : ε * ε = 1) {X : Type*} {H : ℝ → X → ℝ}
    (hH : Periodic H c) : Periodic (signedHamiltonian ε H) c := by
  intro t
  funext x
  simpa [signedHamiltonian_apply] using
    congrArg (ε * · x) (periodic_comp_mul_of_mul_self_eq_one hε hH t)

/-- If `H` is jointly `C^n`, then `signedHamiltonian ε H` is jointly `C^n`. -/
theorem contDiff_uncurry_signedHamiltonian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) {H : ℝ → E → ℝ} {n : WithTop ℕ∞} (hH : ContDiff ℝ n (uncurry H)) :
    ContDiff ℝ n (uncurry (signedHamiltonian ε H)) :=
  contDiff_const.mul (hH.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))

/-- If each `H t` is differentiable, then each `signedHamiltonian ε H t` is differentiable. -/
theorem differentiable_signedHamiltonian_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ε : ℝ) {H : ℝ → E → ℝ} (hHd : ∀ t, Differentiable ℝ (H t)) (t : ℝ) :
    Differentiable ℝ (signedHamiltonian ε H t) :=
  (hHd (ε * t)).const_smul ε

end TauCeti.Floer
