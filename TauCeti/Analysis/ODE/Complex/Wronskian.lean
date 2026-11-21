/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Wronskians of second-order analytic linear equations

For two solutions `y₁, y₂` of a monic second-order equation `y'' + a₁ y' + a₀ y = 0` with
holomorphic coefficients on an open set `U`, the Wronskian is `W = y₁ y₂' - y₁' y₂`. This file
proves Abel's identity `W' = -a₁ W` on `U`, and shows that on a preconnected domain two solutions
are linearly independent exactly when their Wronskian is nonzero at one, equivalently every,
point of the domain. The latter combines the initial-jet map, whose value at a point is the
pair `(y, y')`, with uniqueness of solutions with given initial jet.

Unlike `TauCeti.wronskian_eq_of_hasDerivAt`, which treats globally defined solutions of
`f'' = q f`, the statements here are local to the domain of the equation and allow a
first-derivative term.

## Main results

* `TauCeti.LinearEquation.IsSolution.hasDerivAt_wronskian`: Abel's identity.
* `TauCeti.LinearEquation.linearIndependent_of_wronskian_ne_zero`: solutions whose Wronskian is
  nonzero at a point are linearly independent, and
  `TauCeti.LinearEquation.IsSolution.linearIndependent_of_wronskian_ne_zero` is the same statement
  for solutions given as functions.
* `TauCeti.LinearEquation.linearIndependent_iff_wronskian_ne_zero`: on a preconnected domain the
  converse holds as well.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §3.7.
-/

public noncomputable section

open TopologicalSpace

namespace TauCeti

namespace LinearEquation

variable {U : Opens ℂ} {E : LinearEquation U 2} {y y₁ y₂ : ℂ → ℂ} {z : ℂ}

/-- Solutions of the second-order equation `y'' + a₁ y' + a₀ y = 0` are the functions analytic on
the domain that satisfy it there, written with `deriv` in place of `iteratedDeriv`. -/
theorem isSolution_iff_deriv_deriv :
    E.IsSolution y ↔ AnalyticOnNhd ℂ y U ∧ ∀ z ∈ U, deriv (deriv y) z +
      HolomorphicFunctions.extend (E.coeff 1) z * deriv y z +
        HolomorphicFunctions.extend (E.coeff 0) z * y z = 0 := by
  rw [isSolution_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun z _ ↦ ?_
  simp only [Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, iteratedDeriv_zero,
    iteratedDeriv_one]
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  constructor <;> intro h <;> linear_combination h

/-- A solution of the second-order equation `y'' + a₁ y' + a₀ y = 0` satisfies
`y'' = -(a₁ y') - a₀ y` at every point of the domain. -/
theorem IsSolution.deriv_deriv_eq (hy : E.IsSolution y) (hz : z ∈ U) :
    deriv (deriv y) z = -(HolomorphicFunctions.extend (E.coeff 1) z * deriv y z) -
      HolomorphicFunctions.extend (E.coeff 0) z * y z := by
  linear_combination (isSolution_iff_deriv_deriv.mp hy).2 z hz

/-- **Abel's identity.** The Wronskian `W = y₁ y₂' - y₁' y₂` of two solutions of
`y'' + a₁ y' + a₀ y = 0` satisfies `W' = -a₁ W` at every point of the domain. -/
theorem IsSolution.hasDerivAt_wronskian (hy₁ : E.IsSolution y₁) (hy₂ : E.IsSolution y₂)
    (hz : z ∈ U) :
    HasDerivAt (fun x ↦ y₁ x * deriv y₂ x - deriv y₁ x * y₂ x)
      (-HolomorphicFunctions.extend (E.coeff 1) z *
        (y₁ z * deriv y₂ z - deriv y₁ z * y₂ z)) z := by
  have h₁ := hy₁.analyticOnNhd z hz
  have h₂ := hy₂.analyticOnNhd z hz
  convert (h₁.differentiableAt.hasDerivAt.mul h₂.deriv.differentiableAt.hasDerivAt).sub
    (h₁.deriv.differentiableAt.hasDerivAt.mul h₂.differentiableAt.hasDerivAt) using 1
  rw [hy₁.deriv_deriv_eq hz, hy₂.deriv_deriv_eq hz]
  ring

/-- The initial jets of two solutions are linearly independent exactly when the determinant of
their values and first derivatives is nonzero. -/
private theorem linearIndependent_initialJet_iff {a : ℂ} (ha : a ∈ U) (f g : E.solutionSpace) :
    LinearIndependent ℂ (E.initialJet ha ∘ ![f, g]) ↔
      E.initialJet ha f 0 * E.initialJet ha g 1 -
        E.initialJet ha f 1 * E.initialJet ha g 0 ≠ 0 := by
  have hrow : E.initialJet ha ∘ ![f, g] =
      (Matrix.of ![E.initialJet ha f, E.initialJet ha g]).row := by
    ext i j
    fin_cases i <;> rfl
  rw [hrow, Matrix.linearIndependent_row_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, Matrix.det_fin_two]
  rfl

/-- Two solutions of a second-order equation whose Wronskian is nonzero at some point of the
domain are linearly independent. -/
theorem linearIndependent_of_wronskian_ne_zero {a : ℂ} (ha : a ∈ U) {f g : E.solutionSpace}
    (hW : HolomorphicFunctions.extend f.val a * deriv (HolomorphicFunctions.extend g.val) a -
      deriv (HolomorphicFunctions.extend f.val) a * HolomorphicFunctions.extend g.val a ≠ 0) :
    LinearIndependent ℂ ![f, g] :=
  LinearIndependent.of_comp (E.initialJet ha)
    ((linearIndependent_initialJet_iff ha f g).mpr (by simpa [initialJet_apply] using hW))

/-- Two solutions `y₁, y₂` of a second-order equation whose Wronskian `y₁ y₂' - y₁' y₂` is nonzero
at some point of the domain are linearly independent as elements of the solution space. -/
theorem IsSolution.linearIndependent_of_wronskian_ne_zero (hy₁ : E.IsSolution y₁)
    (hy₂ : E.IsSolution y₂) {a : ℂ} (ha : a ∈ U)
    (hW : y₁ a * deriv y₂ a - deriv y₁ a * y₂ a ≠ 0) :
    LinearIndependent ℂ
      ![hy₁.isCompanionSolution.toSolutionSpace, hy₂.isCompanionSolution.toSolutionSpace] := by
  refine LinearIndependent.of_comp (E.initialJet ha)
    ((linearIndependent_initialJet_iff ha _ _).mpr ?_)
  simpa only [IsCompanionSolution.initialJet_toSolutionSpace, Fin.isValue, Fin.val_zero,
    Fin.val_one, iteratedDeriv_zero, iteratedDeriv_one] using hW

/-- On a preconnected domain, two solutions of a second-order equation are linearly independent
if and only if their Wronskian is nonzero at a given point of the domain. In particular the
Wronskian of two solutions vanishes either everywhere or nowhere on the domain. -/
theorem linearIndependent_iff_wronskian_ne_zero (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) (f g : E.solutionSpace) :
    LinearIndependent ℂ ![f, g] ↔
      HolomorphicFunctions.extend f.val a * deriv (HolomorphicFunctions.extend g.val) a -
        deriv (HolomorphicFunctions.extend f.val) a * HolomorphicFunctions.extend g.val a ≠ 0 := by
  rw [← LinearMap.linearIndependent_iff (E.initialJet ha)
      (LinearMap.ker_eq_bot.mpr (E.initialJet_injective_of_isPreconnected hU ha)),
    linearIndependent_initialJet_iff ha]
  simp [initialJet_apply]

end LinearEquation

end TauCeti
