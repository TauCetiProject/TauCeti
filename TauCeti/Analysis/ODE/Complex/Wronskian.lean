/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
import TauCeti.Analysis.ODE.Complex.ScalarLinear
import TauCeti.Analysis.ODE.Wronskian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Wronskians of second-order analytic linear equations

For two solutions `y₁, y₂` of a monic second-order equation `y'' + a₁ y' + a₀ y = 0` with
holomorphic coefficients on an open set `U`, the Wronskian is `W = y₁ y₂' - y₁' y₂`. This file
proves Abel's identity `W' = -a₁ W` on `U`, and shows that on a preconnected domain two solutions
are linearly independent exactly when their Wronskian is nonzero at one, equivalently every,
point of the domain. The latter combines the initial-jet map, whose value at a point is the
pair `(y, y')`, with uniqueness of solutions with given initial jet.

For the second-order equation `P w'' + Q w' + R w = 0` on a preconnected open set `U ⊆ ℂ`, whose
leading coefficient `P` is nonzero on a dense subset of `U`, the Wronskians of any two solutions
satisfy Abel's identity there, so they are proportional. Hence two solutions whose Wronskian is
nonzero at one point of `U` span all solutions on `U`
(`IsOpen.exists_eq_mul_add_mul_of_secondOrderLinearEquation`). The zeros of `P`, such as the
singular points `0` and `1` of the hypergeometric equation, may lie in `U`.

Unlike `TauCeti.wronskian_eq_of_hasDerivAt`, which treats solutions of `f'' = q f`, the
statements here allow a first-derivative term.

## Main results

* `TauCeti.LinearEquation.IsSolution.hasDerivAt_wronskian`: Abel's identity.
* `TauCeti.LinearEquation.IsSolution.wronskian_eq_of_coeff_one_eq_zero`: without a
  first-derivative term the Wronskian is constant on open preconnected subsets of the domain.
* `TauCeti.LinearEquation.linearIndependent_of_wronskian_ne_zero`: solutions whose Wronskian is
  nonzero at a point are linearly independent, and
  `TauCeti.LinearEquation.IsSolution.linearIndependent_of_wronskian_ne_zero` is the same statement
  for solutions given as functions.
* `TauCeti.LinearEquation.linearIndependent_iff_wronskian_ne_zero`: on a preconnected domain the
  converse holds as well.
* `IsOpen.exists_eq_mul_add_mul_of_secondOrderLinearEquation`: the span criterion for
  `P w'' + Q w' + R w = 0` on a preconnected open set.

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
  exact h₁.differentiableAt.hasDerivAt.wronskian_of_secondOrderLinearEquation
    h₁.deriv.differentiableAt.hasDerivAt h₂.differentiableAt.hasDerivAt
    h₂.deriv.differentiableAt.hasDerivAt ((isSolution_iff_deriv_deriv.mp hy₁).2 z hz)
    ((isSolution_iff_deriv_deriv.mp hy₂).2 z hz)

/-- For an equation `y'' + a₀ y = 0` without first-derivative term, the Wronskian
`y₁ y₂' - y₁' y₂` of two solutions is constant on every open preconnected subset of the domain. -/
theorem IsSolution.wronskian_eq_of_coeff_one_eq_zero (hy₁ : E.IsSolution y₁)
    (hy₂ : E.IsSolution y₂) (hE : E.coeff 1 = 0) {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hVU : V ⊆ U) {x : ℂ} (hx : x ∈ V) (hz : z ∈ V) :
    y₁ x * deriv y₂ x - deriv y₁ x * y₂ x = y₁ z * deriv y₂ z - deriv y₁ z * y₂ z := by
  have hW (x : ℂ) (hx : x ∈ V) :
      HasDerivAt (fun x ↦ y₁ x * deriv y₂ x - deriv y₁ x * y₂ x) 0 x := by
    simpa [hE] using hy₁.hasDerivAt_wronskian hy₂ (hVU hx)
  exact hVo.is_const_of_deriv_eq_zero hVc
    (fun x hx ↦ (hW x hx).differentiableAt.differentiableWithinAt) (fun x hx ↦ (hW x hx).deriv)
    hx hz

/-- The initial jets of two solutions are linearly independent exactly when the determinant of
their values and first derivatives is nonzero. -/
private theorem linearIndependent_initialJet_iff {a : ℂ} (ha : a ∈ U) (f g : E.solutionSpace) :
    LinearIndependent ℂ (E.initialJet ha ∘ ![f, g]) ↔
      E.initialJet ha f 0 * E.initialJet ha g 1 -
        E.initialJet ha f 1 * E.initialJet ha g 0 ≠ 0 := by
  have hrow : E.initialJet ha ∘ ![f, g] =
      (Matrix.of ![E.initialJet ha f, E.initialJet ha g]).row := by
    ext i j
    fin_cases i <;> simp [Matrix.row, Matrix.of_apply]
  rw [hrow, Matrix.linearIndependent_row_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

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

/-- **The span criterion** for a second-order linear equation `P w'' + Q w' + R w = 0` on a
preconnected open set `U ⊆ ℂ` whose leading coefficient `P` is nonzero on `U ∩ S` for a dense
set `S`: if `f₁` and `f₂` are holomorphic on `U`, solve the equation on `U ∩ S`, and have a
Wronskian `𝒲{f₁, f₂}` nonzero at a point `z₀ ∈ U`, then every function `w` holomorphic on `U`
that solves the equation on `U ∩ S` is `A f₁ + B f₂` on `U` with constants `A`, `B`. The
coefficients need not be continuous, and `U` may contain zeros of `P`. -/
theorem _root_.IsOpen.exists_eq_mul_add_mul_of_secondOrderLinearEquation {U S : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hS : Dense S) {P Q R f₁ f₂ w : ℂ → ℂ}
    (hP : ∀ z ∈ U ∩ S, P z ≠ 0)
    (hf₁ : DifferentiableOn ℂ f₁ U) (hf₂ : DifferentiableOn ℂ f₂ U)
    (hw : DifferentiableOn ℂ w U)
    (hf₁' : ∀ z ∈ U ∩ S, P z * deriv (deriv f₁) z + Q z * deriv f₁ z + R z * f₁ z = 0)
    (hf₂' : ∀ z ∈ U ∩ S, P z * deriv (deriv f₂) z + Q z * deriv f₂ z + R z * f₂ z = 0)
    (hw' : ∀ z ∈ U ∩ S, P z * deriv (deriv w) z + Q z * deriv w z + R z * w z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hW : f₁ z₀ * deriv f₂ z₀ - deriv f₁ z₀ * f₂ z₀ ≠ 0) :
    ∃ A B : ℂ, ∀ z ∈ U, w z = A * f₁ z + B * f₂ z := by
  -- On `U ∩ S` every Wronskian of two solutions satisfies Abel's identity, so it is a constant
  -- multiple of `𝒲{f₁, f₂}`, which is nonzero at `z₀`.
  have habel {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hg₁' : ∀ z ∈ U ∩ S, P z * deriv (deriv g₁) z + Q z * deriv g₁ z + R z * g₁ z = 0)
      (hg₂' : ∀ z ∈ U ∩ S, P z * deriv (deriv g₂) z + Q z * deriv g₂ z + R z * g₂ z = 0)
      (z : ℂ) (hz : z ∈ U ∩ S) :
      HasDerivAt (fun ζ ↦ g₁ ζ * deriv g₂ ζ - deriv g₁ ζ * g₂ ζ)
        (-(Q z / P z) * (g₁ z * deriv g₂ z - deriv g₁ z * g₂ z)) z :=
    (hg₁.differentiableAt (hU.mem_nhds hz.1)).hasDerivAt_wronskian_of_secondOrderLinearEquation
      (hP z hz) ((hg₁.deriv hU).differentiableAt (hU.mem_nhds hz.1))
      (hg₂.differentiableAt (hU.mem_nhds hz.1))
      ((hg₂.deriv hU).differentiableAt (hU.mem_nhds hz.1)) (hg₁' z hz) (hg₂' z hz)
  have hW₁₂ := (hf₁.mul (hf₂.deriv hU)).sub ((hf₁.deriv hU).mul hf₂)
  have hratio {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hg₁' : ∀ z ∈ U ∩ S, P z * deriv (deriv g₁) z + Q z * deriv g₁ z + R z * g₁ z = 0)
      (hg₂' : ∀ z ∈ U ∩ S, P z * deriv (deriv g₂) z + Q z * deriv g₂ z + R z * g₂ z = 0) :
      ∃ K : ℂ, ∀ z ∈ U, g₁ z * deriv g₂ z - deriv g₁ z * g₂ z =
        K * (f₁ z * deriv f₂ z - deriv f₁ z * f₂ z) :=
    hU.exists_eq_const_mul_of_hasDerivAt_mul hUc hS
      ((hg₁.mul (hg₂.deriv hU)).sub ((hg₁.deriv hU).mul hg₂)) hW₁₂ hz₀ hW
      (habel hg₁ hg₂ hg₁' hg₂') (habel hf₁ hf₂ hf₁' hf₂')
  obtain ⟨A, hA⟩ := hratio hw hf₂ hw' hf₂'
  obtain ⟨B, hB⟩ := hratio hf₁ hw hf₁' hw'
  -- `𝒲{f₁, f₂} w = 𝒲{f₁, f₂} (A f₁ + B f₂)` on `U`, so `w = A f₁ + B f₂` near `z₀`, where
  -- `𝒲{f₁, f₂}` has no zero; the identity theorem extends this to `U`.
  refine ⟨A, B, fun z hz ↦ (hw.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (((hf₁.const_mul A).add (hf₂.const_mul B)).analyticOnNhd hU) hUc hz₀ ?_ hz⟩
  filter_upwards [((hW₁₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt).eventually_ne hW,
    hU.mem_nhds hz₀] with z hWz hz
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply] at hWz ⊢
  apply mul_right_cancel₀ hWz
  linear_combination f₁ z * hA z hz + f₂ z * hB z hz

end TauCeti
