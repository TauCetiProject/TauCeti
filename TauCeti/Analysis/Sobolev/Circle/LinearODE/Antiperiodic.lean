/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic

import TauCeti.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.Topology.Instances.AddCircle.Coe

/-!
# The antiperiodic loop operator in the periodic gauge

Let `E` be a finite-dimensional complex normed space and `S : AddCircle T → (E →L[ℝ] E)` a
continuous loop of real-linear maps, with propagator `Ψ` of `ζ' = S ζ` and return map
`P = Ψ(T)`. Besides the periodic operator `ζ ↦ ζ' - S ζ` of
`TauCeti.CircleSobolev.loopOperator`, the same differential expression acts on *antiperiodic*
loops, `ζ (t + T) = -ζ t`. Its kernel and cokernel are those of `-1 - P`
(`TauCeti.kerTwistedLinearOperatorEquiv`, `TauCeti.quotientRangeTwistedLinearOperatorEquiv`, for
the realization on `C¹` maps). For the normal operator of an orbit torus these are the operators
twisted by the sign character which is `-1` along the orbit. Since `E` is a complex space, its real
dimension is even, so `det (-1 - P) = (-1) ^ dim_ℝ E * det (1 + P) = det (1 + P)`.

Since `E` is a complex space, multiplication by the phase `u(t) = exp (π i t / T)`, which
satisfies `u (t + T) = -u t`, identifies `T`-periodic loops `η` with `T`-antiperiodic loops
`ζ = u η`. Under this identification `ζ' - S ζ = u (η' - Sₐ η)`, where

`Sₐ(t) v = u(t)⁻¹ S(t) (u(t) v) - (π i / T) v`

(`TauCeti.CircleSobolev.antiperiodicGaugeLoop`,
`TauCeti.CircleSobolev.hasDerivAt_antiperiodicGaugeLoop_add_iff`).
The loop `Sₐ` is `T`-periodic: replacing `u` by `-u` does not change the conjugation
`v ↦ u⁻¹ S (u v)`, because `S` is real-linear. So the antiperiodic operator is realized on the
circle Sobolev spaces as the periodic operator `L_Sₐ = loopOperator T Sₐ : H¹(E) → H⁰(E)`, a
Fredholm operator of index zero (`TauCeti.CircleSobolev.isFredholm_loopOperator`,
`TauCeti.CircleSobolev.index_loopOperator`).

This file computes the propagator and the invertibility of this realization:

* the propagator of `Sₐ` is `Ψₐ(t) = u(t)⁻¹ Ψ(t)`, so the return map of `Sₐ` is `-P`
  (`TauCeti.CircleSobolev.dysonSeriesLeft_antiperiodicGaugeLoop_apply`,
  `TauCeti.CircleSobolev.dysonSeriesLeft_antiperiodicGaugeLoop_period`). Statements about the
  periodic operator `L_Sₐ` phrased through `1 - Ψₐ(T)` are therefore statements about `1 + P`;
* the kernel of `L_Sₐ` consists of the `η ∈ H¹` whose continuous representative, multiplied by
  `u`, solves `ζ' = S ζ` (`TauCeti.CircleSobolev.loopOperator_antiperiodicGaugeLoop_eq_zero_iff`);
* `L_Sₐ` is invertible exactly when `ζ' = S ζ` has no nonzero continuous antiperiodic solution
  (`TauCeti.CircleSobolev.isInvertible_loopOperator_antiperiodicGaugeLoop_iff`), that is,
  exactly when `det (1 + P) ≠ 0`
  (`TauCeti.CircleSobolev.isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero`,
  from `TauCeti.CircleSobolev.isInvertible_loopOperator_iff_det_ne_zero` applied to `Sₐ`), and
  equivalently when `det (-1 - P) ≠ 0`
  (`TauCeti.CircleSobolev.isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_ne_zero`).

## Main definitions

* `TauCeti.CircleSobolev.antiperiodicGaugeLoop T S`: the periodic loop `Sₐ`.

## Main statements

* `TauCeti.CircleSobolev.antiperiodicGaugeLoop_apply_coe`: the formula for `Sₐ(t)`.
* `TauCeti.CircleSobolev.hasDerivAt_antiperiodicGaugeLoop_add_iff`,
  `TauCeti.CircleSobolev.hasDerivAt_antiperiodicGaugeLoop_iff`: `η' = Sₐ η + f` exactly when
  `(u η)' = S (u η) + u f`, and its homogeneous case `f = 0`.
* `TauCeti.CircleSobolev.dysonSeriesLeft_antiperiodicGaugeLoop_apply`,
  `TauCeti.CircleSobolev.dysonSeriesLeft_antiperiodicGaugeLoop_period`: `Ψₐ(t) = u(t)⁻¹ Ψ(t)` and
  `Ψₐ(T) = -Ψ(T)`.
* `TauCeti.CircleSobolev.loopOperator_antiperiodicGaugeLoop_eq_zero_iff`: the kernel of `L_Sₐ`.
* `TauCeti.CircleSobolev.isInvertible_loopOperator_antiperiodicGaugeLoop_iff`,
  `TauCeti.CircleSobolev.isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_ne_zero`,
  `TauCeti.CircleSobolev.isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero`:
  the Fredholm alternative for the antiperiodic operator.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (the operators of an orbit torus twisted by its sign characters).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂_t + S` on `W^{1,2}(S¹)`).
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : ℝ)

/-! ### The phase `u(t) = exp (π i t / T)` -/

private theorem phase_zero : cexp (↑(π / T * 0) * I) = 1 := by simp

private theorem hasDerivAt_phase (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ cexp (↑(π / T * t) * I))
      (cexp (↑(π / T * t) * I) * (↑(π / T) * I)) t := by
  simpa using (((hasDerivAt_id t).const_mul (π / T)).ofReal_comp.mul_const I).cexp

private theorem continuous_phase : Continuous fun t : ℝ ↦ cexp (↑(π / T * t) * I) := by
  fun_prop

/-! ### The periodic loop `Sₐ` -/

/-- The loop `t ↦ u(t)⁻¹ S(t) (u(t) ·) - (π i / T)` on `ℝ`, with `u(t) = exp (π i t / T)`. -/
private def gaugeFun (S : C(AddCircle T, E →L[ℝ] E)) (t : ℝ) : E →L[ℝ] E :=
  (cexp (↑(π / T * t) * I))⁻¹ •
      (S t).comp (cexp (↑(π / T * t) * I) • ContinuousLinearMap.id ℝ E) -
    (↑(π / T) * I) • ContinuousLinearMap.id ℝ E

private theorem gaugeFun_apply (S : C(AddCircle T, E →L[ℝ] E)) (t : ℝ) (v : E) :
    gaugeFun T S t v = (cexp (↑(π / T * t) * I))⁻¹ • S t (cexp (↑(π / T * t) * I) • v) -
      (↑(π / T) * I) • v := by
  simp [gaugeFun]

private theorem continuous_gaugeFun (S : C(AddCircle T, E →L[ℝ] E)) :
    Continuous (gaugeFun T S) := by
  have hu := continuous_phase T
  exact ((hu.inv₀ fun _ ↦ exp_ne_zero _).smul
    ((AddCircle.continuous_comp_coe S).clm_comp (hu.smul continuous_const))).sub
      continuous_const

variable [hT : Fact (0 < T)]

private theorem phase_add_period (t : ℝ) :
    cexp (↑(π / T * (t + T)) * I) = -cexp (↑(π / T * t) * I) := by
  have hT0 : T ≠ 0 := hT.out.ne'
  have h : π / T * (t + T) = π / T * t + π := by field_simp
  rw [h, ofReal_add, add_mul]
  exact exp_antiperiodic _

private theorem phase_period : cexp (↑(π / T * T) * I) = -1 := by
  simpa [phase_zero] using phase_add_period T 0

/-- `Sₐ` is periodic: replacing `u` by `-u` does not change the conjugation by `u`, because `S` is
real-linear. -/
private theorem periodic_gaugeFun (S : C(AddCircle T, E →L[ℝ] E)) :
    Function.Periodic (gaugeFun T S) T := fun t ↦ by
  ext v
  simp only [gaugeFun_apply, phase_add_period, AddCircle.coe_add_period]
  simp

/-- **The antiperiodic operator in the periodic gauge.** For a continuous loop `S` of real-linear
maps of a complex space `E`, the `T`-periodic loop

`Sₐ(t) v = u(t)⁻¹ S(t) (u(t) v) - (π i / T) v`,  `u(t) = exp (π i t / T)`.

Multiplication by `u` identifies `T`-periodic loops `η` with `T`-antiperiodic loops `u η`, and
`(u η)' - S (u η) = u (η' - Sₐ η)`
(`TauCeti.CircleSobolev.hasDerivAt_antiperiodicGaugeLoop_add_iff`),
so the periodic operator `loopOperator T (antiperiodicGaugeLoop T S)` realizes `ζ ↦ ζ' - S ζ` on
antiperiodic loops. -/
def antiperiodicGaugeLoop (S : C(AddCircle T, E →L[ℝ] E)) : C(AddCircle T, E →L[ℝ] E) :=
  ⟨(periodic_gaugeFun T S).lift, continuous_coinduced_dom.2 (continuous_gaugeFun T S)⟩

/-- The value of `Sₐ` at a real time `t`. -/
@[simp]
theorem antiperiodicGaugeLoop_apply_coe (S : C(AddCircle T, E →L[ℝ] E)) (t : ℝ) (v : E) :
    antiperiodicGaugeLoop T S t v =
      (cexp (↑(π / T * t) * I))⁻¹ • S t (cexp (↑(π / T * t) * I) • v) -
        (↑(π / T) * I) • v := by
  rw [← gaugeFun_apply, antiperiodicGaugeLoop, ContinuousMap.coe_mk, Function.Periodic.lift_coe]

/-- The periodic gauge `Sₐ` of a loop of complex-linear maps is a loop of complex-linear maps. -/
theorem antiperiodicGaugeLoop_apply_I_smul {S : C(AddCircle T, E →L[ℝ] E)}
    (hS : ∀ t v, S t (I • v) = I • S t v) (t : AddCircle T) (v : E) :
    antiperiodicGaugeLoop T S t (I • v) = I • antiperiodicGaugeLoop T S t v := by
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    simp only [antiperiodicGaugeLoop_apply_coe, smul_sub]
    rw [smul_comm _ I v, hS, smul_comm _ I, smul_comm _ I v]

/-! ### Solutions -/

/-- **The gauge identity.** With `u(t) = exp (π i t / T)`, a map `η : ℝ → E` satisfies
`η' = Sₐ η + f` at `x` exactly when `u η` satisfies `(u η)' = S (u η) + u f` at `x`. -/
theorem hasDerivAt_antiperiodicGaugeLoop_add_iff (S : C(AddCircle T, E →L[ℝ] E)) {η : ℝ → E}
    {f : E} {x : ℝ} :
    HasDerivAt η (antiperiodicGaugeLoop T S x (η x) + f) x ↔
      HasDerivAt (fun t ↦ cexp (↑(π / T * t) * I) • η t)
        (S x (cexp (↑(π / T * x) * I) • η x) + cexp (↑(π / T * x) * I) • f) x := by
  rw [antiperiodicGaugeLoop_apply_coe,
    ← (hasDerivAt_phase T x).hasDerivAt_iff_hasDerivAt_smul (exp_ne_zero _), smul_add,
    inv_smul_smul₀ (exp_ne_zero _), add_sub_right_comm]

/-- **The homogeneous gauge identity.** With `u(t) = exp (π i t / T)`, a map `η : ℝ → E`
satisfies `η' = Sₐ η` at `x` exactly when `u η` satisfies `(u η)' = S (u η)` at `x`. -/
theorem hasDerivAt_antiperiodicGaugeLoop_iff (S : C(AddCircle T, E →L[ℝ] E)) {η : ℝ → E}
    {x : ℝ} :
    HasDerivAt η (antiperiodicGaugeLoop T S x (η x)) x ↔
      HasDerivAt (fun t ↦ cexp (↑(π / T * t) * I) • η t)
        (S x (cexp (↑(π / T * x) * I) • η x)) x := by
  rw [antiperiodicGaugeLoop_apply_coe]
  exact (hasDerivAt_phase T x).hasDerivAt_iff_hasDerivAt_smul (exp_ne_zero _)

variable [FiniteDimensional ℂ E]

/-- A finite-dimensional complex space is complete, as needed for propagators. -/
local instance instCompleteSpaceAntiperiodic : CompleteSpace E :=
  FiniteDimensional.completeSpace ℂ E

/-- **The propagator of `Sₐ`.** With `Ψ` and `Ψₐ` the propagators of `ζ' = S ζ` and
`η' = Sₐ η`, `Ψₐ(t) = u(t)⁻¹ Ψ(t)` for `u(t) = exp (π i t / T)`. -/
theorem dysonSeriesLeft_antiperiodicGaugeLoop_apply (S : C(AddCircle T, E →L[ℝ] E)) (t : ℝ)
    (v : E) :
    dysonSeriesLeft (fun t : ℝ ↦ antiperiodicGaugeLoop T S t) t v =
      (cexp (↑(π / T * t) * I))⁻¹ • dysonSeriesLeft (fun t : ℝ ↦ S t) t v := by
  set w : ℝ → E := fun t ↦ (cexp (↑(π / T * t) * I))⁻¹ • dysonSeriesLeft (fun t : ℝ ↦ S t) t v
  have hw (x : ℝ) : HasDerivAt w (antiperiodicGaugeLoop T S x (w x)) x := by
    simp only [hasDerivAt_antiperiodicGaugeLoop_iff, w, smul_inv_smul₀ (exp_ne_zero _)]
    exact hasDerivAt_dysonSeriesLeft_apply (AddCircle.continuous_comp_coe S) v x
  have h :=
    eq_dysonSeriesLeft_apply (AddCircle.continuous_comp_coe (antiperiodicGaugeLoop T S)) hw t
  have hw0 : w 0 = v := by simp [w, dysonSeriesLeft_zero]
  rw [hw0] at h
  exact h.symm

/-- **The return map of `Sₐ` is `-P`.** The propagator of `Sₐ` over one period is the negative of
the return map `P = Ψ(T)` of `ζ' = S ζ`, so `1 - Ψₐ(T) = 1 + P`. -/
theorem dysonSeriesLeft_antiperiodicGaugeLoop_period (S : C(AddCircle T, E →L[ℝ] E)) :
    dysonSeriesLeft (fun t : ℝ ↦ antiperiodicGaugeLoop T S t) T =
      -dysonSeriesLeft (fun t : ℝ ↦ S t) T := by
  ext v
  rw [dysonSeriesLeft_antiperiodicGaugeLoop_apply, phase_period]
  simp

/-! ### The Sobolev realization -/

/-- **The kernel of the antiperiodic operator.** An element `a ∈ H¹(E)` lies in the kernel of
`η ↦ η' - Sₐ η` exactly when its continuous representative `η`, multiplied by
`u(t) = exp (π i t / T)`, solves `ζ' = S ζ`. -/
theorem loopOperator_antiperiodicGaugeLoop_eq_zero_iff (S : C(AddCircle T, E →L[ℝ] E))
    (a : CircleSobolev 1 E) :
    loopOperator T (antiperiodicGaugeLoop T S) a = 0 ↔ ∀ x : ℝ,
      HasDerivAt (fun y : ℝ ↦ cexp (↑(π / T * y) * I) • toContinuousMap T (by norm_num) a y)
        (S x (cexp (↑(π / T * x) * I) • toContinuousMap T (by norm_num) a x)) x := by
  rw [loopOperator_eq_zero_iff]
  exact forall_congr' fun x ↦ hasDerivAt_antiperiodicGaugeLoop_iff T S

/-- **Invertibility of the antiperiodic operator.** The realization `L_Sₐ : H¹(E) → H⁰(E)` of
`ζ ↦ ζ' - S ζ` on antiperiodic loops is invertible exactly when `ζ' = S ζ` has no nonzero
continuous `T`-antiperiodic solution. -/
theorem isInvertible_loopOperator_antiperiodicGaugeLoop_iff (S : C(AddCircle T, E →L[ℝ] E)) :
    (loopOperator T (antiperiodicGaugeLoop T S)).IsInvertible ↔
      ∀ ζ : ℝ → E, Continuous ζ → Function.Antiperiodic ζ T →
        (∀ x : ℝ, HasDerivAt ζ (S x (ζ x)) x) → ζ = 0 := by
  rw [isInvertible_loopOperator_iff]
  constructor
  · intro h ζ hζc hζa hζ
    -- `u⁻¹ ζ` is periodic, so it descends to a continuous loop solving `η' = Sₐ η`.
    set η : ℝ → E := fun t ↦ (cexp (↑(π / T * t) * I))⁻¹ • ζ t
    have hηp : Function.Periodic η T := fun t ↦ by
      simp only [η, phase_add_period, hζa t, inv_neg, neg_smul, smul_neg, neg_neg]
    have hηc : Continuous η :=
      ((continuous_phase T).inv₀ fun _ ↦ exp_ne_zero _).smul hζc
    set ηc : C(AddCircle T, E) := ⟨hηp.lift, continuous_coinduced_dom.2 hηc⟩
    have hηc_coe (t : ℝ) : ηc t = η t := hηp.lift_coe t
    have huη (t : ℝ) : cexp (↑(π / T * t) * I) • η t = ζ t := smul_inv_smul₀ (exp_ne_zero _) _
    have hsol (x : ℝ) : HasDerivAt (fun y : ℝ ↦ ηc y) (antiperiodicGaugeLoop T S x (ηc x)) x := by
      simp only [hηc_coe, hasDerivAt_antiperiodicGaugeLoop_iff, huη]
      exact hζ x
    have h0 := h ηc hsol
    funext t
    rw [← huη t, ← hηc_coe, h0, ContinuousMap.zero_apply, smul_zero, Pi.zero_apply]
  · intro h η hη
    -- `u η` is an antiperiodic solution of `ζ' = S ζ`.
    have hsol (x : ℝ) : HasDerivAt (fun y ↦ cexp (↑(π / T * y) * I) • η y)
        (S x (cexp (↑(π / T * x) * I) • η x)) x :=
      (hasDerivAt_antiperiodicGaugeLoop_iff T S).1 (hη x)
    have h0 := h (fun y : ℝ ↦ cexp (↑(π / T * y) * I) • η y)
      ((continuous_phase T).smul (AddCircle.continuous_comp_coe η))
      (fun t ↦ by simp only [phase_add_period, AddCircle.coe_add_period, neg_smul]) hsol
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      have ht := congrFun h0 t
      simp only [Pi.zero_apply, smul_eq_zero, exp_ne_zero, false_or] at ht
      exact ht

/-- **The Fredholm alternative for the antiperiodic operator.** The realization
`L_Sₐ : H¹(E) → H⁰(E)` of `ζ ↦ ζ' - S ζ` on antiperiodic loops is invertible exactly when
`det (1 + P) ≠ 0`, where `P = Ψ(T)` is the return map of `ζ' = S ζ`: the return map of `Sₐ` is
`-P`. -/
theorem isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero
    (S : C(AddCircle T, E →L[ℝ] E)) :
    (loopOperator T (antiperiodicGaugeLoop T S)).IsInvertible ↔
      LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) ≠ 0 := by
  rw [isInvertible_loopOperator_iff_det_ne_zero, dysonSeriesLeft_antiperiodicGaugeLoop_period,
    ContinuousLinearMap.toLinearMap_neg, sub_neg_eq_add]

/-- **The Fredholm alternative in the form `det (-1 - P)`.** The realization
`L_Sₐ : H¹(E) → H⁰(E)` of `ζ ↦ ζ' - S ζ` on antiperiodic loops is invertible exactly when
`det (-1 - P) ≠ 0`, where `P = Ψ(T)` is the return map of `ζ' = S ζ`. Since `E` is a complex
space, its real dimension is even, so `det (-1 - P) = det (1 + P)`. -/
theorem isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_ne_zero
    (S : C(AddCircle T, E →L[ℝ] E)) :
    (loopOperator T (antiperiodicGaugeLoop T S)).IsInvertible ↔
      LinearMap.det ((-1 : ℝ) • 1 -
        (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) ≠ 0 := by
  rw [isInvertible_loopOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero, neg_one_smul,
    ← neg_add', LinearMap.det_neg_of_complex]

end CircleSobolev

end TauCeti
