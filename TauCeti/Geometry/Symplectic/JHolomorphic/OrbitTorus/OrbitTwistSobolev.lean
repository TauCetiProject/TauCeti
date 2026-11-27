/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Antiperiodic
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicSobolev
import TauCeti.Data.SignType.Basic

/-!
# The orbit-torus operator twisted along the orbit

Let `γ` be a closed orbit of the suspension flow of a surface diffeomorphism and `C = S¹ × γ` its
orbit torus in `S¹ × Y_φ`. In a unitary trivialization of the normal bundle, the normal operator of
`C` is

`D u = ∂s u + A u`,  `A ζ = J₀ (ζ' - S ζ)`,

where `A` acts on loops in the coordinate `t` of period `T`, `J₀` is multiplication by `I` on the
fibre `F` and `S` is a loop of real-linear maps, infinitesimally symplectic for `Im ⟪·, ·⟫`; the
return map of `w' = S w` is `P = Ψ(T)`. Of the four real sign characters of the torus, the one
twisted along `γ` only makes `D` act on maps periodic of period `ℓ` in `s` and antiperiodic in `t`,
`u (s, t + T) = -u (s, t)`. The operator untwisted along `γ` is compared with `det (1 - P)` in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicSobolev`; this file compares the one
twisted along `γ` with `det (1 + P)`.

**The realization.** Multiplication by the phase `u(t) = exp (π i t / T)`, which changes sign over
one period, identifies maps periodic in `t` with maps antiperiodic in `t`. It commutes with `∂s`
and with `J₀`, and `ζ' - S ζ = u (η' - Sₐ η)` for `ζ = u η`, where `Sₐ` is the periodic loop
`TauCeti.CircleSobolev.antiperiodicGaugeLoop T S`
(`TauCeti.CircleSobolev.hasDerivAt_antiperiodicGaugeLoop_add_iff`). So the twisted operator is
realized on Sobolev spaces of maps periodic in both variables as
`periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)`, the operator `∂s + J₀ (∂t - Sₐ)`. The
loop `Sₐ` is infinitesimally symplectic with `S`
(`TauCeti.CircleSobolev.im_inner_antiperiodicGaugeLoop_add_eq_zero`), so every result of
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicSobolev` applies to it: it is
Fredholm of index zero (`TauCeti.isFredholm_periodicTorusOperator`,
`TauCeti.index_periodicTorusOperator`). The return map of `Sₐ` is `-P`
(`TauCeti.CircleSobolev.dysonSeriesLeft_antiperiodicGaugeLoop_period`), so `1 - Ψₐ(T) = 1 + P`.

**The comparison with `det (1 + P)`.**

* Its kernel consists of the maps `(a, 0)` independent of `s` for which `exp (π i t / T) a(t)` is an
  antiperiodic solution of `ζ' = S ζ`
  (`TauCeti.periodicTorusOperator_antiperiodicGaugeLoop_eq_zero_iff`).
* Its determinant line is identified with that of the endomorphism `1 + P` of `F`
  (`TauCeti.detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`).
* It is invertible exactly when `det (1 + P) ≠ 0`
  (`TauCeti.isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero`).
* When it is invertible, the orientation of its determinant line induced by `1 + P` and the one
  given by bijectivity differ by the sign of `det (1 + P)`
  (`TauCeti.sign_detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`).

**The reference operator.** For `S = 0` the loop `Sₐ` is the constant `-(π i / T)`
(`TauCeti.CircleSobolev.antiperiodicGaugeLoop_zero`), and the twisted operator
`∂s + J₀ (∂t + π i / T)` is complex linear
(`TauCeti.periodicTorusOperator_antiperiodicGaugeLoop_zero_apply_smul`) and invertible
(`TauCeti.isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_zero`), since `P = 1` and
`det (1 + 1) > 0`. The loop `Sₐ` depends continuously on `S`
(`TauCeti.CircleSobolev.continuous_antiperiodicGaugeLoop`), so along `τ ↦ τ S` the twisted
operators form a continuous path of Fredholm operators from this complex-linear reference to `D`.

## Main results

* `TauCeti.periodicTorusOperator_antiperiodicGaugeLoop_eq_zero_iff`: the kernel of the twisted
  operator.
* `TauCeti.detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`: its determinant line is that of
  `1 + P`.
* `TauCeti.isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero`: it is
  invertible exactly when `det (1 + P) ≠ 0`.
* `TauCeti.detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`,
  `TauCeti.sign_detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`: for
  bijective operators, the two orientations of the determinant line differ by the sign of
  `det (1 + P)`.
* `TauCeti.periodicTorusOperator_antiperiodicGaugeLoop_zero_apply_smul`,
  `TauCeti.isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_zero`: the reference operator is
  complex linear and invertible.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the twisted normal operators of tori and their
  determinant signs).
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂t + S` and the return map).
-/

public section

noncomputable section

open Complex
open LinearMap (ker range)
open scoped Real

namespace TauCeti

open CircleSobolev

section Operator

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceOrbitTwistSobolev : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- **The twisted reference operator is complex linear.** For `S = 0` the operator
`∂s + J₀ (∂t + π i / T)` on maps periodic in `s` and antiperiodic in `t` commutes with
multiplication by complex scalars, the complex structure of the Sobolev spaces acting by `J₀`. -/
theorem periodicTorusOperator_antiperiodicGaugeLoop_zero_apply_smul (ℓ : ℝ) (c : ℂ)
    (x : CircleSobolev 1 F × torusModeSobolev F (periodicModeFrequency ℓ)) :
    periodicTorusOperator T ℓ (antiperiodicGaugeLoop T 0) (c • x) =
      c • periodicTorusOperator T ℓ (antiperiodicGaugeLoop T 0) x := by
  rw [antiperiodicGaugeLoop_zero]
  exact periodicTorusOperator_apply_smul T ℓ (loopOperator_const_smul_id_apply_smul T _) c x

end Operator

section Inner

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {ℓ : ℝ}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceOrbitTwistSobolevInner : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- **The kernel of the operator twisted along the orbit.** For `ℓ ≠ 0` and an infinitesimally
symplectic loop `S`, an element `x = (a, y)` of the domain lies in the kernel of
`∂s + J₀ (∂t - Sₐ)` exactly when it has no modes of nonzero frequency along `s`, `y = 0`, and the
continuous representative of `a`, multiplied by `exp (π i t / T)`, solves `ζ' = S ζ`. That product
is antiperiodic in `t`, so the kernel is the space of antiperiodic solutions of `ζ' = S ζ`. -/
theorem periodicTorusOperator_antiperiodicGaugeLoop_eq_zero_iff (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (x : CircleSobolev 1 F × torusModeSobolev F (periodicModeFrequency ℓ)) :
    periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S) x = 0 ↔ x.2 = 0 ∧ ∀ t : ℝ,
      HasDerivAt (fun y : ℝ ↦ cexp (↑(π / T * y) * I) • toContinuousMap T (by norm_num) x.1 y)
        (S t (cexp (↑(π / T * t) * I) • toContinuousMap T (by norm_num) x.1 t)) t := by
  have hinj := (isInvertible_torusModeOperator_periodic T hℓ _
    (im_inner_antiperiodicGaugeLoop_add_eq_zero T hS)).injective
  rw [periodicTorusOperator_apply, Prod.mk_eq_zero, smul_eq_zero, map_eq_zero_iff _ hinj,
    loopOperator_antiperiodicGaugeLoop_eq_zero_iff]
  simp only [I_ne_zero, false_or]
  exact and_comm

/-- **The determinant line of the operator twisted along the orbit.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the determinant line of `∂s + J₀ (∂t - Sₐ)` on maps periodic
in `s` (`TauCeti.detLinePeriodicTorusOperatorEquiv` for the loop `Sₐ`) is identified with the
determinant line of `1 - Ψₐ(T) = 1 + P`, where `P = Ψ(T)` and `Ψ = TauCeti.dysonSeriesLeft S`
(`TauCeti.CircleSobolev.one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period`). -/
def detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap.detLine ≃ₗ[ℝ]
      (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLine :=
  (detLinePeriodicTorusOperatorEquiv T hℓ _ (im_inner_antiperiodicGaugeLoop_add_eq_zero T hS)).trans
    (LinearMap.detLineCongrOfEq (one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period T S))

/-- `TauCeti.detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv` is the identification of the
determinant line with that of `1 - Ψₐ(T)`, followed by the equality `1 - Ψₐ(T) = 1 + P`. -/
theorem detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv_apply (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (x : (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap.detLine) :
    detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv T hℓ S hS x =
      LinearMap.detLineCongrOfEq (one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period T S)
        (detLinePeriodicTorusOperatorEquiv T hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero T hS) x) :=
  (rfl)

/-- **The Fredholm alternative for the operator twisted along the orbit.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the operator `∂s + J₀ (∂t - Sₐ)` is invertible exactly when
`det (1 + P) ≠ 0`, where `P = Ψ(T)`. In the geometric application, the normal operator of an orbit
torus twisted along the orbit only is invertible exactly when the linearized return map of the
orbit does not have `-1` as an eigenvalue. -/
theorem isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero
    (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).IsInvertible ↔
      LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)) ≠ 0 := by
  rw [isInvertible_periodicTorusOperator_iff_det_ne_zero T hℓ _
    (im_inner_antiperiodicGaugeLoop_add_eq_zero T hS),
    one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period]

/-- **The twisted reference operator is invertible.** For `ℓ ≠ 0` the operator
`∂s + J₀ (∂t + π i / T)` on maps periodic in `s` and antiperiodic in `t` is invertible: for `S = 0`
the return map is `P = 1`, and `det (1 + 1) = 2 ^ dim_ℝ F ≠ 0`. -/
theorem isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_zero (hℓ : ℓ ≠ 0) :
    (periodicTorusOperator T ℓ
      (antiperiodicGaugeLoop T (0 : C(AddCircle T, F →L[ℝ] F)))).IsInvertible := by
  rw [isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero T hℓ 0
    (fun _ _ _ ↦ by simp)]
  have hΨ : dysonSeriesLeft (fun t : ℝ ↦ (0 : C(AddCircle T, F →L[ℝ] F)) t) T = 1 := by
    simp [dysonSeriesLeft_const]
  rw [hΨ, ContinuousLinearMap.toLinearMap_one, ← two_smul ℝ (1 : F →ₗ[ℝ] F), LinearMap.det_smul,
    map_one, mul_one]
  exact pow_ne_zero _ two_ne_zero

/-- **The determinant line of a nondegenerate operator twisted along the orbit.** Let
`∂s + J₀ (∂t - Sₐ)` be bijective, equivalently `det (1 + P) ≠ 0`. Transporting its determinant
line to that of `1 + P` (`TauCeti.detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`) and
applying the canonical trivialization of the determinant line of an endomorphism
(`LinearMap.detLineEndEquiv`) gives `(det (1 + P))⁻¹` times the trivialization of the determinant
line of the bijective operator (`LinearMap.detLineEquivOfBijective`). -/
theorem detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hD : Function.Bijective (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap)
    (x : (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap.detLine) :
    LinearMap.detLineEndEquiv (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
        (detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv T hℓ S hS x) =
      (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)))⁻¹ *
        (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap.detLineEquivOfBijective
          hD x := by
  rw [detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv_apply,
    LinearMap.detLineEndEquiv_detLineCongrOfEq,
    detLineEndEquiv_detLinePeriodicTorusOperatorEquiv T hℓ _ _ hD x,
    one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period]

/-- **The orientation sign of a nondegenerate operator twisted along the orbit.** In the situation
of `TauCeti.detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv`, the
orientation of the determinant line of `∂s + J₀ (∂t - Sₐ)` induced by the canonical trivialization
for `1 + P` and the orientation given by bijectivity differ by the sign of `det (1 + P)`. -/
theorem sign_detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hD : Function.Bijective (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap)
    (x : (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T S)).toLinearMap.detLine) :
    SignType.sign (LinearMap.detLineEndEquiv
          (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
          (detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv T hℓ S hS x)) =
      SignType.sign (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))) *
        SignType.sign ((periodicTorusOperator T ℓ
          (antiperiodicGaugeLoop T S)).toLinearMap.detLineEquivOfBijective hD x) := by
  rw [detLineEndEquiv_detLinePeriodicTorusOperatorAntiperiodicGaugeLoopEquiv T hℓ S hS hD x,
    sign_mul, TauCeti.sign_inv]

end Inner

end TauCeti
