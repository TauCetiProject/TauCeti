/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.OrbitTwistSobolev
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicOrientation

/-!
# The orbit-torus operators on covers along the orbit

Let `γ` be a closed orbit of the suspension flow of a surface diffeomorphism and `C = S¹ × γ` its
orbit torus in `S¹ × Y_φ`. In a unitary trivialization of the normal bundle, the normal operator of
`C` is `D = ∂s + J₀ (∂t - S)` for a loop `S` of period `T` along `γ`, infinitesimally symplectic for
`Im ⟪·, ·⟫`, with return map `P = Ψ(T)` of `ζ' = S ζ`. The operators twisted by the real sign
characters of `C` that are trivial on the circle factor have determinant signs `sgn det (1 - P)`
and `sgn det (1 + P)`
(`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det` and its twisted
version).

Taubes's weighted count also needs the twisted normal operators on the finite covers of `C`, which
carry the multiply covered tori. The `n`-fold cover of `C` along `γ` is the orbit torus of `γ`
traversed `n` times: its normal operator is the same operator for the loop `S` read with period
`n T`, that is, for the pullback `AddCircle.coverPullback n S` of `S` along the `n`-sheeted
covering `ℝ / n T ℤ → ℝ / T ℤ`. Its return map is `P ^ n`
(`TauCeti.dysonSeriesLeft_coverPullback`). This file transfers the Fredholm alternative and the
determinant signs to these covers:

* the pulled-back loop is again infinitesimally symplectic
  (`TauCeti.im_inner_coverPullback_add_eq_zero`), and complex linear when `S` is
  (`TauCeti.coverPullback_apply_I_smul`);
* on the `n`-fold cover, the untwisted operator is invertible exactly when `det (1 - P ^ n) ≠ 0`
  (`TauCeti.isInvertible_periodicTorusOperator_coverPullback_iff_det_ne_zero`), and the operator
  twisted along the orbit of the cover exactly when `det (1 + P ^ n) ≠ 0`, see
  `isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_coverPullback_iff_det_one_add_ne_zero`;
* the complex orientation, transported along a path of loops to these operators, has sign
  `sgn det (1 - P ^ n)` on the untwisted operator of the cover
  (`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det`) and
  `sgn det (1 + P ^ n)` on the operator twisted along its orbit, see
`sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det`

The sign character of `C` that is nontrivial on `γ` only pulls back to the `n`-fold cover as the
character with sign `(-1) ^ n` along the orbit of the cover. Its operator, the pullback of the
operator of `C` twisted along `γ`, has return map `(-P) ^ n` and determinant sign
`sgn det (1 - (-P) ^ n)`; the theorem
`sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_antiperiodicGaugeLoop_eq_sign_det`
states this. For the double cover the untwisted sign is the product of the two signs of `C`
trivial on the circle factor, `sgn det (1 - P ^ 2) = sgn det (1 - P) · sgn det (1 + P)`
(`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_two_eq_sign_mul_sign`),
the analytic counterpart of `TauCeti.orbitTorusTwistSign_sq_zero`.

The covers along the circle factor need nothing new: the results for the operators periodic of
period `ℓ` in `s` hold for every `ℓ ≠ 0`, in particular for `k ℓ`, so the statements here cover
every cover whose deck group is spanned by `(k ℓ, 0)` and `(0, n T)`. The covers whose deck group is
not spanned by translations along the two factors are treated in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.SkewCover` (`TauCeti.skewTorusOperator`).

## Main results

* The Fredholm alternative on the `n`-fold cover along the orbit:
  `TauCeti.isInvertible_periodicTorusOperator_coverPullback_iff_det_ne_zero` and
  `isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_coverPullback_iff_det_one_add_ne_zero`
* The determinant signs `sgn det (1 ∓ P ^ n)` on the `n`-fold cover:
  `TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det` and
`sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det`
* The sign `sgn det (1 - (-P) ^ n)` of the pullback of the operator twisted along the orbit:
`sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_antiperiodicGaugeLoop_eq_sign_det`
* The double cover law:
  `TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_two_eq_sign_mul_sign`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the twisted normal operators of tori and of their
  multiple covers).
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158, Section 3 (the return maps `P ^ n` of the iterated orbits and their signs).
-/

public section

noncomputable section

open Complex
open Set (uIcc left_mem_uIcc right_mem_uIcc)
open scoped Real lp

namespace TauCeti

open CircleSobolev

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ℓ : ℝ}

/-! ### The pulled-back loop -/

section Loop

variable {T : ℝ} (n : ℕ)

/-- The pullback of an infinitesimally symplectic loop to the `n`-fold cover is infinitesimally
symplectic. -/
theorem im_inner_coverPullback_add_eq_zero {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (t : AddCircle ((n : ℝ) * T)) (v w : F) :
    (inner ℂ (AddCircle.coverPullback n S t v) w).im +
      (inner ℂ v (AddCircle.coverPullback n S t w)).im = 0 := by
  rw [AddCircle.coverPullback_apply]
  exact hS _ v w

/-- The pullback of a loop of complex-linear maps to the `n`-fold cover is a loop of
complex-linear maps. -/
theorem coverPullback_apply_I_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : C(AddCircle T, E →L[ℝ] E)} (hS : ∀ t v, S t (I • v) = I • S t v)
    (t : AddCircle ((n : ℝ) * T)) (v : E) :
    AddCircle.coverPullback n S t (I • v) = I • AddCircle.coverPullback n S t v := by
  rw [AddCircle.coverPullback_apply]
  exact hS _ v

end Loop

variable (T : ℝ) [hT : Fact (0 < T)] [FiniteDimensional ℂ F] (n : ℕ) [NeZero n]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceOrbitTorusCover : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-! ### The Fredholm alternative on the covers -/

/-- **The Fredholm alternative on the `n`-fold cover along the orbit.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S` with return map `P = Ψ(T)`, the operator `∂s + J₀ (∂t - S)` of
the loop traversed `n` times, on maps periodic of period `ℓ` in `s` and `n T` in `t`, is invertible
exactly when `det (1 - P ^ n) ≠ 0`. -/
theorem isInvertible_periodicTorusOperator_coverPullback_iff_det_ne_zero (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator ((n : ℝ) * T) ℓ (AddCircle.coverPullback n S)).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F) ^ n) ≠ 0 := by
  rw [isInvertible_periodicTorusOperator_iff_det_ne_zero _ hℓ _
    (im_inner_coverPullback_add_eq_zero n hS), dysonSeriesLeft_coverPullback,
    ContinuousLinearMap.toLinearMap_pow]

/-- **The Fredholm alternative on the `n`-fold cover, twisted along its orbit.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S` with return map `P = Ψ(T)`, the operator of the loop traversed
`n` times, on maps periodic in `s` and antiperiodic of period `n T` in `t`, is invertible exactly
when `det (1 + P ^ n) ≠ 0`. -/
theorem
    isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_coverPullback_iff_det_one_add_ne_zero
    (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator ((n : ℝ) * T) ℓ
        (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n S))).IsInvertible ↔
      LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F) ^ n) ≠ 0 := by
  rw [isInvertible_periodicTorusOperator_antiperiodicGaugeLoop_iff_det_one_add_ne_zero _ hℓ _
    (im_inner_coverPullback_add_eq_zero n hS), dysonSeriesLeft_coverPullback,
    ContinuousLinearMap.toLinearMap_pow]

/-! ### The determinant signs on the covers -/

variable {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ}

/-- **The untwisted operator on the `n`-fold cover has determinant sign `sgn det (1 - P ^ n)`.**
Let `M` be a path of infinitesimally symplectic loops of period `T`, continuous on `[a, b]`, whose
loop `M a` consists of complex-linear maps, and read the loops with period `n T`. The operator
`∂s + J₀ (∂t - M a)` of the cover is the real map underlying a complex-linear map `f`. If the
operator `∂s + J₀ (∂t - M b)` of the cover is bijective, every element `x` of its determinant line
in the orientation transported from the complex orientation at `a` reads, in the trivialization
given by bijectivity, with the sign of `det (1 - P ^ n)`, where `P = Ψ_b(T)` is the return map of
`ζ' = M b ζ` over one period. -/
theorem sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ =
      periodicTorusOperator ((n : ℝ) * T) ℓ (AddCircle.coverPullback n (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective
      (periodicTorusOperator ((n : ℝ) * T) ℓ (AddCircle.coverPullback n (M b))))
    {x : (periodicTorusOperator ((n : ℝ) * T) ℓ (AddCircle.coverPullback n (M b)) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ periodicTorusOperator ((n : ℝ) * T) ℓ (AddCircle.coverPullback n (M τ))) a b
        ((continuous_periodicTorusOperator _ ℓ).comp_continuousOn
          ((AddCircle.continuous_coverPullback n).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_periodicTorusOperator _ hℓ _
          (im_inner_coverPullback_add_eq_zero n (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator _ hℓ _
              (im_inner_coverPullback_add_eq_zero n (hMs a left_mem_uIcc)))))) :
    SignType.sign ((periodicTorusOperator ((n : ℝ) * T) ℓ (AddCircle.coverPullback n (M b)) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← dysonSeriesLeft_coverPullback]
  exact sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det _
    (M := fun τ ↦ AddCircle.coverPullback n (M τ)) hℓ
    ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_coverPullback_add_eq_zero n (hMs τ hτ))
    (coverPullback_apply_I_smul n hMa) hf hz hb hx hxz

/-- **The operator on the `n`-fold cover twisted along its orbit has determinant sign
`sgn det (1 + P ^ n)`.** In the situation of
`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det`, consider
the operators of the cover on maps antiperiodic of period `n T` along the orbit, realized in the
periodic gauge by the loops `TauCeti.CircleSobolev.antiperiodicGaugeLoop (n T)` of the pulled-back
loops. If the one at `b` is bijective, every element `x` of its determinant line in the orientation
transported from the complex orientation at `a` reads, in the trivialization given by bijectivity,
with the sign of `det (1 + P ^ n)`, where `P = Ψ_b(T)`. -/
theorem
sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator ((n : ℝ) * T) ℓ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M a))))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (periodicTorusOperator ((n : ℝ) * T) ℓ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M b)))))
    {x : (periodicTorusOperator ((n : ℝ) * T) ℓ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M b))) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ periodicTorusOperator ((n : ℝ) * T) ℓ
          (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M τ)))) a b
        ((continuous_periodicTorusOperator _ ℓ).comp_continuousOn
          ((continuous_antiperiodicGaugeLoop _).comp_continuousOn
            ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)))
        (fun τ hτ ↦ isFredholm_periodicTorusOperator _ hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero _
            (im_inner_coverPullback_add_eq_zero n (hMs τ hτ))))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator _ hℓ _
              (im_inner_antiperiodicGaugeLoop_add_eq_zero _
                (im_inner_coverPullback_add_eq_zero n (hMs a left_mem_uIcc))))))) :
    SignType.sign ((periodicTorusOperator ((n : ℝ) * T) ℓ
        (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M b))) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← dysonSeriesLeft_coverPullback]
  exact sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det _
    (M := fun τ ↦ AddCircle.coverPullback n (M τ)) hℓ
    ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_coverPullback_add_eq_zero n (hMs τ hτ))
    (coverPullback_apply_I_smul n hMa) hf hz hb hx hxz

/-- **The pullback of the operator twisted along the orbit has determinant sign
`sgn det (1 - (-P) ^ n)`.** The sign character of the orbit torus that is nontrivial on the orbit
only pulls back to the `n`-fold cover as the character with sign `(-1) ^ n` along the orbit of the
cover. Its operator on the cover is that of the pullback of the periodic gauge
`TauCeti.CircleSobolev.antiperiodicGaugeLoop T S`, whose return map over one period is `-P`. In the
situation of `TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det`
for these loops, if the operator at `b` is bijective, every element `x` of its determinant line in
the orientation transported from the complex orientation at `a` reads, in the trivialization given
by bijectivity, with the sign of `det (1 - (-P) ^ n)`, where `P = Ψ_b(T)`. -/
theorem
sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_antiperiodicGaugeLoop_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator ((n : ℝ) * T) ℓ
      (AddCircle.coverPullback n (antiperiodicGaugeLoop T (M a))))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (periodicTorusOperator ((n : ℝ) * T) ℓ
      (AddCircle.coverPullback n (antiperiodicGaugeLoop T (M b)))))
    {x : (periodicTorusOperator ((n : ℝ) * T) ℓ
      (AddCircle.coverPullback n (antiperiodicGaugeLoop T (M b))) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ periodicTorusOperator ((n : ℝ) * T) ℓ
          (AddCircle.coverPullback n (antiperiodicGaugeLoop T (M τ)))) a b
        ((continuous_periodicTorusOperator _ ℓ).comp_continuousOn
          ((AddCircle.continuous_coverPullback n).comp_continuousOn
            ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM)))
        (fun τ hτ ↦ isFredholm_periodicTorusOperator _ hℓ _
          (im_inner_coverPullback_add_eq_zero n
            (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ))))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator _ hℓ _
              (im_inner_coverPullback_add_eq_zero n
                (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs a left_mem_uIcc))))))) :
    SignType.sign ((periodicTorusOperator ((n : ℝ) * T) ℓ
        (AddCircle.coverPullback n (antiperiodicGaugeLoop T (M b))) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (-(↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F)) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_neg, ← dysonSeriesLeft_antiperiodicGaugeLoop_period]
  exact sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det T n
    (M := fun τ ↦ antiperiodicGaugeLoop T (M τ)) hℓ
    ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ))
    (antiperiodicGaugeLoop_apply_I_smul T hMa) hf hz hb hx hxz

/-- **The double cover law.** On the double cover along the orbit, the untwisted operator has
determinant sign `sgn det (1 - P) · sgn det (1 + P)`: the product of the signs of the two operators
of the orbit torus twisted by the sign characters trivial on the circle factor, the characters
whose pullbacks to the double cover are trivial. In the situation of
`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det` for `n = 2`,
every element `x` of the determinant line at `b` in the transported complex orientation reads, in
the trivialization given by bijectivity, with this sign, where `P = Ψ_b(T)`. -/
theorem sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_two_eq_sign_mul_sign
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ =
      periodicTorusOperator (((2 : ℕ) : ℝ) * T) ℓ (AddCircle.coverPullback 2 (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective
      (periodicTorusOperator (((2 : ℕ) : ℝ) * T) ℓ (AddCircle.coverPullback 2 (M b))))
    {x : (periodicTorusOperator (((2 : ℕ) : ℝ) * T) ℓ (AddCircle.coverPullback 2 (M b)) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ periodicTorusOperator (((2 : ℕ) : ℝ) * T) ℓ
          (AddCircle.coverPullback 2 (M τ))) a b
        ((continuous_periodicTorusOperator _ ℓ).comp_continuousOn
          ((AddCircle.continuous_coverPullback 2).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_periodicTorusOperator _ hℓ _
          (im_inner_coverPullback_add_eq_zero 2 (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator _ hℓ _
              (im_inner_coverPullback_add_eq_zero 2 (hMs a left_mem_uIcc)))))) :
    SignType.sign ((periodicTorusOperator (((2 : ℕ) : ℝ) * T) ℓ (AddCircle.coverPullback 2 (M b)) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) *
        SignType.sign
          (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) := by
  rw [sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det T 2 hℓ hM hMs
    hMa hf hz hb hx hxz, ← sign_mul, ← map_mul]
  congr 2
  noncomm_ring

end TauCeti
