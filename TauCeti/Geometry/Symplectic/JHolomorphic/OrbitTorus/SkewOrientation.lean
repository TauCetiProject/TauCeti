/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.SkewCover

/-!
# The determinant signs of the orbit-torus operators on the skew covers

Let `γ` be a closed orbit of period `d` of the suspension flow of a surface diffeomorphism and
`C = S¹ × γ` its orbit torus in `S¹ × Y_φ`, with circle factor of length `ℓ₀`. In a unitary
trivialization of the normal bundle, the normal operator of `C` is `D = ∂s + J₀ (∂t - S)` for a
loop `S` of period `d`, infinitesimally symplectic for `Im ⟪·, ·⟫`, with return map `P = Ψ(d)` of
`ζ' = S ζ`. A finite cover of `C` is `ℝ² / Λ` for the lattice `Λ` spanned by `(ℓ, 0)` and
`(σ, n d)`, with `ℓ = k ℓ₀` and `σ = a ℓ₀`, and the operator `D` on the maps periodic under `Λ` is
`TauCeti.skewTorusOperator` for the loop `S` traversed `n` times (take `q = k`). In Taubes's
weighted count, a torus contributes through the determinant signs of its operators on these
covers: the orientation obtained by transporting the complex orientation of a complex-linear
reference operator, such as `∂s + J₀ ∂t`, along a path of loops, read against the orientation
given by invertibility.

This file computes these signs on every cover, the skew covers `σ ≠ 0` included, for the two real
sign characters of the cover trivial on `(ℓ, 0)`. The operator on a skew cover is
`(J₀ L_S) ⊕ B`, the asymptotic operator `J₀ L_S`, `L_S ζ = ζ' - S ζ`, on the `s`-independent mode
beside the invertible operator `B` on the other modes
(`TauCeti.isInvertible_skewTorusModeOperator`), so the orientation transport of
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicOrientation` applies
(`TauCeti.sign_detLineEquivOfBijective_eq_sign_det_of_eq_prodMap_loopOperator`):

* the operator periodic under `Λ` has determinant sign `sgn det (1 - Ψ(T))` for a loop of period
  `T` (`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det`), so
  `sgn det (1 - P ^ n)` on the cover traversing the orbit `n` times
  (`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det`);
* the operator on maps with `u (s + σ, t + T) = -u (s, t)`, realized in the periodic gauge by the
  loop `Sₐ` of `TauCeti.CircleSobolev.antiperiodicGaugeLoop`, whose return map is `-Ψ(T)`, has
  determinant sign `sgn det (1 + Ψ(T))`, so `sgn det (1 + P ^ n)` on the cover traversing the
  orbit `n` times; see
  `sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det` and
  `sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det`.

As for the Fredholm alternative (`TauCeti.isInvertible_skewTorusOperator_iff_det_ne_zero`), only
the number `n` of turns along `γ` enters, not the shear `σ`: these are the signs of the covers along
the orbit (`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_coverPullback_eq_sign_det`).

## Main results

* `TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det`,
  `TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det`: the
  operator on a skew cover has determinant sign `sgn det (1 - Ψ(T))`, and `sgn det (1 - P ^ n)`
  on the cover traversing the orbit `n` times.
* `sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det`,
  `sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det`:
  twisted along the orbit, the sign is `sgn det (1 + Ψ(T))`, and `sgn det (1 + P ^ n)`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the determinant signs of the twisted normal operators
  of tori on their finite unbranched covers).
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158, Section 3 (the return maps `P ^ n` of the iterated orbits and their signs).
-/

public section

noncomputable section

open Complex
open Set (uIcc left_mem_uIcc right_mem_uIcc)
open scoped Real

namespace TauCeti

open CircleSobolev

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] (q : ℕ) [NeZero q] {ℓ : ℝ} (σ : ℝ)
  {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceSkewOrientation : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- **The operator on a skew cover has determinant sign `sgn det (1 - Ψ(T))`.** Let `M` be a path
of infinitesimally symplectic loops of period `T`, continuous on `[a, b]`, whose loop `M a`
consists of complex-linear maps, so that the operator `∂s + J₀ (∂t - M a)` on a skew cover
(`TauCeti.skewTorusOperator`) is the real map underlying a complex-linear map `f`. Let the operator
`∂s + J₀ (∂t - M b)` on the skew cover be bijective, equivalently `det (1 - Ψ_b(T)) ≠ 0`. Every
element `x` of its determinant line in the orientation transported from the complex orientation of
`∂s + J₀ (∂t - M a)` reads, in the trivialization given by bijectivity
(`LinearMap.detLineEquivOfBijective`), with the sign of `det (1 - Ψ_b(T))`, whatever the shear `σ`
and the integer `q`. -/
theorem sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det (hℓ : ℓ ≠ 0)
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T)) →ₗ[ℂ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))}
    (hf : f.restrictScalars ℝ = skewTorusOperator T q ℓ σ (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (skewTorusOperator T q ℓ σ (M b)))
    {x : (skewTorusOperator T q ℓ σ (M b)).toLinearMap.detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport (T := fun τ ↦ skewTorusOperator T q ℓ σ (M τ)) a b
        ((continuous_skewTorusOperator T q ℓ σ).comp_continuousOn hM)
        (fun τ hτ ↦ isFredholm_skewTorusOperator T q σ hℓ (M τ) (hMs τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator T q σ hℓ (M a) (hMs a left_mem_uIcc))))) :
    SignType.sign ((skewTorusOperator T q ℓ σ (M b)).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :=
  sign_detLineEquivOfBijective_eq_sign_det_of_eq_prodMap_loopOperator T
    (B := fun τ ↦ skewTorusModeOperator ((q : ℝ) * T) ℓ σ _ (AddCircle.coverPullback q (M τ))
      (AddCircle.coverPullback_add_coe_period q (M τ)))
    (fun τ ↦ ContinuousLinearMap.ext (skewTorusOperator_apply T q ℓ σ (M τ))) _ _ hM
    (((continuous_skewTorusModeOperator _ ℓ σ _).comp
      (f := fun S : C(AddCircle T, F →L[ℝ] F) ↦
        (⟨AddCircle.coverPullback q S, AddCircle.coverPullback_add_coe_period q S⟩ :
          {S' : C(AddCircle ((q : ℝ) * T), F →L[ℝ] F) // ∀ t, S' (t + (T : ℝ)) = S' t}))
      ((AddCircle.continuous_coverPullback q).subtype_mk _)).comp_continuousOn hM)
    (fun τ hτ ↦ isInvertible_skewTorusModeOperator _ hℓ σ _
      (im_inner_coverPullback_add_eq_zero q (hMs τ hτ)) _) hMa hf hz hb hx hxz

/-- **The operator on a skew cover twisted along the orbit has determinant sign
`sgn det (1 + Ψ(T))`.** Let `M` be a path of infinitesimally symplectic loops of period `T`,
continuous on `[a, b]`, whose loop `M a` consists of complex-linear maps. On the maps of the skew
cover with `u (s + σ, t + T) = -u (s, t)`, realized in the periodic gauge, the operators are
`∂s + J₀ (∂t - (M τ)ₐ)` for the loops `(M τ)ₐ = TauCeti.CircleSobolev.antiperiodicGaugeLoop T (M τ)`
(`TauCeti.skewTorusOperator`), and the one at `a` is the real map underlying a complex-linear map
`f`. If the one at `b` is bijective, equivalently `det (1 + Ψ_b(T)) ≠ 0`, every element `x` of its
determinant line in the orientation transported from the complex orientation at `a` reads, in the
trivialization given by bijectivity, with the sign of `det (1 + Ψ_b(T))`, where `Ψ_b(T)` is the
return map of `ζ' = M b ζ`. -/
theorem sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T)) →ₗ[ℂ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))}
    (hf : f.restrictScalars ℝ = skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M b))))
    {x : (skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M b))).toLinearMap.detLine}
    (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M τ))) a b
        ((continuous_skewTorusOperator T q ℓ σ).comp_continuousOn
          ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_skewTorusOperator T q σ hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator T q σ hℓ _
              (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs a left_mem_uIcc)))))) :
    SignType.sign ((skewTorusOperator T q ℓ σ
        (antiperiodicGaugeLoop T (M b))).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) := by
  rw [← one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period]
  exact sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det T q σ
    (M := fun τ ↦ antiperiodicGaugeLoop T (M τ)) hℓ
    ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ))
    (antiperiodicGaugeLoop_apply_I_smul T hMa) hf hz hb hx hxz

variable (n : ℕ) [NeZero n]

/-- **The operator on a skew cover traversing the orbit `n` times has determinant sign
`sgn det (1 - P ^ n)`.** Let `M` be a path of infinitesimally symplectic loops of period `T`,
continuous on `[a, b]`, whose loop `M a` consists of complex-linear maps, and read the loops with
period `n T`. On the cover with lattice spanned by `(ℓ, 0)` and `(σ, n T)`, the operator
`∂s + J₀ (∂t - M a)` (`TauCeti.skewTorusOperator`) is the real map underlying a complex-linear
map `f`. If the operator `∂s + J₀ (∂t - M b)` on the cover is bijective, every element `x` of its
determinant line in the orientation transported from the complex orientation at `a` reads, in the
trivialization given by bijectivity, with the sign of `det (1 - P ^ n)`, where `P = Ψ_b(T)` is
the return map of `ζ' = M b ζ` over one period. -/
theorem sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ
        (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T))) →ₗ[ℂ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ
        (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T)))}
    (hf : f.restrictScalars ℝ =
      skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective
      (skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n (M b))))
    {x : (skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (AddCircle.coverPullback n (M b))).toLinearMap.detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n (M τ))) a b
        ((continuous_skewTorusOperator _ q ℓ σ).comp_continuousOn
          ((AddCircle.continuous_coverPullback n).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_skewTorusOperator _ q σ hℓ _
          (im_inner_coverPullback_add_eq_zero n (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator _ q σ hℓ _
              (im_inner_coverPullback_add_eq_zero n (hMs a left_mem_uIcc)))))) :
    SignType.sign ((skewTorusOperator ((n : ℝ) * T) q ℓ σ
        (AddCircle.coverPullback n (M b))).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← dysonSeriesLeft_coverPullback]
  exact sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det _ q σ
    (M := fun τ ↦ AddCircle.coverPullback n (M τ)) hℓ
    ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_coverPullback_add_eq_zero n (hMs τ hτ))
    (coverPullback_apply_I_smul n hMa) hf hz hb hx hxz

/-- **The operator on a skew cover traversing the orbit `n` times, twisted along the orbit, has
determinant sign `sgn det (1 + P ^ n)`.** In the situation of
`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det`, consider the
operators of the cover on maps with `u (s + σ, t + n T) = -u (s, t)`, realized in the periodic
gauge by the loops `TauCeti.CircleSobolev.antiperiodicGaugeLoop (n T)` of the pulled-back loops.
If the one at `b` is bijective, every element `x` of its determinant line in the orientation
transported from the complex orientation at `a` reads, in the trivialization given by
bijectivity, with the sign of `det (1 + P ^ n)`, where `P = Ψ_b(T)`. -/
theorem
sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ
        (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T))) →ₗ[ℂ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ
        (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T)))}
    (hf : f.restrictScalars ℝ = skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M a))))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M b)))))
    {x : (skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M b)))).toLinearMap.detLine}
    (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ skewTorusOperator ((n : ℝ) * T) q ℓ σ
          (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M τ)))) a b
        ((continuous_skewTorusOperator _ q ℓ σ).comp_continuousOn
          ((continuous_antiperiodicGaugeLoop _).comp_continuousOn
            ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)))
        (fun τ hτ ↦ isFredholm_skewTorusOperator _ q σ hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero _
            (im_inner_coverPullback_add_eq_zero n (hMs τ hτ))))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator _ q σ hℓ _
              (im_inner_antiperiodicGaugeLoop_add_eq_zero _
                (im_inner_coverPullback_add_eq_zero n (hMs a left_mem_uIcc))))))) :
    SignType.sign ((skewTorusOperator ((n : ℝ) * T) q ℓ σ
        (antiperiodicGaugeLoop ((n : ℝ) * T)
          (AddCircle.coverPullback n (M b)))).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← dysonSeriesLeft_coverPullback]
  exact sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det _ q σ
    (M := fun τ ↦ AddCircle.coverPullback n (M τ)) hℓ
    ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_coverPullback_add_eq_zero n (hMs τ hτ))
    (coverPullback_apply_I_smul n hMa) hf hz hb hx hxz

end TauCeti
