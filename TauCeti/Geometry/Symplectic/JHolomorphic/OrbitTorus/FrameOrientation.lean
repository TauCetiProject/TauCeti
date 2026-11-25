/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicOrientation
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Trivialization

/-!
# The determinant signs of the orbit-torus operators of a surface map

Let `x` be a periodic point of period `d > 0` of a diffeomorphism of a surface preserving an area
form `σ`, with linearized return map `P = dφ^d_x` on the tangent plane `V`, and let `K(t)` be the
complex structures along the orbit, with the seam identity `P K(t + d) = K(t) P`. A *unitary frame*
is a `C¹` path of isomorphisms `Φ(t) : W → V`, complex linear for `J₀` on the model space `W` and
`K(t)` on `V`, pulling `σ` back to `⟪J₀ ·, ·⟫`, and compatible with the seam,
`P Φ(t + d) = Φ(t)`. Unitary frames exist with `W = ℂ` and `J₀` multiplication by `i`
(`TauCeti.exists_unitary_frame_of_finrank_eq_two`). In such a frame the normal operator
`∂s + K(t) ∂t` of the orbit torus is conjugate to `∂s + J₀ ∂t + S(t)`
(`TauCeti.orbitTorusVerticalOperator_frame_apply`), with `S` the connection of the frame
(`TauCeti.frameConnection`). Written as `∂s + J₀ (∂t - M(t))`, the form of
`TauCeti.periodicTorusOperator`, this is the operator of the loop `M(t) = J₀ S(t)`.

The determinant signs of these model operators are computed from the return map `Ψ(d)` of the
loop equation `ζ' = M ζ`: `sgn det (1 - Ψ(d))` for the operator periodic along both factors
(`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det`) and
`sgn det (1 + Ψ(d))` for the one twisted along the orbit
(`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det`).
This file identifies these with the signs of the actual return map.

* **The loop.** `M` is `d`-periodic and continuous, so it is a loop on `ℝ / dℤ`
  (`TauCeti.exists_continuousMap_addCircle_eq_comp_frameConnection`). For a unitary frame from
  `ℂ` it is infinitesimally symplectic, `Im ⟪M v, w⟫ + Im ⟪v, M w⟫ = 0`, because `S` is symmetric
  (`TauCeti.im_inner_comp_frameConnection_add_eq_zero`); this is the hypothesis under which the
  model operators are Fredholm. It is linear in the loop, so it holds along the straight path
  `τ ↦ τ M` from the complex-linear zero loop to `M`.
* **The return map.** The propagator of `ζ' = M ζ` undoes the frame, so the seam identity gives
  `Φ(d) Ψ(d) = P Φ(d)` (`TauCeti.comp_dysonSeriesLeft_frameConnection_eq_comp`): `Ψ(d)` is
  conjugate to `P`, and `det (1 ∓ Ψ(d)) = det (1 ∓ P)`
  (`TauCeti.det_aeval_dysonSeriesLeft_frameConnection`).
* **The signs.** Along any path of infinitesimally symplectic loops from a complex-linear loop to
  `M`, the complex orientation transports to an orientation of the determinant line of the
  untwisted operator of sign `sgn det (1 - P)`
  (`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det_of_frame`), and to
  one of the operator twisted along the orbit of sign `sgn det (1 + P)`, by
  `sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det_of_frame`.

So the signs of the two operators periodic along the circle factor do not depend on the frame,
and they are the signs `TauCeti.orbitTorusTwistSign` attaches to the return map on the two sign
characters trivial on the circle factor, which label the orbit tori in the orbit zeta function
(`SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative`).
The two characters nontrivial on the circle factor have positive sign for every loop
(`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.AntiperiodicOrientation`). The operators
here are the Sobolev realizations of the model operators in the frame; the conjugation by `Φ` is
only the pointwise identity `TauCeti.orbitTorusVerticalOperator_frame_apply` on classical
sections. Identifying these model operators with a Fredholm realization of the actual normal
operator of the orbit torus is not done here.

## Main results

* `TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det_of_frame` and
  `sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det_of_frame`:
  the determinant signs `sgn det (1 - P)` and `sgn det (1 + P)`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the determinant signs of the twisted normal operators
  of tori).
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158, Lemma 3.2 (the local factors of the orbit tori of a mapping torus, read off from the
  return maps).
-/

public section

noncomputable section

open Complex ContinuousLinearMap
open Set (uIcc left_mem_uIcc right_mem_uIcc)
open scoped Real lp

namespace TauCeti

open CircleSobolev

section Sign

variable (d : ℝ) [Fact (0 < d)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ℓ : ℝ}
  {J₀ : F →L[ℝ] F} {Φ : ℝ → F →L[ℝ] V} {P : V →L[ℝ] V} {M : ℝ → C(AddCircle d, F →L[ℝ] F)}
  {a b : ℝ}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceFrameOrientation : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

/-- **The untwisted orbit-torus operator has determinant sign `sgn det (1 - P)`.** Let `Φ` be a
`C¹` frame compatible with the seam map `P`, `P Φ(t + d) = Φ(t)`, with `J₀² = -1`, and let `M` be
a path of infinitesimally symplectic loops, continuous on `[a, b]`, from a loop `M a` of
complex-linear maps to the loop `M b = J₀ S` of the frame. If `∂s + J₀ (∂t - M b)` is bijective,
every element `x` of its determinant line in the orientation transported from the complex
orientation of `∂s + J₀ (∂t - M a)` reads, in the trivialization given by bijectivity, with the
sign of `det (1 - P)`. -/
theorem sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det_of_frame (hℓ : ℓ ≠ 0)
    (hΦ1 : ContDiff ℝ 1 Φ) (hΦ : ∀ t, (Φ t).IsInvertible) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hseam : ∀ t, P ∘L Φ (t + d) = Φ t) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    (hMb : ∀ t : ℝ, M b t = J₀ ∘L frameConnection J₀ Φ t)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator d ℓ (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (periodicTorusOperator d ℓ (M b)))
    {x : (periodicTorusOperator d ℓ (M b) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport (T := fun τ ↦ periodicTorusOperator d ℓ (M τ)) a b
        ((continuous_periodicTorusOperator d ℓ).comp_continuousOn hM)
        (fun τ hτ ↦ isFredholm_periodicTorusOperator d hℓ (M τ) (hMs τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator d hℓ (M a) (hMs a left_mem_uIcc))))) :
    SignType.sign ((periodicTorusOperator d ℓ (M b) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign (LinearMap.det (1 - (P : V →ₗ[ℝ] V))) := by
  rw [sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det d hℓ hM hMs hMa hf hz hb hx
    hxz, funext hMb]
  congr 1
  have h := det_aeval_dysonSeriesLeft_frameConnection hΦ1 hΦ hJ₀sq hseam (1 - Polynomial.X)
  simpa only [map_sub (Polynomial.aeval _), map_one (Polynomial.aeval _), Polynomial.aeval_X]
    using h

/-- **The orbit-torus operator twisted along the orbit has determinant sign `sgn det (1 + P)`.**
In the situation of
`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det_of_frame`, on maps
periodic in `s` and antiperiodic along the orbit, realized in the periodic gauge by the loops
`TauCeti.CircleSobolev.antiperiodicGaugeLoop d (M τ)`: if the operator at `b` is bijective, every
element of its determinant line in the orientation transported from the complex orientation at `a`
reads, in the trivialization given by bijectivity, with the sign of `det (1 + P)`. -/
theorem
    sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det_of_frame
    (hℓ : ℓ ≠ 0) (hΦ1 : ContDiff ℝ 1 Φ) (hΦ : ∀ t, (Φ t).IsInvertible)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hseam : ∀ t, P ∘L Φ (t + d) = Φ t)
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    (hMb : ∀ t : ℝ, M b t = J₀ ∘L frameConnection J₀ Φ t)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator d ℓ (antiperiodicGaugeLoop d (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (periodicTorusOperator d ℓ (antiperiodicGaugeLoop d (M b))))
    {x : (periodicTorusOperator d ℓ (antiperiodicGaugeLoop d (M b)) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ periodicTorusOperator d ℓ (antiperiodicGaugeLoop d (M τ))) a b
        ((continuous_periodicTorusOperator d ℓ).comp_continuousOn
          ((CircleSobolev.continuous_antiperiodicGaugeLoop d).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_periodicTorusOperator d hℓ _
          (CircleSobolev.im_inner_antiperiodicGaugeLoop_add_eq_zero d (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator d hℓ _
              (CircleSobolev.im_inner_antiperiodicGaugeLoop_add_eq_zero d
                (hMs a left_mem_uIcc)))))) :
    SignType.sign ((periodicTorusOperator d ℓ (antiperiodicGaugeLoop d (M b)) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign (LinearMap.det (1 + (P : V →ₗ[ℝ] V))) := by
  rw [sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det d hℓ
    hM hMs hMa hf hz hb hx hxz, funext hMb]
  congr 1
  have h := det_aeval_dysonSeriesLeft_frameConnection hΦ1 hΦ hJ₀sq hseam (1 + Polynomial.X)
  simpa only [map_add (Polynomial.aeval _), map_one (Polynomial.aeval _), Polynomial.aeval_X]
    using h

end Sign

end TauCeti
