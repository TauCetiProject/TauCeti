/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Complex
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.SkewCover

/-!
# The determinant sign of the orbit-torus operators twisted along the circle factor

Let `γ` be a closed orbit of the suspension flow of a surface diffeomorphism and `C = S¹ × γ` its
orbit torus in `S¹ × Y_φ`. In a unitary trivialization of the normal bundle, the normal operator of
`C` is `D = ∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, for a loop `S` which is infinitesimally symplectic for
`Im ⟪·, ·⟫`. In Taubes's weighted count, each of the four real sign characters of the torus
twists `D`, and the twisted operator contributes the sign of its determinant line: the
orientation obtained by transporting the complex orientation of a complex-linear reference
operator, such as `∂s + J₀ ∂t`, along a path of Fredholm operators to `D`, compared with a
reference orientation of the determinant line of `D`. For the characters twisted along the circle
factor, `D` acts on maps antiperiodic in `s` and is invertible along the whole path
`τ ↦ ∂s + J₀ (∂t - τ S)` (`TauCeti.isInvertible_torusModeOperator_antiperiodic`), so its
determinant line is canonically trivialized by invertibility and the sign is read against that
trivialization.

This file proves that the sign is positive for the character twisted along the circle factor and
untwisted along `γ`, the operator `TauCeti.torusModeOperator` with the antiperiodic frequencies
`ωₖ = (2k + 1)π/ℓ`. More generally, let the frequencies satisfy `ω₀ ≤ |ωₖ|` for some `ω₀ > 0`.
Along any path `M` of infinitesimally symplectic loops starting at a loop whose operator is
complex linear, every operator `∂s + J₀ (∂t - M τ)` is invertible, so transporting a complex
positive element of the determinant line of the reference operator gives the orientation of the
endpoint given by invertibility
(`TauCeti.detLineOrientationTransport_rayOfNeZero_torusModeOperator`). This is the general
statement
`TauCeti.detLineOrientationTransport_rayOfNeZero_detLineCongrOfEq_of_isComplexPositiveDetLine`
for these operators. For the zero loop the reference operator is `∂s + J₀ ∂t`, which is complex
linear (`TauCeti.torusModeOperator_zero_apply_smul`), and for every infinitesimally symplectic
loop `S` the straight path `τ ↦ τ • S` is such a path.

**Skew covers.** The same holds on every finite cover of the orbit torus, the skew covers
included. A cover has a lattice spanned by `(ℓ, 0)` and `(σ, T)`, and a map on it twisted by a sign
character that is `-1` on `(ℓ, 0)` is antiperiodic of antiperiod `ℓ` in `s`, with the frequencies
`ωₖ = (2k + 1)π/ℓ`, and invariant, up to the sign of the character on `(σ, T)`, under the
translation by `(σ, T)`. On the maps invariant under a translation (`TauCeti.skewTorusModeSobolev`),
the orbit-torus operator is invertible wherever it is on all the maps with the same frequencies
(`TauCeti.isInvertible_skewTorusModeOperator`), so along a path of such operators the complex
orientation is again transported to the orientation of invertibility
(`TauCeti.detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator`). For the antiperiodic
frequencies and the loops read with period `q T` this is the statement on the skew covers,
`TauCeti.detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator_antiperiodic_coverPullback`;
the sign `-1` on `(σ, T)` is absorbed by passing to the loops
`TauCeti.CircleSobolev.antiperiodicGaugeLoop T (M τ)`, as in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.SkewCover`. The character twisted along both
factors of the orbit torus itself is the case `q = 2`, `σ = ℓ`: then `cos (ωₖ ℓ) = -1` and
`sin (ωₖ ℓ) = 0`, so the invariant maps are those whose modes are antiperiodic of antiperiod `T`
in `t` on the double cover of `γ` (`TauCeti.mem_skewTorusModeSobolev_iff`). Thus both characters
nontrivial along the circle factor contribute a positive sign.

## Main results

* `TauCeti.detLineOrientationTransport_rayOfNeZero_torusModeOperator`: transport of the complex
  orientation along a path of orbit-torus operators with gapped frequencies gives the orientation
  of invertibility.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_torusModeOperator_antiperiodic`: the case of
  maps antiperiodic in `s`, the character twisted along the circle factor and untwisted along `γ`.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator`: the same transport on
  maps invariant under a translation.
* `detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator_antiperiodic_coverPullback`: the
  characters nontrivial on `(ℓ, 0)` on a skew cover.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (orientations of determinant lines by
  transport from complex-linear operators).
-/

public section

noncomputable section

open Set
open scoped Real lp

namespace TauCeti

open CircleSobolev

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceAntiperiodicOrientation : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- **Transport of the complex orientation along orbit-torus operators.** Let the frequencies
satisfy `ω₀ ≤ |ωₖ|` for some `ω₀ > 0`, and let `M` be a path of infinitesimally symplectic loops,
continuous between `a` and `b` in the uniform norm, such that the orbit-torus operator
`∂s + J₀ (∂t - M a)` on maps with the frequencies `ω` along `s` is complex linear, the real map
underlying `f`, as for the zero loop. Transporting the complex orientation of
`∂s + J₀ (∂t - M a)`, that of any complex positive element `z` of its determinant line, along the
operators `∂s + J₀ (∂t - M τ)` gives the orientation of the determinant line of
`∂s + J₀ (∂t - M b)` given by its invertibility. -/
theorem detLineOrientationTransport_rayOfNeZero_torusModeOperator {ω : ℕ → ℝ} {ω₀ : ℝ}
    (hω₀ : 0 < ω₀) (hω : ∀ k, ω₀ ≤ |ω k|) {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ}
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    {f : torusModeSobolev F ω →ₗ[ℂ] 𝕐[F]} (hf : f.restrictScalars ℝ = torusModeOperator T ω (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport (T := fun τ ↦ torusModeOperator T ω (M τ)) a b
        ((continuous_torusModeOperator T _).comp_continuousOn hM)
        (fun τ hτ ↦ (isInvertible_torusModeOperator T hω₀ hω (M τ) (hMs τ hτ)).isFredholm)
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z) (hz.detLineCongrOfEq_ne_zero hf
          (isInvertible_torusModeOperator T hω₀ hω (M a) (hMs a left_mem_uIcc)).surjective)) =
      rayOfNeZero ℝ ((LinearMap.detLineEquivOfBijective
        (isInvertible_torusModeOperator T hω₀ hω (M b) (hMs b right_mem_uIcc)).bijective).symm 1)
        ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero) :=
  detLineOrientationTransport_rayOfNeZero_detLineCongrOfEq_of_isComplexPositiveDetLine _
    (fun τ hτ ↦ isInvertible_torusModeOperator T hω₀ hω (M τ) (hMs τ hτ)) hf hz

/-- **The orbit-torus operator twisted along the circle factor has positive determinant sign.**
This is `TauCeti.detLineOrientationTransport_rayOfNeZero_torusModeOperator` for the maps
antiperiodic of antiperiod `ℓ` in `s`, whose frequencies `ωₖ = (2k + 1)π/ℓ` satisfy
`π/|ℓ| ≤ |ωₖ|`. -/
theorem detLineOrientationTransport_rayOfNeZero_torusModeOperator_antiperiodic {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    {f : torusModeSobolev F (antiperiodicModeFrequency ℓ) →ₗ[ℂ] 𝕐[F]}
    (hf : f.restrictScalars ℝ = torusModeOperator T (antiperiodicModeFrequency ℓ) (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport
        (T := fun τ ↦ torusModeOperator T (antiperiodicModeFrequency ℓ) (M τ)) a b
        ((continuous_torusModeOperator T _).comp_continuousOn hM)
        (fun τ hτ ↦ (isInvertible_torusModeOperator_antiperiodic T hℓ (M τ) (hMs τ hτ)).isFredholm)
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z) (hz.detLineCongrOfEq_ne_zero hf
          (isInvertible_torusModeOperator_antiperiodic T hℓ (M a)
            (hMs a left_mem_uIcc)).surjective)) =
      rayOfNeZero ℝ ((LinearMap.detLineEquivOfBijective
        (isInvertible_torusModeOperator_antiperiodic T hℓ (M b)
          (hMs b right_mem_uIcc)).bijective).symm 1)
        ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero) := by
  refine detLineOrientationTransport_rayOfNeZero_torusModeOperator T
    (div_pos Real.pi_pos (abs_pos.2 hℓ)) (fun k ↦ ?_) hM hMs hf hz
  rw [antiperiodicModeFrequency_apply, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * k + 1) * π)]
  gcongr
  nlinarith [Real.pi_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-! ### The operators twisted along the circle factor on the skew covers -/

/-- **Transport of the complex orientation on maps invariant under a translation.** Let `M` be a
path of loops invariant under the rotation by `θ`, continuous between `a` and `b` in the uniform
norm, such that every orbit-torus operator `∂s + J₀ (∂t - M τ)` on the maps with the frequencies
`ω` along `s` is invertible, as for infinitesimally symplectic loops and frequencies bounded away
from zero (`TauCeti.isInvertible_torusModeOperator`), and such that the operator
`∂s + J₀ (∂t - M a)` on those maps invariant under the translation by `(σ, θ)`
(`TauCeti.skewTorusModeOperator`) is complex linear, the real map underlying `f`. The operators on
the invariant maps are then invertible too (`TauCeti.isInvertible_skewTorusModeOperator`), so
transporting the complex orientation of `∂s + J₀ (∂t - M a)`, that of any complex positive element
`z` of its determinant line, along them gives the orientation of the determinant line of
`∂s + J₀ (∂t - M b)` given by its invertibility. -/
theorem detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator {ω : ℕ → ℝ} (σ : ℝ)
    {θ : AddCircle T} {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ}
    (hM : ContinuousOn M (uIcc a b)) (hM' : ∀ τ t, M τ (t + θ) = M τ t)
    (hinv : ∀ τ ∈ uIcc a b, (torusModeOperator T ω (M τ)).IsInvertible)
    {f : skewTorusModeSobolev F ω σ θ →ₗ[ℂ] skewTorusModeL2 F ω σ θ}
    (hf : f.restrictScalars ℝ = skewTorusModeOperator T ω σ θ (M a) (hM' a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport (T := fun τ ↦ skewTorusModeOperator T ω σ θ (M τ) (hM' τ)) a b
        (continuousOn_skewTorusModeOperator T ω σ hM hM')
        (fun τ hτ ↦ (isInvertible_skewTorusModeOperator T σ (hM' τ) (hinv τ hτ)).isFredholm)
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z) (hz.detLineCongrOfEq_ne_zero hf
          (isInvertible_skewTorusModeOperator T σ (hM' a) (hinv a left_mem_uIcc)).surjective)) =
      rayOfNeZero ℝ ((LinearMap.detLineEquivOfBijective
        (isInvertible_skewTorusModeOperator T σ (hM' b) (hinv b right_mem_uIcc)).bijective).symm 1)
        ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero) :=
  detLineOrientationTransport_rayOfNeZero_detLineCongrOfEq_of_isComplexPositiveDetLine _
    (fun τ hτ ↦ isInvertible_skewTorusModeOperator T σ (hM' τ) (hinv τ hτ)) hf hz

/-- **On the skew covers, the orbit-torus operators twisted along the circle factor have positive
determinant sign.** Let `M` be a path of infinitesimally symplectic loops of period `T`, continuous
between `a` and `b` in the uniform norm, and read the loops with period `q T`
(`AddCircle.coverPullback`). Consider the operators `∂s + J₀ (∂t - M τ)` on the maps antiperiodic of
antiperiod `ℓ` in `s`, whose frequencies are `ωₖ = (2k + 1)π/ℓ`, invariant under the translation by
`(σ, T)` (`TauCeti.skewTorusModeOperator`), and let the one at `a` be complex linear, the real map
underlying `f`. Transporting the complex orientation of the operator at `a` along them gives the
orientation of the determinant line of the operator at `b` given by its invertibility, whatever
the shear `σ` and the integer `q`.

When `q σ ∈ 2 ℓ ℤ` these are all the maps `u` with `u (s + ℓ, t) = -u (s, t)` and
`u (s + σ, t + T) = u (s, t)`, the maps on the cover with lattice spanned by `(ℓ, 0)` and `(σ, T)`
twisted by its sign character that is `-1` on `(ℓ, 0)` and `1` on `(σ, T)`; every finite cover of
an orbit torus with circle factor of length `ℓ₀` has such a lattice, with `q = 2 k` for
`ℓ = k ℓ₀`. For the loops `TauCeti.CircleSobolev.antiperiodicGaugeLoop T (M τ)`, which are again
infinitesimally symplectic (`TauCeti.CircleSobolev.im_inner_antiperiodicGaugeLoop_add_eq_zero`),
these operators are, in the periodic gauge, those twisted by the sign character that is `-1` on
both generators. So on every finite cover of an orbit torus both sign characters nontrivial on
`(ℓ, 0)` contribute a positive sign. -/
theorem detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator_antiperiodic_coverPullback
    (q : ℕ) [NeZero q] {ℓ : ℝ} (hℓ : ℓ ≠ 0) (σ : ℝ) {M : ℝ → C(AddCircle T, F →L[ℝ] F)}
    {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    {f : skewTorusModeSobolev F (antiperiodicModeFrequency ℓ) σ
        ((T : ℝ) : AddCircle ((q : ℝ) * T)) →ₗ[ℂ]
      skewTorusModeL2 F (antiperiodicModeFrequency ℓ) σ ((T : ℝ) : AddCircle ((q : ℝ) * T))}
    (hf : f.restrictScalars ℝ = skewTorusModeOperator ((q : ℝ) * T)
      (antiperiodicModeFrequency ℓ) σ _ (AddCircle.coverPullback q (M a))
      (AddCircle.coverPullback_add_coe_period q (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport
        (T := fun τ ↦ skewTorusModeOperator ((q : ℝ) * T) (antiperiodicModeFrequency ℓ) σ _
          (AddCircle.coverPullback q (M τ)) (AddCircle.coverPullback_add_coe_period q (M τ))) a b
        (continuousOn_skewTorusModeOperator _ _ σ
          ((AddCircle.continuous_coverPullback q).comp_continuousOn hM) _)
        (fun τ hτ ↦ (isInvertible_skewTorusModeOperator _ σ _
          (isInvertible_torusModeOperator_antiperiodic _ hℓ _
            (im_inner_coverPullback_add_eq_zero q (hMs τ hτ)))).isFredholm)
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z) (hz.detLineCongrOfEq_ne_zero hf
          (isInvertible_skewTorusModeOperator _ σ _
            (isInvertible_torusModeOperator_antiperiodic _ hℓ _
              (im_inner_coverPullback_add_eq_zero q (hMs a left_mem_uIcc)))).surjective)) =
      rayOfNeZero ℝ ((LinearMap.detLineEquivOfBijective
        (isInvertible_skewTorusModeOperator _ σ _
          (isInvertible_torusModeOperator_antiperiodic _ hℓ _
            (im_inner_coverPullback_add_eq_zero q (hMs b right_mem_uIcc)))).bijective).symm 1)
        ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero) :=
  detLineOrientationTransport_rayOfNeZero_skewTorusModeOperator _
    (ω := antiperiodicModeFrequency ℓ) σ (M := fun τ ↦ AddCircle.coverPullback q (M τ))
    ((AddCircle.continuous_coverPullback q).comp_continuousOn hM)
    (fun τ ↦ AddCircle.coverPullback_add_coe_period q (M τ))
    (fun τ hτ ↦ isInvertible_torusModeOperator_antiperiodic _ hℓ _
      (im_inner_coverPullback_add_eq_zero q (hMs τ hτ))) hf hz

end TauCeti
