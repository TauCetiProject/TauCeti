/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Complex
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.ModeSobolev

/-!
# The determinant sign of the orbit-torus operator twisted along the circle factor

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
`ωₖ = (2k + 1)π/ℓ`. Along any path `M` of infinitesimally symplectic loops starting at a loop
whose operator is complex linear, every operator `∂s + J₀ (∂t - M τ)` is invertible, so
transporting a complex positive element of the determinant line of the reference operator gives
the orientation of the endpoint given by invertibility
(`TauCeti.detLineOrientationTransport_rayOfNeZero_torusModeOperator_antiperiodic`). This is the
general statement `TauCeti.detLineOrientationTransport_rayOfNeZero_of_isInvertible`
for these operators. For the zero loop the reference operator is `∂s + J₀ ∂t`, which is complex
linear (`TauCeti.torusModeOperator_zero_apply_smul`), and for every infinitesimally symplectic
loop `S` the straight path `τ ↦ τ • S` is such a path.

## Main results

* `TauCeti.detLineOrientationTransport_rayOfNeZero_torusModeOperator_antiperiodic`: transport of
  the complex orientation along a path of orbit-torus operators on maps antiperiodic in `s` gives
  the orientation of invertibility.

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

/-- **The orbit-torus operator twisted along the circle factor has positive determinant sign.**
Let `M` be a path of infinitesimally symplectic loops, continuous between `a` and `b` in the
uniform norm, such that the orbit-torus operator `∂s + J₀ (∂t - M a)` on maps antiperiodic of
antiperiod `ℓ` in `s` is complex linear, the real map underlying `f`, as for the zero loop.
Transporting the complex orientation of `∂s + J₀ (∂t - M a)`, that of any complex positive element
`z` of its determinant line, along the operators `∂s + J₀ (∂t - M τ)` gives the orientation of the
determinant line of `∂s + J₀ (∂t - M b)` given by its invertibility. -/
theorem detLineOrientationTransport_rayOfNeZero_torusModeOperator_antiperiodic {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    {f : torusModeSobolev F (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) →ₗ[ℂ] 𝕐[F]}
    (hf : f.restrictScalars ℝ = torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport
        (T := fun τ ↦ torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) (M τ)) a b
        ((continuous_torusModeOperator T _).comp_continuousOn hM)
        (fun τ hτ ↦ (isInvertible_torusModeOperator_antiperiodic T hℓ (M τ) (hMs τ hτ)).isFredholm)
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z) ((LinearEquiv.map_ne_zero_iff _).2
          (hz.ne_zero_of_surjective fun y ↦
            ((isInvertible_torusModeOperator_antiperiodic T hℓ (M a)
              (hMs a left_mem_uIcc)).surjective y).imp fun x hx ↦
                (congrArg (fun g : _ →ₗ[ℝ] _ ↦ g x) hf).trans hx))) =
      rayOfNeZero ℝ ((LinearMap.detLineEquivOfBijective
        (isInvertible_torusModeOperator_antiperiodic T hℓ (M b)
          (hMs b right_mem_uIcc)).bijective).symm 1)
        ((LinearEquiv.map_ne_zero_iff _).2 one_ne_zero) :=
  detLineOrientationTransport_rayOfNeZero_of_isInvertible _
    (fun τ hτ ↦ isInvertible_torusModeOperator_antiperiodic T hℓ (M τ) (hMs τ hτ)) hf hz

end TauCeti
