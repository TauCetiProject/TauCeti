/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Clutching
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Topology.Circle.Degree.Square
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
public import Mathlib.Algebra.Polynomial.Eval.Defs
import TauCeti.Algebra.Polynomial.Homogenize
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomial spheres in `CPⁿ` and the generator of `π₂(CPⁿ⁺¹)`

The boundary map of the Hopf fibration `S¹ → S²ⁿ⁺¹ → CPⁿ` identifies `π₂(CPⁿ)` with
`π₁(S¹) ≅ ℤ` for `n ≥ 1` (`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`). This file evaluates
that identification on polynomial spheres. Let `P₀, …, Pₙ` be polynomials of degree at most `d`
without common zero whose vector `p_d` of coefficients of `X^d` is nonzero, and let `u` be the map
of the Riemann sphere to `CPⁿ` with `u z = [P₀(z) : ⋯ : Pₙ(z)]` for `z ∈ ℂ` and `u ∞ = [p_d]`,
read as a sphere through the standard sphere `TauCeti.riemannSphereSquare` of the Riemann sphere.
Its class is sent to `d`
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_map_riemannSphereSquare_of_polynomial`): a
polynomial sphere of degree `d` is `d` times the generator. Every holomorphic sphere in projective
space has this form (`TauCeti.RiemannSurface.exists_polynomial_eq_mk`), so its class is its
polynomial degree.

The coordinate line `[1 : z : 0 : ⋯ : 0]` of `CPⁿ⁺¹` is the polynomial sphere of `(1, X, 0, …, 0)`,
of degree one. Read through the standard sphere (`TauCeti.ComplexProjectiveSpace.lineSquare`) and
based at `[e₁]` (`TauCeti.ComplexProjectiveSpace.lineClass`), it is sent to `1`
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_lineClass`). So the generator of `π₂(CPⁿ⁺¹)` is the
class of a projective line with its complex orientation
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_symm_ofAdd_one`), the line class `L` of the
quantum relation `x^(n+2) = q^L` and of the period group of `CPⁿ⁺¹`.

**The lift.** At a point of the square with sup-radius `r` (`TauCeti.cubeRadius`) and offset `c`
from the centre (`TauCeti.squareCenterOffset`), the sphere is `u z` with `z = 2 c / √(1 - r²)`.
Since the `Pⱼ` have degree at most `d`, `√(1 - r²)^d P(z)` is the value of the homogenization
of `P` in degree `d` (`Polynomial.homogenize`) at `(2 c, √(1 - r²))`, which is continuous on the
closed square, nowhere zero, and equal to `(2 c)^d p_d` on its boundary. Its normalization is a
lift of `u` to the unit sphere, equal to `(c / |c|)^d p_d / |p_d|` on the boundary. The boundary
map is read off a lift that starts at `v` and stays there over the boundary of the cube
(`TauCeti.TopCat.fibrationBoundary_mk`), for a unit vector `v` over `u ∞`. So the lift is rotated
by `μ λ^d`, where `μ` is the unit scalar with `μ p_d / |p_d| = v` and `λ` is the phase
`exp (-i χ (arg (-c) + π))`, the weight `χ` being `1` on the bottom, top and left edges of the
square and `0` on the segment from the centre to the midpoint of the right edge, the cut of
`arg (-c)`. The phase is continuous on the whole square, and `λ c / |c| = 1` on those three edges,
so the rotated lift is a boundary lift. Its end is the loop `t ↦ (λ(1, t) c / |c|)^d v` of the
fibre circle over `u ∞`, read along the right edge.

**The degree.** Since `λ` is continuous on the whole square, `λ c / |c|` has the degree of the
direction `c / |c|` from the centre around the boundary of the square
(`TauCeti.squareBoundaryDegree_mul_of_continuous`), which is one
(`TauCeti.squareBoundaryDegree_squareCenterDirection`). Being constant on three edges, it turns
once along the right edge (`TauCeti.squareBoundaryDegree_mul_two_pi_eq_of_edges`), so its `d`-th
power, the end loop, turns `d` times.

**Base points.** The coordinate line is based at `affineParam 1 0`, and `pi2MulEquivInt` at the
class `mk (n + 1) e₁` of the unit vector `e₁ = affineUnitVector 1 0`. These points are equal
(`TauCeti.ComplexProjectiveSpace.affineParam_def`), and the class of the line is carried from one
to the other by `HomotopyGroup.map` of the identity (`TauCeti.ComplexProjectiveSpace.lineClass`).

## Main results

* `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_map_riemannSphereSquare_of_polynomial`: a
  polynomial sphere of degree `d` in `CPⁿ` is sent to `d` by `π₂(CPⁿ) ≃* ℤ`.
* `TauCeti.ComplexProjectiveSpace.lineClass`: the class of the coordinate line in `π₂(CPⁿ⁺¹)`
  at the base point `[e₁]`.
* `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_lineClass`: the coordinate line is sent to
  `1` by `π₂(CPⁿ⁺¹) ≃* ℤ`.
* `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_symm_ofAdd_one`: the generator of `π₂(CPⁿ⁺¹)`
  is the class of the coordinate line.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 (the exact homotopy sequence of a fibration) and Example 4.45 (the Hopf
  fibration and `π₂(CPⁿ) ≅ ℤ`).
-/

public section

noncomputable section

open Metric unitInterval
open scoped OnePoint

namespace TauCeti.ComplexProjectiveSpace

/-! ### A phase on the square -/

/-- The weight `χ = min 1 (2 |t - 1/2| + max 0 (1 - 2 s))` at a point `(s, t)` of the square: it
is `1` on the bottom, top and left edges, and `0` on the segment from the centre to the midpoint of
the right edge. -/
private def squarePhaseWeight (y : Fin 2 → I) : ℝ :=
  min 1 (2 * |(y 1 : ℝ) - 1 / 2| + max 0 (1 - 2 * (y 0 : ℝ)))

private theorem continuous_squarePhaseWeight : Continuous squarePhaseWeight := by
  unfold squarePhaseWeight
  fun_prop

private theorem squarePhaseWeight_nonneg (y : Fin 2 → I) : 0 ≤ squarePhaseWeight y :=
  le_min zero_le_one (add_nonneg (by positivity) (le_max_left _ _))

/-- The weight vanishes where the offset from the centre is a nonnegative real number. -/
private theorem squarePhaseWeight_eq_zero {y : Fin 2 → I}
    (hy : -squareCenterOffset y ∉ Complex.slitPlane) : squarePhaseWeight y = 0 := by
  rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hy
  simp only [Complex.neg_re, Complex.neg_im, re_squareCenterOffset, im_squareCenterOffset,
    neg_eq_zero, neg_nonpos, sub_nonneg, sub_eq_zero] at hy
  obtain ⟨h0, h1⟩ := hy
  rw [squarePhaseWeight, h1, sub_self, abs_zero, mul_zero, zero_add,
    max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

/-- The bottom, top and left edges of the square. -/
private def IsPhaseEdge (y : Fin 2 → I) : Prop :=
  y 0 = 0 ∨ y 1 = 0 ∨ y 1 = 1

private theorem IsPhaseEdge.mem_boundary {y : Fin 2 → I} (hy : IsPhaseEdge y) :
    y ∈ Cube.boundary (Fin 2) := by
  rcases hy with h | h | h
  exacts [⟨0, .inl h⟩, ⟨1, .inl h⟩, ⟨1, .inr h⟩]

private theorem squarePhaseWeight_eq_one {y : Fin 2 → I} (hy : IsPhaseEdge y) :
    squarePhaseWeight y = 1 := by
  refine min_eq_left ?_
  rcases hy with h | h | h <;> simp only [h, Set.Icc.coe_zero, Set.Icc.coe_one]
  · rw [mul_zero, sub_zero, max_eq_right zero_le_one]
    linarith [abs_nonneg ((y 1 : ℝ) - 1 / 2)]
  · rw [show |(0 : ℝ) - 1 / 2| = 1 / 2 by norm_num [abs_of_neg]]
    linarith [le_max_left (0 : ℝ) (1 - 2 * (y 0 : ℝ))]
  · rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num [abs_of_pos]]
    linarith [le_max_left (0 : ℝ) (1 - 2 * (y 0 : ℝ))]

/-- The angle `χ (arg (-c) + π)` of the phase, for the offset `c` from the centre. -/
private def squarePhaseAngle (y : Fin 2 → I) : ℝ :=
  squarePhaseWeight y * (Complex.arg (-squareCenterOffset y) + Real.pi)

private theorem continuous_squarePhaseAngle : Continuous squarePhaseAngle := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  by_cases hy : -squareCenterOffset y ∈ Complex.slitPlane
  · exact continuous_squarePhaseWeight.continuousAt.mul
      (((Complex.continuousAt_arg hy).comp (f := fun z ↦ -squareCenterOffset z)
        (by fun_prop)).add continuousAt_const)
  · -- The weight vanishes at `y`, and the second factor is bounded by `2π`.
    have h0 : squarePhaseAngle y = 0 := by
      rw [squarePhaseAngle, squarePhaseWeight_eq_zero hy, zero_mul]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (a := fun z ↦ 2 * Real.pi * squarePhaseWeight z) (fun z ↦ ?_) ?_
    · rw [squarePhaseAngle, norm_mul, Real.norm_of_nonneg (squarePhaseWeight_nonneg z),
        mul_comm (2 * Real.pi)]
      refine mul_le_mul_of_nonneg_left ?_ (squarePhaseWeight_nonneg z)
      rw [Real.norm_of_nonneg (by linarith [Complex.neg_pi_lt_arg (-squareCenterOffset z)])]
      linarith [Complex.arg_le_pi (-squareCenterOffset z)]
    · simpa [squarePhaseWeight_eq_zero hy] using
        (continuous_squarePhaseWeight.tendsto y).const_mul (2 * Real.pi)

/-- The phase `exp (-i χ (arg (-c) + π))`, a circle-valued map continuous on the whole square. -/
private def squarePhase (y : Fin 2 → I) : Circle :=
  Circle.exp (-squarePhaseAngle y)

private theorem continuous_squarePhase : Continuous squarePhase :=
  (map_continuous Circle.exp).comp continuous_squarePhaseAngle.neg

/-- The direction from the centre, twisted by the phase. -/
private def squareTwist : (Fin 2 → I) → Circle :=
  squareCenterDirection * squarePhase

/-- On the bottom, top and left edges the twisted direction is `1`. -/
private theorem squareTwist_eq_one {y : Fin 2 → I} (hy : IsPhaseEdge y) : squareTwist y = 1 := by
  have hc := squareCenterOffset_ne_zero_of_mem hy.mem_boundary
  -- The direction `c / ‖c‖` is `exp (i (arg (-c) + π))`.
  have key : squareCenterDirection y =
      Circle.exp (Complex.arg (-squareCenterOffset y) + Real.pi) := by
    refine Circle.ext ?_
    simp [coe_squareCenterDirection hc, Complex.exp_arg_mul_I (neg_ne_zero.2 hc)]
    ring
  rw [squareTwist, Pi.mul_apply, squarePhase, squarePhaseAngle, squarePhaseWeight_eq_one hy,
    one_mul, key, ← Circle.exp_add, add_neg_cancel, Circle.exp_zero]

/-- The twisted direction turns once around the circle along the boundary of the square. -/
private theorem squareBoundaryDegree_squareTwist : squareBoundaryDegree squareTwist = 1 := by
  rw [squareTwist, squareBoundaryDegree_mul_of_continuous continuous_squarePhase,
    squareBoundaryDegree_squareCenterDirection]

/-- The angle along the right edge `t ↦ (1, t)`. -/
private def rightEdgeAngle (t : I) : ℝ :=
  Complex.arg (squareCenterOffset ![1, t]) - squarePhaseAngle ![1, t]

private theorem continuous_rightEdgeAngle : Continuous rightEdgeAngle := by
  have hc : Continuous fun t : I ↦ (![1, t] : Fin 2 → I) :=
    continuous_const.matrixVecCons (continuous_id.matrixVecCons continuous_const)
  refine (continuous_iff_continuousAt.2 fun t ↦ ?_).sub (continuous_squarePhaseAngle.comp hc)
  refine (Complex.continuousAt_arg ?_).comp (f := fun t : I ↦ squareCenterOffset ![1, t])
    (continuous_squareCenterOffset.comp hc).continuousAt
  exact Complex.mem_slitPlane_iff.2 (.inl (by norm_num))

/-- `rightEdgeAngle` is an angle function of the twisted direction along the right edge. -/
private theorem exp_rightEdgeAngle (t : I) :
    Circle.exp (rightEdgeAngle t) = squareTwist ![1, t] := by
  have hc : squareCenterOffset ![1, t] ≠ 0 :=
    squareCenterOffset_ne_zero_of_mem ⟨0, .inr rfl⟩
  refine Circle.ext ?_
  simp [squareTwist, squarePhase, rightEdgeAngle, coe_squareCenterDirection hc,
    Complex.exp_arg_mul_I hc, div_eq_mul_inv]

/-- Along the right edge the angle increases by one full turn. -/
private theorem rightEdgeAngle_one_sub_rightEdgeAngle_zero :
    rightEdgeAngle 1 - rightEdgeAngle 0 = (1 : ℤ) * (2 * Real.pi) := by
  have h := squareBoundaryDegree_mul_two_pi_eq_of_edges (Γ := squareTwist) (c := 1)
    (continuousOn_squareCenterDirection.mul continuous_squarePhase.continuousOn)
    (fun s ↦ squareTwist_eq_one (.inr (.inl rfl))) (fun s ↦ squareTwist_eq_one (.inr (.inr rfl)))
    (fun t ↦ squareTwist_eq_one (.inl rfl)) (fun t ↦ rfl) continuous_rightEdgeAngle
    exp_rightEdgeAngle
  rw [← h, squareBoundaryDegree_squareTwist]

/-- The `d`-th power of the twisted direction along the right edge, a loop in the circle at `1`. -/
private def rightEdgeLoop (d : ℕ) : Path (1 : Circle) 1 where
  toFun t := squareTwist ![1, t] ^ d
  continuous_toFun :=
    (((map_continuous Circle.exp).comp continuous_rightEdgeAngle).congr exp_rightEdgeAngle).pow d
  source' := by simp only [squareTwist_eq_one (y := ![1, 0]) (.inr (.inl rfl)), one_pow]
  target' := by simp only [squareTwist_eq_one (y := ![1, 1]) (.inr (.inr rfl)), one_pow]

private theorem rightEdgeLoop_apply (d : ℕ) (t : I) :
    rightEdgeLoop d t = squareTwist ![1, t] ^ d :=
  (rfl)

/-- The `d`-th power of the twisted direction turns `d` times around the circle along the right
edge. -/
private theorem degree_rightEdgeLoop (d : ℕ) : Circle.degree (rightEdgeLoop d) = d :=
  Circle.degree_eq_of_sub_eq (θ := fun t ↦ (d : ℝ) * rightEdgeAngle t) (rightEdgeLoop d)
    (continuous_const.mul continuous_rightEdgeAngle)
    (fun t ↦ by rw [Circle.exp_natCast_mul, exp_rightEdgeAngle, rightEdgeLoop_apply])
    (by rw [← mul_sub, rightEdgeAngle_one_sub_rightEdgeAngle_zero]; push_cast; ring)

/-! ### A lift of a polynomial sphere to the unit sphere -/

section PolynomialLift

open Polynomial

variable {n : ℕ} (P : Fin (n + 1) → ℂ[X]) (d : ℕ)

/-- The vector `(H₀(2 c, √(1 - r²)), …, Hₙ(2 c, √(1 - r²)))` of `ℂⁿ⁺¹` at a point of the square
with sup-radius `r` and offset `c` from the centre, where `Hⱼ = Polynomial.homogenize (P j) d` is
the homogenization of `P j` in degree `d`. -/
private def polyLiftVector (y : Fin 2 → I) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun j ↦ MvPolynomial.aeval
    ![2 * squareCenterOffset y, ((√(1 - cubeRadius y ^ 2) : ℝ) : ℂ)] ((P j).homogenize d)

private theorem continuous_polyLiftVector : Continuous (polyLiftVector P d) := by
  have := continuous_cubeRadius (N := Fin 2)
  have := continuous_squareCenterOffset
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦ ?_)
  simp only [MvPolynomial.aeval_eq_eval]
  exact (MvPolynomial.continuous_eval _).comp (by fun_prop)

/-- On the boundary of the square the lift vector is `(2 c)^d p_d`, for the vector `p_d` of
coefficients of `X^d`. -/
private theorem polyLiftVector_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    polyLiftVector P d y =
      (2 * squareCenterOffset y) ^ d • WithLp.toLp 2 fun j ↦ (P j).coeff d := by
  ext j
  simp only [polyLiftVector, WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply]
  rw [aeval_homogenize_of_eq_zero _ _ _
    (by simp [(cubeRadius_eq_one_iff y).2 hy])]
  simp [mul_comm]

variable {P d}

/-- Away from the boundary of the square the lift vector is `√(1 - r²)^d` times the value of `P` at
`z = 2 c / √(1 - r²)`. -/
private theorem polyLiftVector_of_notMem (hdeg : ∀ j, (P j).natDegree ≤ d) {y : Fin 2 → I}
    (hy : y ∉ Cube.boundary (Fin 2)) :
    polyLiftVector P d y = (((√(1 - cubeRadius y ^ 2) : ℝ) : ℂ) ^ d) •
      WithLp.toLp 2 fun j ↦
        (P j).eval (2 * squareCenterOffset y / (√(1 - cubeRadius y ^ 2) : ℝ)) := by
  ext j
  simp only [polyLiftVector, WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply]
  rw [aeval_homogenize (hdeg j) _
    (by simpa using Real.sqrt_ne_zero'.2 (one_sub_cubeRadius_sq_pos hy))]
  simp [mul_comm]

end PolynomialLift

/-! ### The lift covers the polynomial sphere -/

section PolynomialSphere

open Polynomial

variable {n : ℕ} {P : Fin (n + 1) → ℂ[X]} {d : ℕ}

private theorem polyLiftVector_ne_zero (hdeg : ∀ j, (P j).natDegree ≤ d)
    (hc : (fun j ↦ (P j).coeff d) ≠ 0) (hz : ∀ z : ℂ, (fun j ↦ (P j).eval z) ≠ 0)
    (y : Fin 2 → I) : polyLiftVector P d y ≠ 0 := by
  by_cases hy : y ∈ Cube.boundary (Fin 2)
  · rw [polyLiftVector_of_mem P d hy]
    exact smul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero
      (squareCenterOffset_ne_zero_of_mem hy))) ((WithLp.toLp_eq_zero 2).not.2 hc)
  · rw [polyLiftVector_of_notMem hdeg hy]
    exact smul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2
      (Real.sqrt_ne_zero'.2 (one_sub_cubeRadius_sq_pos hy)))) ((WithLp.toLp_eq_zero 2).not.2 (hz _))

variable (hdeg : ∀ j, (P j).natDegree ≤ d) (hc : (fun j ↦ (P j).coeff d) ≠ 0)
  (hz : ∀ z : ℂ, (fun j ↦ (P j).eval z) ≠ 0)

/-- The normalization of `polyLiftVector`, a lift of the polynomial sphere to the unit sphere of
`ℂⁿ⁺¹` (`mk_polyLiftUnit`). -/
private def polyLiftUnit : C(Fin 2 → I, sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :=
  normalizeToSphere (polyLiftVector P d) (continuous_polyLiftVector P d)
    (polyLiftVector_ne_zero hdeg hc hz)

/-- **The lift covers the polynomial sphere**: `[polyLiftUnit y]` is the value of `u` at the point
`riemannSphereSquare y` of the Riemann sphere, for a map `u` which is `[P(z)]` at `z ∈ ℂ` and
`[p_d]` at `∞`. -/
private theorem mk_polyLiftUnit {u : OnePoint ℂ → ComplexProjectiveSpace n}
    (hinf : homeomorphProjectivization n (u ∞) = Projectivization.mk ℂ _ hc)
    (hfin : ∀ z : ℂ, homeomorphProjectivization n (u z) = Projectivization.mk ℂ _ (hz z))
    (y : Fin 2 → I) : mk n (polyLiftUnit hdeg hc hz y) = u (riemannSphereSquare y) := by
  refine (homeomorphProjectivization n).injective ?_
  -- The lift is `‖L‖⁻¹ L` for the lift vector `L`, a multiple of `p_d` on the boundary of the
  -- square and of `P(z)` away from it.
  by_cases hy : y ∈ Cube.boundary (Fin 2)
  · rw [riemannSphereSquare_apply_of_mem hy, hinf]
    refine (homeomorphProjectivization_mk_eq_mk_iff n _ _).2
      ⟨((‖polyLiftVector P d y‖⁻¹ : ℝ) : ℂ) * (2 * squareCenterOffset y) ^ d, ?_⟩
    rw [polyLiftUnit, coe_normalizeToSphere_apply, NormedSpace.normalize,
      polyLiftVector_of_mem P d hy, WithLp.ofLp_smul, WithLp.ofLp_smul, ← Complex.coe_smul,
      smul_smul]
  · rw [riemannSphereSquare_apply_of_notMem hy, hfin]
    refine (homeomorphProjectivization_mk_eq_mk_iff n _ _).2
      ⟨((‖polyLiftVector P d y‖⁻¹ : ℝ) : ℂ) * ((√(1 - cubeRadius y ^ 2) : ℝ) : ℂ) ^ d, ?_⟩
    rw [polyLiftUnit, coe_normalizeToSphere_apply, NormedSpace.normalize,
      polyLiftVector_of_notMem hdeg hy, WithLp.ofLp_smul, WithLp.ofLp_smul, ← Complex.coe_smul,
      smul_smul]

/-- On the boundary of the square the lift is `(c / ‖c‖)^d (p_d / ‖p_d‖)`. -/
private theorem coe_polyLiftUnit_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    (polyLiftUnit hdeg hc hz y : EuclideanSpace ℂ (Fin (n + 1))) =
      ((squareCenterDirection y : ℂ) ^ d) •
        NormedSpace.normalize (WithLp.toLp 2 fun j ↦ (P j).coeff d) := by
  have hc' := squareCenterOffset_ne_zero_of_mem hy
  rw [polyLiftUnit, coe_normalizeToSphere_apply, polyLiftVector_of_mem P d hy,
    coe_squareCenterDirection hc', NormedSpace.normalize, NormedSpace.normalize,
    ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  have h0 : (‖squareCenterOffset y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc'
  have h1 : (‖WithLp.toLp 2 fun j ↦ (P j).coeff d‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 ((WithLp.toLp_eq_zero 2).not.2 hc)
  simp only [norm_smul, norm_pow, norm_mul, Complex.norm_ofNat]
  push_cast
  field_simp
  rw [← mul_pow]
  congr 1
  field_simp

end PolynomialSphere

/-! ### The boundary map on a polynomial sphere -/

section Boundary

open Polynomial

/-- The point `(s, t)` of the square for the homotopy parameter `s` and the cube point `t` of
`I^(Fin 1)`. -/
private def squarePoint (p : I × (Fin 1 → I)) : Fin 2 → I :=
  ![p.1, p.2 0]

private theorem continuous_squarePoint : Continuous squarePoint :=
  continuous_fst.matrixVecCons
    (((continuous_apply 0).comp continuous_snd).matrixVecCons continuous_const)

/-- Reindexing a point of `I^(Option (Fin 1))` along `finSuccEquiv 1` gives the point `(s, t)` of
the square. -/
private theorem comp_finSuccEquiv_piOptionEquivProdHomeomorph_symm (p : I × (Fin 1 → I)) :
    (fun m ↦ (piOptionEquivProdHomeomorph fun _ ↦ I).symm p (finSuccEquiv 1 m)) =
      squarePoint p := by
  funext m
  refine Fin.cases ?_ (fun j ↦ ?_) m
  · rw [finSuccEquiv_zero, piOptionEquivProdHomeomorph_symm_apply_none, squarePoint,
      Matrix.cons_val_zero]
  · rw [finSuccEquiv_succ, Subsingleton.elim j 0, piOptionEquivProdHomeomorph_symm_apply_some,
      squarePoint, Matrix.cons_val_succ, Matrix.cons_val_zero]

variable {n : ℕ} {P : Fin (n + 1) → ℂ[X]} {d : ℕ} (hdeg : ∀ j, (P j).natDegree ≤ d)
  (hc : (fun j ↦ (P j).coeff d) ≠ 0) (hz : ∀ z : ℂ, (fun j ↦ (P j).eval z) ≠ 0)
  {v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1} (μ : Circle)

/-- **The lift of a polynomial sphere through the Hopf fibration**: the lift `polyLiftUnit`
rotated by the `d`-th power of the phase and by a constant `μ`. -/
private def polyLift :
    C(I × (Fin 1 → I), TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)) where
  toFun p := (μ * squarePhase (squarePoint p) ^ d) • polyLiftUnit hdeg hc hz (squarePoint p)
  continuous_toFun :=
    (continuous_const.mul ((continuous_squarePhase.comp continuous_squarePoint).pow d)).smul
      ((polyLiftUnit hdeg hc hz).continuous.comp continuous_squarePoint)

/-- `polyLift` at `p` is `polyLiftUnit` at `squarePoint p` rotated by `μ λ^d`. -/
private theorem coe_polyLift_apply (p : I × (Fin 1 → I)) :
    ((polyLift hdeg hc hz μ p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
        EuclideanSpace ℂ (Fin (n + 1))) =
      ((μ * squarePhase (squarePoint p) ^ d : Circle) : ℂ) •
        (polyLiftUnit hdeg hc hz (squarePoint p) : EuclideanSpace ℂ (Fin (n + 1))) :=
  (rfl)

/-- Over the boundary of the square the lift is the `d`-th power of the twisted direction times
`v`, when `μ` rotates the unit leading vector `p_d / ‖p_d‖` to `v`. -/
private theorem coe_polyLift_of_mem
    (hμ : (μ : ℂ) • NormedSpace.normalize (WithLp.toLp 2 fun j ↦ (P j).coeff d) =
      (v : EuclideanSpace ℂ (Fin (n + 1)))) {p : I × (Fin 1 → I)}
    (hp : squarePoint p ∈ Cube.boundary (Fin 2)) :
    ((polyLift hdeg hc hz μ p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
        EuclideanSpace ℂ (Fin (n + 1))) =
      ((squareTwist (squarePoint p) ^ d : Circle) : ℂ) • (v : EuclideanSpace ℂ (Fin (n + 1))) := by
  rw [coe_polyLift_apply, coe_polyLiftUnit_of_mem hdeg hc hz hp, ← hμ, smul_smul, smul_smul,
    squareTwist, Pi.mul_apply]
  congr 1
  push_cast
  ring

/-- `polyLift` is a boundary lift of the polynomial sphere, read in `I^(Option (Fin 1))`. -/
private theorem isBoundaryLift_polyLift {u : C(OnePoint ℂ, ComplexProjectiveSpace n)}
    (hinf : homeomorphProjectivization n (u ∞) = Projectivization.mk ℂ _ hc)
    (hfin : ∀ z : ℂ, homeomorphProjectivization n (u z) = Projectivization.mk ℂ _ (hz z))
    (hv : u ∞ = mk n v)
    (hμ : (μ : ℂ) • NormedSpace.normalize (WithLp.toLp 2 fun j ↦ (P j).coeff d) =
      (v : EuclideanSpace ℂ (Fin (n + 1)))) :
    TopCat.IsBoundaryLift (hopfHom n) ⟨v, rfl⟩
      (GenLoop.congr (mk n v) (finSuccEquiv 1) (GenLoop.map u hv riemannSphereSquare))
      (polyLift hdeg hc hz μ) where
  proj_apply p := by
    rw [GenLoop.congr_apply, GenLoop.map_apply,
      comp_finSuccEquiv_piOptionEquivProdHomeomorph_symm]
    exact (mk_circle_smul _ _ _).trans (mk_polyLiftUnit hdeg hc hz hinf hfin _)
  apply_zero t := Subtype.ext <| by
    rw [coe_polyLift_of_mem hdeg hc hz μ hμ (p := (0, t)) (IsPhaseEdge.mem_boundary (.inl rfl)),
      squareTwist_eq_one (.inl rfl), one_pow, Circle.coe_one, one_smul]
  apply_of_mem_boundary s t ht := by
    obtain ⟨i, hi⟩ := ht
    rw [Subsingleton.elim i 0] at hi
    refine Subtype.ext ?_
    rw [coe_polyLift_of_mem hdeg hc hz μ hμ (p := (s, t)) (IsPhaseEdge.mem_boundary (.inr hi)),
      squareTwist_eq_one (.inr hi), one_pow, Circle.coe_one, one_smul]

/-- A unit vector spanning the line `[p_d]` is a unit complex multiple of `p_d / ‖p_d‖`. -/
private theorem exists_circle_smul_normalize
    (h : homeomorphProjectivization n (mk n v) = Projectivization.mk ℂ _ hc) :
    ∃ μ : Circle, (μ : ℂ) • NormedSpace.normalize (WithLp.toLp 2 fun j ↦ (P j).coeff d) =
      (v : EuclideanSpace ℂ (Fin (n + 1))) := by
  have hvw := (homeomorphProjectivization n).symm_apply_apply (mk n v)
  rw [h, homeomorphProjectivization_symm_mk_eq_mk_inv_norm_smul] at hvw
  obtain ⟨μ, hμ⟩ := (mk_eq_mk_iff_exists_circle_smul n v _).1 hvw.symm
  refine ⟨μ, ?_⟩
  rw [← hμ, Circle.coe_smul_sphere, NormedSpace.normalize, ← Complex.coe_smul, Complex.ofReal_inv]

end Boundary

/-! ### The class of a polynomial sphere -/

open Polynomial in
/-- **The class of a polynomial sphere in `π₂(CPⁿ)` is its degree.** Let `u : ℂℙ¹ → CPⁿ`,
`n ≥ 1`, be a continuous map from the Riemann sphere given by polynomials `P₀, …, Pₙ` of degree at
most `d` without common zero, `u z = [P₀(z) : ⋯ : Pₙ(z)]` at `z ∈ ℂ` and
`u ∞ = [p_d]` for the nonzero vector `p_d` of their coefficients of `X^d`, with the points of
`CPⁿ` read as lines through `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`. Then the
isomorphism `π₂(CPⁿ) ≃* ℤ` of the Hopf fibration, at any unit vector `v` over `u ∞`, sends the
class of `u` composed with the standard sphere `TauCeti.riemannSphereSquare` to `d`. -/
theorem pi2MulEquivInt_map_riemannSphereSquare_of_polynomial {n : ℕ} (hn : n ≠ 0)
    {P : Fin (n + 1) → ℂ[X]} {d : ℕ} (hdeg : ∀ j, (P j).natDegree ≤ d)
    {u : C(OnePoint ℂ, ComplexProjectiveSpace n)}
    (hinf : ∃ h : (fun j ↦ (P j).coeff d) ≠ 0,
      homeomorphProjectivization n (u ∞) = Projectivization.mk ℂ _ h)
    (hfin : ∀ z : ℂ, ∃ h : (fun j ↦ (P j).eval z) ≠ 0,
      homeomorphProjectivization n (u z) = Projectivization.mk ℂ _ h)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (hv : u ∞ = mk n v) :
    pi2MulEquivInt v hn (HomotopyGroup.map u hv ⟦riemannSphereSquare⟧) =
      Multiplicative.ofAdd (d : ℤ) := by
  obtain ⟨hc, hinf⟩ := hinf
  choose hz hfin using hfin
  obtain ⟨μ, hμ⟩ := exists_circle_smul_normalize hc (hv ▸ hinf)
  have hL := isBoundaryLift_polyLift hdeg hc hz μ hinf hfin hv hμ
  -- The boundary map is the class of the end of the boundary lift `polyLift`, the loop
  -- `rightEdgeLoop d` of the fibre circle over `[v]`.
  have hb : hopfBoundary v (Fin 1) (HomotopyGroup.congrEquiv (finSuccEquiv 1)
      (HomotopyGroup.map u hv ⟦riemannSphereSquare⟧)) =
      HomotopyGroup.map ⟨Circle.homeomorphSphere, Homeomorph.continuous _⟩ (by ext; simp)
        ⟦(genLoopEquivOfUnique (Fin 1)).symm (rightEdgeLoop d)⟧ := by
    rw [HomotopyGroup.map_mk, HomotopyGroup.congrEquiv_mk]
    refine (hopfBoundary_apply _ _).trans <|
      (congrArg _ (TopCat.fibrationBoundary_mk (mk_mem_serreFibrations n) hL)).trans <|
      (HomotopyGroup.homeomorphEquivOfEq_apply _ _ _).trans <|
      (HomotopyGroup.map_mk _ _ _).trans <| Eq.trans ?_ (HomotopyGroup.map_mk _ _ _).symm
    refine congrArg _ (GenLoop.ext _ _ fun t ↦ ?_)
    rw [GenLoop.map_apply, GenLoop.map_apply]
    refine (hopfFiberHomeomorph _).symm_apply_eq.2 (Subtype.ext (Subtype.ext ?_))
    rw [TopCat.IsBoundaryLift.endLoop_apply_coe, coe_hopfFiberHomeomorph_apply,
      coe_polyLift_of_mem hdeg hc hz μ hμ (p := (1, t)) ⟨0, .inr rfl⟩, ContinuousMap.coe_mk,
      GenLoop.genLoopEquivOfUnique_symm_apply, rightEdgeLoop_apply, Sphere.coe_sphere_smul,
      Circle.coe_homeomorphSphere_apply, squarePoint, Subsingleton.elim (default : Fin 1) 0]
  have h1 : Circle.homeomorphSphere (1 : Circle) = 1 := by ext; simp
  -- The circle reads the boundary loop as `rightEdgeLoop d`, of degree `d`.
  have hcircle : HomotopyGroup.map ⟨Circle.homeomorphSphere.symm, Homeomorph.continuous _⟩
      (by ext; simp)
      (HomotopyGroup.map ⟨Circle.homeomorphSphere, Homeomorph.continuous _⟩ h1
        ⟦(genLoopEquivOfUnique (Fin 1)).symm (rightEdgeLoop d)⟧) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (.mk (rightEdgeLoop d))) := by
    rw [HomotopyGroup.pi1MulEquivFundamentalGroup_symm_fromPath_mk, HomotopyGroup.map_mk,
      HomotopyGroup.map_mk]
    refine congrArg _ (GenLoop.ext _ _ fun t ↦ ?_)
    rw [GenLoop.map_apply, GenLoop.map_apply]
    exact Circle.homeomorphSphere.symm_apply_apply _
  rw [pi2MulEquivInt_apply]
  refine (congrArg (fun a ↦ Circle.fundamentalGroupMulEquiv 1
    (HomotopyGroup.pi1MulEquivFundamentalGroup (HomotopyGroup.map _ _ a))) hb).trans ?_
  refine (congrArg (fun a ↦ Circle.fundamentalGroupMulEquiv 1
    (HomotopyGroup.pi1MulEquivFundamentalGroup a)) hcircle).trans ?_
  rw [MulEquiv.apply_symm_apply, Circle.fundamentalGroupMulEquiv_fromPath, degree_rightEdgeLoop]

/-! ### The class of the coordinate line -/

variable (n : ℕ)

/-- The base point `affineParam 1 0` of the coordinate line is the base point `[e₁]` of
`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`. -/
private theorem id_affineParam_one_zero :
    ContinuousMap.id (ComplexProjectiveSpace (n + 1)) (affineParam 1 0) =
      mk (n + 1) (affineUnitVector 1 0) :=
  (ContinuousMap.id_apply _).trans (affineParam_def 1 0)

/-- The class of the coordinate line `lineSquare n` in `π₂(CPⁿ⁺¹)` at the base point
`[e₁] = mk (n + 1) (affineUnitVector 1 0)` of `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`,
carried there by `HomotopyGroup.map` of the identity from its own base point `affineParam 1 0`,
which is the same point (`affineParam_def`). -/
def lineClass :
    HomotopyGroup (Fin 2) (ComplexProjectiveSpace (n + 1)) (mk (n + 1) (affineUnitVector 1 0)) :=
  HomotopyGroup.map (ContinuousMap.id _) (id_affineParam_one_zero n) ⟦lineSquare n⟧

/-- `lineClass n` is the class of `lineSquare n` carried to `[e₁]` by `HomotopyGroup.map` of the
identity. -/
theorem lineClass_def :
    lineClass n = HomotopyGroup.map (ContinuousMap.id _)
      ((ContinuousMap.id_apply _).trans (affineParam_def 1 0)) ⟦lineSquare n⟧ :=
  (rfl)

/-- Any quantity depending on a base point and a class in `π₂(CPⁿ⁺¹)` at that point takes the same
value on `lineClass n` at `[e₁]` as on `⟦lineSquare n⟧` at `affineParam 1 0`: the two base points
agree and `lineClass n` is `⟦lineSquare n⟧` carried along `HomotopyGroup.map` of the identity. -/
theorem apply_lineClass {α : Sort*}
    (f : ∀ y, HomotopyGroup (Fin 2) (ComplexProjectiveSpace (n + 1)) y → α) :
    f _ (lineClass n) = f (affineParam 1 0) ⟦lineSquare n⟧ := by
  rw [lineClass_def]
  exact HomotopyGroup.apply_map_id f _ _

/-- `lineClass n` is the class of the coordinate line composed with the standard sphere of the
Riemann sphere. -/
private theorem lineClass_eq_map :
    lineClass n = HomotopyGroup.map (coordinateLine n)
      ((coordinateLine_infty (n := n)).trans (affineParam_def 1 0)) ⟦riemannSphereSquare⟧ := by
  rw [lineClass_def, mk_lineSquare_eq_map]
  exact (HomotopyGroup.map_comp_apply _ _ _ _ _).trans
    (HomotopyGroup.map_congr (ContinuousMap.id_comp _) _ _ _)

open Polynomial in
/-- The polynomials `(1, X, 0, …, 0)` of the coordinate line. -/
private def linePolynomial (j : Fin (n + 2)) : ℂ[X] :=
  C ((Pi.single 1 1 : Fin (n + 2) → ℂ) j) * X + C ((Pi.single 0 1 : Fin (n + 2) → ℂ) j)

/-- The leading coefficients of `(1, X, 0, …, 0)` are `e₁`. -/
private theorem coeff_one_linePolynomial :
    (fun j ↦ (linePolynomial n j).coeff 1) = Pi.single 1 1 := by
  ext j
  simp [linePolynomial]

/-- The value of `(1, X, 0, …, 0)` at `z` is `(1, z, 0, …, 0)`. -/
private theorem eval_linePolynomial (z : ℂ) :
    (fun j ↦ (linePolynomial n j).eval z) =
      WithLp.ofLp (affineVector 0 (Pi.single 0 z : Fin (n + 1) → ℂ)) := by
  ext j
  induction j using Fin.succAboveCases 0 with
  | x => simp [linePolynomial, affineVector_apply_self]
  | p j =>
    rw [affineVector_apply_succAbove]
    induction j using Fin.cases with
    | zero => simp [linePolynomial]
    | succ k => simp [linePolynomial, Fin.ext_iff]

/-- **The coordinate line generates `π₂(CPⁿ⁺¹)`.** The isomorphism `π₂(CPⁿ⁺¹) ≃* ℤ` of the Hopf
fibration sends the class `lineClass n` of the coordinate line `[1 : z : 0 : ⋯ : 0]`, read as a
sphere through the standard sphere of the Riemann sphere, to `1`: it is the polynomial sphere of
the polynomials `(1, X, 0, …, 0)`, of degree one. -/
theorem pi2MulEquivInt_lineClass :
    pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero (lineClass n) =
      Multiplicative.ofAdd 1 := by
  rw [lineClass_eq_map]
  have hc : (fun j ↦ (linePolynomial n j).coeff 1) ≠ 0 := by
    rw [coeff_one_linePolynomial]
    exact fun h ↦ (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congr_fun h (1 : Fin (n + 2)))
  refine pi2MulEquivInt_map_riemannSphereSquare_of_polynomial (P := linePolynomial n) (d := 1)
    _ (fun j ↦ Polynomial.natDegree_linear_le) ⟨hc, ?_⟩ (fun z ↦ ⟨?_, ?_⟩) _ _
  · rw [coordinateLine_infty, affineParam_def]
    refine (homeomorphProjectivization_mk_eq_mk_iff _ _ _).2 ⟨1, ?_⟩
    rw [one_smul, coeff_one_linePolynomial, coe_affineUnitVector_zero]
    simp
  · rw [eval_linePolynomial]
    exact (WithLp.ofLp_eq_zero 2).not.2 (affineVector_ne_zero 0 _)
  · rw [coordinateLine_coe, affineParam_def]
    refine (homeomorphProjectivization_mk_eq_mk_iff _ _ _).2
      ⟨((‖affineVector 0 (Pi.single 0 z : Fin (n + 1) → ℂ)‖⁻¹ : ℝ) : ℂ), ?_⟩
    rw [coe_affineUnitVector_apply, WithLp.ofLp_smul, Complex.coe_smul, eval_linePolynomial]

/-- **The generator of `π₂(CPⁿ⁺¹)` is the coordinate line**: the element of `π₂(CPⁿ⁺¹)` sent to `1`
by `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt` is the class `lineClass n` of `lineSquare n`,
carried to the base point `[e₁]` along `affineParam 1 0 = [e₁]`. -/
theorem pi2MulEquivInt_symm_ofAdd_one :
    (pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero).symm (Multiplicative.ofAdd 1) =
      lineClass n :=
  (MulEquiv.symm_apply_eq _).2 (pi2MulEquivInt_lineClass n).symm

end TauCeti.ComplexProjectiveSpace
