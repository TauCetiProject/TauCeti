/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.NormedSpace
public import TauCeti.Geometry.Symplectic.Liouville.LinearAtInfinity
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The closed ball of a symplectic vector space as a Liouville domain

Let `ω` be a linear symplectic form on a finite-dimensional real inner product space `E`, regarded
as the constant symplectic form `TauCeti.SymplecticForm.constSmooth ω` on `E`, with its radial
primitive `λₓ(v) = ω(x, v) / 2` (`TauCeti.SymplecticForm.radialPrimitive`) and Liouville field
`Z(x) = x / 2`. No compatibility between `ω` and the inner product is needed.

The Liouville field points strictly out of every closed ball `B = closedBall 0 r`, `r > 0`, along
its boundary sphere, the level `‖x‖² = r²`: the derivative of `‖x‖²` along `Z` is `‖x‖²`. So `B` is
a Liouville domain (`TauCeti.SymplecticForm.isLiouvilleDomain_closedBall`). The flow of `Z` is the
dilation `x ↦ e^(t/2) • x` (`TauCeti.flowOf_dilation`), which is defined for all time and shrinks
every point into `B`, so `E` is the completion of `B`
(`TauCeti.SymplecticForm.isLiouvilleCompletion_closedBall`).

The point `x` with `‖x‖ > r` is reached from the boundary point `(r / ‖x‖) • x` by flowing for the
time `2 log (‖x‖ / r)`, so the radial coordinate of the cylindrical end is
`ρ(x) = ‖x‖² / r²` there, and `1` on `B`
(`TauCeti.liouvilleRadialCoordinate_closedBall`). For the unit ball it is `‖x‖²` outside the
ball.
In particular the quadratic Hamiltonian `a ‖x‖²` is linear at infinity, with slope `a r²`
(`TauCeti.isLinearAtInfinity_mul_norm_sq`). These are the Hamiltonians whose direct
limit over the slope defines the symplectic homology of the ball.

For `E = ℝ²ⁿ` with coordinates `(q, p)` and `ω = Σⱼ dqⱼ ∧ dpⱼ`, the primitive is
`λ = ½ Σⱼ (qⱼ dpⱼ - pⱼ dqⱼ)` and `B` is the standard ball `D²ⁿ`. The opposite primitive
`½ Σⱼ (pⱼ dqⱼ - qⱼ dpⱼ)`, whose differential is `-ω`, is the primitive of no Liouville domain for
`ω` (`TauCeti.SymplecticForm.not_isLiouvilleDomain_neg_radialPrimitive`).

## Main results

* `TauCeti.SymplecticForm.isLiouvilleDomain_closedBall`: a closed ball of positive radius is a
  Liouville domain for the constant form and its radial primitive.
* `TauCeti.SymplecticForm.isLiouvilleCompletion_closedBall`: the vector space is its completion.
* `TauCeti.SymplecticForm.not_isLiouvilleDomain_neg_radialPrimitive`: the opposite primitive
  `-λ` is the primitive of no Liouville domain.
* `TauCeti.liouvilleRadialCoordinate_closedBall`: the radial coordinate is
  `max 1 (‖x‖² / r²)`.
* `TauCeti.isLinearAtInfinity_mul_norm_sq`: `a ‖x‖²` is linear at infinity with
  slope `a r²`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the radial Liouville vector field of a symplectic vector space).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Liouville domains, their completions and Hamiltonians linear at infinity).
-/

public section

noncomputable section

open Metric
open scoped Manifold InnerProductSpace

namespace TauCeti

section RadialCoordinate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ}

/-- The backward flow of the field `x / 2` carries `x` into the closed ball of radius `r > 0` at a
time `t ≥ 0` exactly when `t ≥ 2 log (‖x‖ / r)`. -/
private theorem flowOf_neg_two_inv_smul_mem_closedBall_iff (hr : 0 < r) (x : E) {t : ℝ}
    (ht : 0 ≤ t) :
    flowOf (I := 𝓘(ℝ, E)) (fun y : E ↦ (2⁻¹ : ℝ) • y) (-t) x ∈ closedBall (0 : E) r ↔
      2 * Real.log (‖x‖ / r) ≤ t := by
  rw [flowOf_dilation, mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx, zero_div, Real.log_zero, mul_zero, mul_zero]
    exact iff_of_true hr.le ht
  · -- Take logarithms: the condition becomes `-t / 2 + log ‖x‖ ≤ log r`.
    rw [← Real.log_le_log_iff (by positivity) hr, Real.log_mul (Real.exp_pos _).ne' hx.ne',
      Real.log_exp, Real.log_div hx.ne' hr.ne']
    constructor <;> intro h <;> linarith

/-- The backward flow of the field `x / 2` carries every point into the closed ball of radius
`r > 0`. -/
private theorem exists_flowOf_two_inv_smul_mem_closedBall (hr : 0 < r) (x : E) :
    ∃ t, flowOf (I := 𝓘(ℝ, E)) (fun y : E ↦ (2⁻¹ : ℝ) • y) t x ∈ closedBall (0 : E) r :=
  ⟨_, (flowOf_neg_two_inv_smul_mem_closedBall_iff hr x (le_max_left 0 _)).2 (le_max_right _ _)⟩

/-- **The radial coordinate of the dilation field over a closed ball.** For the field `x / 2`,
the Liouville field of the radial primitive of a linear symplectic form, and the closed ball of
radius `r > 0`, the radial coordinate is `1` on the ball and `‖x‖² / r²` outside it. For the unit
ball it is `‖x‖²` outside the ball. -/
theorem liouvilleRadialCoordinate_closedBall (hr : 0 < r) (x : E) :
    liouvilleRadialCoordinate (I := 𝓘(ℝ, E)) (fun y : E ↦ (2⁻¹ : ℝ) • y) (closedBall (0 : E) r)
      x = max 1 (‖x‖ ^ 2 / r ^ 2) := by
  -- The admissible times form the ray `[max 0 (2 log (‖x‖ / r)), ∞)`.
  have hset : {t : ℝ | 0 ≤ t ∧ flowOf (I := 𝓘(ℝ, E)) (fun y : E ↦ (2⁻¹ : ℝ) • y) (-t) x ∈
      closedBall (0 : E) r} = Set.Ici (max 0 (2 * Real.log (‖x‖ / r))) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, max_le_iff]
    exact ⟨fun h ↦ ⟨h.1, (flowOf_neg_two_inv_smul_mem_closedBall_iff hr x h.1).1 h.2⟩,
      fun h ↦ ⟨h.1, (flowOf_neg_two_inv_smul_mem_closedBall_iff hr x h.1).2 h.2⟩⟩
  refine (liouvilleRadialCoordinate_def _ _ x).trans ?_
  rw [hset, csInf_Ici, Real.exp_monotone.map_max, Real.exp_zero]
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx, zero_div, Real.log_zero, mul_zero, Real.exp_zero]
    simp
  · rw [← Nat.cast_two, ← Real.log_pow, Real.exp_log (by positivity), div_pow]

/-- **Quadratic Hamiltonians are linear at infinity.** Over the closed ball of radius `r > 0` in a
finite-dimensional real normed space, with the field `x / 2`, the Hamiltonian `a ‖x‖²` is linear at
infinity with slope `a r²`: outside the ball it is `a r²` times the radial coordinate. -/
theorem isLinearAtInfinity_mul_norm_sq [ProperSpace E] (hr : 0 < r) (a : ℝ) :
    IsLinearAtInfinity (I := 𝓘(ℝ, E)) (fun y : E ↦ (2⁻¹ : ℝ) • y) (closedBall (0 : E) r)
      (fun x ↦ a * ‖x‖ ^ 2) (a * r ^ 2) := by
  refine isLinearAtInfinity_def.2 ⟨closedBall 0 r, isCompact_closedBall 0 r, 0, fun x hx ↦ ?_⟩
  have hgt : 1 < ‖x‖ ^ 2 / r ^ 2 :=
    (one_lt_div (pow_pos hr 2)).2 (pow_lt_pow_left₀ (not_le.1 (mt mem_closedBall_zero_iff.2 hx))
      hr.le two_ne_zero)
  rw [liouvilleRadialCoordinate_closedBall hr, max_eq_right hgt.le, add_zero, mul_assoc,
    mul_div_cancel₀ _ (pow_pos hr 2).ne']

end RadialCoordinate

namespace SymplecticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℝ}

/-- The derivative of `‖x‖²` along the Liouville field `Z(x) = x / 2` is `‖x‖²`. -/
private theorem mvfderiv_norm_sq_two_inv_smul (x : E) :
    mvfderiv 𝓘(ℝ, E) (fun y : E ↦ ‖y‖ ^ 2) x ((2⁻¹ : ℝ) • x) = ‖x‖ ^ 2 := by
  refine (mvfderiv_eq_fderiv_apply _ x _).trans ?_
  simp [fderiv_norm_sq_apply]

variable [FiniteDimensional ℝ E] (ω : SymplecticForm E)

/-- **A closed ball of a symplectic vector space is a Liouville domain.** For a linear symplectic
form `ω` on a finite-dimensional real inner product space and `r > 0`, the closed ball of radius
`r` is a Liouville domain for the constant form `ω` with its radial primitive
`λₓ(v) = ω(x, v) / 2`: the Liouville field `x / 2` points strictly outwards along the sphere
`‖x‖² = r²`. -/
theorem isLiouvilleDomain_closedBall (hr : 0 < r) :
    IsLiouvilleDomain ω.constSmooth ω.radialPrimitive (closedBall (0 : E) r) where
  isNondegenerate := ω.isNondegenerate_constSmooth
  mextDeriv_eq := ω.mextDeriv_radialPrimitive
  isCompact := isCompact_closedBall 0 r
  subset_interior := by simp [ModelWithCorners.interior_eq_univ]
  exists_liouville_outward := by
    refine ⟨fun x : E ↦ (2⁻¹ : ℝ) • x, contMDiff_dilation _ _, ω.constSmooth_interior_two_inv_smul,
      fun x : E ↦ ‖x‖ ^ 2, r ^ 2, continuous_norm.pow 2, Set.ext fun x ↦ ?_,
      fun x hx ↦ ⟨(contDiff_norm_sq ℝ).contMDiff.contMDiffAt, ?_⟩⟩
    · rw [mem_closedBall_zero_iff, Set.mem_ofPred_eq, sq_le_sq₀ (norm_nonneg x) hr.le]
    · beta_reduce at hx
      rw [mvfderiv_norm_sq_two_inv_smul, hx]
      exact pow_pos hr 2

/-- **A symplectic vector space is the completion of each of its closed balls.** The flow
`x ↦ e^(t/2) • x` of the Liouville field `x / 2` of the radial primitive is defined for all time,
and carries every point into the closed ball of radius `r > 0`. -/
theorem isLiouvilleCompletion_closedBall (hr : 0 < r) :
    IsLiouvilleCompletion ω.constSmooth ω.radialPrimitive (closedBall (0 : E) r) where
  toIsLiouvilleDomain := ω.isLiouvilleDomain_closedBall hr
  exists_isCompleteVectorField := ⟨fun x : E ↦ (2⁻¹ : ℝ) • x,
    ω.constSmooth_interior_two_inv_smul, isCompleteVectorField_dilation _,
    exists_flowOf_two_inv_smul_mem_closedBall hr⟩

end SymplecticForm

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V] (ω : SymplecticForm V)

/-- **The opposite radial primitive is excluded.** On a nonzero symplectic vector space, no set is
a Liouville domain for the constant form `ω` with the primitive `-λ`, `λₓ(v) = ω(x, v) / 2`: its
differential is `-ω`. For `ω = Σⱼ dqⱼ ∧ dpⱼ` this primitive is `½ Σⱼ (pⱼ dqⱼ - qⱼ dpⱼ)`, so the
standard ball `D²ⁿ` is a Liouville domain for `½ Σⱼ (qⱼ dpⱼ - pⱼ dqⱼ)` but not for its negative
`½ Σⱼ (pⱼ dqⱼ - qⱼ dpⱼ)`. -/
theorem not_isLiouvilleDomain_neg_radialPrimitive (W : Set V) :
    ¬ IsLiouvilleDomain ω.constSmooth (-ω.radialPrimitive) W :=
  not_isLiouvilleDomain_neg_of_mextDeriv_eq ω.mextDeriv_radialPrimitive W

end SymplecticForm

end TauCeti
