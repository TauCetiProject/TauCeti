/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Basic

/-!
# The Lyapunov--Perron graph

Let `A` and `P` be bounded operators on a real Banach space `X` such that the linear flow
`exp (t A)` damps `P v` exponentially in forward time and `v - P v` exponentially in backward
time, with constant `K` and rate `α > 0`; let `N` be globally `ε`-Lipschitz, with `2 K ε < α`.
When moreover `P` is idempotent and commutes with `A`, the initial values of the solutions of
`y' = A y + N y` that stay bounded on `[0, ∞)` are exactly the fixed points of
`ξ ↦ lyapunovPerronSolution ξ 0`.

This file identifies that fixed-point set as a **Lipschitz graph over the range of `P`**. The
graph map `ContinuousLinearMap.lyapunovPerronGraphMap` records how far the initial value of a
Lyapunov--Perron solution sits from `P ξ`. It takes values in the kernel of `P`, depends only on
`P ξ`, and is Lipschitz with a constant that tends to `0` with `ε`: in the limit of a vanishing
nonlinearity the graph flattens onto the range of `P`. The projection `P` and the parametrization
`v ↦ v + graph map v` invert each other, so `P` is a bijection from the fixed-point set onto the
range of `P`.

When the nonlinearity fixes the origin, the fixed-point set is the set of initial values of
forward solutions tending to the equilibrium `0`. The graph description is therefore the Lipschitz
form of the stable-manifold theorem for a globally small nonlinearity; the local theorem at a
hyperbolic equilibrium follows once the nonlinearity has been cut off outside a small ball, and
the passage from a Lipschitz graph to a differentiable one is a separate argument.

## Main declarations

* `ContinuousLinearMap.lyapunovPerronGraphMap`: the displacement of the initial value of a
  Lyapunov--Perron solution away from the range of `P`.
* `ContinuousLinearMap.apply_lyapunovPerronGraphMap`: it takes values in the kernel of `P`.
* `ContinuousLinearMap.lipschitzWith_lyapunovPerronGraphMap`: it is Lipschitz, with a constant
  that tends to `0` with the Lipschitz constant of the nonlinearity;
  `ContinuousLinearMap.norm_lyapunovPerronGraphMap_le` is the resulting cone bound.
* `ContinuousLinearMap.setOf_lyapunovPerronSolution_zero_eq_image`: the fixed-point set is the
  graph of the graph map over the range of `P`.
* `ContinuousLinearMap.invOn_lyapunovPerronGraphMap` and
  `ContinuousLinearMap.bijOn_apply_setOf_lyapunovPerronSolution_zero`: `P` parametrizes the
  fixed-point set by the range of `P`.
* `ContinuousLinearMap.setOf_exists_isIntegralCurveOn_bounded_eq_image` and
  `ContinuousLinearMap.setOf_exists_isIntegralCurveOn_tendsto_eq_image`: the initial values of
  the bounded forward solutions, respectively of the forward solutions tending to `0`, form that
  graph.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629, Springer,
  1978, Chapter 5.
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter NormedSpace Topology
open scoped NNReal

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K α : ℝ≥0} {N : X → X} {ε : ℝ≥0}
variable (A P : X →L[ℝ] X) (N : X → X)
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hN : LipschitzWith ε N) (hsmall : 2 * K * ε < α)

/-- The **Lyapunov--Perron graph map**: the displacement of the initial value
`lyapunovPerronSolution ξ 0` of the Lyapunov--Perron solution with input parameter `ξ` away from
`P ξ`.

When `P` is idempotent and commutes with `A`, this displacement lies in the kernel of `P` and
depends only on `P ξ`, so the initial values of the bounded forward solutions of `y' = A y + N y`
form the graph of this map over the range of `P`. -/
def lyapunovPerronGraphMap (ξ : X) : X :=
  lyapunovPerronSolution A P N hs hu hα hN hsmall ξ 0 - P ξ

variable {A P N}

/-- The graph map is the displacement of the initial value of the Lyapunov--Perron solution away
from `P ξ`. -/
theorem lyapunovPerronGraphMap_eq_sub (ξ : X) :
    lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ =
      lyapunovPerronSolution A P N hs hu hα hN hsmall ξ 0 - P ξ :=
  (rfl)

/-- The initial value of a Lyapunov--Perron solution splits as `P ξ` plus the graph
displacement. -/
theorem lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap (ξ : X) :
    lyapunovPerronSolution A P N hs hu hα hN hsmall ξ 0 =
      P ξ + lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ := by
  rw [lyapunovPerronGraphMap_eq_sub]
  abel

/-- The graph displacement is the value at time `0` of the integral terms of the Lyapunov--Perron
equation: at time `0` the homogeneous term contributes exactly `P ξ`. -/
theorem lyapunovPerronGraphMap_eq_lyapunovPerronIntegral (ξ : X) :
    lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ =
      lyapunovPerronIntegral A P
        (fun s ↦ N (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ s.toNNReal)) 0 := by
  rw [lyapunovPerronGraphMap_eq_sub, lyapunovPerronSolution_apply, NNReal.coe_zero, zero_smul,
    exp_zero, one_apply_eq_self, add_sub_cancel_left]

/-- When `P` is idempotent and commutes with `A`, the graph displacement lies in the kernel of
`P`. -/
@[simp]
theorem apply_lyapunovPerronGraphMap (hP : IsIdempotentElem P) (hAP : Commute A P) (ξ : X) :
    P (lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ) = 0 := by
  rw [lyapunovPerronGraphMap_eq_sub, map_sub,
    apply_lyapunovPerronSolution_zero hs hu hα hN hsmall hP hAP, ← mul_apply_eq_comp P P, hP.eq,
    sub_self]

/-- When `P` is idempotent, the graph displacement depends only on the `P`-component of the input
parameter. -/
@[simp]
theorem lyapunovPerronGraphMap_map (hP : IsIdempotentElem P) (ξ : X) :
    lyapunovPerronGraphMap A P N hs hu hα hN hsmall (P ξ) =
      lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ := by
  rw [lyapunovPerronGraphMap_eq_sub, lyapunovPerronGraphMap_eq_sub,
    lyapunovPerronSolution_map hs hu hα hN hsmall hP, ← mul_apply_eq_comp P P, hP.eq]

/-- If the nonlinearity vanishes at the origin, so does the graph map. -/
@[simp]
theorem lyapunovPerronGraphMap_zero (hN0 : N 0 = 0) :
    lyapunovPerronGraphMap A P N hs hu hα hN hsmall 0 = 0 := by
  simp [lyapunovPerronGraphMap_eq_sub, lyapunovPerronSolution_zero hs hu hα hN hsmall hN0]

/-- **The Lyapunov--Perron graph map is Lipschitz.** Its constant, which equals
`2 K² ε / (α - 2 K ε)`, tends to `0` with the Lipschitz constant `ε` of the nonlinearity: in the
limit of a vanishing nonlinearity the graph flattens onto the range of `P`. -/
theorem lipschitzWith_lyapunovPerronGraphMap :
    LipschitzWith (2 * K * ε / α * (K / (1 - 2 * K * ε / α)))
      (lyapunovPerronGraphMap A P N hs hu hα hN hsmall) := by
  have hlt : 2 * K * ε / α < 1 := (div_lt_one hα).2 hsmall
  have hcoe : ((2 * K * ε / α : ℝ≥0) : ℝ) = 2 * K * ε / α := by push_cast; ring
  have hcoe1 : ((1 - 2 * K * ε / α : ℝ≥0) : ℝ) = 1 - 2 * K * ε / α := by
    rw [NNReal.coe_sub hlt.le, NNReal.coe_one, hcoe]
  refine LipschitzWith.of_dist_le_mul fun ξ ζ ↦ ?_
  -- Both graph displacements are values at time `0` of the Lyapunov--Perron operator with input
  -- parameter `0`, whose homogeneous term then cancels in the difference.
  have hgraph : dist (lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ)
      (lyapunovPerronGraphMap A P N hs hu hα hN hsmall ζ) ≤
      2 * K * ε / α * dist (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ)
        (lyapunovPerronSolution A P N hs hu hα hN hsmall ζ) := by
    have h : dist (lyapunovPerronMap A P N hs hu hα hN (0 : X)
          (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ) 0)
        (lyapunovPerronMap A P N hs hu hα hN (0 : X)
          (lyapunovPerronSolution A P N hs hu hα hN hsmall ζ) 0) ≤
        2 * K * ε / α * dist (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ)
          (lyapunovPerronSolution A P N hs hu hα hN hsmall ζ) :=
      (BoundedContinuousFunction.dist_coe_le_dist _).trans
        (dist_lyapunovPerronMap_le hs hu hα hN _ _ _)
    rwa [dist_eq_norm, lyapunovPerronMap_apply, lyapunovPerronMap_apply, add_sub_add_left_eq_sub,
      NNReal.coe_zero, ← lyapunovPerronGraphMap_eq_lyapunovPerronIntegral hs hu hα hN hsmall,
      ← lyapunovPerronGraphMap_eq_lyapunovPerronIntegral hs hu hα hN hsmall,
      ← dist_eq_norm] at h
  have hL : dist (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ)
      (lyapunovPerronSolution A P N hs hu hα hN hsmall ζ) ≤
      (K : ℝ) / (1 - 2 * K * ε / α) * dist ξ ζ := by
    have h := (lipschitzWith_lyapunovPerronSolution hs hu hα hN hsmall).dist_le_mul ξ ζ
    rwa [NNReal.coe_div, hcoe1] at h
  calc dist (lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ)
        (lyapunovPerronGraphMap A P N hs hu hα hN hsmall ζ)
      ≤ 2 * K * ε / α * dist (lyapunovPerronSolution A P N hs hu hα hN hsmall ξ)
          (lyapunovPerronSolution A P N hs hu hα hN hsmall ζ) := hgraph
    _ ≤ 2 * K * ε / α * ((K : ℝ) / (1 - 2 * K * ε / α) * dist ξ ζ) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = ((2 * K * ε / α * (K / (1 - 2 * K * ε / α)) : ℝ≥0) : ℝ) * dist ξ ζ := by
        rw [NNReal.coe_mul, hcoe, NNReal.coe_div, hcoe1]; ring

/-- If the nonlinearity vanishes at the origin, the graph lies in a cone around the range of `P`
whose opening tends to `0` with the Lipschitz constant of the nonlinearity. -/
theorem norm_lyapunovPerronGraphMap_le (hN0 : N 0 = 0) (ξ : X) :
    ‖lyapunovPerronGraphMap A P N hs hu hα hN hsmall ξ‖ ≤
      ((2 * K * ε / α * (K / (1 - 2 * K * ε / α)) : ℝ≥0) : ℝ) * ‖ξ‖ := by
  have h := (lipschitzWith_lyapunovPerronGraphMap hs hu hα hN hsmall).dist_le_mul ξ 0
  rwa [lyapunovPerronGraphMap_zero hs hu hα hN hsmall hN0, dist_zero_right, dist_zero_right] at h

section Graph

variable (hP : IsIdempotentElem P) (hAP : Commute A P)
include hP hAP

/-- The projection `P` and the parametrization `v ↦ v + graph map v` are mutually inverse between
the Lyapunov--Perron fixed-point set and the range of `P`. -/
theorem invOn_lyapunovPerronGraphMap :
    Set.InvOn (fun v ↦ v + lyapunovPerronGraphMap A P N hs hu hα hN hsmall v) P
      {x : X | lyapunovPerronSolution A P N hs hu hα hN hsmall x 0 = x} (Set.range P) := by
  constructor
  · intro x hx
    dsimp only
    rw [lyapunovPerronGraphMap_map hs hu hα hN hsmall hP,
      ← lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap]
    exact hx
  · rintro _ ⟨w, rfl⟩
    rw [map_add, apply_lyapunovPerronGraphMap hs hu hα hN hsmall hP hAP, add_zero,
      ← mul_apply_eq_comp P P, hP.eq]

/-- **The Lyapunov--Perron fixed-point set is a graph over the range of `P`.** When `P` is
idempotent and commutes with `A`, the fixed points of `ξ ↦ lyapunovPerronSolution ξ 0` are exactly
the points `v + graph map v` with `v` in the range of `P`. The graph map is Lipschitz by
`ContinuousLinearMap.lipschitzWith_lyapunovPerronGraphMap` and takes values in the kernel of `P`
by `ContinuousLinearMap.apply_lyapunovPerronGraphMap`. -/
theorem setOf_lyapunovPerronSolution_zero_eq_image :
    {x : X | lyapunovPerronSolution A P N hs hu hα hN hsmall x 0 = x} =
      (fun v ↦ v + lyapunovPerronGraphMap A P N hs hu hα hN hsmall v) '' Set.range P := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_range]
  constructor
  · exact fun hx ↦
      ⟨P x, ⟨x, rfl⟩, (invOn_lyapunovPerronGraphMap hs hu hα hN hsmall hP hAP).1 hx⟩
  · rintro ⟨-, ⟨w, rfl⟩, rfl⟩
    rw [lyapunovPerronGraphMap_map hs hu hα hN hsmall hP,
      ← lyapunovPerronSolution_zero_eq_add_lyapunovPerronGraphMap,
      lyapunovPerronSolution_lyapunovPerronSolution_zero hs hu hα hN hsmall hP hAP]

/-- **The projection `P` parametrizes the Lyapunov--Perron fixed-point set by its range.** -/
theorem bijOn_apply_setOf_lyapunovPerronSolution_zero :
    Set.BijOn P {x : X | lyapunovPerronSolution A P N hs hu hα hN hsmall x 0 = x}
      (Set.range P) :=
  (invOn_lyapunovPerronGraphMap hs hu hα hN hsmall hP hAP).bijOn (fun x _ ↦ ⟨x, rfl⟩) fun v hv ↦ by
    rw [setOf_lyapunovPerronSolution_zero_eq_image hs hu hα hN hsmall hP hAP]
    exact ⟨v, hv, rfl⟩

/-- **The initial values of the bounded forward solutions form a graph over the range of `P`.** -/
theorem setOf_exists_isIntegralCurveOn_bounded_eq_image :
    {x : X | ∃ y : ℝ → X, IsIntegralCurveOn y (fun _ y ↦ A y + N y) (Set.Ici 0) ∧ y 0 = x ∧
        ∃ B, ∀ t ∈ Set.Ici (0 : ℝ), ‖y t‖ ≤ B} =
      (fun v ↦ v + lyapunovPerronGraphMap A P N hs hu hα hN hsmall v) '' Set.range P := by
  rw [← setOf_lyapunovPerronSolution_zero_eq_image hs hu hα hN hsmall hP hAP]
  exact Set.ext fun x ↦ exists_isIntegralCurveOn_bounded_iff hs hu hα hN hsmall hP hAP x

/-- **The stable set of the equilibrium `0` is a graph over the range of `P`.** When the
nonlinearity fixes the origin, the initial values of the solutions of `y' = A y + N y` on `[0, ∞)`
that tend to `0` are exactly the points `v + graph map v` with `v` in the range of `P`. This is
the Lipschitz stable-manifold theorem for a globally small nonlinearity. -/
theorem setOf_exists_isIntegralCurveOn_tendsto_eq_image (hN0 : N 0 = 0) :
    {x : X | ∃ y : ℝ → X, IsIntegralCurveOn y (fun _ y ↦ A y + N y) (Set.Ici 0) ∧ y 0 = x ∧
        Tendsto y atTop (𝓝 0)} =
      (fun v ↦ v + lyapunovPerronGraphMap A P N hs hu hα hN hsmall v) '' Set.range P := by
  rw [← setOf_lyapunovPerronSolution_zero_eq_image hs hu hα hN hsmall hP hAP]
  exact Set.ext fun x ↦ exists_isIntegralCurveOn_tendsto_iff hs hu hα hN hsmall hN0 hP hAP x

end Graph

end ContinuousLinearMap

end
