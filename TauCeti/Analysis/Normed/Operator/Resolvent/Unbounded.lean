/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Module
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# Neumann perturbations of an unbounded operator's resolvent

The continuous-inverse foundation, the resolvent identity, and the bridge to Mathlib's algebraic
resolvent are developed in `TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic`. This file
proves the normed theory on complete normed spaces over nontrivially normed fields: a sufficiently
small bounded perturbation of an operator preserves a resolvent point, and perturbing the
spectral parameter gives a local Neumann formula and openness of the resolvent set.

For `A : X →ₗ.[𝕜] X`, the chosen inverse `A.resolvent lambda` is a bounded operator whenever
`lambda ∈ A.resolventSet`. No semigroup assumption is needed, so this theory applies to
operators not yet known to generate a semigroup, as in the Hille--Yosida generation theorem.

## Main results

* `ContinuousLinearMap.isResolventAt_vadd_of_norm_mul_resolvent_lt_one`: the inverse after a
  bounded perturbation small against the resolvent.
* `TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one` and
  `LinearPMap.isOpen_resolventSet`: the Neumann perturbation of a resolvent point and openness
  of the resolvent set.
* `TauCeti.LinearPMap.resolvent_eq_mul_inverse_one_sub`: the local Neumann formula for the
  resolvent itself.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1 and
Theorem II.3.5; Pazy, *Semigroups of Linear Operators and Applications to Partial Differential
Equations*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

open _root_.LinearPMap (IsResolventAt resolvent_eq_of_isResolventAt)

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]
variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}

/-- If `lambda` lies in the resolvent set of `A` and `‖B R(lambda, A)‖ < 1`, then
`R(lambda, A) (I - B R(lambda, A))⁻¹` inverts `lambda • I - (B + A)`. -/
theorem _root_.ContinuousLinearMap.isResolventAt_vadd_of_norm_mul_resolvent_lt_one
    (B : X →L[𝕜] X)
    (h : lambda ∈ A.resolventSet) (hB : ‖B * A.resolvent lambda‖ < 1) :
    IsResolventAt ((B : X →ₗ[𝕜] X) +ᵥ A) lambda
      (A.resolvent lambda * Ring.inverse (1 - B * A.resolvent lambda)) :=
  ContinuousLinearMap.isResolventAt_vadd_of_isUnit_one_sub_mul_resolvent B h
    (isUnit_one_sub_of_norm_lt_one hB)

private theorem isResolventAt_of_norm_mul_lt_one (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) :
    IsResolventAt A mu
      (A.resolvent lambda * Ring.inverse (1 - (lambda - mu) • A.resolvent lambda)) := by
  let B : X →L[𝕜] X := (lambda - mu) • 1
  have hBR : B * A.resolvent lambda = (lambda - mu) • A.resolvent lambda := by
    simp only [B, smul_mul_assoc, one_mul]
  have hB : ‖B * A.resolvent lambda‖ < 1 := by
    rwa [hBR, norm_smul, norm_sub_rev]
  let U : X →L[𝕜] X :=
    A.resolvent lambda * Ring.inverse (1 - (lambda - mu) • A.resolvent lambda)
  have hpert : IsResolventAt ((B : X →ₗ[𝕜] X) +ᵥ A) lambda U := by
    simpa only [U, hBR] using B.isResolventAt_vadd_of_norm_mul_resolvent_lt_one h hB
  suffices IsResolventAt A mu U by simpa only [U]
  refine ⟨hpert.mem_domain, fun y => ?_, fun x => ?_⟩
  · calc
      mu • _ - A ⟨_, hpert.mem_domain y⟩ =
          lambda • _ - ((B : X →ₗ[𝕜] X) +ᵥ A) ⟨_, hpert.mem_domain y⟩ := by
            rw [LinearPMap.vadd_apply]
            simp only [B, ContinuousLinearMap.coe_coe, one_apply_eq_self, smul_apply]
            module
      _ = y := hpert.smul_sub_apply y
  · calc
      U (mu • (x : X) - A x) =
          U (lambda • (x : X) - ((B : X →ₗ[𝕜] X) +ᵥ A) x) := by
            congr 1
            rw [LinearPMap.vadd_apply]
            simp only [B, ContinuousLinearMap.coe_coe, one_apply_eq_self, smul_apply]
            module
      _ = (x : X) := hpert.apply_smul_sub x

/-- **The Neumann perturbation of a resolvent point.** If `lambda` lies in the resolvent set and
`‖mu - lambda‖ * ‖R(lambda)‖ < 1`, then `mu` lies in it too. -/
theorem mem_resolventSet_of_norm_mul_lt_one (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) : mu ∈ A.resolventSet :=
  (isResolventAt_of_norm_mul_lt_one h hmu).mem_resolventSet

/-- **Local Neumann formula for the resolvent.** Inside the ball
`‖mu - lambda‖ * ‖R(lambda)‖ < 1`, the resolvent at `mu` is obtained by multiplying
`R(lambda)` by the ring inverse of `1 - (lambda - mu) R(lambda)`. -/
theorem resolvent_eq_mul_inverse_one_sub (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) :
    A.resolvent mu = A.resolvent lambda *
      Ring.inverse (1 - (lambda - mu) • A.resolvent lambda) :=
  resolvent_eq_of_isResolventAt (isResolventAt_of_norm_mul_lt_one h hmu)

/-- **The resolvent set is open.** -/
theorem _root_.LinearPMap.isOpen_resolventSet (A : X →ₗ.[𝕜] X) : IsOpen (A.resolventSet) := by
  rw [Metric.isOpen_iff]
  intro lambda h
  refine ⟨1 / (‖A.resolvent lambda‖ + 1), by positivity, fun mu hmu => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hmu
  refine mem_resolventSet_of_norm_mul_lt_one h ?_
  have hlt : ‖mu - lambda‖ * (‖A.resolvent lambda‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp (by simpa using hmu)
  calc ‖mu - lambda‖ * ‖A.resolvent lambda‖
      ≤ ‖mu - lambda‖ * (‖A.resolvent lambda‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < 1 := hlt

end TauCeti.LinearPMap

end
