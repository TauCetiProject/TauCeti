/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# Bounded perturbations of a resolvent point

Adding a bounded operator `B` to an unbounded operator `A` does not change the domain, so the
perturbed operator is Mathlib's `B +ᵥ A`. On `D(A)` the two operators are related by the
factorisation

`lambda • I - (B + A) = (I - B R(lambda, A)) (lambda • I - A)`,

whose first factor is invertible by the geometric series as soon as `‖B‖ ‖R(lambda, A)‖ < 1`.
This file turns that observation into the three facts a perturbation theorem needs: the resolvent
point survives, the perturbed resolvent is `R(lambda, A) (I - B R(lambda, A))⁻¹`, and it obeys
the bound `r / (1 - ‖B‖ r)`.

All the statements take an upper bound `r` for `‖R(lambda, A)‖` rather than that norm itself,
because that is the form in which callers have their information: a semigroup growth bound
`(omega, M)` supplies `r = M / (lambda - omega)`, and the conclusion then reads
`M / (lambda - omega - M ‖B‖)`.

## Main results

* `TauCeti.LinearPMap.isResolventAt_vadd`: the perturbed inverse, as an `IsResolventAt` witness.
* `TauCeti.LinearPMap.mem_resolventSet_vadd`: a resolvent point survives a bounded perturbation
  small against the resolvent.
* `TauCeti.LinearPMap.resolvent_vadd`: the perturbed resolvent in closed form.
* `TauCeti.LinearPMap.norm_resolvent_vadd_le`: the norm bound for the perturbed resolvent.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section III.1;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 3, Theorem 1.1.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {A : X →ₗ.[ℝ] X} {lambda r : ℝ}

/-- **The inverse of a small bounded perturbation.** If `lambda` lies in the resolvent set of `A`
and the bounded operator `B` satisfies `‖B‖ * r < 1` for some bound `r` on `‖R(lambda, A)‖`, then
`R(lambda, A) (I - B R(lambda, A))⁻¹` inverts `lambda • I - (B + A)`. -/
theorem isResolventAt_vadd (B : X →L[ℝ] X) (h : lambda ∈ resolventSet A)
    (hr : ‖resolvent A lambda‖ ≤ r) (hB : ‖B‖ * r < 1) :
    IsResolventAt ((B : X →ₗ[ℝ] X) +ᵥ A) lambda
      (resolvent A lambda * Ring.inverse (1 - B * resolvent A lambda)) := by
  apply isResolventAt_vadd_of_norm_mul_resolvent_lt_one B h
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr (norm_nonneg B)) hB

/-- **A resolvent point survives a small bounded perturbation.** If `lambda` lies in the
resolvent set of `A` and the bounded operator `B` satisfies `‖B‖ * r < 1` for some bound `r` on
`‖R(lambda, A)‖`, then `lambda` lies in the resolvent set of `B +ᵥ A`. -/
theorem mem_resolventSet_vadd (B : X →L[ℝ] X) (h : lambda ∈ resolventSet A)
    (hr : ‖resolvent A lambda‖ ≤ r) (hB : ‖B‖ * r < 1) :
    lambda ∈ resolventSet ((B : X →ₗ[ℝ] X) +ᵥ A) :=
  (isResolventAt_vadd B h hr hB).mem_resolventSet

/-- **The perturbed resolvent in closed form.** Under the hypotheses of
`TauCeti.LinearPMap.mem_resolventSet_vadd`, the resolvent of `B +ᵥ A` is
`R(lambda, A) (I - B R(lambda, A))⁻¹`. -/
theorem resolvent_vadd (B : X →L[ℝ] X) (h : lambda ∈ resolventSet A)
    (hr : ‖resolvent A lambda‖ ≤ r) (hB : ‖B‖ * r < 1) :
    resolvent ((B : X →ₗ[ℝ] X) +ᵥ A) lambda =
      resolvent A lambda * Ring.inverse (1 - B * resolvent A lambda) :=
  resolvent_eq_of_isResolventAt (isResolventAt_vadd B h hr hB)

/-- **The perturbed resolvent bound.** Under the hypotheses of
`TauCeti.LinearPMap.mem_resolventSet_vadd`, the resolvent of `B +ᵥ A` is bounded by
`r / (1 - ‖B‖ r)`. -/
theorem norm_resolvent_vadd_le (B : X →L[ℝ] X) (h : lambda ∈ resolventSet A)
    (hr : ‖resolvent A lambda‖ ≤ r) (hB : ‖B‖ * r < 1) :
    ‖resolvent ((B : X →ₗ[ℝ] X) +ᵥ A) lambda‖ ≤ r / (1 - ‖B‖ * r) := by
  have hrnonneg : 0 ≤ r := (norm_nonneg _).trans hr
  have hden : 0 < 1 - ‖B‖ * r := by linarith
  have hp := mem_resolventSet_vadd B h hr hB
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hrnonneg hden.le) fun y => ?_
  set x : X := resolvent ((B : X →ₗ[ℝ] X) +ᵥ A) lambda y with hxdef
  have hmem : x ∈ A.domain := resolvent_mem_domain hp y
  have hy : lambda • x - (B x + A ⟨x, hmem⟩) = y := by
    have := smul_sub_apply_resolvent hp y
    rwa [LinearPMap.vadd_apply] at this
  have hsplit : lambda • x - A ⟨x, hmem⟩ = y + B x := by
    rw [← hy]; abel
  have hx : x = resolvent A lambda (y + B x) := by
    rw [← hsplit, resolvent_smul_sub_apply h ⟨x, hmem⟩]
  have hbound : ‖x‖ ≤ r * (‖y‖ + ‖B‖ * ‖x‖) := by
    calc ‖x‖ = ‖resolvent A lambda (y + B x)‖ := by rw [← hx]
      _ ≤ ‖resolvent A lambda‖ * ‖y + B x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ r * (‖y‖ + ‖B‖ * ‖x‖) := by
          refine mul_le_mul hr ((norm_add_le _ _).trans ?_) (norm_nonneg _) hrnonneg
          gcongr
          exact B.le_opNorm x
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [norm_nonneg x, norm_nonneg y]

end TauCeti.LinearPMap

end

end
