/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.Instances.AddCircle.Lift

/-!
# Derivatives of lifts of circle maps

A map of the circle `AddCircle T` of degree one is described by a lift `F : ℝ → ℝ` with
`F (x + T) = F x + T` (see `TauCeti.Topology.Instances.AddCircle.Lift`). The derivative of a
differentiable lift is `T`-periodic, so a lift with continuous positive derivative, the lift of an
orientation-preserving `C¹` diffeomorphism, has derivative bounded between two positive
constants, and its inverse is again a lift, with derivative the reciprocal of `F'`.

## Main declarations

* `AddCircle.periodic_deriv_of_lift`: the derivative of a lift is `T`-periodic.
* `AddCircle.exists_pos_le_deriv_le_of_lift`: a lift with continuous positive derivative has
  derivative in some interval `[c, M]` with `0 < c`.
* `AddCircle.exists_lift_inverse`: a lift with positive derivative has an inverse `G`, which is
  again a lift, with derivative `G' y = (F' (G y))⁻¹`.
-/

public section

namespace AddCircle

variable {T : ℝ} {F F' : ℝ → ℝ}

/-- The derivative of a lift `F` with `F (x + T) = F x + T` is `T`-periodic. -/
theorem periodic_deriv_of_lift (hF : ∀ x, HasDerivAt F (F' x) x)
    (hper : ∀ x, F (x + T) = F x + T) : Function.Periodic F' T := fun x ↦ by
  have h₁ : HasDerivAt (fun y ↦ F (y + T)) (F' (x + T)) x := (hF (x + T)).comp_add_const x T
  have h₂ : HasDerivAt (fun y ↦ F (y + T)) (F' x) x := by
    simpa only [hper] using (hF x).add_const T
  exact h₁.unique h₂

variable [hT : Fact (0 < T)]

/-- A lift with continuous positive derivative has derivative bounded above and below by
positive constants: a `C¹` lift of an orientation-preserving diffeomorphism of the circle has
derivative in some `[c, M]` with `0 < c`. -/
theorem exists_pos_le_deriv_le_of_lift (hF : ∀ x, HasDerivAt F (F' x) x)
    (hper : ∀ x, F (x + T) = F x + T) (hF' : Continuous F') (hpos : ∀ x, 0 < F' x) :
    ∃ c M : ℝ, 0 < c ∧ (∀ x, c ≤ F' x) ∧ ∀ x, F' x ≤ M := by
  have hK := (periodic_deriv_of_lift hF hper).compact_of_continuous hT.out.ne' hF'
  obtain ⟨_, ⟨x₀, rfl⟩, hmin⟩ := hK.exists_isLeast (Set.range_nonempty F')
  obtain ⟨M, hM⟩ := hK.isBounded.bddAbove
  exact ⟨F' x₀, M, hpos x₀, fun x ↦ hmin ⟨x, rfl⟩, fun x ↦ hM ⟨x, rfl⟩⟩

/-- **The inverse of a lift.** A lift `F` with `F (x + T) = F x + T` and positive derivative `F'`
is a bijection of `ℝ`. Its inverse `G` is again a lift, `G (y + T) = G y + T`, and it is
differentiable with `G' y = (F' (G y))⁻¹`. So the inverse of an orientation-preserving
diffeomorphism of the circle with lift `F` has the lift `G`. -/
theorem exists_lift_inverse (hF : ∀ x, HasDerivAt F (F' x) x) (hper : ∀ x, F (x + T) = F x + T)
    (hpos : ∀ x, 0 < F' x) :
    ∃ G : ℝ → ℝ, Function.LeftInverse G F ∧ Function.RightInverse G F ∧
      (∀ y, G (y + T) = G y + T) ∧ ∀ y, HasDerivAt G (F' (G y))⁻¹ y := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF hpos
  have hshift (k : ℤ) : F (k * T) = F 0 + k * T := by
    simpa using lift_add_int_mul hper 0 k
  have htop : Filter.Tendsto F Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b ↦ ⟨⌈(b - F 0) / T⌉ * T, fun x hx ↦ ?_⟩
    have h : (b - F 0) / T * T ≤ ⌈(b - F 0) / T⌉ * T :=
      mul_le_mul_of_nonneg_right (Int.le_ceil _) hT.out.le
    rw [div_mul_cancel₀ _ hT.out.ne'] at h
    linarith [hmono.monotone hx, hshift ⌈(b - F 0) / T⌉]
  have hbot : Filter.Tendsto F Filter.atBot Filter.atBot := by
    refine Filter.tendsto_atBot_atBot.2 fun b ↦ ⟨⌊(b - F 0) / T⌋ * T, fun x hx ↦ ?_⟩
    have h : ⌊(b - F 0) / T⌋ * T ≤ (b - F 0) / T * T :=
      mul_le_mul_of_nonneg_right (Int.floor_le _) hT.out.le
    rw [div_mul_cancel₀ _ hT.out.ne'] at h
    linarith [hmono.monotone hx, hshift ⌊(b - F 0) / T⌋]
  set e := StrictMono.orderIsoOfSurjective F hmono (hFc.surjective htop hbot)
  have hFG (y : ℝ) : F (e.symm y) = y := by
    simpa only [e, StrictMono.coe_orderIsoOfSurjective] using e.apply_symm_apply y
  refine ⟨e.symm, fun x ↦ StrictMono.orderIsoOfSurjective_symm_apply_self F hmono _ x, hFG,
    fun y ↦ hmono.injective ?_, fun y ↦ ?_⟩
  · rw [hFG, hper, hFG]
  · exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hF _) (hpos _).ne'
      (Filter.Eventually.of_forall hFG)

end AddCircle
