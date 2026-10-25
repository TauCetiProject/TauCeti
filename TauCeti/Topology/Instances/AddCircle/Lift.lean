/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.Instances.AddCircle.Real

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Maps of the circle given by a lift

A map `φ : AddCircle T → AddCircle T` of degree one is described by a lift `F : ℝ → ℝ` with
`F (x + T) = F x + T` and `φ x = F x` for every real `x`. This file records the basic properties
of such maps used to work with diffeomorphisms of the circle through their lifts.

A continuous lift makes `φ` continuous, and a continuous strictly monotone lift makes `φ` a
homeomorphism, `AddCircle.homeomorphOfLift`: such a lift maps each fundamental interval
`(t, t + T]` onto the fundamental interval `(F t, F t + T]`. The derivative of a differentiable
lift is `T`-periodic, so a lift with continuous positive derivative, the lift of an
orientation-preserving `C¹` diffeomorphism, has derivative bounded between two positive
constants.

## Main declarations

* `AddCircle.bijective_of_lift`: a circle map with a continuous strictly monotone lift is
  bijective, and `AddCircle.homeomorphOfLift` is the resulting homeomorphism.
* `AddCircle.periodic_deriv_of_lift`: the derivative of a lift is `T`-periodic.
* `AddCircle.exists_pos_le_deriv_le_of_lift`: a lift with continuous positive derivative has
  derivative in some interval `[c, M]` with `0 < c`.
-/

public section

noncomputable section

open Set

namespace AddCircle

variable {T : ℝ} {φ : AddCircle T → AddCircle T} {F F' : ℝ → ℝ}

/-- A lift `F` with `F (x + T) = F x + T` shifts integer multiples of the period. -/
theorem lift_add_int_mul (hper : ∀ x, F (x + T) = F x + T) (x : ℝ) (k : ℤ) :
    F (x + k * T) = F x + k * T := by
  have h : Function.Periodic (fun x ↦ F x - x) T := fun x ↦ by simp [hper]
  have h' : F (x + k * T) - (x + k * T) = F x - x := h.int_mul k x
  linarith

/-- A strictly monotone lift `F` maps the fundamental interval `(0, T]` into `(F 0, F 0 + T]`. -/
theorem image_Ioc_subset_of_lift (hF : StrictMono F) (hper : ∀ x, F (x + T) = F x + T) :
    F '' Ioc 0 T ⊆ Ioc (F 0) (F 0 + T) := by
  rintro _ ⟨x, hx, rfl⟩
  have hT' : F T = F 0 + T := by simpa using hper 0
  exact ⟨hF hx.1, hT' ▸ hF.monotone hx.2⟩

/-- A circle map with a continuous lift is continuous. -/
theorem continuous_of_lift (hF : Continuous F) (hφ : ∀ x : ℝ, φ x = F x) : Continuous φ := by
  rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff,
    show φ ∘ (↑) = ((↑) : ℝ → AddCircle T) ∘ F from funext hφ]
  exact continuous_quotient_mk'.comp hF

variable [hT : Fact (0 < T)]

/-- A continuous strictly monotone lift `F` maps the fundamental interval `(0, T]` onto
`(F 0, F 0 + T]`. -/
theorem image_Ioc_of_lift (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) : F '' Ioc 0 T = Ioc (F 0) (F 0 + T) := by
  refine (image_Ioc_subset_of_lift hF hper).antisymm ?_
  have hT' : F T = F 0 + T := by simpa using hper 0
  exact hT' ▸ intermediate_value_Ioc hT.out.le hFc.continuousOn

/-- A circle map with a continuous strictly monotone lift is bijective. -/
theorem bijective_of_lift (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) : Function.Bijective φ := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hxy : ((F x : ℝ) : AddCircle T) = (F y : ℝ) := by simpa only [hφ] using hxy
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hxy)
    have hk : F y = F (x + k * T) := by rw [lift_add_int_mul hper, ← zsmul_eq_mul, hk]; ring
    rw [hF.injective hk, AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero, add_zero]
  · intro y
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨x, -, hx⟩ := (image_Ioc_of_lift hF hFc hper).symm ▸
      toIocMod_mem_Ioc hT.out (F 0) y
    refine ⟨x, ?_⟩
    rw [hφ, hx]
    exact QuotientAddGroup.eq_iff_sub_mem.2 (by
      rw [toIocMod_sub_self]
      exact zsmul_mem (AddSubgroup.mem_zmultiples T) _)

/-- The homeomorphism of the circle given by a continuous strictly monotone lift `F` with
`F (x + T) = F x + T`. -/
def homeomorphOfLift (φ : AddCircle T → AddCircle T) (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) : AddCircle T ≃ₜ AddCircle T :=
  (continuous_of_lift (φ := φ) hFc hφ).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective φ (bijective_of_lift hF hFc hper hφ))

@[simp]
theorem coe_homeomorphOfLift (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) :
    ⇑(homeomorphOfLift φ hF hFc hper hφ) = φ :=
  (rfl)

@[simp]
theorem homeomorphOfLift_symm_apply_apply (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (x : AddCircle T) :
    (homeomorphOfLift φ hF hFc hper hφ).symm (φ x) = x :=
  (homeomorphOfLift φ hF hFc hper hφ).symm_apply_apply x

theorem apply_homeomorphOfLift_symm_apply (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (x : AddCircle T) :
    φ ((homeomorphOfLift φ hF hFc hper hφ).symm x) = x :=
  (homeomorphOfLift φ hF hFc hper hφ).apply_symm_apply x

omit hT in
/-- The derivative of a lift `F` with `F (x + T) = F x + T` is `T`-periodic. -/
theorem periodic_deriv_of_lift (hF : ∀ x, HasDerivAt F (F' x) x)
    (hper : ∀ x, F (x + T) = F x + T) : Function.Periodic F' T := fun x ↦ by
  have h₁ : HasDerivAt (fun y ↦ F (y + T)) (F' (x + T)) x := (hF (x + T)).comp_add_const x T
  have h₂ : HasDerivAt (fun y ↦ F (y + T)) (F' x) x := by
    simpa only [hper] using (hF x).add_const T
  exact h₁.unique h₂

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

end AddCircle
