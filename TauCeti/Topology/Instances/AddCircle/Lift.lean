/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real

import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Maps of the circle given by a lift

A map `φ : AddCircle T → AddCircle T` of degree one is described by a lift `F : ℝ → ℝ` with
`F (x + T) = F x + T` and `φ x = F x` for every real `x`. This file records the basic properties
of such maps used to work with diffeomorphisms of the circle through their lifts.

A continuous lift makes `φ` continuous, and a continuous strictly monotone lift makes `φ` a
homeomorphism, `AddCircle.homeomorphOfLift`: such a lift maps each fundamental interval
`(t, t + T]` onto the fundamental interval `(F t, F t + T]`. Derivatives of lifts are treated in
`TauCeti.Analysis.Calculus.Deriv.AddCircle`.

Conversely, every continuous circle map has a continuous lift, by the lifting property of the
universal covering `ℝ → AddCircle T`, and two continuous lifts of the same map differ by a
constant. So a continuous lift `F` of any continuous circle map has a degree, an integer `d` with
`F (x + T) = F x + d * T`. For a homeomorphism `φ` the degree is `±1`: a lift `G` of `φ⁻¹` gives
`G ∘ F = id + c`, so `F` is injective and the degrees multiply to `1`. A continuous injective map
of `ℝ` is strictly monotone or strictly antitone, so every continuous lift of a homeomorphism of
the circle is either strictly monotone of degree one or strictly antitone of degree `-1`.

## Main declarations

* `AddCircle.bijective_of_lift`: a circle map with a continuous strictly monotone lift is
  bijective, and `AddCircle.homeomorphOfLift` is the resulting homeomorphism.
* `AddCircle.exists_continuous_lift`: every continuous circle map has a continuous lift.
* `AddCircle.exists_forall_eq_add_of_lift`: two continuous lifts of the same circle map differ
  by a constant.
* `AddCircle.exists_int_forall_add_period_eq_of_lift`: a continuous lift has an integer degree
  `d`, and then shifts integer multiples of the period by multiples of `d * T`
  (`AddCircle.lift_add_int_mul_of_degree`, stated for any real increment per period).
* `AddCircle.add_mul_sub_add_period`: for any weight `c`, the interpolation
  `x ↦ x + c * (F x - x)` between the identity and a lift `F` is again a lift.
* `AddCircle.periodic_sub_of_lift`: the displacement `x ↦ F x - x` of a lift is periodic.
* `Homeomorph.exists_addCircle_lift_symm_comp_eq_add`: for a homeomorphism `φ` of the circle, a
  continuous lift of `φ⁻¹` composed with a continuous lift of `φ` is a translation.
* `AddCircle.strictMono_or_strictAnti_of_lift`: a continuous lift of a homeomorphism of the
  circle is strictly monotone of degree one or strictly antitone of degree `-1`.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 1.33 (the lifting criterion).
* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.1 (homeomorphisms of the
  circle and their lifts).
-/

public section

noncomputable section

open Set

namespace AddCircle

variable {T : ℝ} {φ : AddCircle T → AddCircle T} {F F' : ℝ → ℝ}

/-- A map `F` that increases by `a` over each period, `F (x + T) = F x + a`, increases by `k * a`
over `k` periods: `F (x + k * T) = F x + k * a`. For a lift of degree `d`, `a = d * T`. -/
theorem lift_add_int_mul_of_degree {a : ℝ} (hper : ∀ x, F (x + T) = F x + a)
    (x : ℝ) (k : ℤ) : F (x + k * T) = F x + k * a := by
  simpa only [zsmul_eq_mul, AddConstMap.coe_mk] using
    AddConstMapClass.map_add_zsmul (⟨F, hper⟩ : AddConstMap ℝ ℝ T a) x k

/-- A lift `F` with `F (x + T) = F x + T` shifts integer multiples of the period. -/
theorem lift_add_int_mul (hper : ∀ x, F (x + T) = F x + T) (x : ℝ) (k : ℤ) :
    F (x + k * T) = F x + k * T :=
  lift_add_int_mul_of_degree hper x k

/-- Interpolating between the identity and a lift `F` with a weight `c` gives again a lift:
`x ↦ x + c * (F x - x)` shifts `x + T` to the image of `x` plus `T`. -/
theorem add_mul_sub_add_period (hper : ∀ x, F (x + T) = F x + T) (c x : ℝ) :
    x + T + c * (F (x + T) - (x + T)) = x + c * (F x - x) + T := by
  rw [hper]
  ring

/-- The displacement `x ↦ F x - x` of a lift `F` is periodic. -/
theorem periodic_sub_of_lift (hper : ∀ x, F (x + T) = F x + T) :
    Function.Periodic (fun x ↦ F x - x) T := fun x ↦ by
  simp only [hper]
  ring

/-- A strictly monotone lift `F` maps the fundamental interval `(0, T]` into `(F 0, F 0 + T]`. -/
theorem image_Ioc_subset_of_lift (hF : StrictMono F) (hper : ∀ x, F (x + T) = F x + T) :
    F '' Ioc 0 T ⊆ Ioc (F 0) (F 0 + T) := by
  rintro _ ⟨x, hx, rfl⟩
  have hT' : F T = F 0 + T := by simpa using hper 0
  exact ⟨hF hx.1, hT' ▸ hF.monotone hx.2⟩

/-- A circle map with a continuous lift is continuous. -/
theorem continuous_of_lift (hF : Continuous F) (hφ : ∀ x : ℝ, φ x = F x) : Continuous φ := by
  have hcomp : φ ∘ (↑) = ((↑) : ℝ → AddCircle T) ∘ F := funext hφ
  rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff, hcomp]
  exact continuous_quotient_mk'.comp hF

/-- **Lifting circle maps.** Every continuous map `φ` of the circle `AddCircle T` has a continuous
lift: a continuous `F : ℝ → ℝ` with `φ x = F x` for every real `x`. This is the lifting property
of the universal covering `ℝ → AddCircle T`. -/
theorem exists_continuous_lift (hφ : Continuous φ) :
    ∃ F : ℝ → ℝ, Continuous F ∧ ∀ x : ℝ, φ x = F x := by
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (φ ((0 : ℝ) : AddCircle T))
  obtain ⟨G, ⟨-, hG⟩, -⟩ := (isCoveringMap_coe T).existsUnique_continuousMap_lifts
    ⟨fun x : ℝ ↦ φ x, hφ.comp continuous_quotient_mk'⟩ 0 y hy
  exact ⟨G, G.continuous, fun x ↦ (congr_fun hG x).symm⟩

/-- Two continuous lifts of the same circle map differ by a constant: if `F₁ x` and `F₂ x` have
the same image in `AddCircle T` for every `x`, then `F₁ = F₂ + c`. -/
theorem exists_forall_eq_add_of_lift {F₁ F₂ : ℝ → ℝ} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (h : ∀ x, (F₁ x : AddCircle T) = F₂ x) : ∃ c : ℝ, ∀ x, F₁ x = F₂ x + c :=
  ⟨F₁ 0 - F₂ 0, fun x ↦ by
    have := (isCoveringMap_coe T).const_of_comp (g := fun x ↦ F₁ x - F₂ x) (by fun_prop)
      (fun a a' ↦ by simp [h]) x 0
    linarith⟩

/-- **The degree of a circle map.** A continuous lift `F` of a circle map changes by an integer
multiple of the period over each period: `F (x + T) = F x + d * T` for some integer `d`. -/
theorem exists_int_forall_add_period_eq_of_lift (hF : Continuous F) (hφ : ∀ x : ℝ, φ x = F x) :
    ∃ d : ℤ, ∀ x, F (x + T) = F x + d * T := by
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_lift (T := T) (F₁ := fun x ↦ F (x + T))
    (by fun_prop) hF fun x ↦ by rw [← hφ, ← hφ, AddCircle.coe_add_period]
  have hc0 : ((c : ℝ) : AddCircle T) = 0 := by
    rw [show c = F (0 + T) - F 0 by linarith [hc 0], AddCircle.coe_sub, ← hφ, ← hφ,
      AddCircle.coe_add_period, sub_self]
  obtain ⟨d, hd⟩ := (AddCircle.coe_eq_zero_iff T).1 hc0
  exact ⟨d, fun x ↦ by simpa [← hd, zsmul_eq_mul] using hc x⟩

/-- A continuous lift `G` of the inverse of a homeomorphism `φ` of the circle, composed with a
continuous lift `F` of `φ`, lifts the identity, so it is a translation: `G (F x) = x + c`. -/
theorem _root_.Homeomorph.exists_addCircle_lift_symm_comp_eq_add (φ : AddCircle T ≃ₜ AddCircle T)
    (hF : Continuous F) (hφ : ∀ x : ℝ, φ x = F x) :
    ∃ (G : ℝ → ℝ) (c : ℝ), Continuous G ∧ (∀ x : ℝ, φ.symm x = G x) ∧ ∀ x, G (F x) = x + c := by
  obtain ⟨G, hG, hψ⟩ := exists_continuous_lift φ.symm.continuous
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_lift (T := T) (hG.comp hF) continuous_id
    fun x ↦ by simp [← hψ, ← hφ]
  exact ⟨G, c, hG, hψ, hc⟩

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

/-- The composition form of `apply_homeomorphOfLift_symm_apply`, usable by `simp`: the applied
form cannot be a simp lemma, because its left-hand side has the variable `φ` as head symbol. -/
@[simp]
theorem comp_homeomorphOfLift_symm (hF : StrictMono F) (hFc : Continuous F)
    (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) :
    φ ∘ (homeomorphOfLift φ hF hFc hper hφ).symm = id :=
  (homeomorphOfLift φ hF hFc hper hφ).self_comp_symm

/-- **Lifts of homeomorphisms of the circle.** A continuous lift `F` of a homeomorphism `φ` of
`AddCircle T` is either strictly monotone with `F (x + T) = F x + T` (the orientation-preserving
case) or strictly antitone with `F (x + T) = F x - T` (the orientation-reversing case). -/
theorem strictMono_or_strictAnti_of_lift {φ : AddCircle T ≃ₜ AddCircle T} (hF : Continuous F)
    (hφ : ∀ x : ℝ, φ x = F x) :
    (StrictMono F ∧ ∀ x, F (x + T) = F x + T) ∨ (StrictAnti F ∧ ∀ x, F (x + T) = F x - T) := by
  obtain ⟨d, hd⟩ := exists_int_forall_add_period_eq_of_lift hF hφ
  obtain ⟨G, c, hG, hψ, hc⟩ := φ.exists_addCircle_lift_symm_comp_eq_add hF hφ
  obtain ⟨e, he⟩ := exists_int_forall_add_period_eq_of_lift hG hψ
  have hFi : Function.Injective F := fun x y hxy ↦ by
    have hx := hc x
    have hy := hc y
    rw [hxy] at hx
    linarith
  -- the degrees of `φ` and of its inverse multiply to `1`
  have hde : d * e = 1 := by
    have h₁ : G (F T) = T + c := by simpa using hc T
    have h₀ : G (F 0) = c := by simpa using hc 0
    have hFT : F T = F 0 + d * T := by simpa using hd 0
    rw [hFT, lift_add_int_mul_of_degree he, h₀] at h₁
    have : ((d * e : ℤ) : ℝ) * T = 1 * T := by push_cast; linarith
    exact_mod_cast mul_right_cancel₀ hT.out.ne' this
  have hT0 := hT.out
  rcases hF.strictMono_of_inj hFi with hm | ha
  · refine .inl ⟨hm, fun x ↦ ?_⟩
    have hlt : F 0 < F (0 + T) := hm (by linarith)
    rw [hd] at hlt
    have hd0 : 0 < d := by
      have : (0 : ℝ) < d := pos_of_mul_pos_left (by linarith : (0 : ℝ) < d * T) hT0.le
      exact_mod_cast this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hde with rfl | rfl
    · simpa using hd x
    · omega
  · refine .inr ⟨ha, fun x ↦ ?_⟩
    have hlt : F (0 + T) < F 0 := ha (by linarith)
    rw [hd] at hlt
    have hd0 : d < 0 := by
      have : (d : ℝ) < 0 := by nlinarith
      exact_mod_cast this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hde with rfl | rfl
    · omega
    · simpa [sub_eq_add_neg] using hd x

end AddCircle
