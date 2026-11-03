/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic

/-!
# Jordan curves parametrized by compact intervals

A closed curve is classically given by a map `γ : ℝ → X`, continuous on a parameter interval
`[a, b]` with `a < b`, which returns to its starting point, `γ a = γ b`, and has no other
repetition: it is injective on `[a, b)`. This file shows that the traces `γ '' [a, b]` of such
curves are exactly the Jordan curves of `X`, the subsets homeomorphic to the circle
(`TauCeti.isJordanCurve_iff_exists_injOn_Ico`). The parametrization is not required to be
differentiable, absolutely continuous or of bounded variation, and every Jordan curve admits such a
parametrization on any prescribed interval, even one continuous on the whole line.

Both directions pass through the additive circle `AddCircle (b - a)`, the parameter interval with
its two endpoints identified. A closed curve injective on `[a, b)` factors through it as a
continuous injection, `AddCircle.liftIco`, which carries the circle onto the trace; conversely a
homeomorphism of a Jordan curve with the circle, composed with the quotient map `ℝ → AddCircle
(b - a)`, is a parametrization. The first direction specializes to closed paths parametrized by
the unit interval as `TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints`.

## Main results

* `TauCeti.isJordanCurve_image_Icc`: the trace of a closed curve injective on `[a, b)` is a
  Jordan curve.
* `TauCeti.IsJordanCurve.exists_continuous_injOn_Ico`: every Jordan curve is the trace of a
  continuous closed curve injective on `[a, b)`.
* `TauCeti.isJordanCurve_iff_exists_injOn_Ico`: the two descriptions of Jordan curves agree.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {C : Set X} {γ : ℝ → X} {a b : ℝ}

/-- **The trace of a simple closed curve is a Jordan curve.** If `γ` is continuous on `[a, b]`
with `a < b`, satisfies `γ a = γ b`, and is injective on `[a, b)`, then `γ '' [a, b]` is
homeomorphic to the circle. No regularity of `γ` beyond continuity is needed. -/
theorem isJordanCurve_image_Icc [T2Space X] (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) : IsJordanCurve (γ '' Icc a b) := by
  have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  have hb : a + (b - a) = b := add_sub_cancel a b
  set f := AddCircle.liftIco (b - a) a γ
  have hf (t : ℝ) (ht : t ∈ Icc a b) : f t = γ t := by
    rcases ht.2.lt_or_eq with htb | htb
    · exact AddCircle.liftIco_coe_apply (by rw [hb]; exact ⟨ht.1, htb⟩)
    -- The endpoint `t = b` is identified with `a`, where `γ` takes the same value.
    · have hba := AddCircle.coe_add_period (b - a) a
      rw [hb] at hba
      rw [htb, hba, ← hclosed]
      exact AddCircle.liftIco_coe_apply (by rw [hb]; exact left_mem_Ico.2 hab)
  have hfc : Continuous f := AddCircle.liftIco_continuous (by rwa [hb]) (by rwa [hb])
  -- Every point of `AddCircle (b - a)` is the class of a parameter in `[a, b)`.
  have hrep (x : AddCircle (b - a)) : ∃ t ∈ Ico a b, (t : AddCircle (b - a)) = x :=
    ⟨AddCircle.equivIco (b - a) a x, by simpa [hb] using (AddCircle.equivIco (b - a) a x).2,
      AddCircle.coe_equivIco⟩
  have hfi : Function.Injective f := by
    intro x y hxy
    obtain ⟨s, hs, rfl⟩ := hrep x
    obtain ⟨t, ht, rfl⟩ := hrep y
    rw [hf s (Ico_subset_Icc_self hs), hf t (Ico_subset_Icc_self ht)] at hxy
    rw [hinj hs ht hxy]
  have hrange : f '' univ = γ '' Icc a b := by
    rw [← AddCircle.coe_image_Icc_eq (p := b - a) a, hb, image_image, image_congr hf]
  have huniv : IsJordanCurve (univ : Set (AddCircle (b - a))) :=
    isJordanCurve_iff.mpr ⟨(Homeomorph.Set.univ _).trans
      (AddCircle.homeomorphCircle (sub_pos.2 hab).ne')⟩
  exact hrange ▸ huniv.image hfc.continuousOn hfi.injOn

/-- **Every Jordan curve has a simple closed parametrization on any interval.** For a Jordan curve
`C` and `a < b` there is a map `γ : ℝ → X`, continuous on the whole line, with `γ a = γ b`,
injective on `[a, b)`, whose trace `γ '' [a, b]` is `C`. -/
theorem IsJordanCurve.exists_continuous_injOn_Ico (h : IsJordanCurve C) (hab : a < b) :
    ∃ γ : ℝ → X, Continuous γ ∧ γ a = γ b ∧ InjOn γ (Ico a b) ∧ γ '' Icc a b = C := by
  have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  have hb : a + (b - a) = b := add_sub_cancel a b
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  set g : AddCircle (b - a) → X :=
    jordanParam e ∘ AddCircle.homeomorphCircle (sub_pos.2 hab).ne'
  have hg : Function.Injective g :=
    (jordanParam_injective e).comp (AddCircle.homeomorphCircle _).injective
  refine ⟨fun t => g t, ?_, ?_, ?_, ?_⟩
  · exact ((continuous_jordanParam e).comp (AddCircle.homeomorphCircle _).continuous).comp
      (AddCircle.continuous_mk' (b - a))
  · exact congrArg g ((AddCircle.coe_add_period (b - a) a).symm.trans (congrArg _ hb))
  · intro s hs t ht hst
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (by rwa [hb]) (by rwa [hb])).1 (hg hst)
  · have hIcc := AddCircle.coe_image_Icc_eq (p := b - a) a
    rw [hb] at hIcc
    rw [← image_image g, hIcc, image_univ,
      (AddCircle.homeomorphCircle _).surjective.range_comp, range_jordanParam]

/-- **Jordan curves are the traces of simple closed curves.** For `a < b`, a subset `C` of a
Hausdorff space is a Jordan curve exactly when it is `γ '' [a, b]` for some `γ : ℝ → X` that is
continuous on `[a, b]`, satisfies `γ a = γ b`, and is injective on `[a, b)`. -/
theorem isJordanCurve_iff_exists_injOn_Ico [T2Space X] (hab : a < b) :
    IsJordanCurve C ↔ ∃ γ : ℝ → X, ContinuousOn γ (Icc a b) ∧ γ a = γ b ∧ InjOn γ (Ico a b) ∧
      γ '' Icc a b = C := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨γ, hγ, hclosed, hinj, himage⟩ := h.exists_continuous_injOn_Ico hab
    exact ⟨γ, hγ.continuousOn, hclosed, hinj, himage⟩
  · rintro ⟨γ, hγ, hclosed, hinj, rfl⟩
    exact isJordanCurve_image_Icc hab hγ hclosed hinj

end TauCeti
