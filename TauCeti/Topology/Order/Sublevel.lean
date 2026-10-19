/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sublevels of real functions

If a real function has a unique global minimum and one compact sublevel strictly above it,
then sufficiently small sublevels lie in any prescribed open neighbourhood of the minimum
(`TauCeti.exists_pos_sublevel_subset_of_unique_min`).
This allows local descriptions near the minimum to describe whole sublevels. Continuity is
needed only on the one compact sublevel, not on the entire space.

If a continuous motion of the space lowers `f` at unit speed through the band `a ≤ f ≤ b`, then
following it until the level `a` is reached retracts the sublevel `{f ≤ b}` onto `{f ≤ a}`, by a
homotopy fixing `{f ≤ a}` pointwise (`TauCeti.exists_sublevelDeformation_of_apply_eq_sub`); here
`TauCeti.sublevelInclusion` is the inclusion of `{f ≤ a}` into `{f ≤ b}`. This
is the topological half of the deformation of sublevels across a band without critical points,
where the motion is the flow of a vector field `X` with `df(X) = -1` on the band.
-/

public section

open Set

namespace TauCeti

/-- Small sublevels of a function with a unique global minimum lie in any open neighbourhood
of that minimum, provided one sublevel strictly above the minimum is compact and `f` is
continuous on it. -/
theorem exists_pos_sublevel_subset_of_unique_min {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} {a : ℝ}
    (hcompact : IsCompact {y | f y ≤ a}) (hf : ContinuousOn f {y | f y ≤ a})
    (ha : f x < a) (hmin : ∀ y, f y ≤ f x → y = x)
    {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ ε > 0, {y | f y ≤ f x + ε} ⊆ U := by
  by_cases hne : ({y | f y ≤ a} \ U).Nonempty
  · obtain ⟨z, hz, hzm⟩ := (hcompact.diff hU).exists_isMinOn hne
      (hf.mono sdiff_subset)
    have hxz : f x < f z := by
      by_contra! hle
      exact hz.2 (hmin z hle ▸ hx)
    let ε := min (a - f x) (f z - f x) / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, hε, fun y hy ↦ ?_⟩
    have hεa : ε ≤ (a - f x) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hεz : ε ≤ (f z - f x) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    by_contra hyU
    have hyK : y ∈ {y | f y ≤ a} \ U := ⟨by dsimp at hy ⊢; linarith, hyU⟩
    have hzy : f z ≤ f y := hzm hyK
    dsimp at hy
    linarith
  · refine ⟨(a - f x) / 2, by positivity, fun y hy ↦ ?_⟩
    by_contra hyU
    exact hne ⟨y, ⟨by dsimp at hy ⊢; linarith, hyU⟩⟩

/-- The inclusion `{f ≤ a} → {f ≤ b}` of sublevels of `f`, for `a ≤ b`. -/
def sublevelInclusion {X β : Type*} [TopologicalSpace X] [Preorder β] (f : X → β) (a b : β)
    (hab : a ≤ b) : C({x | f x ≤ a}, {x | f x ≤ b}) :=
  ContinuousMap.inclusion (ofPred_subset_ofPred.2 fun _ hx ↦ hx.trans hab)

@[simp]
theorem coe_sublevelInclusion_apply {X β : Type*} [TopologicalSpace X] [Preorder β] (f : X → β)
    {a b : β} (hab : a ≤ b) (x : {x | f x ≤ a}) : (sublevelInclusion f a b hab x : X) = x :=
  (rfl)

/-- **Deformation of sublevels along a unit-speed descent.** Let `φ t` be a continuous motion of
`X`, with `φ 0` the identity, which lowers `f` at unit speed through the band `a ≤ f ≤ b`: if
`f x ≤ b` and `f x - t ≥ a` with `t ≥ 0`, then `f (φ t x) = f x - t`. Moving each point of
`{f ≤ b}` until it reaches the level `a` is a retraction `r` of `{f ≤ b}` onto `{f ≤ a}`, and moving
it only part of the way is a homotopy from the inclusion of `r` to the identity fixing `{f ≤ a}`
pointwise. -/
theorem exists_sublevelDeformation_of_apply_eq_sub {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (φ : ℝ → X → X)
    (hφ : Continuous (Function.uncurry φ)) (hφ0 : ∀ x, φ 0 x = x)
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t) :
    ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}),
      (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((sublevelInclusion f a b hab).comp r)
        (ContinuousMap.id _) {x | f x ≤ a}) := by
  -- Each point of `{f ≤ b}` needs the time `τ x = max (f x - a) 0` to reach `{f ≤ a}`.
  set τ : X → ℝ := fun x ↦ max (f x - a) 0
  have hτ : Continuous τ := (hf.sub continuous_const).max continuous_const
  have hτ0 : ∀ x, f x ≤ a → τ x = 0 := fun x hx ↦ max_eq_right (by linarith)
  have hfφ : ∀ x, f x ≤ b → ∀ s : ℝ, 0 ≤ s → s ≤ 1 → f (φ (s * τ x) x) = f x - s * τ x := by
    intro x hx s hs0 hs1
    by_cases hxa : f x ≤ a
    · simp [hτ0 x hxa, hφ0]
    · have hτx : τ x = f x - a := max_eq_left (by linarith)
      refine hφf x _ (by rw [hτx]; nlinarith) ?_ hx
      rw [hτx]
      nlinarith
  have hra : ∀ x : {x | f x ≤ b}, φ (τ x.1) x.1 ∈ {x | f x ≤ a} := fun x ↦ by
    have h := hfφ x.1 x.2 1 zero_le_one le_rfl
    rw [one_mul] at h
    rw [mem_ofPred_eq, h]
    linarith [le_max_left (f x.1 - a) 0]
  obtain ⟨r, hr⟩ : ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}), ∀ x, (r x : X) = φ (τ x.1) x.1 :=
    ⟨⟨fun x ↦ ⟨φ (τ x.1) x.1, hra x⟩,
      (hφ.comp ((hτ.comp continuous_subtype_val).prodMk continuous_subtype_val)).subtype_mk _⟩,
      fun _ ↦ rfl⟩
  refine ⟨r, fun x ↦ Subtype.ext ?_, ⟨?_⟩⟩
  · simp [hr, hτ0 x.1 x.2, hφ0]
  have hHb : ∀ p : unitInterval × {x | f x ≤ b},
      φ ((1 - (p.1 : ℝ)) * τ p.2.1) p.2.1 ∈ {x | f x ≤ b} := fun p ↦ by
    have h := hfφ p.2.1 p.2.2 (1 - p.1) (by linarith [p.1.2.2]) (by linarith [p.1.2.1])
    have hb : f p.2.1 ≤ b := p.2.2
    have : 0 ≤ (1 - (p.1 : ℝ)) * τ p.2.1 := mul_nonneg (by linarith [p.1.2.2]) (le_max_right _ _)
    rw [mem_ofPred_eq, h]
    linarith
  have hx : Continuous fun p : unitInterval × {x | f x ≤ b} ↦ (p.2 : X) :=
    continuous_subtype_val.comp continuous_snd
  exact
    { toFun := fun p ↦ ⟨φ ((1 - (p.1 : ℝ)) * τ p.2.1) p.2.1, hHb p⟩
      continuous_toFun := (hφ.comp (((continuous_const.sub
        (continuous_subtype_val.comp continuous_fst)).mul (hτ.comp hx)).prodMk hx)).subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext <| by simp [hr]
      map_one_left := fun x ↦ Subtype.ext <| by simp [hφ0]
      prop' := fun t x hx ↦ Subtype.ext <| by simp [hr, hτ0 x.1 hx, hφ0] }

end TauCeti
