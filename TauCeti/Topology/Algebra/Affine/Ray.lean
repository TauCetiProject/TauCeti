/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Continuous parametrizations of two affine rays

Two rays from a point `z` along directions on which a real linear functional `ℓ` takes opposite
signs form the range of a continuous section of the coordinate `y ↦ ℓ (y -ᵥ z)`. The section
uses one direction for negative parameters and the other for positive parameters. This gives a
graph description of two rays meeting at a vertex, used to construct local charts for polygonal
curves.

No norm or continuity of `ℓ` is needed: continuity of scalar multiplication and the affine
action suffices.

## Main results

* `LinearMap.exists_continuous_range_eq_rays`: two rays with opposite signs under `ℓ` are the
  range of a continuous section of `y ↦ ℓ (y -ᵥ z)`.
-/

public section

namespace LinearMap

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] [AddTorsor V P] [TopologicalSpace P]
  [ContinuousVAdd V P]

/-- If `ℓ d₁ < 0 < ℓ d₂`, the union of the rays from `z` along `d₁` and along `d₂` is the range of
a continuous map `g` with `ℓ (g s -ᵥ z) = s`: it runs out along `d₁` for negative parameters and
along `d₂` for positive ones. -/
theorem exists_continuous_range_eq_rays (ℓ : V →ₗ[ℝ] ℝ) {d₁ d₂ : V} (h₁ : ℓ d₁ < 0)
    (h₂ : 0 < ℓ d₂) (z : P) : ∃ g : ℝ → P, Continuous g ∧ (∀ s, ℓ (g s -ᵥ z) = s) ∧
      ∀ y, y ∈ Set.range g ↔
        (∃ t : ℝ, 0 ≤ t ∧ y = t • d₁ +ᵥ z) ∨ (∃ t : ℝ, 0 ≤ t ∧ y = t • d₂ +ᵥ z) := by
  refine ⟨fun s => if s ≤ 0 then (s / ℓ d₁) • d₁ +ᵥ z else (s / ℓ d₂) • d₂ +ᵥ z,
    continuous_if_le continuous_id continuous_const (by fun_prop) (by fun_prop)
      (fun s hs => by simp [hs]), fun s => ?_, fun y => ⟨?_, ?_⟩⟩
  · by_cases hs : s ≤ 0 <;> simp [hs, h₁.ne, h₂.ne']
  · rintro ⟨s, rfl⟩
    by_cases hs : s ≤ 0
    · exact .inl ⟨s / ℓ d₁, div_nonneg_of_nonpos hs h₁.le, by simp [hs]⟩
    · exact .inr ⟨s / ℓ d₂, div_nonneg (le_of_not_ge hs) h₂.le, by simp [hs]⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · have hs : t * ℓ d₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht h₁.le
      exact ⟨t * ℓ d₁, by simp [hs, mul_div_cancel_right₀ _ h₁.ne]⟩
    · by_cases ht0 : t = 0
      · subst t
        exact ⟨0, by simp⟩
      · have hs : 0 < t * ℓ d₂ := mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) h₂
        exact ⟨t * ℓ d₂, by simp [not_le.mpr hs, mul_div_cancel_right₀ _ h₂.ne']⟩

end LinearMap
