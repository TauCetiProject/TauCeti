/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Gluing two maps along the halves of a parameter

Given a continuous parameter `s : C(Z, I)` and two maps `a, a' : C(Z, X)` that agree where
`s = 1/2`, `ContinuousMap.glueHalves s a a'` is `a` on `s ≤ 1/2` and `a'` on `1/2 ≤ s`.

## Main definitions

* `ContinuousMap.glueHalves`: the glued map, with the evaluation lemmas
  `ContinuousMap.glueHalves_of_le` and `ContinuousMap.glueHalves_of_not_le`.
-/

public section

open unitInterval

namespace ContinuousMap

/-- Glue two maps along the two halves `s ≤ 1/2` and `1/2 ≤ s` of the parameter `s`, assuming
that they agree where `s = 1/2`. -/
noncomputable def glueHalves {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X] (s : C(Z, I))
    (a a' : C(Z, X)) (h : ∀ z, (s z : ℝ) = 2⁻¹ → a z = a' z) : C(Z, X) :=
  ⟨fun z ↦ if (s z : ℝ) ≤ 2⁻¹ then a z else a' z,
    Continuous.if_le a.continuous a'.continuous (continuous_subtype_val.comp s.continuous)
      continuous_const h⟩

variable {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X] (s : C(Z, I))
  (a a' : C(Z, X)) (h : ∀ z, (s z : ℝ) = 2⁻¹ → a z = a' z) {z : Z}

@[simp]
theorem glueHalves_of_le (hz : (s z : ℝ) ≤ 2⁻¹) : glueHalves s a a' h z = a z :=
  by simp only [glueHalves, ContinuousMap.coe_mk, hz, ↓reduceIte]

@[simp]
theorem glueHalves_of_not_le (hz : ¬ (s z : ℝ) ≤ 2⁻¹) : glueHalves s a a' h z = a' z :=
  by simp only [glueHalves, ContinuousMap.coe_mk, hz, ↓reduceIte]

end ContinuousMap
