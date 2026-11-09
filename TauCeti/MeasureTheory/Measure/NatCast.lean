/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Data.Int.Cast.Basic

/-!
# Natural casts of bounded count measures

For a measure on natural counts bounded almost surely by `n`, casting and then applying
`x ↦ n - x` agrees with taking the natural complement before casting. This transports native
count-complement identities to additive groups with measurable subtraction.
-/

public section

namespace MeasureTheory.Measure

/-- For counts bounded almost surely by `n`, reflection after casting agrees with casting
the natural complement. -/
theorem map_sub_map_cast_of_ae_le {R : Type*} [AddGroupWithOne R] [MeasurableSpace R]
    [MeasurableSub R] (μ : Measure ℕ) {n : ℕ} (h : ∀ᵐ k ∂μ, k ≤ n) :
    (μ.map (Nat.cast : ℕ → R)).map (fun x ↦ (n : R) - x) =
      (μ.map (fun k ↦ n - k)).map (Nat.cast : ℕ → R) := by
  rw [map_map (measurable_const_sub _) Measurable.of_discrete,
    map_map Measurable.of_discrete Measurable.of_discrete]
  apply map_congr
  filter_upwards [h] with k hk
  exact (Nat.cast_sub hk).symm

end MeasureTheory.Measure
