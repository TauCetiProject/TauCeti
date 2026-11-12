/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Filtration

/-!
# Sampling a filtration

Composing a filtration with a monotone time map gives a filtration on the sampling index.
-/

public section

namespace MeasureTheory.Filtration

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]

/-- Sample a filtration along a monotone time map. -/
def comp (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ) : Filtration κ m where
  seq n := ℱ (τ n)
  mono' _ _ h := ℱ.mono (hτ h)
  le' n := ℱ.le (τ n)

/-- The sampled filtration at an index is the original filtration at its sampling time. -/
@[simp]
theorem comp_apply (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ) (n : κ) :
    ℱ.comp hτ n = ℱ (τ n) := (rfl)

end MeasureTheory.Filtration
