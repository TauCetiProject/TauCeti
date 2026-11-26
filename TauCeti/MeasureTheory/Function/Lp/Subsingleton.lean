/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Unique instances on `AEEqFun` and `Lp` over a subsingleton codomain

When the target type is a subsingleton, every almost-everywhere equivalence class in `α →ₘ[μ] β` and
every `Lᵖ` class in `Lp E p μ` is equal to the default (`0` on `Lp`), giving canonical `Unique` (and
hence `Subsingleton`) instances.

## Main declarations

* `MeasureTheory.AEEqFun.instUniqueOfSubsingleton`: `Unique (α →ₘ[μ] β)` when `[Inhabited β]` and
  `[Subsingleton β]`.
* `MeasureTheory.Lp.instUniqueOfSubsingleton`: `Unique (Lp E p μ)` when `[Subsingleton E]`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- Over an inhabited subsingleton target, `α →ₘ[μ] β` has a unique element. -/
instance AEEqFun.instUniqueOfSubsingleton {α β : Type*} [MeasurableSpace α] [TopologicalSpace β]
    [Inhabited β] [Subsingleton β] {μ : Measure α} : Unique (α →ₘ[μ] β) where
  default := AEEqFun.const α default
  uniq _ := AEEqFun.ext (Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _)

/-- Over a subsingleton codomain, `Lp E p μ` has `0` as its unique element. -/
instance Lp.instUniqueOfSubsingleton {α E : Type*} {_ : MeasurableSpace α} [NormedAddCommGroup E]
    [Subsingleton E] {p : ℝ≥0∞} {μ : Measure α} : Unique (Lp E p μ) where
  default := 0
  uniq _ := Lp.ext (Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _)

end MeasureTheory
