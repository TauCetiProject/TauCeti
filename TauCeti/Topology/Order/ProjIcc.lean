/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous extension from a closed interval

A function continuous on a nonempty closed interval `[a, b]` of a linear order with the order
topology agrees on `[a, b]` with a continuous function on the whole space: extend it by its
endpoint values with `Set.IccExtend`.

## Main results

* `ContinuousOn.exists_continuous_eqOn_Icc`: a function continuous on `[a, b]`, with `a ≤ b`,
  agrees on `[a, b]` with a continuous function.
-/

public section

open Set

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace β] {a b : α} {f : α → β}

/-- A function continuous on a nonempty closed interval `[a, b]` agrees there with a continuous
function, namely its extension `Set.IccExtend` by the endpoint values. -/
theorem ContinuousOn.exists_continuous_eqOn_Icc (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) :
    ∃ g : α → β, Continuous g ∧ EqOn g f (Icc a b) :=
  ⟨IccExtend hab ((Icc a b).domRestrict f), (continuous_IccExtend_iff (h := hab)).2 hf.domRestrict,
    fun _ hx ↦ by rw [IccExtend_of_mem _ _ hx, domRestrict_apply]⟩
