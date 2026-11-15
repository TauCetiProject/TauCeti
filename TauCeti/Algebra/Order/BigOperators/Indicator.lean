/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Basic.Real.Basic

/-!
# Products of indicator functions

A finite product of `{0, 1}`-valued indicators has absolute value at most one
(`Finset.abs_prod_indicator_le_one`).
-/

public section

namespace Finset

/-- A finite product of `{0, 1}`-valued indicators of coordinates has absolute value at most
one. -/
theorem abs_prod_indicator_le_one {ι β : Type*} (s : Finset ι) (f : ι → β) (B : ι → Set β) :
    |∏ i ∈ s, (B i).indicator (fun _ => (1 : ℝ)) (f i)| ≤ 1 := by
  have h0 : (0 : ℝ) ≤ ∏ i ∈ s, (B i).indicator (fun _ => (1 : ℝ)) (f i) :=
    Finset.prod_nonneg fun i _ => Set.indicator_apply_nonneg fun _ => zero_le_one
  rw [abs_of_nonneg h0]
  exact Finset.prod_le_one₀ (fun i _ => Set.indicator_apply_nonneg fun _ => zero_le_one)
    fun i _ => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one

end Finset
