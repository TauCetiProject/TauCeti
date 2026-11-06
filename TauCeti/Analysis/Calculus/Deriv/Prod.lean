/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constant components of product-valued curves

A curve into a product whose derivative on a closed interval has vanishing first component has
constant first component on that interval.

## Main results

* `TauCeti.fst_apply_eq_fst_apply_left_of_hasDerivWithinAt`: the first component of such a curve
  agrees with its value at the left endpoint.
-/

public section

namespace TauCeti

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A curve in a product whose derivative on a closed interval has vanishing first component has
constant first component on that interval. -/
theorem fst_apply_eq_fst_apply_left_of_hasDerivWithinAt {γ : ℝ → E × F} {γ' : ℝ → E × F}
    {a b : ℝ} (h : ∀ t ∈ Icc a b, HasDerivWithinAt γ (γ' t) (Icc a b) t)
    (h₁ : ∀ t ∈ Icc a b, (γ' t).1 = 0) {t : ℝ} (ht : t ∈ Icc a b) : (γ t).1 = (γ a).1 := by
  rcases lt_or_ge a b with hab | hab
  · have hβ : ∀ t ∈ Icc a b, HasDerivWithinAt (Prod.fst ∘ γ) 0 (Icc a b) t := fun t ht => by
      simpa [h₁ t ht] using
        HasFDerivAt.comp_hasDerivWithinAt t (ContinuousLinearMap.fst ℝ E F).hasFDerivAt (h t ht)
    exact constant_of_derivWithin_zero (fun t ht => (hβ t ht).differentiableWithinAt)
      (fun t ht => (hβ t (Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt (Ico_subset_Icc_self ht))) t ht
  · rw [le_antisymm (ht.2.trans hab) ht.1]

end TauCeti
