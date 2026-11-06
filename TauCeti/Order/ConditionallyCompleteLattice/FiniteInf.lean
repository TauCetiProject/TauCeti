/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Data.Fintype.Order

/-!
# Bounding a finite infimum of real numbers

An infimum of a finite nonempty family of real numbers is attained, so it is bounded in absolute
value by `B` as soon as the family is bounded below by `-B` and one member is at most `B`.

## Main declarations

* `TauCeti.abs_iInf_le_of_forall_neg_le`: the bound for the infimum of a finite family.
-/

public section

namespace TauCeti

/-- The infimum of a finite family of reals is bounded in absolute value by `B` when every member
is at least `-B` and some member is at most `B`. -/
theorem abs_iInf_le_of_forall_neg_le {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → ℝ} {B : ℝ}
    (hlb : ∀ i, -B ≤ f i) {i₀ : ι} (hub : f i₀ ≤ B) : |⨅ i, f i| ≤ B := by
  refine abs_le.2 ⟨?_, (ciInf_le (Finite.bddBelow_range f) i₀).trans hub⟩
  obtain ⟨i₁, hi₁⟩ := exists_eq_ciInf_of_finite (f := f)
  rw [← hi₁]
  exact hlb i₁

end TauCeti
