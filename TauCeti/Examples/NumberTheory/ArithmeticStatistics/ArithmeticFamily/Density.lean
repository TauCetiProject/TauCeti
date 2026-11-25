/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.ArithmeticStatistics.ArithmeticFamily.Density

/-!
# Examples of relative densities

The `0 / 0 = 0` convention gives the empty family density zero in itself, while every
nonempty family, finite or not, has density one in itself. In the natural numbers ordered by
size, a finite set has density zero and its complement has density one.
-/

open Set

namespace TauCeti.ArithmeticFamily

-- The empty ambient family has density zero in itself and cannot have density one.
example {ι : Type*} (F : ArithmeticFamily ι) :
    F.HasDensity ∅ ∅ 0 ∧ ¬ F.HasDensity ∅ ∅ 1 :=
  ⟨hasDensity_empty ∅, fun h ↦ zero_ne_one ((hasDensity_empty ∅).unique h)⟩

-- A singleton has density one in itself: infinitude is not needed.
example {ι : Type*} (F : ArithmeticFamily ι) (a : ι) : F.HasDensity {a} {a} 1 :=
  hasDensity_self (singleton_nonempty a)

-- In `ℕ` ordered by size, `{0, 1, 2}` has density zero and its complement density one,
-- for strict cutoffs as well.
example :
    let F : ArithmeticFamily ℕ := @ofNat ℕ id ⟨fun b ↦ finite_Iic b⟩
    F.HasDensity {0, 1, 2} univ 0 ∧ F.HasDensity (univ \ {0, 1, 2}) univ 1 ∧
      Filter.Tendsto (F.ratioLT (univ \ {0, 1, 2}) univ) Filter.atTop (nhds 1) := by
  intro F
  have h₀ : F.HasDensity {0, 1, 2} univ 0 := hasDensity_zero_of_finite (toFinite _) infinite_univ
  have h₁ : F.HasDensity (univ \ {0, 1, 2}) univ 1 := by
    simpa using h₀.sdiff univ_nonempty
  exact ⟨h₀, h₁, hasDensity_iff_tendsto_ratioLT.mp h₁⟩

end TauCeti.ArithmeticFamily
