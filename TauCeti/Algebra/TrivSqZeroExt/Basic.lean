/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DualNumber

/-!
# Nilpotency in trivial square-zero extensions

Every element `y : TrivSqZeroExt R M` differs from `TrivSqZeroExt.inl y.fst` by
`TrivSqZeroExt.inr y.snd`, which is nilpotent by Mathlib's `TrivSqZeroExt.isNilpotent_inr`
(`TauCeti/Algebra/TrivSqZeroExt/Basic.lean`: `TrivSqZeroExt.isNilpotent_sub_inl_fst`).
-/

public section

namespace TrivSqZeroExt

/-- Every element `y : TrivSqZeroExt R M` differs from `inl y.fst` by a nilpotent element. -/
theorem isNilpotent_sub_inl_fst {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (y : TrivSqZeroExt R M) :
    IsNilpotent (y - inl y.fst) := by
  have hy : y - inl y.fst = inr y.snd := by ext <;> simp
  rw [hy]
  exact isNilpotent_inr y.snd

end TrivSqZeroExt
