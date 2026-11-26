/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Nilpotency in trivial square-zero extensions

Every element of the square-zero ideal `TrivSqZeroExt.inr m` in a trivial square-zero extension
`TrivSqZeroExt R M` squares to zero and is therefore nilpotent (`TrivSqZeroExt.isNilpotent_inr`).
Consequently, every `y : TrivSqZeroExt R M` differs from `TrivSqZeroExt.inl y.fst` by a nilpotent
element (`TrivSqZeroExt.isNilpotent_sub_inl_fst`).
-/

public section

namespace TrivSqZeroExt

/-- Every element in the image of `TrivSqZeroExt.inr` is nilpotent (with square zero). -/
theorem isNilpotent_inr {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Module Rᵐᵒᵖ M] (m : M) :
    IsNilpotent (inr m : TrivSqZeroExt R M) :=
  ⟨2, ext (by simp) (by simp [snd_pow_eq_sum, List.range_succ])⟩

/-- Every element `y : TrivSqZeroExt R M` differs from `inl y.fst` by a nilpotent element. -/
theorem isNilpotent_sub_inl_fst {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] (y : TrivSqZeroExt R M) :
    IsNilpotent (y - inl y.fst) := by
  have hy : y - inl y.fst = inr y.snd := by ext <;> simp
  rw [hy]
  exact isNilpotent_inr y.snd

end TrivSqZeroExt
