/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-!
# Bounded homomorphisms on trivial square-zero extensions

With the `ℓ¹` norm `‖(r, m)‖ = ‖r‖ + ‖m‖` on `TrivSqZeroExt R M`, both the canonical inclusion
`TrivSqZeroExt.inlHom R M : R →+* TrivSqZeroExt R M` and the canonical projection
`(TrivSqZeroExt.fstHom S R M).toRingHom : TrivSqZeroExt R M →+* R` are bounded ring
homomorphisms of operator norm at most `1`.
-/

public section

namespace TrivSqZeroExt

/-- The canonical inclusion `inlHom R M : R →+* TrivSqZeroExt R M` is bounded with constant `1`
for the `ℓ¹` norm. -/
theorem isBounded_inlHom (R M : Type*) [SeminormedRing R] [SeminormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] :
    (inlHom R M).IsBounded :=
  ⟨1, zero_lt_one, fun x ↦ by simp⟩

/-- The canonical projection `(fstHom S R M).toRingHom : TrivSqZeroExt R M →+* R` is bounded
with constant `1` for the `ℓ¹` norm. -/
theorem isBounded_fstHom (S R M : Type*) [CommSemiring S] [SeminormedRing R]
    [SeminormedAddCommGroup M] [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]
    [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] :
    (fstHom S R M).toRingHom.IsBounded :=
  ⟨1, zero_lt_one, fun y ↦ by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fstHom_apply, one_mul, norm_def]
    exact le_add_of_nonneg_right (norm_nonneg _)⟩

end TrivSqZeroExt
