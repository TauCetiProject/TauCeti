/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.BaseChange
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descent of group-like elements

Being group-like can be checked after faithfully flat extension of scalars. This allows a
character whose coefficients lie in a smaller field to be regarded as a character over that field.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R K C : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [Module.FaithfullyFlat R K] [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- An element of a coalgebra is group-like if and only if it is group-like after faithfully
flat extension of scalars. -/
@[simp]
theorem isGroupLikeElem_one_tmul_iff (x : C) :
    IsGroupLikeElem K ((1 : K) ⊗ₜ[R] x) ↔ IsGroupLikeElem R x := by
  constructor
  · intro hx
    constructor
    · apply FaithfulSMul.algebraMap_injective R K
      simpa [Algebra.smul_def] using hx.counit_eq_one
    · have hcomul := hx.comul_eq_tmul_self
      rw [Coalgebra.baseChange_comul_tmul] at hcomul
      have h := (TensorProduct.AlgebraTensorModule.distribBaseChange R K C C).injective
        (hcomul.trans
          (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul R K x x 1).symm)
      apply sub_eq_zero.mp
      apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff R _ (A := K) _).mp
      simpa only [TensorProduct.tmul_sub, sub_eq_zero] using h
  · intro hx
    constructor
    · simp [hx.counit_eq_one]
    · rw [Coalgebra.baseChange_comul_tmul, hx.comul_eq_tmul_self,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

end TauCeti
