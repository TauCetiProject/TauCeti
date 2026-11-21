/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Injectivity of a sum of a linear combination and a section

If a linear map `dF` kills a linearly independent family `X` and inverts a linear map `S`, then
`(a, b) ↦ ∑ i, aᵢ • Xᵢ + S b` is injective
(`LinearMap.injective_coprod_linearCombination`).
-/

public section

open Function

namespace LinearMap

/-- The map `(a, b) ↦ ∑ i, aᵢ • Xᵢ + S b`, for `a : ι → R` and `b` in a module `B`, is injective
when a linear map `dF : E → B` inverts `S : B → E` and kills the linearly independent family
`X`. -/
theorem injective_coprod_linearCombination {R E B ι : Type*} [Ring R] [AddCommGroup E]
    [Module R E] [AddCommGroup B] [Module R B] [Fintype ι] {X : ι → E}
    (hX : LinearIndependent R X) {S : B →ₗ[R] E} (dF : E →ₗ[R] B) (hdFX : ∀ i, dF (X i) = 0)
    (hdFs : ∀ b, dF (S b) = b) : Injective ((Fintype.linearCombination R X).coprod S) := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨a, b⟩ h ↦ ?_
  rw [coprod_apply, Fintype.linearCombination_apply] at h
  have hb : b = 0 := by
    have := congrArg dF h
    simpa only [map_add, map_sum, map_smul, hdFX, smul_zero, Finset.sum_const_zero, zero_add,
      hdFs, map_zero] using this
  subst hb
  rw [map_zero, add_zero] at h
  exact Prod.ext (funext (Fintype.linearIndependent_iff.1 hX a h)) rfl

end LinearMap
