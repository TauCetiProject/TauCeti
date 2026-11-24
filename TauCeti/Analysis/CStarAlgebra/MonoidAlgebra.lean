/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.MonoidAlgebra.Star
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Group ⋆-algebras in C⋆-rings

A ⋆-algebra homomorphism `ρ` from the group algebra `ℂ[G]` into a C⋆-ring sends every group
element to a unitary, which has norm at most `1`. So `‖ρ x‖` is bounded by the `ℓ¹` norm of the
coefficients of `x`, `MonoidAlgebra.norm_starAlgHom_apply_le_sum_norm_coeff`. This makes the
supremum of `‖ρ x‖` over all such `ρ`, the universal C⋆-seminorm of `ℂ[G]`, finite.
-/

public section

namespace MonoidAlgebra

/-- A ⋆-algebra homomorphism from a group algebra into a C⋆-ring is bounded by the `ℓ¹` norm of
the coefficients, since group elements map to unitaries. -/
theorem norm_starAlgHom_apply_le_sum_norm_coeff {G B : Type*} [Group G] [NormedRing B]
    [StarRing B] [CStarRing B] [NormedAlgebra ℂ B]
    (ρ : MonoidAlgebra ℂ G →⋆ₐ[ℂ] B) (x : MonoidAlgebra ℂ G) :
    ‖ρ x‖ ≤ x.coeff.sum fun _ r => ‖r‖ := by
  conv_lhs => rw [← sum_coeff_single x]
  rw [Finsupp.sum, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [← smul_single_one, map_smul]
  refine (norm_smul_le _ _).trans ?_
  simpa using mul_le_mul_of_nonneg_left
    (CStarRing.norm_le_one_of_mem_unitary (Unitary.map_mem ρ (single_one_mem_unitary g)))
    (norm_nonneg (x.coeff g))

end MonoidAlgebra
