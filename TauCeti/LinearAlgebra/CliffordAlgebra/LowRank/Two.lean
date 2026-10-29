/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: injectivity of the Clifford generator is used only in the dimension comparison.
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# Clifford algebras in dimension two

The odd component of a two-dimensional Clifford algebra consists entirely of vector generators.
Indeed, the generator image lies in the odd component, and both spaces have dimension two: the
generator is injective, while the odd component has dimension `2 ^ (2 - 1)`.

This is a general grading fact, independent of the Lipschitz and Spin groups. Multiplying by a
fixed vector `a` of invertible norm exchanges the two components, so every even element is a
product `ι a * ι w` of `a` with another vector.

## Main results

* `CliffordAlgebra.range_ι_eq_evenOdd_one_of_finrank_eq_two`: every odd Clifford element in
  dimension two is a vector generator.
* `CliffordAlgebra.mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two`: every even Clifford element in
  dimension two is a product `ι a * ι w`, for any fixed `a` of invertible norm.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- In dimension two, every odd Clifford element is a vector generator. -/
theorem range_ι_eq_evenOdd_one_of_finrank_eq_two (Q : QuadraticForm K V)
    (hV : finrank K V = 2) : LinearMap.range (ι Q) = evenOdd Q 1 := by
  let _ : FiniteDimensional K V :=
    FiniteDimensional.of_finrank_pos (by rw [hV]; decide)
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; decide)
  apply Submodule.eq_of_le_of_finrank_eq (range_ι_le_evenOdd_one Q)
  rw [LinearMap.finrank_range_of_inj (ι_injective Q), finrank_evenOdd Q, hV]
  norm_num

/-- In dimension two, the even Clifford elements are exactly the products `ι a * ι w`, for any
fixed vector `a` of invertible norm. -/
theorem mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two (Q : QuadraticForm K V)
    (hV : finrank K V = 2) (a : V) [Invertible (Q a)] {x : CliffordAlgebra Q} :
    x ∈ even Q ↔ ∃ w, x = ι Q a * ι Q w := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hx' : x ∈ evenOdd Q 0 := by rwa [← even_toSubmodule, Subalgebra.mem_toSubmodule]
    have hodd : ι Q a * x ∈ evenOdd Q 1 :=
      add_zero (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mem_evenOdd_one Q a) hx'
    rw [← range_ι_eq_evenOdd_one_of_finrank_eq_two Q hV] at hodd
    obtain ⟨w, hw⟩ := hodd
    refine ⟨⅟(Q a) • w, ?_⟩
    rw [map_smul, mul_smul_comm, hw, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, smul_smul,
      invOf_mul_self, one_smul]
  · rintro ⟨w, rfl⟩
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero Q a w

end CliffordAlgebra
