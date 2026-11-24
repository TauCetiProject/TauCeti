/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Right-invariant elements of a group algebra

An element `γ` of the group algebra `R[G]` that is invariant under right multiplication by every
basis element `single g 1` has all its coefficients equal to its coefficient at the identity.
When `G` is finite, `γ` is therefore the constant combination `∑ g, single g (γ.coeff 1)`, a
multiple of the norm element `∑ g, single g 1`.

## Main results

* `MonoidAlgebra.coeff_eq_coeff_one_of_mul_single_eq_self`: the coefficients of a right-invariant
  element are constant.
* `MonoidAlgebra.eq_sum_single_coeff_one_of_mul_single_eq_self`: over a finite group, a
  right-invariant element is the constant combination with coefficient `γ.coeff 1`.
-/

public section

namespace MonoidAlgebra

variable {R G : Type*} [Semiring R] [Group G] {γ : MonoidAlgebra R G}

/-- An element of a group algebra invariant under right multiplication by every group element
has all its coefficients equal to its coefficient at the identity. -/
theorem coeff_eq_coeff_one_of_mul_single_eq_self (hinv : ∀ g, γ * single g 1 = γ) (g : G) :
    γ.coeff g = γ.coeff 1 := by
  simpa using congrArg (fun z : MonoidAlgebra R G ↦ z.coeff 1) (hinv g⁻¹)

/-- An element of a finite group algebra invariant under right multiplication by every group
element is the constant combination `∑ g, single g (γ.coeff 1)`. -/
theorem eq_sum_single_coeff_one_of_mul_single_eq_self [Fintype G]
    (hinv : ∀ g, γ * single g 1 = γ) :
    γ = ∑ g, single g (γ.coeff 1) := by
  ext g
  simpa only [coeff_sum, coeff_single, Finsupp.finsetSum_apply,
    Finsupp.univ_sum_single_apply'] using coeff_eq_coeff_one_of_mul_single_eq_self hinv g

end MonoidAlgebra
