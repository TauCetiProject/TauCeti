/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.TotallyReal.Finrank

/-!
# Nonpositive subspaces of quadratic forms are totally real

Let `Q` be a quadratic form over a commutative semiring whose partial order is compatible with
addition, and `J` a linear endomorphism. If `Q(v) + Q(Jv)` is positive for every nonzero `v`, then
every submodule on which `Q` is nonpositive is totally real for `J`. No almost-complex identity,
finite-dimensionality, division, linear order, or inner product is required. Over such a field
in finite dimension, `J` is then automatically injective on such a subspace, so the subspace has
at most half the ambient dimension. With a linear order, the negative index of inertia of `Q`
has the same bound. The inertia bound applies the subspace bound to the maximal
negative-definite subspace provided by Mathlib's
`QuadraticForm.exists_finrank_eq_sigNeg_and_negDef`.

The complex-dimension consequences for almost complex structures are in
`TauCeti.Geometry.Symplectic.QuadraticForm`.

## Main declarations

* `QuadraticForm.isTotallyReal_of_add_comp_posDef`: a nonpositive submodule is totally real for a
  linear endomorphism `J` when the sum of a quadratic form and its pullback by `J` is positive
  definite.
* `QuadraticForm.two_mul_finrank_le_of_add_comp_posDef`: such a nonpositive subspace has at most
  half the ambient dimension.
* `QuadraticForm.two_mul_sigNeg_le_finrank_of_add_comp_posDef`: the negative index of inertia has
  the same bound.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Module

namespace QuadraticForm

section CommSemiring

variable {R E : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [AddCommMonoid E] [Module R E]
variable (Q : QuadraticForm R E)
variable {W : Submodule R E}

/-- A submodule on which `Q` is nonpositive is totally real for a linear endomorphism `J` if
`Q(v) + Q(Jv)` is positive for every nonzero `v`. -/
theorem isTotallyReal_of_add_comp_posDef (J : E →ₗ[R] E)
    (hQJ : (Q + Q.comp J).PosDef)
    (hW : ∀ v ∈ W, Q v ≤ 0) :
    TauCeti.IsTotallyReal J W := by
  rw [TauCeti.isTotallyReal_iff, Submodule.disjoint_def]
  rintro _ hxW ⟨v, hvW, rfl⟩
  have hv : v = 0 := hQJ.le_zero_iff.mp <| by
    simpa only [add_apply, QuadraticMap.comp_apply] using add_nonpos (hW v hvW) (hW (J v) hxW)
  simp [hv]

end CommSemiring

section FiniteDimensional

variable {K E : Type*} [Field K] [PartialOrder K] [IsOrderedAddMonoid K]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (Q : QuadraticForm K E)
variable {W : Submodule K E}

/-- Every subspace on which `Q` is nonpositive has at most half the dimension of `E` if
`Q(v) + Q(Jv)` is positive for every nonzero `v`, for a linear endomorphism `J`. -/
theorem two_mul_finrank_le_of_add_comp_posDef (J : E →ₗ[K] E)
    (hQJ : (Q + Q.comp J).PosDef)
    (hW : ∀ v ∈ W, Q v ≤ 0) :
    2 * finrank K W ≤ finrank K E := by
  refine (Q.isTotallyReal_of_add_comp_posDef J hQJ hW).two_mul_finrank_le ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hv
  apply Subtype.ext
  exact hQJ.le_zero_iff.mp <| by
    simpa only [add_apply, QuadraticMap.comp_apply, hv, QuadraticMap.map_zero, add_zero]
      using hW v v.2

end FiniteDimensional

section LinearOrder

variable {K E : Type*} [Field K] [LinearOrder K] [IsOrderedAddMonoid K]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (Q : QuadraticForm K E)

/-- If `Q(v) + Q(Jv)` is positive for every nonzero `v`, for a linear endomorphism `J`, then twice
the negative index of inertia of `Q` is at most the dimension of `E`. -/
theorem two_mul_sigNeg_le_finrank_of_add_comp_posDef (J : E →ₗ[K] E)
    (hQJ : (Q + Q.comp J).PosDef) :
    2 * sigNeg Q ≤ finrank K E := by
  obtain ⟨W, hWdim, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  rw [← hWdim]
  exact Q.two_mul_finrank_le_of_add_comp_posDef J hQJ fun v hv ↦ by
    simpa only [QuadraticMap.restrict_apply, neg_apply, neg_nonneg] using hWneg.nonneg ⟨v, hv⟩

end LinearOrder

end QuadraticForm
