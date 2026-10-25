/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.LinearAlgebra.TotallyReal.QuadraticForm

/-!
# Quadratic forms and almost complex structures

Let `Q` be a real quadratic form and `J` an almost complex structure. If
`Q(v) + Q(Jv)` is positive for every nonzero `v`, then every subspace on which `Q` is negative
definite is totally real. It therefore has dimension at most the complex dimension determined by
`J`. Applying this to the maximal negative-definite subspace provided by Mathlib's
`QuadraticForm.exists_finrank_eq_sigNeg_and_negDef` bounds the negative index of inertia of `Q`.

This is the linear-algebraic index estimate behind the Morse-theoretic consequence of strict Levi
positivity. No compatibility between `J` and an inner product is required. The totally-real
criterion and the half-dimension bounds for an arbitrary linear endomorphism are in
`TauCeti.LinearAlgebra.TotallyReal.QuadraticForm`.

## Main declarations

* `QuadraticForm.finrank_le_complexFinrank_of_add_comp_posDef`: every such negative subspace has
  at most the complex dimension of the ambient space.
* `QuadraticForm.sigNeg_le_complexFinrank_of_add_comp_posDef`: the negative index of inertia has
  the same bound.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Module

namespace QuadraticForm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (Q : QuadraticForm ℝ E)
variable {W : Submodule ℝ E}

section FiniteDimensional

variable [FiniteDimensional ℝ E] (J : TauCeti.AlmostComplexStructure E)

/-- Every negative-definite subspace of `Q` has dimension at most the complex dimension defined
by `J` when `Q(v) + Q(Jv)` is positive away from zero. -/
theorem finrank_le_complexFinrank_of_add_comp_posDef
    (hQJ : (Q + Q.comp J.toLinearMap).PosDef)
    (hW : ((-Q).restrict W).PosDef) :
    finrank ℝ W ≤ J.complexFinrank := by
  have hdim := Q.two_mul_finrank_le_of_add_comp_posDef J.toLinearMap hQJ fun v hv ↦ by
    simpa only [QuadraticMap.restrict_apply, neg_apply, neg_nonneg] using hW.nonneg ⟨v, hv⟩
  rw [J.finrank_real_eq_two_mul_complexFinrank] at hdim
  omega

/-- If `Q(v) + Q(Jv)` is positive for every nonzero `v`, then the negative index of inertia of
`Q` is at most the complex dimension defined by `J`. -/
theorem sigNeg_le_complexFinrank_of_add_comp_posDef
    (hQJ : (Q + Q.comp J.toLinearMap).PosDef) :
    sigNeg Q ≤ J.complexFinrank := by
  obtain ⟨W, hWdim, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  rw [← hWdim]
  exact Q.finrank_le_complexFinrank_of_add_comp_posDef J hQJ hWneg

end FiniteDimensional

end QuadraticForm
