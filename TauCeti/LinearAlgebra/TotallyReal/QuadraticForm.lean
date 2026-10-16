/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.TotallyReal.Finrank
import Mathlib.Tactic.Linarith

/-!
# Negative subspaces of quadratic forms are totally real

Let `Q` be a quadratic form over an ordered commutative ring and `J` a linear endomorphism. If
`Q(v) + Q(Jv)` is positive for every nonzero `v`, then every subspace on which `Q` is negative
definite is totally real for `J`. No almost-complex identity, finite-dimensionality, division, or
inner product is required. Over an ordered field in finite dimension, `J` is then automatically
injective on such a subspace, so the subspace has at most half the ambient dimension, and so does
the negative index of inertia of `Q`. The inertia bound applies the subspace bound to the maximal
negative-definite subspace provided by Mathlib's
`QuadraticForm.exists_finrank_eq_sigNeg_and_negDef`.

The complex-dimension consequences for almost complex structures are in
`TauCeti.Geometry.Symplectic.QuadraticForm`.

## Main declarations

* `QuadraticForm.isTotallyReal_of_add_comp_posDef`: a negative subspace is totally real for a
  linear endomorphism `J` when the sum of a quadratic form and its pullback by `J` is positive
  definite.
* `QuadraticForm.two_mul_finrank_le_of_add_comp_posDef`: such a negative subspace has at most half
  the ambient dimension.
* `QuadraticForm.two_mul_sigNeg_le_finrank_of_add_comp_posDef`: the negative index of inertia has
  the same bound.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Module

namespace QuadraticForm

section CommRing

variable {R E : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup E] [Module R E]
variable (Q : QuadraticForm R E)
variable {W : Submodule R E}

/-- A negative-definite subspace of `Q` is totally real for a linear endomorphism `J` if
`Q(v) + Q(Jv)` is positive for every nonzero `v`. -/
theorem isTotallyReal_of_add_comp_posDef (J : E →ₗ[R] E)
    (hQJ : (Q + Q.comp J).PosDef)
    (hW : ((-Q).restrict W).PosDef) :
    TauCeti.IsTotallyReal J W := by
  rw [TauCeti.isTotallyReal_iff, disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨hxW, hxJW⟩ := hx
  obtain ⟨v, hvW, rfl⟩ := hxJW
  by_contra hJv
  have hv : v ≠ 0 := fun hv ↦ hJv (by simp [hv])
  have hv' : (⟨v, hvW⟩ : W) ≠ 0 := by
    intro h
    exact hv (Subtype.ext_iff.mp h)
  have hJv' : (⟨J v, hxW⟩ : W) ≠ 0 := by
    intro h
    exact hJv (Subtype.ext_iff.mp h)
  have hnegv := hW ⟨v, hvW⟩ hv'
  have hnegJv := hW ⟨J v, hxW⟩ hJv'
  have hpos := hQJ v hv
  simp only [add_apply, QuadraticMap.comp_apply, neg_apply,
    QuadraticMap.restrict_apply] at hnegv hnegJv hpos
  linarith

end CommRing

section FiniteDimensional

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (Q : QuadraticForm K E)
variable {W : Submodule K E}

/-- Every negative-definite subspace of `Q` has at most half the dimension of `E` if
`Q(v) + Q(Jv)` is positive for every nonzero `v`, for a linear endomorphism `J`. -/
theorem two_mul_finrank_le_of_add_comp_posDef (J : E →ₗ[K] E)
    (hQJ : (Q + Q.comp J).PosDef)
    (hW : ((-Q).restrict W).PosDef) :
    2 * finrank K W ≤ finrank K E := by
  refine (Q.isTotallyReal_of_add_comp_posDef J hQJ hW).two_mul_finrank_le ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  have hneg := hW v hv0
  have hpos := hQJ v (fun h ↦ hv0 (Subtype.ext h))
  rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hv
  simp only [add_apply, QuadraticMap.comp_apply, neg_apply, QuadraticMap.restrict_apply, hv,
    QuadraticMap.map_zero] at hneg hpos
  linarith

/-- If `Q(v) + Q(Jv)` is positive for every nonzero `v`, for a linear endomorphism `J`, then twice
the negative index of inertia of `Q` is at most the dimension of `E`. -/
theorem two_mul_sigNeg_le_finrank_of_add_comp_posDef (J : E →ₗ[K] E)
    (hQJ : (Q + Q.comp J).PosDef) :
    2 * sigNeg Q ≤ finrank K E := by
  obtain ⟨W, hWdim, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  rw [← hWdim]
  exact Q.two_mul_finrank_le_of_add_comp_posDef J hQJ hWneg

end FiniteDimensional

end QuadraticForm
