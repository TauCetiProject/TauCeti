/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution.Quotient
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CartanInvolution
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.InverseTranspose

/-!
# The Cartan involution of a transpose-stable subgroup of `GLₙ`

Let `G ⊆ GLₙ` be a closed subgroup, cut out by a Hopf ideal `I` of the coordinate Hopf algebra of
`GLₙ`, and suppose that `G` is stable under transpose. Since `G` is a subgroup, this is the same as
stability under inverse transpose `θ(g) = (g⁻¹)ᵀ`, and in coordinates it says that `θ` maps `I` onto
itself (`TauCeti.GeneralLinear.comapOfSurjective_inverseTransposeCoordinateIso_eq_iff`). Then `θ`
restricts to an automorphism of `G` (`TauCeti.GeneralLinear.inverseTransposeQuotientIso`).

Over `ℝ` this restriction is a Cartan involution of `G`: its twisted real points are the complex
points of `G` whose matrices are unitary, a closed subset of the compact unitary group `U(n)`. Its
fixed points are the points of `G` whose matrices are orthogonal
(`TauCeti.GeneralLinear.comp_inverseTransposeQuotientIso_eq_self_iff`, in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.InverseTranspose`). Its real
fixed-point subgroup is `G(ℝ) ∩ O(n)`.

## Main results

* `TauCeti.GeneralLinear.mem_twistedRealPoints_inverseTransposeQuotientIso_iff`: its twisted real
  points are the complex points of the subgroup with unitary matrices.
* `TauCeti.GeneralLinear.isCartanInvolution_inverseTransposeQuotientIso`: over `ℝ`, inverse
  transpose is a Cartan involution of every transpose-stable closed subgroup of `GLₙ`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, notes, version of 16 September 2017, §1,
  Example 1.17(b), p. 15.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

variable {n : ℕ}

section Real

variable (I : HopfIdeal ℝ (coordinateHopfAlgebra ℝ n))
  (hI : I.comapOfSurjective (inverseTransposeCoordinateIso ℝ n).hom.hom
    (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso ℝ n).hom).2 = I)

/-- **The twisted real points of the restricted inverse transpose are the unitary points.** A
complex point `p` of the closed subgroup cut out by `I` satisfies `p = θ(conj p)` exactly when the
matrix of the complex point `p ∘ (O(GLₙ) → O(GLₙ) ⧸ I)` of `GLₙ` is unitary. -/
theorem mem_twistedRealPoints_inverseTransposeQuotientIso_iff
    (p : coordinateHopfAlgebra ℝ n ⧸ I.toIdeal →ₐ[ℝ] ℂ) :
    p ∈ twistedRealPoints (inverseTransposeQuotientIso I hI) ↔
      pointsMulEquiv n (toConv (p.comp (Ideal.Quotient.mkₐ ℝ I.toIdeal))) ∈
        unitarySubgroup (GL (Fin n) ℂ) := by
  rw [inverseTransposeQuotientIso_def, mem_twistedRealPoints_quotientIsoOfComapEq_iff,
    mem_twistedRealPoints_inverseTransposeCoordinateIso_iff]

/-- **Inverse transpose is a Cartan involution of a transpose-stable subgroup of `GLₙ`** (Milne,
Example 1.17(b)). If the closed subgroup `G ⊆ GLₙ` over `ℝ` cut out by `I` is stable under
transpose, then inverse transpose restricts to a Cartan involution of `G`: its twisted real points
are the points of `G(ℂ)` lying in the compact unitary group `U(n)`. -/
theorem isCartanInvolution_inverseTransposeQuotientIso :
    IsCartanInvolution (inverseTransposeQuotientIso I hI) :=
  inverseTransposeQuotientIso_def I hI ▸
    isCartanInvolution_inverseTransposeCoordinateIso.quotient hI

end Real

end TauCeti.GeneralLinear
