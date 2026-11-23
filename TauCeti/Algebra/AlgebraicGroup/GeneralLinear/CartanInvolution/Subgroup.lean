/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution.Quotient
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CartanInvolution
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic

/-!
# The Cartan involution of a transpose-stable subgroup of `GLₙ`

Let `G ⊆ GLₙ` be a closed subgroup, cut out by a Hopf ideal `I` of the coordinate Hopf algebra of
`GLₙ`, and suppose that `G` is stable under transpose. Since `G` is a subgroup, this is the same as
stability under inverse transpose `θ(g) = (g⁻¹)ᵀ`, and in coordinates it says that `θ` maps `I` onto
itself (`TauCeti.GeneralLinear.comapOfSurjective_inverseTransposeCoordinateIso_eq_iff`). Then `θ`
restricts to an automorphism of `G` (`TauCeti.GeneralLinear.inverseTransposeQuotientIso`).

Over `ℝ` this restriction is a Cartan involution of `G`: its twisted real points are the complex
points of `G` whose matrices are unitary, a closed subset of the compact unitary group `U(n)`. Its
fixed points are the points of `G` whose matrices are orthogonal, so the associated maximal compact
subgroup of `G(ℝ)` is `G(ℝ) ∩ O(n)`.

## Main declarations

* `TauCeti.GeneralLinear.inverseTransposeQuotientIso`: inverse transpose restricted to a closed
  subgroup of `GLₙ` that it maps onto itself.

## Main results

* `TauCeti.GeneralLinear.comapOfSurjective_inverseTransposeCoordinateIso_eq_iff`: the Hopf ideal
  `I` is stable under inverse transpose exactly when every group of algebra-valued points of the
  subgroup it cuts out is stable under inverse transpose.
* `TauCeti.GeneralLinear.toConv_comp_inverseTransposeQuotientIso_eq_self_iff`: the fixed points of
  the restricted involution are the points of the subgroup with orthogonal matrices.
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

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Precomposing a point with the inverse-transpose coordinate automorphism, read back from inverse
transpose of its matrix. -/
private theorem pointsMulEquiv_symm_inverseTranspose (A : Type v) [CommRing A] [Algebra R A]
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (pointsMulEquiv n).symm
        (Matrix.GeneralLinearGroup.inverseTranspose (pointsMulEquiv n f)) =
      toConv (f.ofConv.comp ((inverseTransposeCoordinateIso R n).hom.hom :
        coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n)) := by
  rw [← pointsMulEquiv_toConv_comp_inverseTransposeCoordinateIso, MulEquiv.symm_apply_apply]

/-- **Stability under inverse transpose, in coordinates and on points.** The inverse-transpose
coordinate automorphism of `GLₙ` maps the Hopf ideal `I` onto itself exactly when, for every
commutative `R`-algebra `A`, the subgroup of `GLₙ(A)` cut out by `I` is stable under inverse
transpose. For a subgroup this is the same as stability under transpose. -/
theorem comapOfSurjective_inverseTransposeCoordinateIso_eq_iff
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) :
    I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
        (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I ↔
      ∀ (A : Type u) [CommRing A] [Algebra R A], ∀ g ∈ hopfIdealPointsSubgroup (R := R) n I A,
        Matrix.GeneralLinearGroup.inverseTranspose g ∈ hopfIdealPointsSubgroup n I A := by
  set θ := (inverseTransposeCoordinateIso R n).hom.hom
  constructor
  · intro hI A _ _ g hg
    rw [mem_hopfIdealPointsSubgroup_iff] at hg ⊢
    intro x hx
    rw [← (pointsMulEquiv (R := R) n).apply_symm_apply g, pointsMulEquiv_symm_inverseTranspose]
    rw [← hI, HopfIdeal.mem_comapOfSurjective] at hx
    exact hg _ hx
  · intro h
    -- Test stability on the universal point of the subgroup, the quotient map.
    have hle (x : coordinateHopfAlgebra R n) (hx : x ∈ I) : θ x ∈ I := by
      let f : WithConv (coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n ⧸ I.toIdeal) :=
        toConv (Ideal.Quotient.mkₐ R I.toIdeal)
      have hf : pointsMulEquiv n f ∈ hopfIdealPointsSubgroup n I _ := by
        rw [mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply]
        intro y hy
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
      have hθf := h _ _ hf
      rw [mem_hopfIdealPointsSubgroup_iff, pointsMulEquiv_symm_inverseTranspose] at hθf
      have := hθf x hx
      simp only [AlgHom.comp_apply, f] at this
      exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp this)
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ HopfIdeal.mem_comapOfSurjective.mpr (hle x hx))
    have hθθ : θ (θ x) = x :=
      congr($(inverseTransposeCoordinateIso_hom_comp_self (R := R) (n := n)).hom x)
    rw [← hθθ]
    exact hle _ (HopfIdeal.mem_comapOfSurjective.mp hx)

section GeneralRing

variable (I : HopfIdeal R (coordinateHopfAlgebra R n))
  (hI : I.comapOfSurjective (inverseTransposeCoordinateIso R n).hom.hom
    (ConcreteCategory.bijective_of_isIso (inverseTransposeCoordinateIso R n).hom).2 = I)

/-- **Inverse transpose on a transpose-stable closed subgroup of `GLₙ`.** The coordinate
automorphism of the closed subgroup cut out by a Hopf ideal `I` that is stable under inverse
transpose, induced by the inverse-transpose coordinate automorphism of `GLₙ`. -/
noncomputable def inverseTransposeQuotientIso :
    _root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I ≅
      _root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I :=
  CommHopfAlgCat.quotientIsoOfComapEq (inverseTransposeCoordinateIso R n) I hI

/-- The restricted inverse transpose sends the class of `x` to the class of its inverse
transpose. -/
theorem inverseTransposeQuotientIso_hom_mk (x : coordinateHopfAlgebra R n) :
    (inverseTransposeQuotientIso I hI).hom.hom (Ideal.Quotient.mk I.toIdeal x) =
      Ideal.Quotient.mk I.toIdeal ((inverseTransposeCoordinateIso R n).hom.hom x) :=
  quotientIsoOfComapEq_hom_mk hI x

/-- The restricted inverse transpose is an involution. -/
@[reassoc (attr := simp)]
theorem inverseTransposeQuotientIso_hom_comp_self :
    (inverseTransposeQuotientIso I hI).hom ≫ (inverseTransposeQuotientIso I hI).hom =
      𝟙 (_root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) :=
  quotientIsoOfComapEq_hom_comp_self inverseTransposeCoordinateIso_hom_comp_self hI

/-- **The fixed points of the restricted inverse transpose are the orthogonal points.** A point `p`
of the closed subgroup cut out by `I` is fixed by inverse transpose exactly when the matrix of the
point `p ∘ (O(GLₙ) → O(GLₙ) ⧸ I)` of `GLₙ` is orthogonal. -/
theorem toConv_comp_inverseTransposeQuotientIso_eq_self_iff (A : Type v) [CommRing A]
    [Algebra R A] (p : coordinateHopfAlgebra R n ⧸ I.toIdeal →ₐ[R] A) :
    p.comp ((inverseTransposeQuotientIso I hI).hom.hom :
        coordinateHopfAlgebra R n ⧸ I.toIdeal →ₐ[R] coordinateHopfAlgebra R n ⧸ I.toIdeal) = p ↔
      pointsMulEquiv n (toConv (p.comp (Ideal.Quotient.mkₐ R I.toIdeal))) ∈
        GLOrthogonal (Fin n) A := by
  rw [← toConv_comp_inverseTransposeCoordinateIso_eq_self_iff, toConv_injective.eq_iff,
    ofConv_toConv]
  constructor
  · intro hp
    ext x
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    conv_rhs => rw [← hp]
    exact congrArg p (inverseTransposeQuotientIso_hom_mk I hI x).symm
  · intro hp
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := congr($hp x)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact (congrArg p (inverseTransposeQuotientIso_hom_mk I hI x)).trans this

end GeneralRing

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
  rw [inverseTransposeQuotientIso, mem_twistedRealPoints_quotientIsoOfComapEq_iff,
    mem_twistedRealPoints_inverseTransposeCoordinateIso_iff]

/-- **Inverse transpose is a Cartan involution of a transpose-stable subgroup of `GLₙ`** (Milne,
Example 1.17(b)). If the closed subgroup `G ⊆ GLₙ` over `ℝ` cut out by `I` is stable under
transpose, then inverse transpose restricts to a Cartan involution of `G`: its twisted real points
are the points of `G(ℂ)` lying in the compact unitary group `U(n)`. -/
theorem isCartanInvolution_inverseTransposeQuotientIso :
    IsCartanInvolution (inverseTransposeQuotientIso I hI) :=
  isCartanInvolution_inverseTransposeCoordinateIso.quotient hI

end Real

end TauCeti.GeneralLinear
