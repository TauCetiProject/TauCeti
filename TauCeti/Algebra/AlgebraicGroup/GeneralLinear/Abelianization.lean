/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Derived
public import TauCeti.Algebra.AlgebraicGroup.Derived.Abelianization
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants

/-!
# The determinant quotient and the abelianization of `GLₙ`

In positive rank, the determinant exhibits the multiplicative group as the quotient of
`GLₙ` by `SLₙ`, both on every algebra of points and as an fppf sheaf. Over an arbitrary
commutative base ring, the functions invariant under `SLₙ` are exactly the functions of
the determinant. Over a field, where the scheme-theoretic derived subgroup is `SLₙ`, this
identifies the affine abelianization of `GLₙ` with the multiplicative group.

The rank hypothesis is essential: the determinant of the rank-zero group is constant.
The assertions about abelianization concern group schemes, rather than abelianization of
the group of rational points, which can behave differently over small finite fields.

The proof reuses Mathlib's `Matrix.GeneralLinearGroup.det_surjective`, the determinant
comparison on convolution points, the kernel-quotient comparison, and
`Algebra.IsEffective.of_section` for descent of invariant functions.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§5 and 6d.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The natural comparison `GLₙ(A) / SLₙ(A) → 𝔾ₘ(A)` is an isomorphism for every
commutative value algebra. Its value on a quotient class is given by the existing
`CommHopfAlgCat.kernelPointwiseQuotientMap_mk`. -/
theorem isIso_kernelPointwiseQuotientNatTrans_determinant (hn : 0 < n) :
    IsIso (CommHopfAlgCat.kernelPointwiseQuotientNatTrans.{u, u, v}
      (determinantCoordinateMap R n)) := by
  have hsurj (A : CommAlgCat.{v} R) : Function.Surjective
      ((CommHopfAlgCat.Hom.mapPointsFunctor (determinantCoordinateMap R n)).app A) := by
    intro y
    obtain ⟨g, hg⟩ := determinantPoints_surjective (R := R) hn y
    refine ⟨g, ?_⟩
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply]
    exact (determinantPoints_apply_apply R n g x).symm.trans
      (congrArg (fun p ↦ p.ofConv x) hg)
  have (A : CommAlgCat.{v} R) : IsIso
      ((CommHopfAlgCat.kernelPointwiseQuotientNatTrans
        (determinantCoordinateMap R n)).app A) := by
    rw [CommHopfAlgCat.kernelPointwiseQuotientNatTrans_app]
    have := CommHopfAlgCat.kernelPointwiseQuotientMap_isIso _ A (hsurj A)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The determinant represents the fppf quotient of `GLₙ` by `SLₙ` in positive rank.
The comparison is compatible with the quotient projection by
`CommHopfAlgCat.fppfQuotientProjection_comp_kernelFppfQuotientHom`. -/
theorem isIso_kernelFppfQuotientHom_determinant (hn : 0 < n) :
    IsIso (CommHopfAlgCat.kernelFppfQuotientHom (determinantCoordinateMap R n)) := by
  apply CommHopfAlgCat.isIso_kernelFppfQuotientHom_of_exists_lift
  intro A y
  obtain ⟨g, hg⟩ := determinantPoints_surjective (R := R) hn (toConv y)
  refine ⟨A, 𝟙 A, g.ofConv, ?_, ?_, ?_⟩
  · exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  · exact RingHom.FinitePresentation.id A
  · apply AlgHom.ext
    intro x
    exact (determinantPoints_apply_apply R n g x).symm.trans
      (congrArg (fun p ↦ p.ofConv x) hg)

/-- Over any commutative base ring, a regular function on `GLₙ` is invariant under `SLₙ`
exactly when it is pulled back from the multiplicative group by the determinant. -/
theorem coinvariants_specialLinear_eq_range_determinant (hn : 0 < n) :
    (SpecialLinear.definingHopfIdeal R n).coinvariants =
      (determinantCoordinateMap R n).hom.toAlgHom.range := by
  obtain ⟨s, hs⟩ := exists_retraction_determinantCoordinateMap (R := R) hn
  apply CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range_of_isEffective
  let := (determinantCoordinateMap R n).hom.toAlgHom.toAlgebra
  let s' : coordinateHopfAlgebra R n →ₐ[MonoidAlgebra R (Multiplicative ℤ)]
      MonoidAlgebra R (Multiplicative ℤ) :=
    { s.toRingHom with commutes' := fun x ↦ DFunLike.congr_fun hs x }
  exact Algebra.IsEffective.of_section s'

section Field

variable {k : Type u} [Field k]

/-- The coordinate algebra of the affine abelianization of `GLₙ` is the group algebra of
`ℤ`, with its inclusion into `O(GLₙ)` given by the determinant coordinate map. -/
noncomputable def abelianizationIso (hn : 0 < n) :
    _root_.CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative ℤ)) ≅
      CommHopfAlgCat.coinvariants
        (CommHopfAlgCat.isNormal_derivedDefiningIdeal (coordinateHopfAlgebra k n)) := by
  let Q := CommHopfAlgCat.coinvariants
    (CommHopfAlgCat.isNormal_derivedDefiningIdeal (coordinateHopfAlgebra k n))
  let f : _root_.CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative ℤ)) ⟶ Q :=
    CommHopfAlgCat.liftCoinvariants
      (CommHopfAlgCat.isNormal_derivedDefiningIdeal (coordinateHopfAlgebra k n))
      (determinantCoordinateMap k n)
      (SpecialLinear.definingHopfIdeal_le_derivedDefiningIdeal k n)
  have hfx (x) : (f.hom x : coordinateHopfAlgebra k n) =
      (determinantCoordinateMap k n).hom x :=
    CommHopfAlgCat.coe_liftCoinvariants_apply _ _ _ x
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply injective_determinantCoordinateMap hn
      have h := congrArg (fun z : Q ↦ (z : coordinateHopfAlgebra k n)) hxy
      exact (hfx x).symm.trans (h.trans (hfx y))
    · intro y
      have hy : (y : coordinateHopfAlgebra k n) ∈
          (SpecialLinear.definingHopfIdeal k n).coinvariants := by
        simpa only [derivedDefiningIdeal_eq_specialLinear_definingHopfIdeal] using y.property
      rw [coinvariants_specialLinear_eq_range_determinant hn] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext ((hfx x).trans hx)⟩
  have := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  exact asIso f

/-- Under the abelianization isomorphism the canonical projection is the determinant. -/
@[reassoc (attr := simp)]
theorem abelianizationIso_hom_comp_coinvariantsι (hn : 0 < n) :
    (abelianizationIso (k := k) hn).hom ≫
        CommHopfAlgCat.coinvariantsι
          (CommHopfAlgCat.isNormal_derivedDefiningIdeal (coordinateHopfAlgebra k n)) =
      determinantCoordinateMap k n := by
  exact CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι
    (CommHopfAlgCat.isNormal_derivedDefiningIdeal (coordinateHopfAlgebra k n))
    (determinantCoordinateMap k n)
    (SpecialLinear.definingHopfIdeal_le_derivedDefiningIdeal k n)

/-- The inverse abelianization isomorphism also identifies the two quotient projections. -/
@[reassoc (attr := simp)]
theorem abelianizationIso_inv_comp_determinantCoordinateMap (hn : 0 < n) :
    (abelianizationIso (k := k) hn).inv ≫ determinantCoordinateMap k n =
      CommHopfAlgCat.coinvariantsι
        (CommHopfAlgCat.isNormal_derivedDefiningIdeal (coordinateHopfAlgebra k n)) := by
  rw [Iso.inv_comp_eq]
  exact (abelianizationIso_hom_comp_coinvariantsι hn).symm

/-- Every homomorphism from `GLₙ` to a commutative affine group factors uniquely through
the determinant, over every field and in positive rank. Coordinate arrows are reversed. -/
theorem _root_.CommHopfAlgCat.Hom.existsUnique_comp_determinantCoordinateMap
    {Q : _root_.CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k Q]
    (f : Q ⟶ coordinateHopfAlgebra k n) (hn : 0 < n) :
    ∃! g : Q ⟶ _root_.CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative ℤ)),
      g ≫ determinantCoordinateMap k n = f := by
  obtain ⟨g, hg, -⟩ := f.existsUnique_comp_coinvariantsι_derivedDefiningIdeal
  refine ⟨g ≫ (abelianizationIso hn).inv, ?_, ?_⟩
  · simpa only [Category.assoc, abelianizationIso_inv_comp_determinantCoordinateMap] using hg
  · intro g' hg'
    have : Mono (determinantCoordinateMap k n) :=
      ConcreteCategory.mono_of_injective _ (injective_determinantCoordinateMap hn)
    apply (cancel_mono (determinantCoordinateMap k n)).mp
    simpa only [Category.assoc, abelianizationIso_inv_comp_determinantCoordinateMap, hg]
      using hg'

end Field

end TauCeti.GeneralLinear
