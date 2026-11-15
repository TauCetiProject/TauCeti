/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Limit
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Kernel

/-!
# The dynamic Levi as an fppf quotient

For a cocharacter `λ` of an affine group scheme, the limit morphism on the dynamic
parabolic factors through the dynamic Levi. Its section is the Levi inclusion and its
scheme-theoretic kernel is the dynamic unipotent subgroup. Consequently the fppf
quotient `P(λ)/U(λ)` is represented by `Z(λ)`, compatibly with the limit projection.

These statements hold over an arbitrary commutative base ring, without smoothness,
reductivity or finite-type hypotheses, and retain the full subgroup scheme structures.
They supply the quotient interpretation of the dynamic Levi decomposition.

The construction uses the represented limit in `Dynamic.Limit` and the fppf first
isomorphism theorem `CommHopfAlgCat.isIso_kernelFppfQuotientHom_of_exists_lift`.
The Levi section provides global lifts over every value algebra.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory WithConv TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u w

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]

private theorem leviDefiningHopfIdeal_le_ker_parabolicLimitCoordinateMap
    (l : H →ₐc[R] LaurentPolynomial R) :
    (leviDefiningHopfIdeal l).toIdeal ≤
      RingHom.ker (parabolicLimitCoordinateMap l).hom.toAlgHom := by
  let P := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
    (parabolicDefiningHopfIdeal l)
  let A := CommAlgCat.of R P
  let q : HopfAlgebra.points (R := R) (H := P) A := toConv (AlgHom.id R P)
  have hg := limit_mem_levi ((parabolicPointsIso l).hom.app A q)
  rw [← quotientPointsSubgroup_leviDefiningHopfIdeal,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg
  intro x hx
  have h := hg x (HopfIdeal.mem_toIdeal.mp hx)
  rw [← mapPointsFunctor_parabolicLimitCoordinateMap_app l A q,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply] at h
  exact h

/-- The coordinate morphism of the dynamic limit with codomain the Levi subgroup:
contravariantly, `O(Z(λ)) → O(P(λ))`. -/
noncomputable def parabolicLimitToLeviCoordinateMap (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l) ⟶
      CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l) :=
  CommHopfAlgCat.liftQuotient (H := _root_.CommHopfAlgCat.of R H)
    (K := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l))
    (leviDefiningHopfIdeal l) (parabolicLimitCoordinateMap l)
    (leviDefiningHopfIdeal_le_ker_parabolicLimitCoordinateMap l)

/-- The Levi-valued limit followed by the ambient Levi inclusion is the represented limit. -/
@[simp↓, reassoc (attr := simp)]
theorem mkQuotient_comp_parabolicLimitToLeviCoordinateMap
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l) ≫
        parabolicLimitToLeviCoordinateMap l = parabolicLimitCoordinateMap l :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- On a quotient class, the Levi-valued limit sends a function to the constant Laurent
coefficient of its conjugation family, restricted to the parabolic. -/
@[simp↓]
theorem parabolicLimitToLeviCoordinateMap_mk (l : H →ₐc[R] LaurentPolynomial R) (h : H) :
    (parabolicLimitToLeviCoordinateMap l).hom
        ((CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
          (leviDefiningHopfIdeal l)).hom h) =
      (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l)).hom ((conjugationAlgHom l h).coeff 0) := by
  rw [← _root_.CommHopfAlgCat.comp_apply,
    mkQuotient_comp_parabolicLimitToLeviCoordinateMap, parabolicLimitCoordinateMap_apply]

/-- Inclusion of the dynamic Levi is a section of the Levi-valued limit. -/
@[simp↓, reassoc (attr := simp)]
theorem parabolicLimitToLeviCoordinateMap_comp_quotientMapOfLe
    (l : H →ₐc[R] LaurentPolynomial R) :
    parabolicLimitToLeviCoordinateMap l ≫
        CommHopfAlgCat.quotientMapOfLe (_root_.CommHopfAlgCat.of R H)
          (by rw [leviDefiningHopfIdeal_def]; exact le_sup_left) = 𝟙 _ := by
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← Category.assoc, mkQuotient_comp_parabolicLimitToLeviCoordinateMap,
    parabolicLimitCoordinateMap_comp_quotientMapOfLe, Category.comp_id]

/-- The kernel of the Levi-valued dynamic limit is the dynamic unipotent subgroup,
with its defining ideal transported into the parabolic coordinate algebra. -/
theorem kernelHopfIdeal_parabolicLimitToLeviCoordinateMap
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.kernelHopfIdeal (parabolicLimitToLeviCoordinateMap l) =
      l.unipotentDefiningHopfIdeal.map
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l)).hom := by
  rw [← CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective
    (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l))
    (CommHopfAlgCat.mkQuotient_surjective _ _),
    mkQuotient_comp_parabolicLimitToLeviCoordinateMap, kernelHopfIdeal_parabolicLimitCoordinateMap]

/-- On every value algebra, the ambient point of the Levi-valued limit is the dynamic
limit of the represented parabolic point. -/
theorem quotientPointsHom_parabolicLimitToLeviCoordinateMap
    (l : H →ₐc[R] LaurentPolynomial R) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R)
      (H := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l)) A) :
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
        (leviDefiningHopfIdeal l) A
        ((CommHopfAlgCat.Hom.mapPointsFunctor (parabolicLimitToLeviCoordinateMap l)).app A g) =
      limit A l ((parabolicPointsIso l).hom.app A g) := by
  exact (CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (H := _root_.CommHopfAlgCat.of R H)
    (K := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l))
    (leviDefiningHopfIdeal l) (parabolicLimitToLeviCoordinateMap l)
    (parabolicLimitCoordinateMap l) (mkQuotient_comp_parabolicLimitToLeviCoordinateMap l)
    A g).symm.trans (mapPointsFunctor_parabolicLimitCoordinateMap_app l A g)

/-- The dynamic unipotent subgroup is normal in the represented dynamic parabolic. -/
theorem isNormal_unipotentDefiningHopfIdeal_map_parabolic
    (l : H →ₐc[R] LaurentPolynomial R) :
    (l.unipotentDefiningHopfIdeal.map
      (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l)).hom).IsNormal := by
  rw [← kernelHopfIdeal_parabolicLimitToLeviCoordinateMap]
  exact CommHopfAlgCat.isNormal_kernelHopfIdeal _

/-- The kernel-quotient comparison for the Levi-valued limit is an isomorphism of
fppf sheaf groups. The Levi section lifts every point over its original value algebra. -/
instance isIso_kernelFppfQuotientHom_parabolicLimitToLeviCoordinateMap
    (l : H →ₐc[R] LaurentPolynomial R) :
    IsIso (CommHopfAlgCat.kernelFppfQuotientHom (parabolicLimitToLeviCoordinateMap l)) := by
  apply CommHopfAlgCat.isIso_kernelFppfQuotientHom_of_exists_lift
  intro A y
  let s : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l) ⟶
      CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l) :=
    CommHopfAlgCat.quotientMapOfLe (_root_.CommHopfAlgCat.of R H)
      (by rw [leviDefiningHopfIdeal_def]; exact le_sup_left)
  refine ⟨A, 𝟙 A, y.comp s.hom.toAlgHom, ?_, ?_, ?_⟩
  · exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  · exact RingHom.FinitePresentation.id A
  · ext x
    have hx := congrArg (fun f ↦ f.hom x)
      (parabolicLimitToLeviCoordinateMap_comp_quotientMapOfLe l)
    exact congrArg y hx

private theorem parabolicUnipotentKernel_eq (l : H →ₐc[R] LaurentPolynomial R) :
    (⟨l.unipotentDefiningHopfIdeal.map
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l)).hom,
      isNormal_unipotentDefiningHopfIdeal_map_parabolic l⟩ :
      {I : HopfIdeal R (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l)) // I.IsNormal}) =
      ⟨CommHopfAlgCat.kernelHopfIdeal (parabolicLimitToLeviCoordinateMap l),
        CommHopfAlgCat.isNormal_kernelHopfIdeal _⟩ :=
  Subtype.ext (kernelHopfIdeal_parabolicLimitToLeviCoordinateMap l).symm

/-- **The fppf quotient `P(λ)/U(λ)` is the dynamic Levi `Z(λ)`.** The subgroup in the
quotient is given by its actual defining ideal inside the parabolic coordinate ring. -/
noncomputable def parabolicLeviFppfQuotientIso (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.fppfQuotientSheaf
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l))
        (l.unipotentDefiningHopfIdeal.map
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
            (parabolicDefiningHopfIdeal l)).hom)
        (isNormal_unipotentDefiningHopfIdeal_map_parabolic l) ≅
      CommHopfAlgCat.pointsFppfGroupObject
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
          (leviDefiningHopfIdeal l)) :=
  eqToIso (congrArg (fun I ↦ CommHopfAlgCat.fppfQuotientSheaf _ I.val I.property)
    (parabolicUnipotentKernel_eq l)) ≪≫
    asIso (CommHopfAlgCat.kernelFppfQuotientHom (parabolicLimitToLeviCoordinateMap l))

/-- The quotient identification carries the projection onto `P(λ)/U(λ)` to the
dynamic limit with values in the Levi. -/
@[simp↓, reassoc (attr := simp↓)]
theorem fppfQuotientProjection_comp_parabolicLeviFppfQuotientIso_hom
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.fppfQuotientProjection
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l))
        (l.unipotentDefiningHopfIdeal.map
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
            (parabolicDefiningHopfIdeal l)).hom)
        (isNormal_unipotentDefiningHopfIdeal_map_parabolic l) ≫
        (parabolicLeviFppfQuotientIso l).hom =
      CommHopfAlgCat.pointsFppfGroupObjectMap (parabolicLimitToLeviCoordinateMap l) := by
  rw [parabolicLeviFppfQuotientIso, Iso.trans_hom, eqToIso.hom, asIso_hom,
    ← Category.assoc]
  have ht := eqToHom_naturality
    (fun I : {I : HopfIdeal R
        (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l)) // I.IsNormal} ↦
      CommHopfAlgCat.fppfQuotientProjection _ I.val I.property)
    (parabolicUnipotentKernel_eq l)
  simp only [eqToHom_refl, Category.id_comp] at ht
  rw [ht, CommHopfAlgCat.fppfQuotientProjection_comp_kernelFppfQuotientHom]

end BialgHom
