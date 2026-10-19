/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel

/-!
# The represented dynamic limit

For a cocharacter `l` of an affine group, the dynamic limit on its parabolic subgroup
is a morphism of affine groups. Its coordinate morphism sends a function to the constant
Laurent coefficient of universal conjugation, restricted to the parabolic. Its
scheme-theoretic kernel is the dynamic unipotent subgroup, including on nonreduced value
algebras. Restriction to the Levi subgroup recovers its ambient inclusion.

The coordinate formula computes the limit of any parabolic point over a commutative value
algebra in an arbitrary universe. The kernel identity identifies the quotient of the
parabolic coordinate algebra defining the fibre over the identity with the coordinate
algebra of the dynamic unipotent subgroup.
The isomorphism `BialgHom.parabolicLimitKernelIso` realizes this identification as an
isomorphism of group schemes over the base, compatible with their inclusions into the parabolic.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory WithConv TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u w

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The coordinate morphism of the dynamic limit `P(l) → G`. Its direction is
`O(G) → O(P(l))`, opposite to the morphism of affine groups. -/
noncomputable def parabolicLimitCoordinateMap (l : H →ₐc[R] LaurentPolynomial R) :
    _root_.CommHopfAlgCat.of R H ⟶
      CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l) :=
  CommHopfAlgCat.homOfPointsMap
    ((parabolicPointsIso l).hom ≫ limitToLeviNatTrans l ≫ leviFunctorIncl l)

/-- The dynamic limit coordinate morphism evaluates the universal constant coefficient on
the parabolic quotient. -/
-- The categorical morphism carries sealed object types, so use this formula with `rw`.
theorem parabolicLimitCoordinateMap_apply (l : H →ₐc[R] LaurentPolynomial R) (h : H) :
    (parabolicLimitCoordinateMap l).hom h =
      (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l)).hom ((conjugationAlgHom l h).coeff 0) := by
  let P := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
    (parabolicDefiningHopfIdeal l)
  let A := CommAlgCat.of R P
  let q : HopfAlgebra.points (R := R) (H := P) A := toConv (AlgHom.id R P)
  have hm :
      (CommHopfAlgCat.Hom.mapPointsFunctor (parabolicLimitCoordinateMap l)).app A q =
        limit A l ((parabolicPointsIso l).hom.app A q) := by
    rw [parabolicLimitCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap]
    -- The component has a sealed functor-object domain. Naming that carrier lets the
    -- categorical composition rules apply to the quotient point.
    change (((parabolicPointsIso l).hom ≫ limitToLeviNatTrans l ≫
      leviFunctorIncl l).app A)
      (show (HopfAlgebra.pointsFunctor (R := R) (H := P)).obj A from q) = _
    rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply,
      limitToLeviNatTrans_app, leviFunctorIncl_app]
    exact coe_limitToLevi_apply A l _
  let g : parabolic A l := (parabolicPointsIso l).hom.app A q
  have hg : g.1 = CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l) A q :=
    coe_parabolicPointsIso_hom_app_apply l A q
  have hv : q.ofConv ((parabolicLimitCoordinateMap l).hom h) =
      (limit A l g).ofConv h :=
    (CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply
      (parabolicLimitCoordinateMap l) A q h).symm.trans
      (congrArg (fun p : WithConv (H →ₐ[R] A) ↦ p.ofConv h) hm)
  rw [limit_apply_eq_coeff_conjugate, coeff_conjugate, hg,
    CommHopfAlgCat.quotientPointsHom_apply] at hv
  simpa only [q, A, P, ofConv_toConv, AlgHom.comp_apply, AlgHom.id_apply,
    BialgHom.coe_toAlgHom] using hv

/-- On every commutative value algebra, precomposition by the coordinate morphism is
exactly the dynamic limit of the represented parabolic point. -/
-- Sealed functor-object carriers prevent this formula from matching even its own LHS with simp.
-- Use `rw [mapPointsFunctor_parabolicLimitCoordinateMap_app]` in importing modules.
theorem mapPointsFunctor_parabolicLimitCoordinateMap_app
    (l : H →ₐc[R] LaurentPolynomial R) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R)
      (H := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l)) A) :
    (CommHopfAlgCat.Hom.mapPointsFunctor (parabolicLimitCoordinateMap l)).app A g =
      limit A l ((parabolicPointsIso l).hom.app A g) := by
  let p : parabolic A l := (parabolicPointsIso l).hom.app A g
  have hp : p.1 = CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l) A g :=
    coe_parabolicPointsIso_hom_app_apply l A g
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  suffices hv : g.ofConv ((parabolicLimitCoordinateMap l).hom h) =
      (limit A l p).ofConv h by
    exact (CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply
      (parabolicLimitCoordinateMap l) A g h).trans hv
  rw [parabolicLimitCoordinateMap_apply, limit_apply_eq_coeff_conjugate,
    coeff_conjugate, hp, CommHopfAlgCat.quotientPointsHom_apply]
  rfl

/-- Restricting the represented limit to the Levi subgroup gives its ambient inclusion. -/
@[simp]
theorem parabolicLimitCoordinateMap_comp_quotientMapOfLe
    (l : H →ₐc[R] LaurentPolynomial R) :
    parabolicLimitCoordinateMap l ≫
        CommHopfAlgCat.quotientMapOfLe (_root_.CommHopfAlgCat.of R H)
          (by rw [leviDefiningHopfIdeal_def]; exact le_sup_left) =
      CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
        (leviDefiningHopfIdeal l) := by
  let Z := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
    (leviDefiningHopfIdeal l)
  let A := CommAlgCat.of R Z
  let q : HopfAlgebra.points (R := R) (H := Z) A := toConv (AlgHom.id R Z)
  let g := CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
    (leviDefiningHopfIdeal l) A q
  have hg : g ∈ levi A l := by
    rw [← quotientPointsSubgroup_leviDefiningHopfIdeal]
    exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ A q
  apply _root_.CommHopfAlgCat.hom_ext
  ext h
  rw [_root_.CommHopfAlgCat.comp_apply, parabolicLimitCoordinateMap_apply,
    ← _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]
  have hc := congrArg (fun p : WithConv (H →ₐ[R] A) => p.ofConv h)
    (limit_of_mem_levi hg)
  rw [limit_apply_eq_coeff_conjugate, coeff_conjugate] at hc
  simpa only [g, q, A, Z, CommHopfAlgCat.quotientPointsHom_apply, ofConv_toConv,
    AlgHom.comp_apply, AlgHom.id_apply, BialgHom.coe_toAlgHom] using hc

/-- The scheme-theoretic kernel of the dynamic limit is the dynamic unipotent subgroup.
The ideal is written in the parabolic coordinate algebra by mapping the ambient unipotent
ideal through the parabolic quotient. -/
theorem kernelHopfIdeal_parabolicLimitCoordinateMap
    (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.kernelHopfIdeal (parabolicLimitCoordinateMap l) =
      (unipotentDefiningHopfIdeal l).map
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l)).hom := by
  let q := CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
    (parabolicDefiningHopfIdeal l)
  let K := CommHopfAlgCat.kernelHopfIdeal (parabolicLimitCoordinateMap l)
  have hq : Function.Surjective q.hom := CommHopfAlgCat.mkQuotient_surjective _ _
  apply le_antisymm
  · rw [← HopfIdeal.toIdeal_le_toIdeal, CommHopfAlgCat.kernelHopfIdeal_toIdeal,
      Ideal.map_le_iff_le_comap]
    intro h hh
    have hc : Coalgebra.counit (R := R) h = 0 :=
      (HopfIdeal.mem_augmentation R H).mp (HopfIdeal.mem_toIdeal.mp hh)
    have hm := HopfIdeal.mem_map_of_mem q.hom
      (coeff_conjugationAlgHom_sub_counit_mem_unipotentDefiningHopfIdeal l h)
    apply Ideal.mem_comap.mpr
    apply HopfIdeal.mem_toIdeal.mpr
    have hm' : q.hom ((conjugationAlgHom l h).coeff 0) ∈
        (unipotentDefiningHopfIdeal l).map q.hom := by
      simpa only [hc, map_zero, sub_zero] using hm
    exact (parabolicLimitCoordinateMap_apply l h).symm ▸ hm'
  · rw [HopfIdeal.map_le_iff_le_comapOfSurjective hq,
      unipotentDefiningHopfIdeal_le_iff]
    constructor
    · intro h hh
      apply HopfIdeal.mem_comapOfSurjective.mpr
      have hz := (CommHopfAlgCat.mkQuotient_eq_zero_iff
        (_root_.CommHopfAlgCat.of R H) (parabolicDefiningHopfIdeal l) h).mpr hh
      exact hz ▸ K.toIdeal.zero_mem
    · intro h
      apply HopfIdeal.mem_comapOfSurjective.mpr
      have hc : Coalgebra.counit (R := R)
          (h - algebraMap R H (Coalgebra.counit (R := R) h)) = 0 := by simp
      have hm := CommHopfAlgCat.mem_kernelHopfIdeal_of_mem_augmentation
        (parabolicLimitCoordinateMap l) hc
      have hm' : (parabolicLimitCoordinateMap l).hom h -
          algebraMap R _ (Coalgebra.counit (R := R) h) ∈ K := by
        simpa only [map_sub, AlgHomClass.commutes] using hm
      rw [parabolicLimitCoordinateMap_apply] at hm'
      simpa only [map_sub, AlgHomClass.commutes] using hm'

/-- The scheme-theoretic kernel of the dynamic limit is canonically the group scheme
represented by the dynamic unipotent Hopf quotient. -/
noncomputable def parabolicLimitKernelIso (l : H →ₐc[R] LaurentPolynomial R) :
    CommHopfAlgCat.kernelSpec (parabolicLimitCoordinateMap l) ≅
      CommHopfAlgCat.quotientSpec (_root_.CommHopfAlgCat.of R H)
        (unipotentDefiningHopfIdeal l) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq
      (CommHopfAlgCat.quotientMapOfLe (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l))
      (CommHopfAlgCat.quotientMapOfLe_surjective _ _)
      (by rw [kernelHopfIdeal_parabolicLimitCoordinateMap]
          exact CommHopfAlgCat.kerOfSurjective_quotientMapOfLe
            (_root_.CommHopfAlgCat.of R H)
            (parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l))).symm.op

/-- Under the kernel identification, the unipotent inclusion into the parabolic is the
canonical kernel inclusion. -/
@[simp]
theorem parabolicLimitKernelIso_hom_comp_quotientSpecMapOfLe
    (l : H →ₐc[R] LaurentPolynomial R) :
    (parabolicLimitKernelIso l).hom ≫
        CommHopfAlgCat.quotientSpecMapOfLe (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l) =
      CommHopfAlgCat.kernelSpecι (parabolicLimitCoordinateMap l) := by
  rw [parabolicLimitKernelIso, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom,
    CommHopfAlgCat.quotientSpecMapOfLe_def, CommHopfAlgCat.kernelSpecι_def,
    CommHopfAlgCat.quotientSpecι_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp, ← op_comp,
    CommHopfAlgCat.Hom.comp_quotientIsoOfKerOfSurjectiveEq_inv]

end BialgHom
