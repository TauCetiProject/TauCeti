/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation

/-!
# Conjugates of numbered root subgroups in the short-root G₂ carrier

Conjugation by any prime-field carrier point transports a numbered root subgroup to a
closed additive subgroup scheme. The coordinate pullback represents the conjugation on
points over every commutative `𝔽₃`-algebra, and its parameters are injective and natural.
This supplies the shared scheme construction for explicit nonsimple root subgroups.

The coordinate construction follows
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup`.
See R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 6.4.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

local notation "Q" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
  (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- A numbered root homomorphism conjugated by the scalar extension of a carrier point. -/
def conjugateRootSubgroupPoints (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2)
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  (MulAut.conj (pointsMap (Algebra.ofId (ZMod 3) A) g)).toMonoidHom.comp
    (rootSubgroupPoints j A)

/-- The transported homomorphism is the specified conjugate of a numbered root point. -/
theorem conjugateRootSubgroupPoints_apply (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2)
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] (u : Multiplicative A) :
    conjugateRootSubgroupPoints g j A u =
      pointsMap (Algebra.ofId (ZMod 3) A) g * rootSubgroupPoints j A u *
        (pointsMap (Algebra.ofId (ZMod 3) A) g)⁻¹ :=
  (rfl)

/-- Coefficient change preserves conjugated root points. -/
@[simp]
theorem pointsMap_conjugateRootSubgroupPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2)
    (u : Multiplicative A) :
    pointsMap f (conjugateRootSubgroupPoints g j A u) =
      conjugateRootSubgroupPoints g j B (Multiplicative.ofAdd (f u.toAdd)) := by
  have hbase : pointsMap f (pointsMap (Algebra.ofId (ZMod 3) A) g) =
      pointsMap (Algebra.ofId (ZMod 3) B) g := by
    rw [← MonoidHom.comp_apply, ← pointsMap_comp, Algebra.comp_ofId]
  simp only [conjugateRootSubgroupPoints_apply, map_mul, map_inv,
    pointsMap_rootSubgroupPoints, hbase]

/-- Pullback of a conjugated root subgroup: inner conjugation followed by the numbered
root-coordinate map. -/
def conjugateRootSubgroupCoordinateMap (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2) :
    Q ⟶ AdditiveGroup.coordinateHopfAlgebra (ZMod 3) :=
  (CommHopfAlgCat.innerConjugationIso Q
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g)).hom ≫
      CommHopfAlgCat.commonKernelLift generator (.inl j)

/-- The coordinate pullback is the composite of inner conjugation and a numbered root map. -/
theorem conjugateRootSubgroupCoordinateMap_def (g : points (ZMod 3))
    (j : Fin 2 ⊕ Fin 2) :
    conjugateRootSubgroupCoordinateMap g j =
      (CommHopfAlgCat.innerConjugationIso Q
        ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g)).hom ≫
          CommHopfAlgCat.commonKernelLift generator (.inl j) :=
  (rfl)

/-- The coordinate pullback induces the conjugation homomorphism over every value algebra. -/
theorem pointsMulEquiv_conjugateRootSubgroupCoordinateMap (g : points (ZMod 3))
    (j : Fin 2 ⊕ Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
      (CommAlgCat.of (ZMod 3) A)) :
    pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
      ((CommHopfAlgCat.Hom.mapPointsFunctor (conjugateRootSubgroupCoordinateMap g j)).app
        (CommAlgCat.of (ZMod 3) A) q) =
      conjugateRootSubgroupPoints g j A (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [conjugateRootSubgroupCoordinateMap_def,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom]
  -- The point-functor presentation carries the same group law, but its instances differ.
  erw [HopfAlgebra.innerConjugationPointNatIso_hom_app_apply, map_mul, map_mul, map_inv]
  apply Subtype.ext
  simp only [conjugateRootSubgroupPoints_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hconstant :
      (pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
        (HopfAlgebra.extendPoint Q (CommAlgCat.of (ZMod 3) A)
          ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g))).val =
        (pointsMap (Algebra.ofId (ZMod 3) A) g).val := by
    conv_rhs => rw [coe_pointsMap,
      ← (pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).apply_symm_apply g]
    rw [HopfAlgebra.extendPoint_apply, coe_pointsMulEquiv_apply, coe_pointsMulEquiv_apply]
    -- The quotient's concrete WithConv group instance differs from the point-functor one.
    erw [CommHopfAlgCat.quotientPointsHom_apply, CommHopfAlgCat.quotientPointsHom_apply]
    rw [← GeneralLinear.pointsMulEquiv_mapValue]
    simp only [AlgHom.mapValue_apply, AlgHom.comp_assoc]
  -- The common-kernel point uses the concrete CommAlgCat.of algebra instance.
  erw [hconstant, pointsMulEquiv_commonKernelLift_root]

/-- Each conjugated root-coordinate map is surjective. -/
theorem conjugateRootSubgroupCoordinateMap_surjective (g : points (ZMod 3))
    (j : Fin 2 ⊕ Fin 2) :
    Function.Surjective (conjugateRootSubgroupCoordinateMap g j).hom := by
  rw [conjugateRootSubgroupCoordinateMap_def, CommHopfAlgCat.hom_comp]
  exact (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl j)
    (generator_surjective _)).comp (by
      rw [← CommHopfAlgCat.coe_ofIso]
      exact (CommHopfAlgCat.ofIso (CommHopfAlgCat.innerConjugationIso Q
        ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm g))).surjective)

/-- The closed additive subgroup obtained by conjugating a numbered root subgroup. -/
def conjugateRootSubgroup (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2) :
    AdditiveGroup.groupScheme (ZMod 3) ⟶ groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
    (hopfSpec (CommRingCat.of (ZMod 3))).map (conjugateRootSubgroupCoordinateMap g j).op ≫
      eqToHom (by rw [groupScheme_def, definingIdeal_def])

/-- The subgroup morphism is the spectrum of the specified coordinate pullback. -/
theorem conjugateRootSubgroup_def (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2) :
    conjugateRootSubgroup g j = eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
      (hopfSpec (CommRingCat.of (ZMod 3))).map (conjugateRootSubgroupCoordinateMap g j).op ≫
        eqToHom (by rw [groupScheme_def, definingIdeal_def]) :=
  (rfl)

/-- Conjugated root-subgroup morphisms are closed immersions of group schemes over `𝔽₃`. -/
instance isClosedImmersion_conjugateRootSubgroup (g : points (ZMod 3))
    (j : Fin 2 ⊕ Fin 2) : IsClosedImmersion (conjugateRootSubgroup g j).hom.hom.left := by
  rw [conjugateRootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def (ZMod 3))
    (by rw [groupScheme_def, definingIdeal_def]) (conjugateRootSubgroupCoordinateMap g j)).2
      (conjugateRootSubgroupCoordinateMap_surjective g j)

/-- Conjugated root homomorphisms have injective parameters over every coefficient algebra. -/
theorem conjugateRootSubgroupPoints_injective (g : points (ZMod 3)) (j : Fin 2 ⊕ Fin 2)
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    Function.Injective (conjugateRootSubgroupPoints g j A) := by
  intro u v h
  apply (AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) (A := A)).symm.injective
  apply CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
    (conjugateRootSubgroupCoordinateMap g j)
    (conjugateRootSubgroupCoordinateMap_surjective g j) (CommAlgCat.of (ZMod 3) A)
  apply (pointsMulEquiv (CommAlgCat.of (ZMod 3) A)).injective
  rw [pointsMulEquiv_conjugateRootSubgroupCoordinateMap,
    pointsMulEquiv_conjugateRootSubgroupCoordinateMap,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact h

end

end TauCeti.G2ShortRoot.PrimeField
