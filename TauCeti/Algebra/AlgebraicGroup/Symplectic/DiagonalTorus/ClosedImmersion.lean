/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification
import TauCeti.CategoryTheory.Comma.Over

/-!
# The diagonal torus as a closed subgroup of the symplectic group

Over every commutative ring, the diagonal map from the rank-`m` split torus to `Sp₂ₘ` is a
closed immersion. Its defining Hopf ideal is the kernel of restriction to diagonal coordinates,
the quotient is isomorphic to the split-torus coordinate Hopf algebra, and the ideal is
compatible with scalar extension. These constructions make the diagonal torus available as a
closed subgroup when studying maximal tori and pinnings.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The diagonal split torus is a closed subgroup of `Sp₂ₘ` over every commutative ring. -/
instance isClosedImmersion_diagonalTorus :
    IsClosedImmersion (diagonalTorus (R := R) (m := m)).hom.hom.left := by
  -- Scheme packaging follows `GeneralLinear.DiagonalTorus.ClosedImmersion`.
  rw [diagonalTorus_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  exact (CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff _).2
    diagonalTorusCoordinateMap_surjective

/-- The diagonal split torus, bundled as a closed subgroup scheme of `Sp₂ₘ`. -/
noncomputable def diagonalTorusClosedSubgroup : ClosedSubgroupScheme (groupScheme R m) :=
  ClosedSubgroupScheme.mk (diagonalTorus (R := R) (m := m))

/-- The closed diagonal torus has the subobject represented by the diagonal morphism. -/
@[simp]
theorem coe_diagonalTorusClosedSubgroup :
    (diagonalTorusClosedSubgroup R m).1 =
      Subobject.mk (diagonalTorus (R := R) (m := m)) :=
  ClosedSubgroupScheme.coe_mk _

/-- The defining Hopf ideal of the diagonal torus is the kernel of coordinate restriction. -/
noncomputable def diagonalTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R m) :=
  (⊥ : HopfIdeal R _).comapOfSurjective
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom
    diagonalTorusCoordinateMap_surjective

/-- A function belongs to the diagonal-torus ideal precisely when its restriction vanishes. -/
@[simp]
theorem mem_diagonalTorusDefiningIdeal (x : coordinateHopfAlgebra R m) :
    x ∈ diagonalTorusDefiningIdeal R m ↔
      (diagonalTorusCoordinateMap (R := R) (m := m)).hom x = 0 := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.comapOfSurjective_bot,
    HopfIdeal.mem_kerOfSurjective]

/-- The closed-subgroup classification recovers the diagonal torus's defining Hopf ideal. -/
@[simp↓]
theorem hopfIdealOrderIsoClosedSubgroup_symm_apply_diagonalTorusClosedSubgroup :
    (CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup (coordinateHopfAlgebra R m)).symm
        (diagonalTorusClosedSubgroup R m) =
      OrderDual.toDual (diagonalTorusDefiningIdeal R m) := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.comapOfSurjective_bot]
  apply CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup_symm_apply_eq_ker
    (coordinateHopfAlgebra R m) _ (diagonalTorusClosedSubgroup R m)
    ((eqToIso (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin m))))).symm ≪≫
      (ClosedSubgroupScheme.mkIso (diagonalTorus (R := R) (m := m))).symm)
  simp [diagonalTorusClosedSubgroup, diagonalTorus_def]

/-- The quotient by the diagonal-torus ideal is the rank-`m` split-torus coordinate algebra. -/
noncomputable def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R m,
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal R m) ≅
      DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin m))) :=
  ObjectProperty.isoMk _ <|
    -- Quotient comparison follows `GeneralLinear.DiagonalTorus.Maximal`.
    CommHopfAlgCat.quotientIsoOfSurjective
      (diagonalTorusCoordinateMap (R := R) (m := m))
      diagonalTorusCoordinateMap_surjective ⊥ ≪≫
    CommHopfAlgCat.quotientBotIso _

/-- The quotient isomorphism identifies the quotient map with restriction to the torus. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient ⟨coordinateHopfAlgebra R m,
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (diagonalTorusDefiningIdeal R m) ≫
        (diagonalTorusCoordinateIso R m).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap (R := R) (m := m)) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, diagonalTorusCoordinateIso,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, diagonalTorusDefiningIdeal,
    Iso.trans_hom]
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfSurjective_hom
      (diagonalTorusCoordinateMap (R := R) (m := m)) diagonalTorusCoordinateMap_surjective,
    ← CommHopfAlgCat.quotientBotIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The coordinate quotient defining the symplectic diagonal torus is a split torus. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra R m,
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal R m)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨m, ⟨(diagonalTorusCoordinateIso R m).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal R m

private theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R m) (diagonalTorusDefiningIdeal R m) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
          (_root_.CommHopfAlgCat.{u} R)).mapIso (diagonalTorusCoordinateIso R m)).hom =
      diagonalTorusCoordinateMap (R := R) (m := m) := by
  have h := congrArg
    (fun f ↦ (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).map f)
    (mkQuotient_comp_diagonalTorusCoordinateIso_hom R m)
  rw [Functor.map_comp] at h
  -- A morphism in an `ObjectProperty.FullSubcategory` is definitionally its underlying
  -- morphism, so applying the forgetful functor changes only the wrapper. There is no
  -- propositional rewrite lemma for this reducible coercion.
  change CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R m)
      (diagonalTorusDefiningIdeal R m) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
          (_root_.CommHopfAlgCat.{u} R)).mapIso (diagonalTorusCoordinateIso R m)).hom =
      diagonalTorusCoordinateMap (R := R) (m := m) at h
  exact h

/-- The base-change isomorphism of symplectic coordinate Hopf algebras carries the base-changed
diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [CommRing K] [Algebra R K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal R m)).map
        (coordinateHopfAlgebraBaseChangeIso R K m).hom.hom =
      diagonalTorusDefiningIdeal K m :=
  CommHopfAlgCat.map_baseChangeHopfIdeal_of_quotientIso
    (diagonalTorusDefiningIdeal R m) (diagonalTorusDefiningIdeal K m)
    (coordinateHopfAlgebraBaseChangeIso R K m)
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
      (SplitTorus.characterGroup (ULift.{u} (Fin m))))
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
      (_root_.CommHopfAlgCat.{u} R)).mapIso (diagonalTorusCoordinateIso R m))
    (mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat R m)
    (diagonalTorusCoordinateMap_baseChange (m := m) R K)
    (fun x ↦ mem_diagonalTorusDefiningIdeal K m x)

/-- Over a field, the coordinate quotient defining the symplectic diagonal torus is a torus. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal
    (k : Type u) [Field k] (m : ℕ) :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient ⟨coordinateHopfAlgebra k m,
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k m)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k m).torus k _

grind_pattern torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal k m

end TauCeti.Symplectic
