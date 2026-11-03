/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.ClosedGenerators
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.Lie.E7.Minuscule.WeightTorus

/-!
# The closed weight torus of the generated E₇ subgroup

Restriction from the ground-ring-generated E₇ carrier to its weight torus is surjective.
Its kernel defines a closed rank-seven split torus contained in the generated positive subgroup.
The torus ideal commutes with free scalar extension.

This is the torus inside `generatedCoordinateHopfAlgebra`, not the specialization of the
integral carrier studied in `E7.Minuscule.WeightTorus`. No equality of those carriers or
maximality of this torus is asserted.

The quotient uses the Hopf-algebra first isomorphism theorem. The split-torus property and
point comparison are transported from `E7.Minuscule.WeightTorus` through the common torus
coordinates.
-/

public section

open CategoryTheory
open TauCeti.DynkinType

namespace TauCeti.E7Minuscule.Generated

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

/-- Restriction of the generated carrier's coordinates to the weight torus is surjective. -/
theorem generatedCoordinateLift_torus_surjective :
    Function.Surjective (generatedCoordinateLift R (.inr ())).hom := by
  have h : Function.Surjective (generatorCoordinateMap R (.inr ())).hom := by
    rw [generatorCoordinateMap_inr, ← coordinateMap_comp_weightTorusToBaseChangeCoordinateMap]
    exact (weightTorusToBaseChangeCoordinateMap_surjective R).comp (coordinateMap_surjective R)
  rw [← generatedCoordinateMap_comp_generatedCoordinateLift] at h
  exact Function.Surjective.of_comp h

/-- The defining ideal of the weight torus inside the ground-ring-generated E₇ carrier. -/
def weightTorusDefiningIdeal : HopfIdeal R (generatedCoordinateHopfAlgebra R) :=
  HopfIdeal.kerOfSurjective (generatedCoordinateLift R (.inr ())).hom
    (generatedCoordinateLift_torus_surjective R)

/-- A carrier coordinate lies in the torus ideal precisely when its torus restriction vanishes. -/
@[simp]
theorem mem_weightTorusDefiningIdeal (x : generatedCoordinateHopfAlgebra R) :
    x ∈ weightTorusDefiningIdeal R ↔ (generatedCoordinateLift R (.inr ())).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the intrinsic torus ideal is the rank-seven split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient (finiteTypeGeneratedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 7)) :=
  ObjectProperty.isoMk _ <|
    _root_.CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso
      (generatedCoordinateLift R (.inr ())) (generatedCoordinateLift_torus_surjective R)

/-- The quotient identification recovers restriction to the weight torus. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient (finiteTypeGeneratedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) ≫ (weightTorusCoordinateIso R).hom =
      ObjectProperty.homMk (generatedCoordinateLift R (.inr ())) := by
  apply ObjectProperty.hom_ext
  exact _root_.CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom
    (generatedCoordinateLift R (.inr ())) (generatedCoordinateLift_torus_surjective R)

/-- The closed subgroup cut out by the torus ideal is split over any commutative base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeGeneratedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R)) := by
  exact (splitTorusCommHopfAlgProperty R).prop_of_iso
    (E7Minuscule.weightTorusCoordinateIso R ≪≫ (weightTorusCoordinateIso R).symm)
    (E7Minuscule.splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal R)

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal R

/-- Contravariantly, the closed weight torus lies in the generated positive subgroup. -/
theorem carrierDefiningIdeal_le_weightTorusDefiningIdeal :
    Positive.carrierDefiningIdeal R ≤ weightTorusDefiningIdeal R := by
  intro x hx
  rw [mem_weightTorusDefiningIdeal]
  exact Positive.carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift R (.inr ()) hx

/-- On algebra-valued points, the generated torus lift gives the named weight-torus matrix. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_generatedCoordinateLift_torus
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 7))).obj) A) :
    GeneralLinear.pointsMulEquiv 56
        ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateLift R (.inr ()))).app A
            q)) =
      (weightTorusPoints A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 56) A) := by
  have hg := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (generatedCoordinateMap R) (generatedCoordinateLift R (.inr ())) A q
  have hs := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (coordinateMap R) (weightTorusToBaseChangeCoordinateMap R) A q
  rw [generatedCoordinateMap_comp_generatedCoordinateLift, generatorCoordinateMap_inr] at hg
  rw [coordinateMap_comp_weightTorusToBaseChangeCoordinateMap] at hs
  exact (congrArg (GeneralLinear.pointsMulEquiv 56) (hg.symm.trans hs)).trans
    (E7Minuscule.pointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap R A q)

/-- The closed generated torus maps to precisely the named weight-torus matrices in `GL₅₆`.
The value algebra need not be reduced or a field. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) 56).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A).hom) =
      ((weightTorusPoints A).range).map (points A).subtype := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  -- After removing the subgroup inclusion, composite monoid homomorphisms and
  -- equivalences-to-homomorphisms have the same element map as the point comparison.
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨_, ⟨SplitTorus.pointsMulEquiv q, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    exact (pointsMulEquiv_mapPointsFunctor_generatedCoordinateLift_torus R A q).symm
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    have h := pointsMulEquiv_mapPointsFunctor_generatedCoordinateLift_torus R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s)
    rw [MulEquiv.apply_symm_apply] at h
    exact h

variable (S : Type u) [CommRing S] [Algebra R S] [Module.Free R S]

attribute [local instance high] Algebra.toModule

/-- The generated-carrier comparison transports the torus ideal under free scalar extension. -/
@[simp↓]
theorem map_baseChange_weightTorusDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (weightTorusDefiningIdeal R)).map
        (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom.hom =
      weightTorusDefiningIdeal S := by
  unfold weightTorusDefiningIdeal
  apply CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (generatedCoordinateHopfAlgebraBaseChangeIso R S)
    (generatorCoordinateAlgebraBaseChangeIso R S (.inr ()))
    (generatedCoordinateLift_torus_surjective R) (generatedCoordinateLift_torus_surjective S)
  rw [baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom,
    Iso.inv_hom_id_assoc]

end

end TauCeti.E7Minuscule.Generated
