/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The closed weight torus of the generated doubled E₆ subgroup

The weights of `V(ϖ₁) ⊕ V(ϖ₆)` span the full type-E₆ character lattice. Restriction from the
subgroup generated over the ground ring to its weight torus is therefore surjective. Its kernel
cuts out a closed rank-six split torus, contained in the generated positive subgroup. The torus
ideal commutes with free scalar extension, and its points give precisely the named doubled
minuscule weight-torus matrices over every commutative value algebra.

These are the closed torus data needed for a pinning. Neither maximality nor identification
with the pinned simply connected group is asserted. The generated subgroup is not identified
with the specialization of the integral toral-closure carrier.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The quotient, point and scalar-extension arguments follow
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.WeightTorus`, using the doubled E₆ weights and
  its existing `generatedWeightTorusCoordinateMap` rather than a new torus morphism.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

/-- Restriction of the generated doubled carrier's coordinates to its weight torus is
surjective, since the doubled minuscule weights span the full character lattice. -/
theorem generatedWeightTorusCoordinateMap_surjective :
    Function.Surjective (generatedWeightTorusCoordinateMap R).hom := by
  apply Function.Surjective.of_comp (g := (generatedCoordinateMap R).hom)
  rw [← BialgHom.coe_comp, ← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
    GeneralLinear.weightTorusCoordinateBialgHom_def]
  exact DiagonalizableGroup.surjective_diagonalCoordinateMap _ _
    (SplitTorus.closure_range_weightCharacter_eq_top matrixWeight span_range_matrixWeight_eq_top)

namespace Generated

/-- The defining Hopf ideal of the weight torus inside the ground-ring-generated doubled
minuscule carrier. -/
def weightTorusDefiningIdeal : HopfIdeal R (generatedCoordinateHopfAlgebra R) :=
  HopfIdeal.kerOfSurjective (generatedWeightTorusCoordinateMap R).hom
    (generatedWeightTorusCoordinateMap_surjective R)

/-- A carrier coordinate belongs to the torus ideal exactly when its torus restriction vanishes. -/
@[simp]
theorem mem_weightTorusDefiningIdeal (x : generatedCoordinateHopfAlgebra R) :
    x ∈ weightTorusDefiningIdeal R ↔ (generatedWeightTorusCoordinateMap R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the intrinsic torus ideal is the rank-six split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra R))
        (weightTorusDefiningIdeal R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6)) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (generatedWeightTorusCoordinateMap R)
      (generatedWeightTorusCoordinateMap_surjective R)

/-- The quotient identification recovers restriction to the weight torus. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra R))
        (weightTorusDefiningIdeal R) ≫ (weightTorusCoordinateIso R).hom =
      ObjectProperty.homMk (generatedWeightTorusCoordinateMap R) := by
  apply ObjectProperty.hom_ext
  exact CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- The closed weight torus is split over every commutative base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra R))
        (weightTorusDefiningIdeal R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let e : Multiplicative (Fin 6 →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin 6) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  let i : DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6)) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 6))) :=
    ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R e))
  exact ⟨6, ⟨(weightTorusCoordinateIso R ≪≫ i).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal R

/-- Contravariantly, the closed weight torus lies in the generated positive subgroup. -/
theorem carrierDefiningIdeal_le_weightTorusDefiningIdeal :
    Positive.carrierDefiningIdeal R ≤ weightTorusDefiningIdeal R := by
  intro x hx
  rw [mem_weightTorusDefiningIdeal, generatedWeightTorusCoordinateMap_def]
  exact RingHom.mem_ker.mp
    (Positive.carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift R (.inr ()) hx)

/-- On algebra-valued points, restriction to the torus followed by the carrier inclusion is
the named doubled minuscule weight-torus matrix. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6))).obj) A) :
    GeneralLinear.pointsMulEquiv 54
        ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedWeightTorusCoordinateMap R)).app A q)) =
      (weightTorusPoints A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 54) A) := by
  have hcomp : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hp := CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (generatedCoordinateMap R ≫ generatedWeightTorusCoordinateMap R) A q
  simp only [_root_.CommHopfAlgCat.hom_comp, hcomp] at hp
  have he := (CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (generatedCoordinateMap R) (generatedWeightTorusCoordinateMap R) A q).symm.trans hp
  rw [he, GeneralLinear.pointsMulEquiv_comp_weightTorusCoordinateBialgHom]
  apply Units.ext
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]

/-- The closed generated torus maps to exactly the named weight-torus matrices in `GL₅₄`.
The value algebra need not be reduced or a field. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) 54).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A).hom) =
      ((weightTorusPoints A).range).map (points A).subtype := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  -- Removing the subgroup inclusions leaves the point maps of the characteristic equation.
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨_, ⟨SplitTorus.pointsMulEquiv q, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    exact (pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap R A q).symm
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    have h := pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s)
    rw [MulEquiv.apply_symm_apply] at h
    exact h

variable (S : Type max u v) [CommRing S] [Algebra R S] [Module.Free R S]

/-- Free scalar extension carries the generated torus ideal to the generated torus ideal over
the new base ring, along the existing generated-carrier comparison. -/
@[simp↓]
theorem map_baseChange_weightTorusDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (weightTorusDefiningIdeal R)).map
        (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom.hom =
      weightTorusDefiningIdeal S := by
  unfold weightTorusDefiningIdeal
  apply CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (generatedCoordinateHopfAlgebraBaseChangeIso R S)
    (generatorCoordinateAlgebraBaseChangeIso R S (.inr ()))
    (generatedWeightTorusCoordinateMap_surjective R)
    (generatedWeightTorusCoordinateMap_surjective S)
  rw [generatedWeightTorusCoordinateMap_def,
    baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom,
    Iso.inv_hom_id_assoc, generatedWeightTorusCoordinateMap_def]

end Generated

end

end TauCeti.E6DoubledMinuscule
