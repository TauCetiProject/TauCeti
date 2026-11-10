/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Generated.StandardComodule
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.FullWeight
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The closed weight torus of the generated Geck subgroup

When the Geck weights span the full weight lattice, restriction from the generated Geck
subgroup to its weight torus is surjective. Its kernel defines a closed split torus of rank
`t.rank`. The quotient identification retains the original torus parameters: on every value
algebra its inclusion is the diagonal matrix of the corresponding Geck weight characters.
The defining ideal is compatible with free scalar extension.

The spanning hypothesis holds for E₈, F₄ and G₂ by
`span_range_geckWeight_E8_eq_top`, `span_range_geckWeight_F4_eq_top` and
`span_range_geckWeight_G2_eq_top`. It is not imposed on the point formula, which also describes
nonfaithful torus maps for the other types. No maximality assertion is made. The generated
subgroup is not identified with the specialized integral Geck carrier or the pinned simply
connected group; transferring its constructions to either requires such an identification.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.

The kernel, quotient and scalar-extension constructions follow
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.WeightTorus`.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

universe u v w

noncomputable section

variable (t : DynkinType) (ht : t.Valid) (R : Type u) [CommRing R]

/-- The composite of the generated-carrier inclusion and its torus map is the diagonal
representation with the Geck weights, without any character-spanning hypothesis. -/
theorem hom_geckGeneratedWeightTorusCoordinateMap_comp_hom_geckGeneratedCoordinateMap :
    (t.geckGeneratedWeightTorusCoordinateMap ht R).hom.comp
        (t.geckGeneratedCoordinateMap ht R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) (t.geckWeightFin ht) := by
  rw [← _root_.CommHopfAlgCat.hom_comp,
    geckGeneratedCoordinateMap_comp_geckGeneratedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- On every value algebra, the generated torus map is the diagonal matrix whose entries
are the Geck weight characters evaluated at the original torus parameters. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_geckGeneratedWeightTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (SplitTorus.characterGroup (Fin t.rank))) A) :
    GeneralLinear.pointsMulEquiv (t.geckDim ht)
        ((CommHopfAlgCat.Hom.mapPointsFunctor (t.geckGeneratedCoordinateMap ht R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor
            (t.geckGeneratedWeightTorusCoordinateMap ht R)).app A q)) =
      diagGL (fun i ↦ torusCharacter (SplitTorus.pointsMulEquiv q) (t.geckWeightFin ht i)) := by
  rw [← CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, _root_.CommHopfAlgCat.hom_comp,
    hom_geckGeneratedWeightTorusCoordinateMap_comp_hom_geckGeneratedCoordinateMap]
  exact GeneralLinear.pointsMulEquiv_comp_weightTorusCoordinateBialgHom (t.geckWeightFin ht) A q

variable (hwt : Submodule.span ℤ (Set.range (t.geckWeight ht)) = ⊤)

include hwt in
/-- Full character span makes restriction from the generated Geck subgroup to its weight
torus surjective, over every commutative base ring. -/
theorem geckGeneratedWeightTorusCoordinateMap_surjective :
    Function.Surjective (t.geckGeneratedWeightTorusCoordinateMap ht R).hom := by
  have h : Function.Surjective
      (GeneralLinear.weightTorusCoordinateBialgHom (S := R) (t.geckWeightFin ht)) := by
    rw [GeneralLinear.weightTorusCoordinateBialgHom_def]
    apply DiagonalizableGroup.surjective_diagonalCoordinateMap
    apply SplitTorus.closure_range_weightCharacter_eq_top
    rwa [t.range_geckWeightFin ht]
  rw [← t.hom_geckGeneratedWeightTorusCoordinateMap_comp_hom_geckGeneratedCoordinateMap ht R] at h
  exact Function.Surjective.of_comp h

/-- The ideal of the closed weight torus inside the generated Geck subgroup, for a
full-weight Geck representation. -/
def geckGeneratedWeightTorusDefiningIdeal :
    HopfIdeal R (t.geckGeneratedCoordinateHopfAlgebra ht R) :=
  HopfIdeal.kerOfSurjective (t.geckGeneratedWeightTorusCoordinateMap ht R).hom
    (t.geckGeneratedWeightTorusCoordinateMap_surjective ht R hwt)

/-- A generated-carrier coordinate lies in the torus ideal exactly when its torus restriction
vanishes. -/
@[simp]
theorem mem_geckGeneratedWeightTorusDefiningIdeal
    (x : t.geckGeneratedCoordinateHopfAlgebra ht R) :
    x ∈ t.geckGeneratedWeightTorusDefiningIdeal ht R hwt ↔
      (t.geckGeneratedWeightTorusCoordinateMap ht R).hom x = 0 := by
  rw [geckGeneratedWeightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The closed generated weight torus has the coordinate Hopf algebra of the rank-`t.rank`
split torus, with its specified character coordinates. -/
def geckGeneratedWeightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (t.geckGeneratedCoordinateHopfAlgebra ht R))
        (t.geckGeneratedWeightTorusDefiningIdeal ht R hwt) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin t.rank)) :=
  ObjectProperty.isoMk _ <|
    _root_.CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso
      (t.geckGeneratedWeightTorusCoordinateMap ht R)
      (t.geckGeneratedWeightTorusCoordinateMap_surjective ht R hwt)

/-- The quotient identification recovers the stored weight-torus restriction map. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_geckGeneratedWeightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
          (FiniteTypeCommHopfAlgCat.of R (t.geckGeneratedCoordinateHopfAlgebra ht R))
          (t.geckGeneratedWeightTorusDefiningIdeal ht R hwt) ≫
        (t.geckGeneratedWeightTorusCoordinateIso ht R hwt).hom =
      ObjectProperty.homMk (t.geckGeneratedWeightTorusCoordinateMap ht R) :=
  ObjectProperty.hom_ext _
    (_root_.CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed generated weight torus is split over every commutative base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_geckGeneratedWeightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (t.geckGeneratedCoordinateHopfAlgebra ht R))
        (t.geckGeneratedWeightTorusDefiningIdeal ht R hwt)) :=
  (splitTorusCommHopfAlgProperty R).prop_of_iso
    (t.geckGeneratedWeightTorusCoordinateIso ht R hwt).symm
    (SplitTorus.splitTorus_coordinateRing R (Fin t.rank))

grind_pattern splitTorusCommHopfAlgProperty_quotient_geckGeneratedWeightTorusDefiningIdeal =>
  t.geckGeneratedWeightTorusDefiningIdeal ht R hwt

/-- The closed torus's algebra-valued points, viewed as matrices, are exactly the diagonal
matrices of Geck weight characters. This includes nonreduced value algebras. -/
theorem mem_map_quotientPointsSubgroup_geckGeneratedWeightTorusDefiningIdeal_iff
    (A : CommAlgCat.{v} R) (g : GL (Fin (t.geckDim ht)) A) :
    g ∈ (CommHopfAlgCat.quotientPointsSubgroup (t.geckGeneratedCoordinateHopfAlgebra ht R)
        (t.geckGeneratedWeightTorusDefiningIdeal ht R hwt) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) (t.geckDim ht)).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (t.geckGeneratedCoordinateMap ht R)).app A).hom) ↔
      ∃ s : Fin t.rank → Aˣ, diagGL (fun i ↦ torusCharacter s (t.geckWeightFin ht i)) = g := by
  rw [geckGeneratedWeightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q,
      (t.pointsMulEquiv_mapPointsFunctor_geckGeneratedWeightTorusCoordinateMap ht R A q).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    have h := t.pointsMulEquiv_mapPointsFunctor_geckGeneratedWeightTorusCoordinateMap ht R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s)
    rw [MulEquiv.apply_symm_apply] at h
    exact h

variable (S : Type max u w) [CommRing S] [Algebra R S] [Module.Free R S]

/-- Free scalar extension carries the intrinsic generated weight-torus ideal to the
corresponding ideal over the extended ring. -/
@[simp↓]
theorem map_baseChangeHopfIdeal_geckGeneratedWeightTorusDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S)
        (t.geckGeneratedWeightTorusDefiningIdeal ht R hwt)).map
        (t.geckGeneratedCoordinateHopfAlgebraBaseChangeIso ht R S).hom.hom =
      t.geckGeneratedWeightTorusDefiningIdeal ht S hwt := by
  unfold geckGeneratedWeightTorusDefiningIdeal
  apply CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (t.geckGeneratedCoordinateHopfAlgebraBaseChangeIso ht R S)
    (t.geckGeneratorCoordinateAlgebraBaseChangeIso R S (.inr ()))
    (t.geckGeneratedWeightTorusCoordinateMap_surjective ht R hwt)
    (t.geckGeneratedWeightTorusCoordinateMap_surjective ht S hwt)
  rw [geckGeneratedWeightTorusCoordinateMap_def,
    baseChangeMap_geckGeneratedCoordinateLift,
    Iso.inv_hom_id_assoc, geckGeneratedWeightTorusCoordinateMap_def]

end

end TauCeti.DynkinType
