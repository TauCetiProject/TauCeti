/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.MaximalTorus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal

/-!
# A chosen split maximal torus of the generated tripled D₄ group

Over every field, the generated tripled D₄ carrier has a chosen rank-four split maximal
torus, with its coordinate map in the standard coordinates of `SplitMaximalTorus`.
Its defining ideal is the existing weight-torus ideal. On points its parametrization is
exactly the tripled weight-torus parametrization, after removing the universe lift from
the four node indices. Maximality holds on every geometric fiber, not just among tori
defined over the ground field.

This supplies the chosen torus required by the intrinsic root-space and pinning interfaces.
It does not identify the generated carrier with the specialization of the integral carrier
or with an independently pinned simply connected group. The coordinate reindexing and its
point equation work over arbitrary commutative rings; the chosen maximal torus is constructed
only over fields, where the generated-carrier comparison applies to every field extension.

## Main declarations

* `TauCeti.D4Tripled.Generated.splitMaximalTorus`: the chosen split maximal torus over a field.
* `TauCeti.D4Tripled.Generated.splitMaximalTorus_definingIdeal`: its closed subgroup is the
  existing weight torus.
* `TauCeti.D4Tripled.Generated.pointsMulEquiv_mapDomain_splitMaximalTorusCoordinateMap`:
  its explicit matrix-valued parametrization.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.2.1 and Example 3.2.3.
* The coordinate adapter follows
  `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`.
* Geometric maximality uses the existing generated tripled D₄ weight-torus maximality
  and free-base-change comparison.
-/

public section

open CategoryTheory

namespace TauCeti.D4Tripled.Generated

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

private def torusCharacterEquiv :
    Multiplicative (Fin 4 →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin 4) →₀ ℤ) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr (M := ℤ) Equiv.ulift.symm)

private def torusCoordinateIso :
    (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4))).obj ≅
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 4)))).obj :=
  _root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R torusCharacterEquiv)

private theorem torusCoordinateIso_hom_single
    (c : Multiplicative (Fin 4 →₀ ℤ)) (r : R) :
    (torusCoordinateIso R).hom.hom (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (torusCharacterEquiv c) r := by
  exact MonoidAlgebra.domCongr_single (R := R) torusCharacterEquiv c r

/-- Restriction to the generated weight torus in the standard rank-four coordinates used by
`SplitMaximalTorus`. The only change of coordinates is the universe lift on node indices. -/
def splitMaximalTorusCoordinateMap : generatedCoordinateHopfAlgebra R ⟶
    (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 4)))).obj :=
  generatedWeightTorusCoordinateMap R ≫ (torusCoordinateIso R).hom

/-- The standard-coordinate torus is a closed subgroup of the generated carrier. -/
theorem splitMaximalTorusCoordinateMap_surjective :
    Function.Surjective (splitMaximalTorusCoordinateMap R).hom := by
  rw [splitMaximalTorusCoordinateMap, CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    (generatedWeightTorusCoordinateMap_surjective R)

private theorem ker_splitMaximalTorusCoordinateMap :
    HopfIdeal.kerOfSurjective (splitMaximalTorusCoordinateMap R).hom
      (splitMaximalTorusCoordinateMap_surjective R) = weightTorusDefiningIdeal R := by
  ext x
  rw [HopfIdeal.mem_kerOfSurjective, mem_weightTorusDefiningIdeal,
    splitMaximalTorusCoordinateMap, CommHopfAlgCat.hom_comp, BialgHom.coe_comp,
    Function.comp_apply]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (torusCoordinateIso R).hom).1

/-- The standard-coordinate torus map sends a torus point to the named tripled weight-torus
matrix, with its four parameters read at the lifted node indices. This holds over every
commutative value algebra, including nonreduced ones. -/
@[simp↓]
theorem pointsMulEquiv_mapDomain_splitMaximalTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin 4)))).obj) A) :
    GeneralLinear.pointsMulEquiv 24
        (BialgHom.mapDomain (generatedCoordinateMap R).hom
          (BialgHom.mapDomain (splitMaximalTorusCoordinateMap R).hom q)) =
      (weightTorusPoints A (fun i ↦ SplitTorus.pointsMulEquiv q (ULift.up i)) :
        Matrix.GeneralLinearGroup (Fin 24) A) := by
  rw [splitMaximalTorusCoordinateMap, CommHopfAlgCat.hom_comp, BialgHom.mapDomain_comp,
    MonoidHom.comp_apply]
  have hp := pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap R A
    (BialgHom.mapDomain (torusCoordinateIso R).hom.hom q)
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hp
  simp only [BialgHom.mapDomain_apply] at hp ⊢
  refine hp.trans ?_
  congr 2
  funext i
  ext
  rw [SplitTorus.pointsMulEquiv_apply_coe, SplitTorus.pointsMulEquiv_apply_coe,
    WithConv.ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, torusCoordinateIso_hom_single]
  congr 1
  rw [torusCharacterEquiv, AddEquiv.toMultiplicative_apply_apply,
    toAdd_ofAdd, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single,
    Equiv.ulift_symm_apply]

section Field

variable (k : Type u) [Field k]

private theorem isMaximalTorus_baseChange_weightTorusDefiningIdeal
    (K : Type u) [Field K] [Algebra k K] :
    HopfIdeal.IsMaximalTorus K
      (CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra k))
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (weightTorusDefiningIdeal k)) := by
  let e := generatedCoordinateHopfAlgebraBaseChangeIso k K
  let eft : FiniteTypeCommHopfAlgCat.of K
        (CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra k)) ≅
      generatedFiniteTypeCoordinateHopfAlgebra K := ObjectProperty.isoMk _ e
  have hmax := (isMaximalTorus_weightTorusDefiningIdeal K).comapOfIso eft
  have hmap := map_baseChangeHopfIdeal_weightTorusDefiningIdeal k K
  rw [← hmap] at hmax
  -- The finite-type isomorphism has the same bialgebra map as the underlying Hopf isomorphism.
  simpa only [eft, e, FiniteTypeCommHopfAlgCat.toBialgHom, ObjectProperty.isoMk_hom,
    ObjectProperty.homMk_hom, HopfIdeal.comapOfSurjective_map_of_bijective _ _
      (ConcreteCategory.bijective_of_isIso e.hom)] using hmax

/-- The rank-four weight torus, as a chosen split maximal torus of the generated tripled D₄
carrier over a field. Its maximality includes every geometric fiber. -/
def splitMaximalTorus : SplitMaximalTorus k (generatedCoordinateHopfAlgebra k) 4 where
  coordinateMap := splitMaximalTorusCoordinateMap k
  surjective := splitMaximalTorusCoordinateMap_surjective k
  maximal := by
    intro K _ _ _
    rw [ker_splitMaximalTorusCoordinateMap]
    exact isMaximalTorus_baseChange_weightTorusDefiningIdeal k K

/-- The chosen torus uses restriction to the weight torus in standard lifted coordinates. -/
@[simp]
theorem splitMaximalTorus_coordinateMap :
    (splitMaximalTorus k).coordinateMap = splitMaximalTorusCoordinateMap k :=
  (rfl)

/-- The chosen split maximal torus cuts out the existing closed weight torus. -/
@[simp]
theorem splitMaximalTorus_definingIdeal :
    (splitMaximalTorus k).definingIdeal = weightTorusDefiningIdeal k := by
  ext x
  rw [SplitMaximalTorus.mem_definingIdeal, splitMaximalTorus_coordinateMap,
    ← ker_splitMaximalTorusCoordinateMap, HopfIdeal.mem_kerOfSurjective]

end Field

end

end TauCeti.D4Tripled.Generated
