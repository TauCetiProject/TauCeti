/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Generated.Basic

/-!
# The standard comodule of the generated Geck subgroup

For a valid Dynkin type `t`, the closed subgroup of `GLₙ` generated over a commutative ring `R` by
the `2 · rank` numbered Geck root subgroups and the Geck weight torus acts on `Rⁿ`, with
`n = t.geckDim`. This is its standard comodule, the corestriction of the standard
`O(GLₙ)`-comodule along the quotient coordinate map. It is the Geck module, the adjoint
representation in Geck's construction, read in its integral coordinate basis.

This file records the type-independent facts about it that an argument eliminating normal
unipotent subgroups starts from: the comodule is faithful over every commutative ring; its
subcomodules are stable under the numbered root-subgroup matrices, with any parameter; and its
restriction to the weight torus is the sum of the coordinate lines with the Geck weights
`TauCeti.DynkinType.geckWeightFin`.

Unlike the minuscule and spin carriers, the Geck weights are not all distinct: the zero weight
occurs with multiplicity `t.rank`, once for each coordinate indexed by a simple root. So the weight
decomposition alone does not split a subcomodule into coordinate lines, and simplicity of the
comodule, where it holds, depends on the type and on the characteristic of the field. None is
asserted here, nor is the generated subgroup identified with the base change of the integral Geck
carrier.

## Main declarations

* `TauCeti.DynkinType.geckGeneratedWeightTorusCoordinateMap`: the weight torus factored through
  the generated subgroup.
* `TauCeti.DynkinType.geckGeneratedStandardComodule`: the standard comodule on `Rⁿ`.

## Main results

* `TauCeti.DynkinType.isFaithful_geckGeneratedStandardComodule`: faithfulness over every
  commutative ring.
* `TauCeti.DynkinType.geckRootSubgroupPoints_mulVec_mem_geckGeneratedSubcomodule`: subcomodules
  are stable under the numbered root-subgroup matrices.
* `TauCeti.DynkinType.geckGeneratedTorusCorestrict_eq_ofWeights`: the weight decomposition under
  the weight torus.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.

The construction follows the generated type-`E₇` minuscule subgroup in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix

namespace TauCeti.DynkinType

universe u v

variable (t : DynkinType) (ht : t.Valid) (R : Type u) [CommRing R]

/-- The Geck weight torus factored through the subgroup generated over `R`. -/
noncomputable def geckGeneratedWeightTorusCoordinateMap :
    t.geckGeneratedCoordinateHopfAlgebra ht R ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin t.rank))).obj :=
  t.geckGeneratedCoordinateLift ht R (.inr ())

/-- The generated subgroup's weight torus recovers the ambient Geck weight torus. -/
@[reassoc (attr := simp)]
theorem geckGeneratedCoordinateMap_comp_geckGeneratedWeightTorusCoordinateMap :
    t.geckGeneratedCoordinateMap ht R ≫ t.geckGeneratedWeightTorusCoordinateMap ht R =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ R (t.geckWeightFin ht) := by
  rw [geckGeneratedWeightTorusCoordinateMap,
    geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateLift, geckGeneratorCoordinateMap_inr,
    geckWeightTorusBaseChangeCoordinateMap_def]

/-- A point induced by a generated root-subgroup lift maps to the numbered Geck root-subgroup
matrix with the same parameter, over every value algebra. -/
-- Avoid indexing the lift's dependent codomain; rewrite before `mapDomain_apply` unfolds.
@[simp↓]
theorem pointToGeneralLinear_mapDomain_geckGeneratedCoordinateLift_inl
    (i : Fin t.rank ⊕ Fin t.rank) (B : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) B) :
    GeneralLinear.pointToGeneralLinear (t.geckDim ht)
        (AlgHom.mapDomain (t.geckGeneratedCoordinateMap ht R).hom
          (no_index (toConv
            (q.ofConv.comp (t.geckGeneratedCoordinateLift ht R (.inl i)).hom.toAlgHom)))) =
      (t.geckRootSubgroupPoints ht i B (AdditiveGroup.gaPointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) B) := by
  -- Both composites are the transported root-subgroup map out of `O(GLₙ)`.
  have hcomp : t.geckGeneratedCoordinateMap ht R ≫ t.geckGeneratedCoordinateLift ht R (.inl i) =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht R) ≫
        t.geckRootSubgroupToBaseChangeCoordinateMap ht R i := by
    rw [geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateLift,
      geckGeneratorCoordinateMap_inl, mkQuotient_comp_geckRootSubgroupToBaseChangeCoordinateMap]
  have hpoint : AlgHom.mapDomain (t.geckGeneratedCoordinateMap ht R).hom
      (toConv (q.ofConv.comp (t.geckGeneratedCoordinateLift ht R (.inl i)).hom.toAlgHom)) =
      AlgHom.mapDomain
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht R)).hom
        (toConv
          (q.ofConv.comp (t.geckRootSubgroupToBaseChangeCoordinateMap ht R i).hom.toAlgHom)) := by
    apply WithConv.ext
    ext x
    exact congrArg (fun f ↦ q.ofConv (f.hom x)) hcomp
  rw [hpoint, pointToGeneralLinear_mapDomain_geckRootSubgroupToBaseChangeCoordinateMap]

/-- The standard right comodule of the generated Geck subgroup on `Rⁿ`. -/
@[instance_reducible]
noncomputable def geckGeneratedStandardComodule :
    Comodule R (t.geckGeneratedCoordinateHopfAlgebra ht R) (Fin (t.geckDim ht) → R) :=
  GeneralLinear.corestrictStandardComodule R (t.geckDim ht) (t.geckGeneratedCoordinateMap ht R).hom

attribute [local instance] geckGeneratedStandardComodule

/-- **The standard comodule of the generated Geck subgroup is faithful over every commutative
ring.** -/
theorem isFaithful_geckGeneratedStandardComodule :
    Comodule.IsFaithful (k := R) (H := t.geckGeneratedCoordinateHopfAlgebra ht R)
      (V := Fin (t.geckDim ht) → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R (t.geckDim ht)
    (t.geckGeneratedCoordinateMap ht R).hom (t.geckGeneratedCoordinateMap_surjective ht R)

/-- A subcomodule of the generated Geck subgroup's standard comodule is stable under each numbered
positive and negative root-subgroup matrix, with any parameter. -/
theorem geckRootSubgroupPoints_mulVec_mem_geckGeneratedSubcomodule
    (N : Subcomodule R (t.geckGeneratedCoordinateHopfAlgebra ht R) (Fin (t.geckDim ht) → R))
    (i : Fin t.rank ⊕ Fin t.rank) (s : Multiplicative R) {w : Fin (t.geckDim ht) → R}
    (hw : w ∈ N) :
    ((t.geckRootSubgroupPoints ht i R s : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) R) :
      Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) R) *ᵥ w ∈ N := by
  let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := R)).symm s
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R (t.geckDim ht)
    (t.geckGeneratedCoordinateMap ht R).hom N
    (toConv (q.ofConv.comp (t.geckGeneratedCoordinateLift ht R (.inl i)).hom.toAlgHom)) hw
  rw [pointToGeneralLinear_mapDomain_geckGeneratedCoordinateLift_inl t ht R i
    (CommAlgCat.of R R) q, MulEquiv.apply_symm_apply] at h
  exact h

/-- **Restricting the generated Geck subgroup's standard comodule to the weight torus gives the
direct sum of the coordinate lines, with the Geck weights.** The zero weight occurs on each
coordinate indexed by a simple root. -/
theorem geckGeneratedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (t.geckGeneratedWeightTorusCoordinateMap ht R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (t.geckDim ht)))
        (fun a ↦ SplitTorus.weightCharacter (t.geckWeightFin ht a)) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (t.geckGeneratedCoordinateMap ht R).hom (t.geckGeneratedWeightTorusCoordinateMap ht R).hom
    (t.geckWeightFin ht)
  rw [← _root_.CommHopfAlgCat.hom_comp,
    geckGeneratedCoordinateMap_comp_geckGeneratedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

end TauCeti.DynkinType
