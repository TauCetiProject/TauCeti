/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.BaseChange
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

/-!
# Closed root subgroups of the tripled type-D4 carrier

Each of the eight numbered root-subgroup maps into the tripled type-`D₄` carrier is a closed
immersion over `ℤ`. Its image is therefore a closed subgroup scheme canonically isomorphic to
the additive group scheme, as required for the root subgroups in a pinning.

For each simple root, a tripled weight has simple-coroot coordinate `-1`. The raising operator
sends its basis vector to the reflected basis vector with coefficient one, and the lowering
operator reverses this edge. The represented generators square to zero, so one matrix coordinate
of each root subgroup recovers its additive parameter. The generic Kostant root-step criterion
then gives surjectivity of the coordinate maps. This also proves surjectivity of the transported
root-subgroup coordinate maps over every commutative base ring.

## Main declarations

* `TauCeti.D4Tripled.rootSubgroupIntegralCoordinateMap_surjective`: surjectivity over `ℤ`.
* `TauCeti.D4Tripled.rootSubgroupToBaseChangeCoordinateMap_surjective`: surjectivity after
  arbitrary base change.
* `TauCeti.D4Tripled.isClosedImmersion_rootSubgroup`: every numbered root map is closed.
* `TauCeti.D4Tripled.rootSubgroupClosedSubgroupIso`: its closed image is the additive group.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 12.2.
* The root-step argument and closed-subgroup packaging follow
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.ClosedRootSubgroup`, using the generic minuscule
  representation API for the tripled weight table.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType TauCeti.UniversalEnvelopingAlgebra

noncomputable section

private theorem exists_root_step (k : Fin 4 ⊕ Fin 4) :
    ∃ r s : Fin 24,
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator weightTable.cartanMatrix k))
        ((latticeBasis s : lattice) : Fin 24 → ℚ) =
      (1 : ℤ) • ((latticeBasis r : lattice) : Fin 24 → ℚ) := by
  simp only [coe_latticeBasis, one_smul, rep_def, MinusculeWeightTable.rep_ι_apply]
  cases k with
  | inl i =>
      obtain ⟨a, ha⟩ := exists_d4TripledWeight_apply_eq_neg_one i
      refine ⟨weightTable.reflection i a, a, ?_⟩
      ext b
      simp [Pi.single_apply, ha]
  | inr i =>
      obtain ⟨a, ha⟩ : ∃ a, weightTable.weight a i = -1 :=
        by simpa only [weightTable_weight] using exists_d4TripledWeight_apply_eq_neg_one i
      refine ⟨a, weightTable.reflection i a, ?_⟩
      ext b
      -- Keep the table abstract so its reflection simp lemmas apply.
      simp [Pi.single_apply, ha, -weightTable_reflection, -weightTable_weight]

private theorem represented_rootSubgroupCoordinateMap_surjective (k : Fin 4 ⊕ Fin 4) :
    Function.Surjective
      (kostantRootSubgroupCoordinateMap
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis).hom := by
  obtain ⟨r, s, hstep⟩ := exists_root_step k
  refine kostantRootSubgroupCoordinateMap_surjective
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis
    isUnit_one hstep ?_
  have h := congrArg (fun f : Module.End ℚ (Fin 24 → ℚ) =>
    f ((latticeBasis s : lattice) : Fin 24 → ℚ))
    (weightTable.rep_serreRootGenerator_pow_two k)
  simpa only [rep_def, pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h

/-- Every numbered root-subgroup coordinate map of the tripled carrier is surjective over `ℤ`.
Thus the additive parameter is a regular function on its scheme-theoretic image. -/
theorem rootSubgroupIntegralCoordinateMap_surjective (k : Fin 4 ⊕ Fin 4) :
    Function.Surjective (rootSubgroupIntegralCoordinateMap k).hom := by
  have h := represented_rootSubgroupCoordinateMap_surjective k
  rw [← mkQuotient_comp_rootSubgroupIntegralCoordinateMap] at h
  exact Function.Surjective.of_comp h

/-- Every numbered root-subgroup map into the tripled type-`D₄` carrier is a closed immersion. -/
instance isClosedImmersion_rootSubgroup (k : Fin 4 ⊕ Fin 4) :
    IsClosedImmersion (rootSubgroup k).hom.hom.left := by
  rw [rootSubgroup_def]
  apply isClosedImmersion_kostantRootSubgroupToToral_of_surjective
  exact kostantRootSubgroupToralCoordinateMap_surjective_of_surjective
    _ _ _ _ _ _ _ _ k (represented_rootSubgroupCoordinateMap_surjective k)

/-- Every numbered root-subgroup map into the tripled type-`D₄` carrier is a monomorphism. -/
theorem mono_rootSubgroup (k : Fin 4 ⊕ Fin 4) : Mono (rootSubgroup k) :=
  mono_of_isClosedImmersion_underlying (rootSubgroup k)

/-- Surjectivity of the numbered root-subgroup coordinate maps persists over every commutative
base ring, in the transported quotient presentation of the carrier. -/
theorem rootSubgroupToBaseChangeCoordinateMap_surjective
    (A : Type*) [CommRing A] (k : Fin 4 ⊕ Fin 4) :
    Function.Surjective (rootSubgroupToBaseChangeCoordinateMap A k).hom := by
  rw [← baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap A k]
  exact (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A)).surjective.comp
    ((CommHopfAlgCat.baseChangeMap_surjective (K := A)
      (rootSubgroupIntegralCoordinateMap k)
      (rootSubgroupIntegralCoordinateMap_surjective k)).comp
      (ConcreteCategory.bijective_of_isIso (baseChangeCoordinateIso A).hom).2)

/-- A numbered root subgroup as a closed subgroup scheme of the tripled type-`D₄` carrier. -/
def rootSubgroupClosedSubgroup (k : Fin 4 ⊕ Fin 4) : ClosedSubgroupScheme groupScheme :=
  ClosedSubgroupScheme.mk (rootSubgroup k)

/-- The closed subgroup is represented by the numbered root-subgroup morphism. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (k : Fin 4 ⊕ Fin 4) :
    (rootSubgroupClosedSubgroup k).1 =
      letI := mono_rootSubgroup k
      Subobject.mk (rootSubgroup k) :=
  ClosedSubgroupScheme.coe_mk _

/-- Each closed root subgroup is canonically isomorphic to the additive group scheme over `ℤ`. -/
def rootSubgroupClosedSubgroupIso (k : Fin 4 ⊕ Fin 4) :
    ((rootSubgroupClosedSubgroup k).1 : Grp (Over (Spec (CommRingCat.of ℤ)))) ≅
      AdditiveGroup.groupScheme ℤ :=
  ClosedSubgroupScheme.mkIso (rootSubgroup k)

/-- The parametrization of the closed image followed by its inclusion recovers the root map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (k : Fin 4 ⊕ Fin 4) :
    (rootSubgroupClosedSubgroupIso k).inv ≫ (rootSubgroupClosedSubgroup k).1.arrow =
      rootSubgroup k :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow (rootSubgroup k)

end

end TauCeti.D4Tripled
