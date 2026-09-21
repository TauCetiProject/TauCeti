/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.RootInToral

/-!
# Closed root subgroups of the type-E6 minuscule carrier

The twelve numbered raising and lowering maps into `TauCeti.E6Minuscule.groupScheme` are closed
copies of the additive group scheme. For every Bourbaki node, one explicit edge in the minuscule
weight graph recovers the root-subgroup parameter as a matrix coordinate. The raising operator
carries the basis vector at the negative end of this edge to the basis vector at its positive end
with coefficient one; the lowering operator traverses the same edge in reverse.

The generic Kostant root-subgroup construction turns this unit-coefficient basis step into a
surjective map from the carrier's coordinate Hopf algebra to the coordinate algebra of `𝔾ₐ`.
Consequently each numbered root-subgroup morphism is a closed immersion. Its scheme-theoretic
image is bundled below as a closed subgroup canonically isomorphic to `𝔾ₐ`.

This supplies the closed-root-subgroup component of a pinning for the explicit full-weight
type-`E₆` carrier in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. That carrier is consumed
by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`. No reductivity, Borel, finiteness, or
simplicity statement is made here.

## Main declarations

* `TauCeti.E6Minuscule.rootSubgroupCoordinateMap_surjective`: every numbered root-subgroup
  coordinate map is surjective.
* `TauCeti.E6Minuscule.isClosedImmersion_rootSubgroup`: every numbered root-subgroup morphism is a
  closed immersion.
* `TauCeti.E6Minuscule.rootSubgroupClosedSubgroup`: its image as a closed subgroup scheme.
* `TauCeti.E6Minuscule.rootSubgroupClosedSubgroupIso`: the canonical isomorphism of that image with
  the additive group scheme.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.2.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.E6Minuscule

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)
local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)

noncomputable section

/-! ## A unit-coefficient edge at every simple root -/

/-- A weight whose pairing with the given simple coroot is `-1`. The choice is internal to the
coordinate proof; no public construction depends on which suitable weight is selected. -/
private noncomputable def negativeWeightIndex (i : Fin 6) : Fin 27 :=
  (DynkinType.exists_e6MinusculeWeight_apply_eq_neg_one i).choose

private theorem e6MinusculeWeight_negativeWeightIndex (i : Fin 6) :
    weightTable.weight (negativeWeightIndex i) i = -1 :=
  by
    rw [weightTable_weight]
    exact (DynkinType.exists_e6MinusculeWeight_apply_eq_neg_one i).choose_spec

/-- The source coordinate of the selected edge for a raising or lowering root generator. -/
private def rootSource : Fin 6 ⊕ Fin 6 → Fin 27
  | .inl i => negativeWeightIndex i
  | .inr i => DynkinType.e6MinusculeReflection i (negativeWeightIndex i)

/-- The target coordinate of the selected edge for a raising or lowering root generator. -/
private def rootTarget : Fin 6 ⊕ Fin 6 → Fin 27
  | .inl i => DynkinType.e6MinusculeReflection i (negativeWeightIndex i)
  | .inr i => negativeWeightIndex i

private theorem rep_serreRootGenerator_latticeBasis (k : Fin 6 ⊕ Fin 6) :
    weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator weightTable.cartanMatrix k))
        ((𝓑 (rootSource k) : Λ) : Fin 27 → ℚ) =
      (1 : ℤ) • ((𝓑 (rootTarget k) : Λ) : Fin 27 → ℚ) := by
  cases k with
  | inl i =>
      have hi := e6MinusculeWeight_negativeWeightIndex i
      rw [weightTable_weight] at hi
      rw [TauCeti.serreRootGenerator_inl, weightTable.rep_ι_apply,
        weightTable.rationalSerreRepresentation_serreE,
        TauCeti.coe_coordinateLatticeBasis, Pi.basisFun_apply,
        Matrix.mulVec_single_one, one_smul]
      ext a
      simp [rootSource, rootTarget, Pi.single_apply, hi]
  | inr i =>
      have hi := e6MinusculeWeight_negativeWeightIndex i
      rw [weightTable_weight] at hi
      rw [TauCeti.serreRootGenerator_inr, weightTable.rep_ι_apply,
        weightTable.rationalSerreRepresentation_serreF,
        TauCeti.coe_coordinateLatticeBasis, Pi.basisFun_apply,
        Matrix.mulVec_single_one, one_smul]
      ext a
      simp [rootSource, rootTarget, weightTable_weight, Pi.single_apply, hi]

private theorem rep_serreRootGenerator_pow_two_apply_latticeBasis (k : Fin 6 ⊕ Fin 6) :
    weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix k))
      (weightTable.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (TauCeti.serreRootGenerator weightTable.cartanMatrix k))
        ((𝓑 (rootSource k) : Λ) : Fin 27 → ℚ)) = 0 := by
  have h := congrArg
    (fun f : Module.End ℚ (Fin 27 → ℚ) =>
      f ((𝓑 (rootSource k) : Λ) : Fin 27 → ℚ))
    (weightTable.rep_serreRootGenerator_pow_two k)
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h

/-! ## Closed root-subgroup morphisms -/

/-- **The coordinate morphism of every numbered type-`E₆` minuscule root subgroup is
surjective.** The selected minuscule-weight edge has coefficient one, so one matrix coordinate
recovers the additive parameter. -/
theorem rootSubgroupCoordinateMap_surjective (k : Fin 6 ⊕ Fin 6) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv => weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight k).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv => weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    k weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight
    isUnit_one (rep_serreRootGenerator_latticeBasis k)
    (rep_serreRootGenerator_pow_two_apply_latticeBasis k)

/-- **Every numbered root-subgroup map into the type-`E₆` minuscule carrier is a closed
immersion.** Thus its scheme-theoretic image is a closed copy of `𝔾ₐ`, as required of the root
subgroups in a pinning. -/
instance isClosedImmersion_rootSubgroup (k : Fin 6 ⊕ Fin 6) :
    IsClosedImmersion (rootSubgroup k).hom.hom.left := by
  rw [rootSubgroup_def]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv => weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    k weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight
    isUnit_one (rep_serreRootGenerator_latticeBasis k)
    (rep_serreRootGenerator_pow_two_apply_latticeBasis k)

/-- Every numbered root-subgroup map into the type-`E₆` minuscule carrier is a monomorphism. -/
theorem mono_rootSubgroup (k : Fin 6 ⊕ Fin 6) : Mono (rootSubgroup k) :=
  mono_of_isClosedImmersion_underlying (rootSubgroup k)

/-- **A numbered type-`E₆` minuscule root subgroup as a closed subgroup scheme of the carrier.** -/
noncomputable def rootSubgroupClosedSubgroup (k : Fin 6 ⊕ Fin 6) :
    ClosedSubgroupScheme groupScheme :=
  ClosedSubgroupScheme.mk (rootSubgroup k)

/-- The bundled closed root subgroup is represented by the numbered root-subgroup morphism. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (k : Fin 6 ⊕ Fin 6) :
    (rootSubgroupClosedSubgroup k).1 =
      letI := mono_rootSubgroup k
      Subobject.mk (rootSubgroup k) := by
  exact ClosedSubgroupScheme.coe_mk _

/-- The bundled numbered root subgroup is canonically isomorphic to the additive group scheme. -/
noncomputable def rootSubgroupClosedSubgroupIso (k : Fin 6 ⊕ Fin 6) :
    ((rootSubgroupClosedSubgroup k).1 :
      Grp (Over (Spec (CommRingCat.of ℤ)))) ≅ AdditiveGroup.groupScheme ℤ :=
  ClosedSubgroupScheme.mkIso (rootSubgroup k)

/-- The canonical parametrization of the bundled closed subgroup followed by its inclusion is the
numbered type-`E₆` root-subgroup map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (k : Fin 6 ⊕ Fin 6) :
    (rootSubgroupClosedSubgroupIso k).inv ≫ (rootSubgroupClosedSubgroup k).1.arrow =
      rootSubgroup k :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow (rootSubgroup k)

end

end TauCeti.E6Minuscule
