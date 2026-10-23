/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.Lie.E6.Minuscule.ClosedRootSubgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Tangent

/-!
# Normalized root differentials of the integral E₆ minuscule carrier

The twelve numbered root-subgroup differentials of the 27-dimensional minuscule carrier send
the additive unit tangent vector to the integral raising or lowering matrix. These normalized
vectors are nonzero over every nontrivial commutative coefficient ring, and the differential
identifies the additive tangent module with the line they span. Coefficient change preserves
the normalization, including over rings with nilpotents.

This ties the root parameters to the root vectors used in a pinning. It does not identify their
lines with entire adjoint weight spaces, prove maximality of the torus, or identify the carrier
with an independently pinned simply connected group scheme.

The interface follows the doubled carrier in
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.Root.Differential`. The matrix calculation uses the
Kostant root-subgroup tangent theorem and the minuscule table's integral basis action.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.E6Minuscule

noncomputable section

attribute [local instance high] Algebra.toModule

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)
local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)
local notation "e" => TauCeti.serreRootGenerator weightTable.cartanMatrix
local notation "h" => TauCeti.serreH ℚ weightTable.cartanMatrix
local notation "H" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal

private theorem toMatrix_kostantRootOperator (k : Fin 6 ⊕ Fin 6) :
    LinearMap.toMatrix 𝓑 𝓑
      (kostantRootOperator e h weightTable.rep (Λ).toAddSubgroup
        weightTable.rep_kostantForm_mem_lattice k) =
      Sum.elim raisingMatrix loweringMatrix k := by
  rw [← kostantRootGeneratorIntMatrix_eq_toMatrix e h weightTable.rep (Λ).toAddSubgroup
    weightTable.rep_kostantForm_mem_lattice k 𝓑]
  apply kostantRootGeneratorIntMatrix_eq_of_action
  intro s
  cases k with
  | inl i =>
    simpa only [Sum.elim_inl, raisingMatrix_apply, MinusculeWeightTable.raisingMatrix_apply,
      weightTable_weight, weightTable_reflection] using
      weightTable.rep_serreRootGenerator_inl_coordinateLatticeBasis_eq_sum i s
  | inr i =>
    simpa only [Sum.elim_inr, loweringMatrix_apply, MinusculeWeightTable.loweringMatrix_apply,
      weightTable_weight, weightTable_reflection] using
      weightTable.rep_serreRootGenerator_inr_coordinateLatticeBasis_eq_sum i s

variable {B : Type*} [CommRing B]

/-- A numbered root-subgroup differential has the integral raising or lowering matrix, scaled
by its additive tangent parameter, over every coefficient ring. -/
@[simp↓]
theorem tangentMatrix_derivationComp_rootSubgroup (k : Fin 6 ⊕ Fin 6)
    (d : Derivation ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)
      (Bialgebra.CounitAlgebra ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) B)) :
    GeneralLinear.tangentMatrix 27
        (HopfIdeal.quotientLieHom (B := B) definingIdeal
          (derivationComp (B := B) (rootSubgroupIntegralCoordinateMap k).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d •
        (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → B) := by
  have hcomp : (rootSubgroupIntegralCoordinateMap k).hom.comp
      (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal) =
      (kostantRootSubgroupCoordinateMap e h weightTable.rep (Λ).toAddSubgroup
        weightTable.rep_kostantForm_mem_lattice k
        (weightTable.isNilpotent_rep_serreRootGenerator k) 𝓑).hom := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      mkQuotient_comp_rootSubgroupIntegralCoordinateMap]
  rw [HopfIdeal.quotientLieHom_apply, ← LinearMap.comp_apply, ← derivationComp_comp, hcomp]
  rw [← toMatrix_kostantRootOperator]
  simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
    tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap
      e h weightTable.rep (Λ).toAddSubgroup weightTable.rep_kostantForm_mem_lattice k
      (weightTable.isNilpotent_rep_serreRootGenerator k) 𝓑 d

/-- A numbered root-subgroup differential is injective over every coefficient ring. -/
theorem derivationComp_rootSubgroup_injective (k : Fin 6 ⊕ Fin 6) :
    Function.Injective (derivationComp (B := B) (rootSubgroupIntegralCoordinateMap k).hom) :=
  derivationComp_injective_of_surjective _ (rootSubgroupIntegralCoordinateMap_surjective k)

/-- The normalized root vector is the image of the additive unit tangent vector. -/
def rootVector (k : Fin 6 ⊕ Fin 6) :
    Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B) :=
  derivationComp (B := B) (rootSubgroupIntegralCoordinateMap k).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := B)).symm 1)

/-- The matrix of a normalized root vector is its integral raising or lowering matrix. -/
@[simp]
theorem tangentMatrix_rootVector (k : Fin 6 ⊕ Fin 6) :
    GeneralLinear.tangentMatrix 27
        (HopfIdeal.quotientLieHom (B := B) definingIdeal (rootVector (B := B) k)) =
      (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → B) := by
  rw [rootVector, tangentMatrix_derivationComp_rootSubgroup,
    LinearEquiv.apply_symm_apply, one_smul]

/-- The differential with additive parameter `c` is `c` times the normalized root vector. -/
theorem derivationComp_rootSubgroup_eq_smul_rootVector (k : Fin 6 ⊕ Fin 6)
    (d : Derivation ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)
      (Bialgebra.CounitAlgebra ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) B)) :
    derivationComp (B := B) (rootSubgroupIntegralCoordinateMap k).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • rootVector (B := B) k :=
  AdditiveGroup.derivationComp_eq_smul _ d

/-- Coefficient change preserves the normalized root vector. -/
@[simp↓]
theorem mapValue_rootVector {C : Type*} [CommRing C] (φ : B →ₐ[ℤ] C)
    (k : Fin 6 ⊕ Fin 6) :
    Derivation.mapValue φ (rootVector (B := B) k) = rootVector (B := C) k :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one φ _

/-- Each root-subgroup differential has precisely the normalized root line as its image. -/
theorem range_derivationCompLieHom_rootSubgroup_eq_span (k : Fin 6 ⊕ Fin 6) :
    (derivationCompLieHom (B := B) (rootSubgroupIntegralCoordinateMap k).hom).range.toSubmodule =
      B ∙ rootVector (B := B) k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- A normalized root vector is nonzero over every nontrivial coefficient ring. -/
theorem rootVector_ne_zero [Nontrivial B] (k : Fin 6 ⊕ Fin 6) :
    rootVector (B := B) k ≠ 0 :=
  AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_rootSubgroup_injective (B := B) k)

end

end TauCeti.E6Minuscule
