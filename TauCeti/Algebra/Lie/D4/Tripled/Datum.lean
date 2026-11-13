/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.MinusculeWeightTable
public import TauCeti.Algebra.Lie.D4.Tripled.AdmissibleLattice

/-!
# The tripled D₄ Chevalley datum

`TauCeti.D4Tripled.chevalleyDatum` equips the rational coordinate space of the natural and
both half-spin representations with an action of the pinned type-D₄ Lie algebra. Its
admissible lattice is the existing coordinate lattice, with the existing twenty-four weights
and their full weight lattice in fundamental-weight coordinates. In particular, no orthogonal
image or single eight-dimensional summand is substituted for the tripled representation.

The construction specializes `TauCeti.MinusculeWeightTable.chevalleyDatum` to the tripled
weight table and its weight-span theorem. The generic construction supplies the pinned action,
Cartan-detected faithfulness and square-zero Kostant lattice stability. These data allow
Chevalley-datum comparisons to be applied to the tripled model; no comparison of group schemes
or of their points is asserted here.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18, 27.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.D4Tripled

open DynkinType
open scoped _root_.Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem weightTable_pinnedCartanMatrix :
    weightTable.cartanMatrix = (DynkinType.D 4).cartanMatrixᵀ := by
  simpa only [cartanMatrix_D, rank_D, CartanMatrix.D_transpose] using weightTable_cartanMatrix

private theorem weightTable_span : Submodule.span ℤ (Set.range weightTable.weight) = ⊤ := by
  rw [weightTable_weight]
  exact span_range_d4TripledWeight_eq_top

private theorem datum_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.D 4).lieAlgebra (valid_D.mpr le_rfl)))
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).rootGenerator
      ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).h)
    (v : Fin 24 → ℚ) (hv : v ∈ lattice) :
    weightTable.pinnedRep (t := .D 4) (valid_D.mpr le_rfl)
      weightTable_pinnedCartanMatrix u v ∈ lattice := by
  rw [lattice_def] at hv ⊢
  exact weightTable.pinnedRep_mem_lattice (t := .D 4) (valid_D.mpr le_rfl)
    weightTable_pinnedCartanMatrix u hu v hv

private theorem datum_weight_basis (a : Fin 24) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector
      ((DynkinType.D 4).lieBasis (valid_D.mpr le_rfl)).h
      (weightTable.pinnedRep (t := .D 4) (valid_D.mpr le_rfl) weightTable_pinnedCartanMatrix)
      (fun i => d4TripledWeight a (Fin.cast (rank_D 4) i)) (latticeBasis a : Fin 24 → ℚ) := by
  rw [coe_latticeBasis]
  simpa only [weightTable_weight, rank_D, Fin.cast_eq_self] using
    weightTable.pinnedRep_weight (t := .D 4) (valid_D.mpr le_rfl) weightTable_pinnedCartanMatrix a

/-- The tripled natural and half-spin module as a full-weight Chevalley datum of type D₄.
Its character basis is the standard basis of fundamental weights. -/
-- Keep the existing lattice and numbering in the exposed dependent fields, rather than the
-- generic constructor's chosen finite enumeration. All representation proofs remain generic.
@[expose] def chevalleyDatum : ChevalleyDatum (.D 4) (by decide) where
  __ := weightTable.chevalleyDatum (t := .D 4) (by decide)
    (by exact weightTable_pinnedCartanMatrix) (by exact weightTable_span)
  carrier := Fin 24 → ℚ
  instAddCommGroup := inferInstance
  instModule := inferInstance
  lattice := lattice.toAddSubgroup
  representation_mem_lattice := by exact datum_mem_lattice
  span_lattice_eq_top := by
    rw [lattice_def]
    exact Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := 24
  basis := latticeBasis
  weight := fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i)
  isCartanWeightVector_basis := by exact datum_weight_basis
  weightLatticeBasis := (Pi.basisFun ℤ (Fin 4)).map
    (LinearEquiv.ofTop _ span_range_d4TripledWeight_eq_top).symm

/-- The tripled datum uses the pinned rational weight-table action. -/
@[simp] theorem chevalleyDatum_representation :
    chevalleyDatum.representation = weightTable.pinnedRep (t := .D 4) (by decide)
      (by simpa only [cartanMatrix_D, rank_D, CartanMatrix.D_transpose]
          using weightTable_cartanMatrix) := (rfl)

/-- A numbered Cartan generator acts by the tripled diagonal weight matrix. -/
@[simp↓] theorem chevalleyDatum_representation_h (i : Fin (DynkinType.D 4).rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.D 4).lieBasis (by decide)).h i)) =
      Matrix.toLin' (weightTable.cartanGeneratorMatrixQ (Fin.cast (rank_D 4) i)) := by
  rw [chevalleyDatum_representation]
  exact weightTable.pinnedRep_h (t := .D 4) (by decide) _ i

/-- A numbered raising generator acts by the tripled raising matrix. -/
@[simp↓] theorem chevalleyDatum_representation_e (i : Fin (DynkinType.D 4).rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.D 4).lieBasis (by decide)).e i)) =
      Matrix.toLin' (weightTable.raisingMatrixQ (Fin.cast (rank_D 4) i)) := by
  rw [chevalleyDatum_representation]
  exact weightTable.pinnedRep_e (t := .D 4) (by decide) _ i

/-- A numbered lowering generator acts by the tripled lowering matrix. -/
@[simp↓] theorem chevalleyDatum_representation_f (i : Fin (DynkinType.D 4).rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.D 4).lieBasis (by decide)).f i)) =
      Matrix.toLin' (weightTable.loweringMatrixQ (Fin.cast (rank_D 4) i)) := by
  rw [chevalleyDatum_representation]
  exact weightTable.pinnedRep_f (t := .D 4) (by decide) _ i

/-- The tripled datum uses the existing coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice : chevalleyDatum.lattice = lattice.toAddSubgroup := (rfl)

/-- The tripled datum uses the existing coordinate basis. -/
@[simp] theorem chevalleyDatum_basis : chevalleyDatum.basis = latticeBasis := (rfl)

/-- The tripled datum retains the numbered tripled weights. -/
@[simp] theorem chevalleyDatum_weight :
    chevalleyDatum.weight = fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i) := (rfl)

/-- The tripled datum has the full simply connected weight lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ := by
  rw [ChevalleyDatum.weightLattice_def, chevalleyDatum_weight]
  exact span_range_d4TripledWeight_eq_top

/-- The character basis is the standard fundamental-weight basis. -/
@[simp↓] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.D 4).rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin (DynkinType.D 4).rank → ℤ) = Pi.single i 1 := by
  -- Normalize the native rank before applying the basis map's evaluation equation.
  dsimp only [chevalleyDatum]
  have h := Module.Basis.map_apply (Pi.basisFun ℤ (Fin 4))
    (LinearEquiv.ofTop _ span_range_d4TripledWeight_eq_top).symm (Fin.cast (rank_D 4) i)
  refine (congrArg Subtype.val h).trans ?_
  simp only [LinearEquiv.ofTop_symm_apply, Pi.basisFun_apply]
  -- The remaining transport is only the reflexive equality of the native rank with four.
  rfl

/-- The torus coordinates of the tripled datum are its original fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    chevalleyDatum.coordinateWeight = fun a i => d4TripledWeight a (Fin.cast (rank_D 4) i) := by
  ext j i
  have h := congrFun (chevalleyDatum.sum_coordinateWeight_smul j) i
  simpa only [coe_chevalleyDatum_weightLatticeBasis, ← Pi.single_smul', smul_eq_mul,
    mul_one, Finset.univ_sum_single, chevalleyDatum_weight] using h

/-- The coordinate roots are the original roots in fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin (DynkinType.D 4).numRoots) :
    chevalleyDatum.coordinateRoot γ =
      ((DynkinType.D 4).simplyConnectedRootDatum (by decide)).root γ := by
  ext i
  have h := congrFun (chevalleyDatum.sum_coordinateRoot_smul γ) i
  simpa only [coe_chevalleyDatum_weightLatticeBasis, ← Pi.single_smul', smul_eq_mul,
    mul_one, Finset.univ_sum_single] using h

end

end TauCeti.D4Tripled
