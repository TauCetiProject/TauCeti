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

/-- The tripled natural and half-spin module as a full-weight Chevalley datum of type D₄.
Its character basis is the standard basis of fundamental weights. -/
-- Expose the inherited carrier and dimension for dependent coordinate-space equations.
@[expose] def chevalleyDatum : ChevalleyDatum (.D 4) (by decide) :=
  weightTable.chevalleyDatum (t := .D 4) (by decide)
    (by exact weightTable_pinnedCartanMatrix) (by exact weightTable_span)

/-- The tripled datum uses the pinned rational weight-table action. -/
@[simp] theorem chevalleyDatum_representation :
    chevalleyDatum.representation = weightTable.pinnedRepresentation (t := .D 4) (by decide)
      (by simpa only [cartanMatrix_D, rank_D, CartanMatrix.D_transpose]
          using weightTable_cartanMatrix) := (rfl)

-- Pre-simplify these equations before rewriting the dependent representation projection.
/-- A numbered Cartan generator acts by the tripled diagonal weight matrix. -/
@[simp↓] theorem chevalleyDatum_representation_h (i : Fin (DynkinType.D 4).rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.D 4).lieBasis (by decide)).h i)) =
      Matrix.toLin' (weightTable.cartanGeneratorMatrixQ i) := by
  rw [chevalleyDatum_representation]
  apply LinearMap.ext
  intro v
  exact (weightTable.pinnedRepresentation_ι_lieBasis_h_apply (t := .D 4) (by decide) _ i v).trans
    (Matrix.toLin'_apply _ _).symm

/-- A numbered raising generator acts by the tripled raising matrix. -/
@[simp↓] theorem chevalleyDatum_representation_e (i : Fin (DynkinType.D 4).rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.D 4).lieBasis (by decide)).e i)) =
      Matrix.toLin' (weightTable.raisingMatrixQ i) := by
  rw [chevalleyDatum_representation]
  apply LinearMap.ext
  intro v
  exact (weightTable.pinnedRepresentation_ι_lieBasis_e_apply (t := .D 4) (by decide) _ i v).trans
    (Matrix.toLin'_apply _ _).symm

/-- A numbered lowering generator acts by the tripled lowering matrix. -/
@[simp↓] theorem chevalleyDatum_representation_f (i : Fin (DynkinType.D 4).rank) :
    chevalleyDatum.representation
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.D 4).lieBasis (by decide)).f i)) =
      Matrix.toLin' (weightTable.loweringMatrixQ i) := by
  rw [chevalleyDatum_representation]
  apply LinearMap.ext
  intro v
  exact (weightTable.pinnedRepresentation_ι_lieBasis_f_apply (t := .D 4) (by decide) _ i v).trans
    (Matrix.toLin'_apply _ _).symm

/-- The tripled datum uses the existing coordinate lattice. -/
@[simp] theorem chevalleyDatum_lattice : chevalleyDatum.lattice = lattice.toAddSubgroup :=
  congrArg Submodule.toAddSubgroup lattice_def.symm

/-- The datum basis agrees with the tripled lattice basis in the rational carrier. -/
@[simp↓] theorem coe_chevalleyDatum_basis (i : Fin 24) :
    (chevalleyDatum.basis i).val = (latticeBasis i : Fin 24 → ℚ) := by
  calc
    _ = ((coordinateLatticeBasis (Fin 24)) i).val :=
      congrArg (fun b => (b i).val) (weightTable.chevalleyDatum_basis (t := .D 4) (by decide)
        weightTable_pinnedCartanMatrix weightTable_span)
    _ = Pi.single i 1 := by rw [coe_coordinateLatticeBasis, Pi.basisFun_apply]
    _ = _ := (coe_latticeBasis i).symm

/-- The tripled datum retains the numbered tripled weights. -/
@[simp] theorem chevalleyDatum_weight :
    chevalleyDatum.weight = d4TripledWeight := by
  exact (weightTable.chevalleyDatum_weight (t := .D 4) (by decide)
    weightTable_pinnedCartanMatrix weightTable_span).trans weightTable_weight

/-- The tripled datum has the full simply connected weight lattice. -/
@[simp] theorem chevalleyDatum_weightLattice : chevalleyDatum.weightLattice = ⊤ := by
  exact weightTable.chevalleyDatum_weightLattice (t := .D 4) (by decide)
    weightTable_pinnedCartanMatrix weightTable_span

/-- The character basis is the standard fundamental-weight basis. -/
@[simp↓] theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.D 4).rank) :
    (chevalleyDatum.weightLatticeBasis i : Fin (DynkinType.D 4).rank → ℤ) = Pi.single i 1 := by
  exact weightTable.coe_chevalleyDatum_weightLatticeBasis (t := .D 4) (by decide)
    weightTable_pinnedCartanMatrix weightTable_span i

/-- The torus coordinates of the tripled datum are its original fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateWeight :
    chevalleyDatum.coordinateWeight = d4TripledWeight := by
  exact (weightTable.chevalleyDatum_coordinateWeight (t := .D 4) (by decide)
    weightTable_pinnedCartanMatrix weightTable_span).trans weightTable_weight

/-- The coordinate roots are the original roots in fundamental-weight coordinates. -/
@[simp] theorem chevalleyDatum_coordinateRoot (γ : Fin (DynkinType.D 4).numRoots) :
    chevalleyDatum.coordinateRoot γ =
      ((DynkinType.D 4).simplyConnectedRootDatum (by decide)).root γ := by
  exact congrFun (weightTable.chevalleyDatum_coordinateRoot (t := .D 4) (by decide)
    weightTable_pinnedCartanMatrix weightTable_span) γ

end

end TauCeti.D4Tripled
