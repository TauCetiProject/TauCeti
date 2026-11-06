/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.Lattice

/-!
# The full-weight Chevalley datum

For a valid Dynkin type, the direct sum of its fundamental highest-weight modules over `ℚ`,
with the direct sum of their admissible lattices, is a faithful representation with a numbered
integral weight basis. This file assembles these existing constructions into
`TauCeti.DynkinType.scChevalleyDatum`.

Its weight lattice is the entire lattice `Fin t.rank → ℤ`, not just the root lattice. The chosen
basis consists of the fundamental weights, so the coordinate weights used by the datum's torus
are exactly `TauCeti.DynkinType.scWeight`. Thus this datum supplies the full-weight input to
Chevalley's construction without a change of torus coordinates. In particular its torus is a
closed immersion, by `TauCeti.DynkinType.ChevalleyDatum.isClosedImmersion_torus`.

The representation, lattice, and weight basis are those constructed in
the full-weight lattice module imported above;
the assembly follows the Geck-datum construction in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Geck`. No identification of the resulting group scheme
with an independently constructed reductive group is asserted here.

## Main declarations

* `TauCeti.DynkinType.scChevalleyDatum`: the full-weight module as a Chevalley datum.
* `TauCeti.DynkinType.scChevalleyDatum_weightLattice`: its weights span the full weight lattice.
* `TauCeti.DynkinType.coe_scChevalleyDatum_weightLatticeBasis`: the lattice basis consists of
  the fundamental weights in their standard coordinates.
* `TauCeti.DynkinType.scChevalleyDatum_coordinateWeight`: the coordinate weights are `scWeight`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2, and Chapter 3, the remark after Lemma 27.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

open _root_.TauCeti.UniversalEnvelopingAlgebra

variable (t : DynkinType) (ht : t.Valid)

/-- The full-weight module, with its admissible lattice and weight basis, as a Chevalley datum.
The basis of its weight lattice is the standard basis of fundamental weights. -/
-- The carrier, dimension and lattice must compute so the dependent representation and basis
-- equations below can be stated in terms of the existing full-weight module and lattice.
@[expose] def scChevalleyDatum : ChevalleyDatum t ht where
  carrier := t.scModule ht
  representation := representation ℚ (t.lieAlgebra ht) (t.scModule ht)
  injective_representation_ι := by
    simpa only [representation_ι] using
      (LieModule.IsFaithful.injective_toEnd (R := ℚ) (L := t.lieAlgebra ht)
        (M := t.scModule ht))
  lattice := (t.scLattice ht).toAddSubgroup
  representation_mem_lattice := t.kostantForm_apply_mem_scLattice ht
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := t.scWeightBasisCard ht
  basis := t.scWeightBasis ht
  weight := t.scWeight ht
  isCartanWeightVector_basis := t.isCartanWeightVector_scWeightBasis ht
  weightLatticeBasis := (Pi.basisFun ℤ (Fin t.rank)).map
    (LinearEquiv.ofTop _ (t.span_range_scWeight_eq_top ht)).symm

/-- The dimension of the full-weight datum is the size of its existing weight basis. -/
@[simp]
theorem scChevalleyDatum_dim : (t.scChevalleyDatum ht).dim = t.scWeightBasisCard ht :=
  (rfl)

/-- The representation of the full-weight datum is the natural enveloping-algebra action. -/
@[simp]
theorem scChevalleyDatum_representation :
    (t.scChevalleyDatum ht).representation =
      representation ℚ (t.lieAlgebra ht) (t.scModule ht) :=
  (rfl)

/-- The lattice of the full-weight datum is the direct sum of the fundamental lattices. -/
@[simp]
theorem scChevalleyDatum_lattice :
    (t.scChevalleyDatum ht).lattice = (t.scLattice ht).toAddSubgroup :=
  (rfl)

/-- The weight basis of the full-weight datum is the existing numbered Kostant weight basis. -/
@[simp]
theorem scChevalleyDatum_basis : (t.scChevalleyDatum ht).basis = t.scWeightBasis ht :=
  (rfl)

/-- The weights of the full-weight datum are the existing fundamental-weight coordinate vectors. -/
@[simp]
theorem scChevalleyDatum_weight : (t.scChevalleyDatum ht).weight = t.scWeight ht :=
  (rfl)

/-- The weight lattice of the full-weight datum is the whole weight lattice. -/
@[simp]
theorem scChevalleyDatum_weightLattice : (t.scChevalleyDatum ht).weightLattice = ⊤ :=
  (t.scChevalleyDatum ht).weightLattice_def.trans (t.span_range_scWeight_eq_top ht)

/-- The chosen weight-lattice basis consists of the fundamental weights, in their standard
coordinates. -/
@[simp]
theorem coe_scChevalleyDatum_weightLatticeBasis (i : Fin t.rank) :
    ((t.scChevalleyDatum ht).weightLatticeBasis i : Fin t.rank → ℤ) = Pi.single i 1 := by
  rw [scChevalleyDatum, Module.Basis.map_apply]
  simp [Pi.basisFun_apply]

/-- The torus coordinates of the full-weight datum are the original fundamental-weight
coordinates: no lattice-index correction is needed. -/
@[simp]
theorem scChevalleyDatum_coordinateWeight :
    (t.scChevalleyDatum ht).coordinateWeight = t.scWeight ht := by
  ext j i
  have h := congrFun ((t.scChevalleyDatum ht).sum_coordinateWeight_smul j) i
  simpa [Pi.single_apply] using h

end

end TauCeti.DynkinType
