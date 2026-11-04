/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.WeightSpan

/-!
# The Geck module as a Chevalley datum

Geck's construction realizes the pinned Lie algebra `TauCeti.DynkinType.lieAlgebra t ht` of a
valid Dynkin type as explicit matrices acting on the coordinate space `GeckIndex → ℚ`. Its integral
coordinate lattice is stable under the simple-generator Kostant form, and the standard coordinate
vectors are weight vectors whose weights are zero and the roots, as for the adjoint module. This
file packages these as a Chevalley datum, `TauCeti.DynkinType.geckChevalleyDatum`.

Its weight lattice is the root lattice, the span of the roots of
`TauCeti.DynkinType.simplyConnectedRootDatum`, and the chosen basis of it is the basis of simple
roots supplied by the Bourbaki-numbered base. The coordinate weights are therefore the coefficients
of the weights in the simple roots, and the torus of the datum is the split torus with the root
lattice as character lattice. By `TauCeti.DynkinType.ChevalleyDatum.isClosedImmersion_torus`, it is
a closed subgroup of the group scheme of the datum in every valid type, not only in the types `E₈`,
`F₄` and `G₂` in which the root lattice is the whole weight lattice.

## Main definitions

* `TauCeti.DynkinType.geckChevalleyDatum`: the Geck module, its coordinate lattice and coordinate
  basis, as a Chevalley datum.

## Main results

* `TauCeti.DynkinType.geckChevalleyDatum_weightLattice`: its weight lattice is the root lattice.
* `TauCeti.DynkinType.coe_geckChevalleyDatum_weightLatticeBasis`: the chosen basis of the weight
  lattice consists of the simple roots, in the Bourbaki numbering.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The Geck module as a Chevalley datum.** The representation is Geck's matrix representation
of the pinned Lie algebra, the lattice is the integral coordinate lattice with its standard basis,
whose weights are zero and the roots, and the chosen basis of the root lattice they span is the
basis of simple roots. -/
-- Exposed so that statements about this datum read its carrier, lattice and weight basis as the
-- Geck coordinate data: the lattice and basis are typed against the carrier.
@[expose] def geckChevalleyDatum : ChevalleyDatum t ht where
  carrier := t.GeckIndex ht → ℚ
  representation := t.geckRepresentation ht
  injective_representation_ι := t.geckRepresentation_ι_injective ht
  lattice := (t.geckCoordinateLattice ht).toAddSubgroup
  representation_mem_lattice := t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := t.geckDim ht
  basis := t.geckCoordinateBasisFin ht
  weight := t.geckWeightFin ht
  isCartanWeightVector_basis := t.isCartanWeightVector_geckCoordinateBasisFin ht
  weightLatticeBasis :=
    (((t.simplyConnectedBase ht).toWeightBasisInt).reindex
      (t.simpleSupportEquivSimplyConnectedBase ht).symm).map
      (LinearEquiv.ofEq _ _ (t.span_range_geckWeightFin_eq_rootSpan ht).symm)

/-- The rank of the Geck datum is the Geck dimension. -/
@[simp]
theorem geckChevalleyDatum_dim : (t.geckChevalleyDatum ht).dim = t.geckDim ht :=
  (rfl)

/-- The representation of the Geck datum is Geck's matrix representation. -/
@[simp]
theorem geckChevalleyDatum_representation :
    (t.geckChevalleyDatum ht).representation = t.geckRepresentation ht :=
  (rfl)

/-- The lattice of the Geck datum is the integral coordinate lattice. -/
@[simp]
theorem geckChevalleyDatum_lattice :
    (t.geckChevalleyDatum ht).lattice = (t.geckCoordinateLattice ht).toAddSubgroup :=
  (rfl)

/-- The weight basis of the Geck datum is the finite-ordinal coordinate basis. -/
@[simp]
theorem geckChevalleyDatum_basis :
    (t.geckChevalleyDatum ht).basis = t.geckCoordinateBasisFin ht :=
  (rfl)

/-- The weights of the Geck datum are the finite-ordinal Geck weights. -/
@[simp]
theorem geckChevalleyDatum_weight : (t.geckChevalleyDatum ht).weight = t.geckWeightFin ht :=
  (rfl)

/-- **The weight lattice of the Geck datum is the root lattice.** -/
@[simp]
theorem geckChevalleyDatum_weightLattice :
    (t.geckChevalleyDatum ht).weightLattice = (t.simplyConnectedRootDatum ht).rootSpan ℤ :=
  (t.geckChevalleyDatum ht).weightLattice_def.trans (t.span_range_geckWeightFin_eq_rootSpan ht)

/-- **The chosen basis of the weight lattice of the Geck datum consists of the simple roots**,
in the Bourbaki numbering. -/
@[simp]
theorem coe_geckChevalleyDatum_weightLatticeBasis (i : Fin t.rank) :
    ((t.geckChevalleyDatum ht).weightLatticeBasis i : Fin t.rank → ℤ) =
      (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) := by
  rw [geckChevalleyDatum, Module.Basis.map_apply]
  simp [RootPairing.Base.coe_toWeightBasisInt_apply]

end

end TauCeti.DynkinType
