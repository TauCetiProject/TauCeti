/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.Lattice

/-!
# The simply connected Chevalley group scheme

For a valid Dynkin type `t`, the full-weight module `V_sc(t) = ⨁ᵢ L(ϖᵢ)`, the direct sum of the
fundamental modules of the pinned Lie algebra, carries the admissible lattice `⨁ᵢ U_ℤ · v⁺ᵢ` with
a weight basis whose weights span the whole weight lattice `Fin t.rank → ℤ`. This file packages
these as a Chevalley datum, `TauCeti.DynkinType.scChevalleyDatum`, and names its group scheme
over `ℤ`, the **simply connected Chevalley group scheme** `G_sc(t)`, together with its points over
a commutative ring and its split maximal torus.

Since the weights span `Fin t.rank → ℤ`, the weight lattice `Λ` of the datum is everything, and
the chosen basis of it is the standard one. The coordinate weights of the datum are therefore the
weights themselves (`TauCeti.DynkinType.scChevalleyDatum_coordinateWeight`): for `G_sc(t)` the
torus with character lattice `Λ` and the torus parametrized by the full weight lattice are the
same, so the group scheme is the Kostant toral closure of the full-weight lattice with its weights
read in fundamental-weight coordinates
(`TauCeti.DynkinType.chevalleyGroupScheme_eq_kostantToralGroupScheme`), and its points are the
corresponding points of that closure
(`TauCeti.DynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup`). In particular every diagonal
matrix of a torus parameter `s : Fin t.rank → Aˣ`, acting on each weight vector through its weight
in fundamental-weight coordinates, is a point of `G_sc(t)`.

## Main definitions

* `TauCeti.DynkinType.scChevalleyDatum`: the full-weight module, its lattice and weight basis, as a
  Chevalley datum.
* `TauCeti.DynkinType.chevalleyGroupScheme`: the simply connected Chevalley group scheme
  `G_sc(t)` over `ℤ`.
* `TauCeti.DynkinType.chevalleyGroup`: its points with values in a commutative ring, as a
  subgroup of `GLₙ`.
* `TauCeti.DynkinType.chevalleyTorus`: its split maximal torus, with character lattice the full
  weight lattice.

## Main results

* `TauCeti.DynkinType.scChevalleyDatum_weightLattice`: the weight lattice of the datum is the
  whole weight lattice `Fin t.rank → ℤ`.
* `TauCeti.DynkinType.scChevalleyDatum_coordinateWeight`: its coordinate weights are its weights.
* `TauCeti.DynkinType.chevalleyGroupScheme_eq_kostantToralGroupScheme`: `G_sc(t)` is the Kostant
  toral closure of the full-weight lattice.
* `TauCeti.DynkinType.chevalleyTorus_comp_groupSchemeι` and
  `TauCeti.DynkinType.isClosedImmersion_chevalleyTorus`: the torus is the weight torus of the
  full-weight lattice, and a closed subgroup of `G_sc(t)`.
* `TauCeti.DynkinType.kostantTorusMatrix_mem_chevalleyGroup`: every torus matrix of the full-weight
  lattice is a point of `G_sc(t)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, the remark after Lemma 27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

noncomputable section

universe v

variable (t : DynkinType) (ht : t.Valid)

/-! ## The full-weight Chevalley datum -/

/-- **The full-weight module as a Chevalley datum.** The representation is that of the pinned Lie
algebra on the direct sum `⨁ᵢ L(ϖᵢ)` of its fundamental modules, which is faithful; the lattice is
the direct sum `⨁ᵢ U_ℤ · v⁺ᵢ` of the fundamental lattices with its numbered Kostant weight basis;
and since the weights of that basis span `Fin t.rank → ℤ`, the chosen basis of the lattice they
span is the standard basis. -/
-- Exposed so that statements about this datum read its carrier, lattice and weight basis as the
-- full-weight data: the lattice and basis are typed against the carrier.
@[expose] def scChevalleyDatum : ChevalleyDatum t ht where
  carrier := t.scModule ht
  representation := representation ℚ (t.lieAlgebra ht) (t.scModule ht)
  injective_representation_ι := by
    simpa only [representation_ι] using
      (LieModule.IsFaithful.injective_toEnd :
        Function.Injective (LieModule.toEnd ℚ (t.lieAlgebra ht) (t.scModule ht)))
  lattice := (t.scLattice ht).toAddSubgroup
  representation_mem_lattice := t.kostantForm_apply_mem_scLattice ht
  span_lattice_eq_top := Submodule.IsLattice.span_eq_top (R := ℤ) (A := ℚ)
  dim := t.scWeightBasisCard ht
  basis := t.scWeightBasis ht
  weight := t.scWeight ht
  isCartanWeightVector_basis := t.isCartanWeightVector_scWeightBasis ht
  weightLatticeBasis :=
    (Pi.basisFun ℤ (Fin t.rank)).map
      (LinearEquiv.ofTop _ (t.span_range_scWeight_eq_top ht)).symm

/-- The representation of the full-weight datum is that of the pinned Lie algebra on the
full-weight module. -/
@[simp]
theorem scChevalleyDatum_representation :
    (t.scChevalleyDatum ht).representation =
      representation ℚ (t.lieAlgebra ht) (t.scModule ht) :=
  (rfl)

/-- The lattice of the full-weight datum is the full-weight lattice. -/
@[simp]
theorem scChevalleyDatum_lattice :
    (t.scChevalleyDatum ht).lattice = (t.scLattice ht).toAddSubgroup :=
  (rfl)

/-- The rank of the full-weight datum is the number of vectors of the weight basis of the
full-weight lattice. -/
@[simp]
theorem scChevalleyDatum_dim : (t.scChevalleyDatum ht).dim = t.scWeightBasisCard ht :=
  (rfl)

/-- The weight basis of the full-weight datum is the numbered Kostant weight basis of the
full-weight lattice. -/
@[simp]
theorem scChevalleyDatum_basis : (t.scChevalleyDatum ht).basis = t.scWeightBasis ht :=
  (rfl)

/-- The weights of the full-weight datum are the weights of the full-weight lattice, in
fundamental-weight coordinates. -/
@[simp]
theorem scChevalleyDatum_weight : (t.scChevalleyDatum ht).weight = t.scWeight ht :=
  (rfl)

/-- **The weight lattice of the full-weight datum is the whole weight lattice** `Fin t.rank → ℤ`:
every fundamental weight is a weight of the full-weight lattice. -/
@[simp]
theorem scChevalleyDatum_weightLattice : (t.scChevalleyDatum ht).weightLattice = ⊤ :=
  (t.scChevalleyDatum ht).weightLattice_def.trans (t.span_range_scWeight_eq_top ht)

/-- **The chosen basis of the weight lattice of the full-weight datum is the standard basis** of
`Fin t.rank → ℤ`, that is, the basis of fundamental weights. -/
@[simp]
theorem coe_scChevalleyDatum_weightLatticeBasis (i : Fin t.rank) :
    ((t.scChevalleyDatum ht).weightLatticeBasis i : Fin t.rank → ℤ) = Pi.single i 1 := by
  rw [scChevalleyDatum, Module.Basis.map_apply, LinearEquiv.coe_ofTop_symm_apply,
    Pi.basisFun_apply]

/-- **The coordinate weights of the full-weight datum are its weights.** The chosen basis of its
weight lattice is the standard basis, so writing a weight in that basis does not change it. Hence
the torus of the datum, whose character lattice is its weight lattice, is the torus parametrized
by the full weight lattice. -/
@[simp]
theorem scChevalleyDatum_coordinateWeight :
    (t.scChevalleyDatum ht).coordinateWeight = t.scWeight ht := by
  funext j i
  have h := (t.scChevalleyDatum ht).sum_coordinateWeight_smul j
  simp only [coe_scChevalleyDatum_weightLatticeBasis, scChevalleyDatum_weight] at h
  simp [← h, Finset.sum_apply, Pi.single_apply]

/-! ## The simply connected Chevalley group scheme -/

/-- **The simply connected Chevalley group scheme** `G_sc(t)` over `ℤ`: the group scheme of the
full-weight Chevalley datum, the smallest closed subgroup scheme of `GLₙ` containing the
divided-power exponential root subgroups of the numbered Chevalley generators on the full-weight
lattice and the split torus acting on its weight basis through the weights.

This is an abbreviation, like the group scheme of a Chevalley datum it specializes, so that the
inclusion into `GLₙ`, the torus and the points of that construction apply to it without
transport. -/
abbrev chevalleyGroupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  (t.scChevalleyDatum ht).groupScheme

/-- `G_sc(t)` is the group scheme of the full-weight Chevalley datum. -/
theorem chevalleyGroupScheme_def :
    t.chevalleyGroupScheme ht = (t.scChevalleyDatum ht).groupScheme :=
  (rfl)

/-- **`G_sc(t)` is the Kostant toral closure of the full-weight lattice**, with the torus acting
on each vector of the weight basis through its weight in fundamental-weight coordinates. -/
theorem chevalleyGroupScheme_eq_kostantToralGroupScheme :
    t.chevalleyGroupScheme ht =
      kostantToralGroupScheme
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht) (t.scWeightBasis ht)
        (t.scWeight ht) := by
  rw [chevalleyGroupScheme_def, ChevalleyDatum.groupScheme, scChevalleyDatum_coordinateWeight]
  -- The remaining difference is that the left-hand side reads the representation, lattice and
  -- weight basis through the fields of the datum, which are these by definition.
  rfl

/-- **The points of `G_sc(t)`** with values in a commutative ring `A`: the subgroup of `GLₙ(A)`
cut out by the defining Hopf ideal of the simply connected Chevalley group scheme. -/
abbrev chevalleyGroup (A : Type v) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) :=
  (t.scChevalleyDatum ht).points A

/-- The points of `G_sc(t)` are the points of the full-weight Chevalley datum. -/
theorem chevalleyGroup_def (A : Type v) [CommRing A] :
    t.chevalleyGroup ht A = (t.scChevalleyDatum ht).points A :=
  (rfl)

/-- **The points of `G_sc(t)` are the points of the Kostant toral closure of the full-weight
lattice**, with the torus acting through the weights in fundamental-weight coordinates, so the
generic API of those points applies to them. -/
theorem chevalleyGroup_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    t.chevalleyGroup ht A =
      kostantToralPointsSubgroup
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht) (t.scWeightBasis ht)
        (t.scWeight ht) A := by
  rw [chevalleyGroup_def, ChevalleyDatum.points_eq_kostantToralPointsSubgroup,
    scChevalleyDatum_coordinateWeight]
  -- The remaining difference is that the left-hand side reads the representation, lattice and
  -- weight basis through the fields of the datum, which are these by definition.
  rfl

/-- **Every torus matrix of the full-weight lattice is a point of `G_sc(t)`**: the diagonal matrix
acting on each vector of the weight basis through the value of its weight, in fundamental-weight
coordinates, at a torus parameter `s : Fin t.rank → Aˣ`. -/
theorem kostantTorusMatrix_mem_chevalleyGroup (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    kostantTorusMatrix (t.scLattice ht).toAddSubgroup
        (t.scWeightBasis ht) (t.scWeight ht) s ∈ t.chevalleyGroup ht A := by
  have h := (t.scChevalleyDatum ht).kostantTorusMatrix_mem_points A s
  rwa [scChevalleyDatum_coordinateWeight] at h

/-! ## The torus -/

/-- **The split maximal torus of `G_sc(t)`**: the split torus over `ℤ` with character lattice the
full weight lattice `Fin t.rank → ℤ`, in fundamental-weight coordinates, acting on each vector of
the weight basis through its weight. -/
def chevalleyTorus : SplitTorus.groupScheme ℤ (Fin t.rank) ⟶ t.chevalleyGroupScheme ht :=
  (t.scChevalleyDatum ht).torus

/-- The torus of `G_sc(t)` is the torus of the full-weight Chevalley datum. -/
theorem chevalleyTorus_def : t.chevalleyTorus ht = (t.scChevalleyDatum ht).torus :=
  (rfl)

/-- Included into `GLₙ`, the torus of `G_sc(t)` is the weight torus of the full-weight lattice,
with the weights in fundamental-weight coordinates. -/
@[simp]
theorem chevalleyTorus_comp_groupSchemeι :
    t.chevalleyTorus ht ≫ (t.scChevalleyDatum ht).groupSchemeι =
      GeneralLinear.weightTorus (R := ℤ) (t.scWeight ht) := by
  rw [chevalleyTorus_def, ChevalleyDatum.torus_comp_groupSchemeι,
    scChevalleyDatum_coordinateWeight]
  -- The two sides differ only in writing the rank of the lattice as the rank of the datum or as
  -- `scWeightBasisCard`, which agree by definition of the datum.
  rfl

/-- **The torus of `G_sc(t)` is a closed subgroup of it**, because the weights of the full-weight
lattice span the weight lattice. -/
instance isClosedImmersion_chevalleyTorus :
    IsClosedImmersion (t.chevalleyTorus ht).hom.hom.left :=
  (t.scChevalleyDatum ht).isClosedImmersion_torus

end

end TauCeti.DynkinType
