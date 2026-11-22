/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.Lattice
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.CharacterMap
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.ToralClosure
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.RootSubgroup

/-!
# The full-weight Chevalley datum and the simply connected Chevalley group scheme

For a valid Dynkin type, the direct sum of its fundamental highest-weight modules over `ℚ`,
with the direct sum of their admissible lattices, is a faithful representation with a numbered
integral weight basis. This file assembles these existing constructions into
`TauCeti.DynkinType.scChevalleyDatum`.

Its weight lattice is the entire lattice `Fin t.rank → ℤ`, not just the root lattice. The chosen
basis consists of the fundamental weights, so the coordinate weights used by the datum's torus
are exactly `TauCeti.DynkinType.scWeight`. Thus this datum supplies the full-weight input to
Chevalley's construction without a change of torus coordinates. In particular its torus is a
closed immersion, by `TauCeti.DynkinType.ChevalleyDatum.isClosedImmersion_torus`.

On points, every root subgroup of this datum is injective over every commutative ring: the
fundamental summand at node `i` detects the parameter of the `i`-th simple root subgroup, and
every root subgroup is a signed Weyl conjugate of a simple one.

The representation, lattice, and weight basis are those constructed in
the full-weight lattice module imported above;
the assembly follows the Geck-datum construction in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Geck.Basic`. No identification of the resulting group
scheme with an independently constructed reductive group is asserted here.

The group scheme of this datum over `ℤ` is the **simply connected Chevalley group scheme**
`G_sc(t)` (`TauCeti.DynkinType.chevalleyGroupScheme`), with its points over a commutative ring
(`TauCeti.DynkinType.chevalleyGroup`) and its split maximal torus
(`TauCeti.DynkinType.chevalleyTorus`). Since the coordinate weights are the weights themselves,
`G_sc(t)` is the Kostant toral closure of the full-weight lattice with its weights read in
fundamental-weight coordinates
(`TauCeti.DynkinType.chevalleyGroupScheme_eq_kostantToralGroupScheme`), its points are the
corresponding points of that closure
(`TauCeti.DynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup`), and every diagonal matrix of
a torus parameter `s : Fin t.rank → Aˣ`, acting on each weight vector through its weight, is a
point of `G_sc(t)` (`TauCeti.DynkinType.kostantTorusMatrix_mem_chevalleyGroup`). Diagram symmetries
act on `(t.scChevalleyDatum ht).points A` via `TauCeti.DynkinType.scChevalleyDatumDiagramAut`,
commuting with value-ring maps (`TauCeti.DynkinType.map_comp_scChevalleyDatumDiagramAut`).

## Main declarations

* `TauCeti.DynkinType.scChevalleyDatum`: the full-weight module as a Chevalley datum.
* `TauCeti.DynkinType.scChevalleyDatum_weightLattice`: its weights span the full weight lattice.
* `TauCeti.DynkinType.coe_scChevalleyDatum_weightLatticeBasis`: the lattice basis consists of
  the fundamental weights in their standard coordinates.
* `TauCeti.DynkinType.scChevalleyDatum_coordinateWeight`: the coordinate weights are `scWeight`.
* `TauCeti.DynkinType.scChevalleyDatum_coordinateRoot`: the coordinate roots are the roots, so
  the torus acts on the root subgroup of `γ` through the character `γ`.
* `TauCeti.DynkinType.scChevalleyDatum_rootSubgroupPoints_injective`: every root subgroup of the
  full-weight datum is injective, over every commutative ring.
* `TauCeti.DynkinType.chevalleyGroupScheme`: the simply connected Chevalley group scheme
  `G_sc(t)` over `ℤ`.
* `TauCeti.DynkinType.chevalleyGroup`: its points with values in a commutative ring, as a
  subgroup of `GLₙ`.
* `TauCeti.DynkinType.chevalleyTorus`: its split maximal torus, with character lattice the full
  weight lattice; `TauCeti.DynkinType.isClosedImmersion_chevalleyTorus` makes it a closed
  subgroup.
* `TauCeti.DynkinType.scChevalleyDatumDiagramAutHom` and
  `TauCeti.DynkinType.scChevalleyDatumDiagramAut`: the diagram symmetry action on the points of
  `scChevalleyDatum`, with value-ring naturality (`map_comp_scChevalleyDatumDiagramAut`) and
  character-map compatibility (`isCharacterMap_scChevalleyDatumDiagramAut`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2, and Chapter 3, the remark after Lemma 27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType

noncomputable section

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

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

/-- For the full-weight datum, restriction from the full weight lattice is the identity on torus
parameters. -/
@[simp]
theorem scChevalleyDatum_fullWeightTorusRestriction {A : Type v} [CommRing A]
    (s : Fin t.rank → Aˣ) : (t.scChevalleyDatum ht).fullWeightTorusRestriction A s = s := by
  funext i
  rw [ChevalleyDatum.fullWeightTorusRestriction_apply, coe_scChevalleyDatum_weightLatticeBasis,
    torusCharacter_single, zpow_one]

/-- The coordinate roots of the full-weight datum are the roots themselves, in fundamental-weight
coordinates: the torus acts on the root subgroup of `γ` through the character `γ`. -/
@[simp]
theorem scChevalleyDatum_coordinateRoot (γ : Fin t.numRoots) :
    (t.scChevalleyDatum ht).coordinateRoot γ = (t.simplyConnectedRootDatum ht).root γ := by
  ext i
  have h := congrFun ((t.scChevalleyDatum ht).sum_coordinateRoot_smul γ) i
  simpa [Pi.single_apply] using h

/-- **Every root subgroup of the full-weight datum is injective**, over every commutative ring,
including nonreduced rings and rings of small characteristic. -/
theorem scChevalleyDatum_rootSubgroupPoints_injective (γ : Fin t.numRoots) (A : Type v)
    [CommRing A] :
    Function.Injective ((t.scChevalleyDatum ht).rootSubgroupPoints γ A) := by
  -- At a positive simple root the fundamental summand of that node detects the parameter.
  refine (t.scChevalleyDatum ht).rootSubgroupPoints_injective_of_simple A (fun i => ?_) γ
  refine ((t.scChevalleyDatum ht).rootSubgroupPoints_injective_iff _ A).2 ?_
  rw [chevalleyRootSubgroup_simpleIndex]
  exact t.kostantRootSubgroupParam_scLattice_injective ht A (.inl i)

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

/-! ## Diagram automorphisms on `scChevalleyDatum` -/

section DiagramAut

open Multiplicative

attribute [local instance high] Algebra.toModule

variable {t} {σ τ : Equiv.Perm (Fin t.rank)}

private noncomputable def scPointsEquiv (A : Type v) [CommRing A] :
    (t.scChevalleyDatum ht).points A ≃*
      kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A :=
  MulEquiv.subgroupCongr (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)

/-- The diagram automorphism of the points of `t.scChevalleyDatum ht`, obtained by transporting
`t.scToralDiagramAutPoints ht hσ A` along `chevalleyGroup_eq_kostantToralPointsSubgroup`. -/
noncomputable def scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    MulAut ((t.scChevalleyDatum ht).points A) :=
  MulAut.congr (t.scPointsEquiv ht A).symm (t.scToralDiagramAutPoints ht hσ A)

/-- The diagram symmetry group acts on the points of `t.scChevalleyDatum ht`, obtained by
transporting `t.scToralDiagramAutPointsHom ht A` along `scPointsEquiv`. -/
noncomputable def scChevalleyDatumDiagramAutHom (A : Type v) [CommRing A] :
    t.diagramSymmetry →* MulAut ((t.scChevalleyDatum ht).points A) :=
  (MulAut.congr (t.scPointsEquiv ht A).symm).toMonoidHom.comp
    (t.scToralDiagramAutPointsHom ht A)

/-- Evaluation of the bundled diagram action on `scChevalleyDatum` is
`scChevalleyDatumDiagramAut`. -/
@[simp]
theorem scChevalleyDatumDiagramAutHom_apply (A : Type v) [CommRing A] (g : t.diagramSymmetry) :
    t.scChevalleyDatumDiagramAutHom ht A g = t.scChevalleyDatumDiagramAut ht g.property A :=
  congrArg (MulAut.congr (t.scPointsEquiv ht A).symm) (t.scToralDiagramAutPointsHom_apply ht A g)

private theorem scPointsEquiv_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (g : (t.scChevalleyDatum ht).points A) :
    t.scPointsEquiv ht A (t.scChevalleyDatumDiagramAut ht hσ A g) =
      t.scToralDiagramAutPoints ht hσ A (t.scPointsEquiv ht A g) :=
  (t.scPointsEquiv ht A).apply_symm_apply _

private theorem scPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : (t.scChevalleyDatum ht).points A) :
    (t.scPointsEquiv ht B
        (((t.scChevalleyDatum ht).pointsPresentation A).map
          ((t.scChevalleyDatum ht).pointsPresentation B) f g) :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) B) =
      (((kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) A).map
        (kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) B) f)
        (t.scPointsEquiv ht A g) :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) B) :=
  ((MulEquiv.subgroupCongr_apply (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht B) _).trans
    (GeneralLinear.IntegralPointsPresentation.coe_map
      ((t.scChevalleyDatum ht).pointsPresentation A)
      ((t.scChevalleyDatum ht).pointsPresentation B) f g)).trans <|
    (congrArg (Matrix.GeneralLinearGroup.map f)
      (MulEquiv.subgroupCongr_apply (t.chevalleyGroup_eq_kostantToralPointsSubgroup ht A)
        g).symm).trans
      (GeneralLinear.IntegralPointsPresentation.coe_map
        (kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) A)
        (kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) B)
        f (t.scPointsEquiv ht A g)).symm

/-- The diagram automorphism on `scChevalleyDatum` is natural in the value ring. In particular
it commutes with ring-endomorphism maps such as Frobenius. -/
theorem map_comp_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B) :
    (((t.scChevalleyDatum ht).pointsPresentation A).map
        ((t.scChevalleyDatum ht).pointsPresentation B) f).comp
        (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom =
      (t.scChevalleyDatumDiagramAut ht hσ B).toMonoidHom.comp
        (((t.scChevalleyDatum ht).pointsPresentation A).map
          ((t.scChevalleyDatum ht).pointsPresentation B) f) := by
  ext1 g
  apply (t.scPointsEquiv ht B).injective
  apply Subtype.ext
  have h1 := t.scPointsEquiv_map ht f (t.scChevalleyDatumDiagramAut ht hσ A g)
  have h2 := congrArg
    (fun x => (((kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A).map
      (kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) B) f x) :
      Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) B))
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A g)
  have h3 := congrArg Subtype.val
    (DFunLike.congr_fun (t.map_comp_scToralDiagramAutPoints ht hσ f) (t.scPointsEquiv ht A g))
  have h4 := congrArg
    (fun x => ((t.scToralDiagramAutPoints ht hσ B x :
      Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) B)))
    (Subtype.ext (t.scPointsEquiv_map ht f g).symm)
  have h5 := congrArg Subtype.val
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ B
      (((t.scChevalleyDatum ht).pointsPresentation A).map
        ((t.scChevalleyDatum ht).pointsPresentation B) f g)).symm
  exact ((h1.trans h2).trans (h3.trans h4)).trans h5

/-- The identity diagram symmetry acts as the identity on `(t.scChevalleyDatum ht).points A`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_one (A : Type v) [CommRing A] :
    t.scChevalleyDatumDiagramAut ht t.diagramSymmetry.one_mem A = 1 :=
  (t.scChevalleyDatumDiagramAutHom_apply ht A 1).symm.trans
    (t.scChevalleyDatumDiagramAutHom ht A).map_one

/-- Diagram automorphisms on `(t.scChevalleyDatum ht).points A` compose multiplicatively. -/
@[simp]
theorem scChevalleyDatumDiagramAut_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    t.scChevalleyDatumDiagramAut ht (t.diagramSymmetry.mul_mem hσ hτ) A =
      t.scChevalleyDatumDiagramAut ht hσ A * t.scChevalleyDatumDiagramAut ht hτ A :=
  (t.scChevalleyDatumDiagramAutHom_apply ht A (⟨σ, hσ⟩ * ⟨τ, hτ⟩)).symm.trans <|
    ((t.scChevalleyDatumDiagramAutHom ht A).map_mul ⟨σ, hσ⟩ ⟨τ, hτ⟩).trans <|
      congrArg₂ (· * ·) (t.scChevalleyDatumDiagramAutHom_apply ht A ⟨σ, hσ⟩)
        (t.scChevalleyDatumDiagramAutHom_apply ht A ⟨τ, hτ⟩)

/-- Inverting a diagram symmetry inverts its automorphism on `(t.scChevalleyDatum ht).points A`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_inv (hσ : σ ∈ t.diagramSymmetry) (A : Type v) [CommRing A] :
    t.scChevalleyDatumDiagramAut ht (t.diagramSymmetry.inv_mem hσ) A =
      (t.scChevalleyDatumDiagramAut ht hσ A)⁻¹ :=
  (t.scChevalleyDatumDiagramAutHom_apply ht A ⟨σ, hσ⟩⁻¹).symm.trans <|
    ((t.scChevalleyDatumDiagramAutHom ht A).map_inv ⟨σ, hσ⟩).trans <|
      congrArg Inv.inv (t.scChevalleyDatumDiagramAutHom_apply ht A ⟨σ, hσ⟩)

/-- Every order relation of a diagram symmetry holds on `(t.scChevalleyDatum ht).points A`. -/
theorem scChevalleyDatumDiagramAut_pow_eq_one (hσ : σ ∈ t.diagramSymmetry) (A : Type v)
    [CommRing A] {m : ℕ} (hm : σ ^ m = 1) :
    t.scChevalleyDatumDiagramAut ht hσ A ^ m = 1 :=
  (congrArg (· ^ m) (t.scChevalleyDatumDiagramAutHom_apply ht A ⟨σ, hσ⟩)).symm.trans <|
    ((t.scChevalleyDatumDiagramAutHom ht A).map_pow ⟨σ, hσ⟩ m).symm.trans <|
      (congrArg (t.scChevalleyDatumDiagramAutHom ht A)
        (Subtype.ext hm : (⟨σ, hσ⟩ : t.diagramSymmetry) ^ m = 1)).trans
        (t.scChevalleyDatumDiagramAutHom ht A).map_one

/-- On every root subgroup of `scChevalleyDatum`, the diagram automorphism permutes the root
index by `diagramRootPerm` and multiplies the additive parameter by `chevalleyDiagramSign`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_rootSubgroupPoints (hσ : σ ∈ t.diagramSymmetry)
    (α : Fin t.numRoots) (A : Type v) [CommRing A] (u : A) :
    t.scChevalleyDatumDiagramAut ht hσ A
        ((t.scChevalleyDatum ht).rootSubgroupPoints α A (ofAdd u)) =
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.diagramRootPerm ht hσ α) A
        (ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  have hroot (γ : Fin t.numRoots) (v : A) :
      t.scPointsEquiv ht A ((t.scChevalleyDatum ht).rootSubgroupPoints γ A (ofAdd v)) =
        chevalleyToralRootSubgroupPoints (t := t) (ht := ht)
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) γ A (ofAdd v) :=
    Subtype.ext <| (MulEquiv.subgroupCongr_apply _ _).trans <|
      ((t.scChevalleyDatum ht).coe_rootSubgroupPoints γ A (ofAdd v)).trans
        (coe_chevalleyToralRootSubgroupPoints (t := t) (ht := ht) _ _ _ _ _ _ γ A (ofAdd v)).symm
  exact (t.scPointsEquiv ht A).injective <|
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A _).trans <|
      (congrArg _ (hroot α u)).trans <|
        (t.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints ht hσ α A u).trans
          (hroot _ _).symm

private theorem scPointsEquiv_torusPoints (A : Type v) [CommRing A] (r : Fin t.rank → Aˣ) :
    t.scPointsEquiv ht A ((t.scChevalleyDatum ht).torusPoints A r) =
      kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A r := by
  apply Subtype.ext
  have h1 := (t.scChevalleyDatum ht).coe_torusPoints A r
  rw [t.scChevalleyDatum_coordinateWeight ht] at h1
  exact (MulEquiv.subgroupCongr_apply _ _).trans <|
    h1.trans (coe_kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A r).symm

/-- On the torus of `scChevalleyDatum`, the diagram automorphism relabels parameters by `σ⁻¹`. -/
@[simp]
theorem scChevalleyDatumDiagramAut_torusPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.scChevalleyDatumDiagramAut ht hσ A ((t.scChevalleyDatum ht).torusPoints A s) =
      (t.scChevalleyDatum ht).torusPoints A (fun k => s (σ⁻¹ k)) :=
  (t.scPointsEquiv ht A).injective <|
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A _).trans <|
      (congrArg _ (t.scPointsEquiv_torusPoints ht A s)).trans <|
        (t.scToralDiagramAutPoints_kostantToralWeightTorusPoints ht hσ A s).trans
          (t.scPointsEquiv_torusPoints ht A _).symm

/-- The diagram automorphism on `scChevalleyDatum` has character map equal to the weight map of
the inverse root-datum diagram automorphism, over every commutative ring. -/
theorem isCharacterMap_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom
      (diagramAut ht hσ)⁻¹.toHom.weightMap :=
  isCharacterMap_iff.mpr fun s => (t.scPointsEquiv ht A).injective <|
    (t.scPointsEquiv_scChevalleyDatumDiagramAut ht hσ A _).trans <|
      (congrArg _ (t.scPointsEquiv_torusPoints ht A s)).trans <|
        ((t.isCharacterMap_scToralDiagramAutPoints ht hσ A).map_apply s).trans
          (t.scPointsEquiv_torusPoints ht A _).symm

/-- Conjugating an endomorphism `F` of `(t.scChevalleyDatum ht).points A` by the diagram
automorphism `γ_σ` conjugates its character map by `(diagramAut ht hσ).toHom.weightMap`. -/
theorem isCharacterMap_conj_scChevalleyDatumDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A]
    {F : (t.scChevalleyDatum ht).points A →* (t.scChevalleyDatum ht).points A}
    {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A) F φ) :
    IsCharacterMap ((t.scChevalleyDatum ht).torusPoints A)
      (((t.scChevalleyDatumDiagramAut ht hσ A).toMonoidHom.comp F).comp
        (t.scChevalleyDatumDiagramAut ht hσ A)⁻¹.toMonoidHom)
      ((diagramAut ht hσ).toHom.weightMap * φ * (diagramAut ht hσ)⁻¹.toHom.weightMap) := by
  have hinv := t.isCharacterMap_scChevalleyDatumDiagramAut ht (t.diagramSymmetry.inv_mem hσ) A
  rw [scChevalleyDatumDiagramAut_inv ht hσ A, diagramAut_inv ht hσ, inv_inv] at hinv
  simpa only [mul_assoc] using
    ((t.isCharacterMap_scChevalleyDatumDiagramAut ht hσ A).comp hφ).comp hinv

end DiagramAut

end

end TauCeti.DynkinType
