/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Serre
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootNormalization

/-!
# The standard Chevalley datum of type `A_r`

Pulling the standard representation `TauCeti.SlStd.rep r` of `sl_{r+1}` back along
`TauCeti.SlStd.pinnedLieEquiv` makes the standard rational module `Fin (r + 1) → ℚ` and its
coordinate `ℤ`-lattice `TauCeti.SlStd.lattice r` an admissible faithful representation of the
pinned rational Lie algebra of type `A_r`. With the coordinate weights `ε₀, …, ε_r` of
`TauCeti.SlStd.weight`, this is a Chevalley datum `TauCeti.SlStd.chevalleyDatum r ht` of type
`A_r`.

The pinned equivalence matches the numbered generators without renumbering, so the datum uses the
same weight basis, the same weights and the same numbered root operators as the explicit
full-weight carrier `TauCeti.SlStd.groupScheme r`. Since the weights `ε_k` span the full
fundamental-weight lattice `Fin r → ℤ`, the chosen basis of the weight lattice of the datum is the
standard basis of fundamental weights: its coordinate weights are the weights themselves, its
coordinate roots are the roots of the simply connected root datum, and restriction from the full
weight lattice is the identity on torus parameters. The comparison of its group scheme and points
with `TauCeti.SlStd.groupScheme r` and `TauCeti.SlStd.points r` is
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Realization`.

## Main definitions

* `TauCeti.SlStd.pinnedRepresentation`: the standard representation of the pinned type-`A_r` Lie
  algebra, extended to its universal enveloping algebra.
* `TauCeti.SlStd.chevalleyDatum`: the full-weight Chevalley datum of type `A_r` on the standard
  lattice.

## Main results

* `TauCeti.SlStd.pinnedRepresentation_ι_injective`: the standard representation of the pinned
  algebra is faithful.
* `TauCeti.SlStd.pinnedRepresentation_kostantForm_mem_lattice`: the standard coordinate lattice is
  stable under the Kostant form of the pinned generators.
* `TauCeti.SlStd.chevalleyDatum_weightLattice`: the datum has the full weight lattice.
* `TauCeti.SlStd.chevalleyDatum_coordinateWeight`,
  `TauCeti.SlStd.chevalleyDatum_fullWeightTorusRestriction` and
  `TauCeti.SlStd.chevalleyDatum_coordinateRoot`: weights, torus parameters and roots are read in
  fundamental-weight coordinates without a change of basis.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate I.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The datum assembly follows `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Datum`.
-/

public section

namespace TauCeti.SlStd

open LieAlgebra.SpecialLinear
open scoped _root_.Matrix

universe v

noncomputable section

variable (r : ℕ) (ht : (DynkinType.A r).Valid)

/-! ## The standard representation of the pinned algebra -/

/-- The standard representation of the pinned rational Lie algebra of type `A_r` on
`Fin (r + 1) → ℚ`, extended to its universal enveloping algebra via
`TauCeti.SlStd.pinnedLieEquiv`. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.A r).lieAlgebra ht) →ₐ[ℚ]
      Module.End ℚ (Fin (r + 1) → ℚ) :=
  (rep r).comp (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv r ht).toLieHom)

/-- `pinnedRepresentation` factors `TauCeti.SlStd.rep r` through the enveloping-algebra map of
`TauCeti.SlStd.pinnedLieEquiv`. -/
theorem pinnedRepresentation_def :
    pinnedRepresentation r ht =
      (rep r).comp (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv r ht).toLieHom) :=
  (rfl)

/-- On an element of the pinned Lie algebra, `pinnedRepresentation` acts as `rep r` at the
corresponding element of `sl_{r+1}`. -/
theorem pinnedRepresentation_ι (x : (DynkinType.A r).lieAlgebra ht) :
    pinnedRepresentation r ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (pinnedLieEquiv r ht x)) := by
  rw [pinnedRepresentation_def, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieEquiv.coe_toLieHom]

/-- On the Lie algebra, `pinnedRepresentation` multiplies a coordinate vector by the matrix
`pinnedLieEquiv r ht x`. -/
theorem pinnedRepresentation_ι_apply (x : (DynkinType.A r).lieAlgebra ht)
    (v : Fin (r + 1) → ℚ) :
    pinnedRepresentation r ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      (pinnedLieEquiv r ht x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) *ᵥ v := by
  rw [pinnedRepresentation_ι, rep_ι_apply]

/-- A pinned Cartan generator acts as the standard diagonal difference with the same number. -/
@[simp↓]
theorem pinnedRepresentation_ι_h (i : Fin (DynkinType.A r).rank) :
    pinnedRepresentation r ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.A r).lieBasis ht).h i)) =
      rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator r i)) :=
  (pinnedRepresentation_ι r ht _).trans
    (congrArg (fun x => rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_h r ht i))

/-- A pinned raising generator acts as the upper adjacent matrix unit with the same number. -/
@[simp↓]
theorem pinnedRepresentation_ι_e (i : Fin (DynkinType.A r).rank) :
    pinnedRepresentation r ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.A r).lieBasis ht).e i)) =
      rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inl i))) :=
  (pinnedRepresentation_ι r ht _).trans
    (congrArg (fun x => rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_e r ht i))

/-- A pinned lowering generator acts as the lower adjacent matrix unit with the same number. -/
@[simp↓]
theorem pinnedRepresentation_ι_f (i : Fin (DynkinType.A r).rank) :
    pinnedRepresentation r ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.A r).lieBasis ht).f i)) =
      rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inr i))) :=
  (pinnedRepresentation_ι r ht _).trans
    (congrArg (fun x => rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_f r ht i))

/-- A pinned signed simple-root generator acts as the adjacent matrix unit with the same
number. -/
@[simp↓]
theorem pinnedRepresentation_ι_rootGenerator
    (k : Fin (DynkinType.A r).rank ⊕ Fin (DynkinType.A r).rank) :
    pinnedRepresentation r ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.A r).lieBasis ht).rootGenerator k)) =
      rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)) :=
  (pinnedRepresentation_ι r ht _).trans
    (congrArg (fun x => rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_rootGenerator r ht k))

/-- **The standard representation of the pinned type-`A_r` Lie algebra is faithful.** -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective fun x : (DynkinType.A r).lieAlgebra ht =>
      pinnedRepresentation r ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  intro x y hxy
  apply (pinnedLieEquiv r ht).injective
  apply Subtype.ext
  ext a b
  have hcol := congrFun (DFunLike.congr_fun hxy (Pi.single b 1)) a
  simpa only [pinnedRepresentation_ι_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    LieEquiv.coe_toLieHom] using hcol

/-- **The standard coordinate lattice is stable under the Kostant integral form of the pinned
type-`A_r` generators.** -/
theorem pinnedRepresentation_kostantForm_mem_lattice :
    ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
        ((DynkinType.A r).lieBasis ht).rootGenerator ((DynkinType.A r).lieBasis ht).h,
      ∀ v ∈ (lattice r).toAddSubgroup,
        pinnedRepresentation r ht u v ∈ (lattice r).toAddSubgroup := by
  intro u hu v hv
  rw [pinnedRepresentation_def, AlgHom.comp_apply]
  refine rep_kostantForm_mem_lattice r _ ?_ v hv
  have hmap := TauCeti.UniversalEnvelopingAlgebra.map_kostantForm_of_root_units
    (pinnedLieEquiv r ht).toLieHom
    ((DynkinType.A r).lieBasis ht).rootGenerator ((DynkinType.A r).lieBasis ht).h
    (rootGenerator r) (cartanGenerator r) id id (fun _ => 1) (fun _ => 1)
    Function.surjective_id Function.surjective_id
    (fun k => by
      rw [LieEquiv.coe_toLieHom, Units.val_one, one_smul, id_eq]
      exact pinnedLieEquiv_lieBasis_rootGenerator r ht k)
    (fun i => by
      rw [LieEquiv.coe_toLieHom, Units.val_one, one_smul, id_eq]
      exact pinnedLieEquiv_lieBasis_h r ht i)
  rw [← hmap]
  exact Subring.mem_map.mpr ⟨u, hu, rfl⟩

/-- Every vector of `latticeBasis r` is a Cartan weight vector for the pinned Cartan generators,
of the weight recorded by `TauCeti.SlStd.weight`. -/
theorem isCartanWeightVector_pinnedRepresentation_latticeBasis (k : Fin (r + 1)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector ((DynkinType.A r).lieBasis ht).h
      (pinnedRepresentation r ht) (weight r k)
      ((latticeBasis r k : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr fun i => ?_
  rw [pinnedRepresentation_ι_h]
  exact (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_latticeBasis r k) i

/-! ## The full-weight Chevalley datum of type `A_r` -/

/-- **The standard Chevalley datum of type `A_r`**: the standard representation of the pinned
algebra on `Fin (r + 1) → ℚ`, the coordinate lattice with its coordinate basis
`TauCeti.SlStd.latticeBasis r`, the weights `ε_k` of `TauCeti.SlStd.weight`, and the fundamental
weights as the basis of its weight lattice. -/
-- The carrier, lattice and dimension are exposed so that dependent equations on representations,
-- basis vectors and matrix-valued points match `TauCeti.SlStd` directly.
@[expose] def chevalleyDatum : (DynkinType.A r).ChevalleyDatum ht where
  carrier := Fin (r + 1) → ℚ
  representation := pinnedRepresentation r ht
  injective_representation_ι := pinnedRepresentation_ι_injective r ht
  lattice := (lattice r).toAddSubgroup
  representation_mem_lattice := pinnedRepresentation_kostantForm_mem_lattice r ht
  span_lattice_eq_top := by
    have hlattice : lattice r = TauCeti.coordinateLattice (Fin (r + 1)) := by
      ext v
      simp only [mem_lattice_iff, TauCeti.mem_coordinateLattice_iff]
    simpa only [Submodule.coe_toAddSubgroup, hlattice] using
      (TauCeti.instIsFullLatticeCoordinateLattice (Fin (r + 1))).span_eq_top
  dim := r + 1
  basis := latticeBasis r
  weight := weight r
  isCartanWeightVector_basis := isCartanWeightVector_pinnedRepresentation_latticeBasis r ht
  weightLatticeBasis := (Pi.basisFun ℤ (Fin (DynkinType.A r).rank)).map
    (LinearEquiv.ofTop _ (span_range_weight_eq_top r)).symm

/-- The standard datum of type `A_r` has dimension `r + 1`. -/
theorem chevalleyDatum_dim : (chevalleyDatum r ht).dim = r + 1 :=
  (rfl)

/-- The representation of the datum is `TauCeti.SlStd.pinnedRepresentation`. -/
@[simp]
theorem chevalleyDatum_representation :
    (chevalleyDatum r ht).representation = pinnedRepresentation r ht :=
  (rfl)

/-- The admissible lattice of the datum is `(TauCeti.SlStd.lattice r).toAddSubgroup`. -/
@[simp]
theorem chevalleyDatum_lattice : (chevalleyDatum r ht).lattice = (lattice r).toAddSubgroup :=
  (rfl)

/-- The weight basis of the datum is `TauCeti.SlStd.latticeBasis r`. -/
@[simp]
theorem chevalleyDatum_basis : (chevalleyDatum r ht).basis = latticeBasis r :=
  (rfl)

/-- Each basis vector of the datum is the corresponding standard coordinate vector. -/
@[simp↓]
theorem coe_chevalleyDatum_basis (k : Fin (r + 1)) :
    ((chevalleyDatum r ht).basis k : (chevalleyDatum r ht).carrier) = Pi.single k 1 :=
  coe_latticeBasis r k

/-- The basis weights of the datum are the standard-module weights `TauCeti.SlStd.weight r`. -/
@[simp]
theorem chevalleyDatum_weight : (chevalleyDatum r ht).weight = weight r :=
  (rfl)

/-- **The standard datum of type `A_r` has the full weight lattice.** -/
@[simp]
theorem chevalleyDatum_weightLattice : (chevalleyDatum r ht).weightLattice = ⊤ :=
  (chevalleyDatum r ht).weightLattice_def.trans (span_range_weight_eq_top r)

/-- The chosen weight-lattice basis of the datum is transported from `Pi.basisFun`. -/
theorem chevalleyDatum_weightLatticeBasis :
    (chevalleyDatum r ht).weightLatticeBasis =
      (Pi.basisFun ℤ (Fin (DynkinType.A r).rank)).map
        (LinearEquiv.ofTop _ (chevalleyDatum_weightLattice r ht)).symm :=
  (rfl)

/-- The chosen weight-lattice basis of the datum is the standard basis of fundamental weights. -/
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.A r).rank) :
    ((chevalleyDatum r ht).weightLatticeBasis i : Fin (DynkinType.A r).rank → ℤ) =
      Pi.single i 1 := by
  simp only [chevalleyDatum_weightLatticeBasis, Module.Basis.map_apply,
    LinearEquiv.coe_ofTop_symm_apply, Pi.basisFun_apply]

/-- The coordinate weights of the datum are the standard-module weights, without a change of
basis. -/
@[simp]
theorem chevalleyDatum_coordinateWeight :
    (chevalleyDatum r ht).coordinateWeight = weight r :=
  (chevalleyDatum r ht).coordinateWeight_eq_of_coe_weightLatticeBasis
    (coe_chevalleyDatum_weightLatticeBasis r ht)

/-- Restriction from the full weight lattice is the identity on torus parameters of the
datum. -/
@[simp↓]
theorem chevalleyDatum_fullWeightTorusRestriction {A : Type v} [CommRing A]
    (s : Fin (DynkinType.A r).rank → Aˣ) :
    (chevalleyDatum r ht).fullWeightTorusRestriction A s = s :=
  (chevalleyDatum r ht).fullWeightTorusRestriction_eq_of_coe_weightLatticeBasis A
    (coe_chevalleyDatum_weightLatticeBasis r ht) s

/-- The coordinate roots of the datum are the roots of the simply connected root datum of type
`A_r` in fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateRoot (γ : Fin (DynkinType.A r).numRoots) :
    (chevalleyDatum r ht).coordinateRoot γ =
      ((DynkinType.A r).simplyConnectedRootDatum ht).root γ :=
  (chevalleyDatum r ht).coordinateRoot_eq_of_coe_weightLatticeBasis
    (coe_chevalleyDatum_weightLatticeBasis r ht) γ

end

end TauCeti.SlStd
