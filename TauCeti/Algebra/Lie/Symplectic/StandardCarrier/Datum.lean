/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Pinned
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootNormalization

/-!
# The standard symplectic Chevalley datum of type `C_(n+1)`

Pulling the standard representation `TauCeti.SpStd.rep n` of `sp₂ₙ₊₂` back along
`TauCeti.SpStd.pinnedLieEquiv` makes the standard rational module `(Fin (n + 1) ⊕ Fin (n + 1)) → ℚ`
and its coordinate `ℤ`-lattice `TauCeti.SpStd.lattice n` an admissible faithful representation of
the pinned rational Lie algebra of type `C_(n+1)`. With the coordinate weights `±ε_a` of
`TauCeti.SpStd.basisWeight`, this is a Chevalley datum `TauCeti.SpStd.chevalleyDatum n ht` of type
`C_(n+1)`.

The pinned equivalence matches the numbered generators in Bourbaki order without renumbering, so
the datum uses the same weight basis, the same weights and the same numbered root operators as the
explicit full-weight carrier `TauCeti.SpStd.groupScheme n`. Since the weights `±ε_a` span the full
fundamental-weight lattice `Fin (n + 1) → ℤ`, the chosen basis of the weight lattice of the datum
is the standard basis of fundamental weights: its coordinate weights are the weights themselves,
its coordinate roots are the roots of the simply connected root datum, and restriction from the
full weight lattice is the identity on torus parameters. The comparison of its group scheme and
points with `TauCeti.SpStd.groupScheme n` and `TauCeti.SpStd.points n` is
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Realization`.

Type `C₂` is excluded by `TauCeti.DynkinType.Valid` in favour of `B₂`; the rank-two symplectic
datum, with its renumbering of nodes, is `TauCeti.SpStd.b2ChevalleyDatum`.

## Main definitions

* `TauCeti.SpStd.pinnedRepresentation`: the standard representation of the pinned type-`C_(n+1)`
  Lie algebra, extended to its universal enveloping algebra.
* `TauCeti.SpStd.chevalleyDatum`: the full-weight Chevalley datum of type `C_(n+1)` on the
  standard symplectic lattice.

## Main results

* `TauCeti.SpStd.pinnedRepresentation_ι_injective`: the standard representation of the pinned
  algebra is faithful.
* `TauCeti.SpStd.pinnedRepresentation_kostantForm_mem_lattice`: the standard coordinate lattice is
  stable under the Kostant form of the pinned generators.
* `TauCeti.SpStd.chevalleyDatum_weightLattice`: the datum has the full weight lattice.
* `TauCeti.SpStd.chevalleyDatum_coordinateWeight`,
  `TauCeti.SpStd.chevalleyDatum_fullWeightTorusRestriction` and
  `TauCeti.SpStd.chevalleyDatum_coordinateRoot`: weights, torus parameters and roots are read in
  fundamental-weight coordinates without a change of basis.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate III.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The datum assembly follows `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Datum`.
-/

public section

namespace TauCeti.SpStd

open _root_.Matrix _root_.LieAlgebra.Symplectic

universe v

noncomputable section

variable (n : ℕ) (ht : (DynkinType.C (n + 1)).Valid)

/-! ## The standard representation of the pinned algebra -/

/-- The standard representation of the pinned rational Lie algebra of type `C_(n+1)` on
`(Fin (n + 1) ⊕ Fin (n + 1)) → ℚ`, extended to its universal enveloping algebra via
`TauCeti.SpStd.pinnedLieEquiv`. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.C (n + 1)).lieAlgebra ht) →ₐ[ℚ]
      Module.End ℚ ((Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :=
  (rep n).comp (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv n ht).toLieHom)

/-- `pinnedRepresentation` factors `TauCeti.SpStd.rep n` through the enveloping-algebra map of
`TauCeti.SpStd.pinnedLieEquiv`. -/
theorem pinnedRepresentation_def :
    pinnedRepresentation n ht =
      (rep n).comp (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv n ht).toLieHom) :=
  (rfl)

/-- On an element of the pinned Lie algebra, `pinnedRepresentation` acts as `rep n` at the
corresponding element of `sp₂ₙ₊₂`. -/
theorem pinnedRepresentation_ι (x : (DynkinType.C (n + 1)).lieAlgebra ht) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (pinnedLieEquiv n ht x)) := by
  rw [pinnedRepresentation_def, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieEquiv.coe_toLieHom]

/-- On Lie elements, the pinned action is the linear map associated to the corresponding
symplectic matrix. -/
theorem pinnedRepresentation_ι_matrix (x : (DynkinType.C (n + 1)).lieAlgebra ht) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Matrix.toLinAlgEquiv' (pinnedLieEquiv n ht x : Matrix _ _ ℚ) := by
  rw [pinnedRepresentation_ι, rep_def]
  exact UniversalEnvelopingAlgebra.representation_ι_matrix (pinnedLieEquiv n ht x)

/-- On the Lie algebra, `pinnedRepresentation` multiplies a coordinate vector by the symplectic
matrix `pinnedLieEquiv n ht x`. -/
theorem pinnedRepresentation_ι_apply (x : (DynkinType.C (n + 1)).lieAlgebra ht)
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      (pinnedLieEquiv n ht x :
        Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) *ᵥ v := by
  rw [pinnedRepresentation_ι_matrix, Matrix.toLinAlgEquiv'_apply]

/-- A pinned Cartan generator acts as the standard symplectic simple coroot with the same
number. -/
@[simp↓]
theorem pinnedRepresentation_ι_h (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.C (n + 1)).lieBasis ht).h i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator n i)) :=
  (pinnedRepresentation_ι n ht _).trans
    (congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_h n ht i))

/-- A pinned raising generator acts as the standard symplectic raising operator with the same
number. -/
@[simp↓]
theorem pinnedRepresentation_ι_e (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.C (n + 1)).lieBasis ht).e i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n (.inl i))) :=
  (pinnedRepresentation_ι n ht _).trans
    (congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_e n ht i))

/-- A pinned lowering generator acts as the standard symplectic lowering operator with the same
number. -/
@[simp↓]
theorem pinnedRepresentation_ι_f (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.C (n + 1)).lieBasis ht).f i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n (.inr i))) :=
  (pinnedRepresentation_ι n ht _).trans
    (congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_f n ht i))

/-- A pinned signed simple-root generator acts as the standard signed simple-root operator with the
same number. -/
@[simp↓]
theorem pinnedRepresentation_ι_rootGenerator
    (k : Fin (DynkinType.C (n + 1)).rank ⊕ Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator k)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) :=
  (pinnedRepresentation_ι n ht _).trans
    (congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
      (pinnedLieEquiv_lieBasis_rootGenerator n ht k))

/-- **The standard representation of the pinned type-`C_(n+1)` Lie algebra is faithful.** -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective fun x : (DynkinType.C (n + 1)).lieAlgebra ht =>
      pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  intro x y hxy
  simp only [pinnedRepresentation_ι, rep_def] at hxy
  exact (pinnedLieEquiv n ht).injective
    (UniversalEnvelopingAlgebra.representation_ι_injective ℚ (sp (Fin (n + 1)) ℚ)
      ((Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) hxy)

/-- **The standard coordinate lattice is stable under the Kostant integral form of the pinned
type-`C_(n+1)` generators.** -/
theorem pinnedRepresentation_kostantForm_mem_lattice :
    ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
        ((DynkinType.C (n + 1)).lieBasis ht).rootGenerator ((DynkinType.C (n + 1)).lieBasis ht).h,
      ∀ v ∈ (lattice n).toAddSubgroup,
        pinnedRepresentation n ht u v ∈ (lattice n).toAddSubgroup := by
  intro u hu v hv
  rw [pinnedRepresentation_def, AlgHom.comp_apply]
  refine rep_kostantForm_mem_lattice n _ ?_ v hv
  have hmap := TauCeti.UniversalEnvelopingAlgebra.map_kostantForm_of_root_units
    (pinnedLieEquiv n ht).toLieHom
    ((DynkinType.C (n + 1)).lieBasis ht).rootGenerator ((DynkinType.C (n + 1)).lieBasis ht).h
    (rootGenerator n) (cartanGenerator n) id id (fun _ => 1) (fun _ => 1)
    Function.surjective_id Function.surjective_id
    (fun k => by
      rw [LieEquiv.coe_toLieHom, Units.val_one, one_smul, id_eq]
      exact pinnedLieEquiv_lieBasis_rootGenerator n ht k)
    (fun i => by
      rw [LieEquiv.coe_toLieHom, Units.val_one, one_smul, id_eq]
      exact pinnedLieEquiv_lieBasis_h n ht i)
  rw [← hmap]
  exact Subring.mem_map.mpr ⟨u, hu, rfl⟩

/-- Every vector of `latticeBasis n` is a Cartan weight vector for the pinned Cartan generators,
of the weight recorded by `TauCeti.SpStd.basisWeight`. -/
theorem isCartanWeightVector_pinnedRepresentation_latticeBasis (a : Fin ((n + 1) + (n + 1))) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      ((DynkinType.C (n + 1)).lieBasis ht).h (pinnedRepresentation n ht) (basisWeight n a)
      ((latticeBasis n a : (lattice n).toAddSubgroup) : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr fun i => ?_
  rw [pinnedRepresentation_ι_h]
  exact (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_latticeBasis n a) i

/-! ## The full-weight Chevalley datum of type `C_(n+1)` -/

/-- **The standard symplectic Chevalley datum of type `C_(n+1)`**: the standard representation of
the pinned algebra on `(Fin (n + 1) ⊕ Fin (n + 1)) → ℚ`, the coordinate lattice with its
coordinate basis `TauCeti.SpStd.latticeBasis n`, the weights `±ε_a` of
`TauCeti.SpStd.basisWeight`, and the fundamental weights as the basis of its weight lattice. -/
-- The carrier, lattice and dimension are exposed so that dependent equations on representations,
-- basis vectors and matrix-valued points match `TauCeti.SpStd` directly.
@[expose] def chevalleyDatum : (DynkinType.C (n + 1)).ChevalleyDatum ht where
  carrier := (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ
  representation := pinnedRepresentation n ht
  injective_representation_ι := pinnedRepresentation_ι_injective n ht
  lattice := (lattice n).toAddSubgroup
  representation_mem_lattice := pinnedRepresentation_kostantForm_mem_lattice n ht
  span_lattice_eq_top := by
    simpa only [Submodule.coe_toAddSubgroup] using (instIsFullLatticeLattice n).span_eq_top
  dim := (n + 1) + (n + 1)
  basis := latticeBasis n
  weight := basisWeight n
  isCartanWeightVector_basis := isCartanWeightVector_pinnedRepresentation_latticeBasis n ht
  weightLatticeBasis := (Pi.basisFun ℤ (Fin (DynkinType.C (n + 1)).rank)).map
    (LinearEquiv.ofTop _ (span_range_basisWeight_eq_top n)).symm

/-- The standard symplectic datum of type `C_(n+1)` has dimension `2n + 2`. -/
theorem chevalleyDatum_dim : (chevalleyDatum n ht).dim = (n + 1) + (n + 1) :=
  (rfl)

/-- The representation of the datum is `TauCeti.SpStd.pinnedRepresentation`. -/
@[simp]
theorem chevalleyDatum_representation :
    (chevalleyDatum n ht).representation = pinnedRepresentation n ht :=
  (rfl)

/-- The datum acts through `TauCeti.SpStd.pinnedRepresentation` on enveloping algebra elements. -/
-- Rewrite before simplifying the argument, since the generator equations are keyed on `ι`.
@[simp↓]
theorem chevalleyDatum_representation_apply
    (u : _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.C (n + 1)).lieAlgebra ht)) :
    (chevalleyDatum n ht).representation u = pinnedRepresentation n ht u :=
  DFunLike.congr_fun (chevalleyDatum_representation n ht) u

/-- The admissible lattice of the datum is `(TauCeti.SpStd.lattice n).toAddSubgroup`. -/
@[simp]
theorem chevalleyDatum_lattice : (chevalleyDatum n ht).lattice = (lattice n).toAddSubgroup :=
  (rfl)

/-- The weight basis of the datum is `TauCeti.SpStd.latticeBasis n`. -/
@[simp]
theorem chevalleyDatum_basis : (chevalleyDatum n ht).basis = latticeBasis n :=
  (rfl)

/-- Each basis vector of the datum is the corresponding standard coordinate vector. -/
@[simp↓]
theorem coe_chevalleyDatum_basis (a : Fin ((n + 1) + (n + 1))) :
    ((chevalleyDatum n ht).basis a : (chevalleyDatum n ht).carrier) =
      Pi.single (finSumFinEquiv.symm a) 1 :=
  coe_latticeBasis n a

/-- The basis weights of the datum are the standard-module weights `TauCeti.SpStd.basisWeight n`. -/
@[simp]
theorem chevalleyDatum_weight : (chevalleyDatum n ht).weight = basisWeight n :=
  (rfl)

/-- **The standard symplectic datum of type `C_(n+1)` has the full weight lattice.** -/
@[simp]
theorem chevalleyDatum_weightLattice : (chevalleyDatum n ht).weightLattice = ⊤ :=
  (chevalleyDatum n ht).weightLattice_def.trans (span_range_basisWeight_eq_top n)

/-- The chosen weight-lattice basis of the datum is transported from `Pi.basisFun`. -/
theorem chevalleyDatum_weightLatticeBasis :
    (chevalleyDatum n ht).weightLatticeBasis =
      (Pi.basisFun ℤ (Fin (DynkinType.C (n + 1)).rank)).map
        (LinearEquiv.ofTop _ (chevalleyDatum_weightLattice n ht)).symm :=
  (rfl)

/-- The chosen weight-lattice basis of the datum is the standard basis of fundamental weights. -/
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.C (n + 1)).rank) :
    ((chevalleyDatum n ht).weightLatticeBasis i : Fin (DynkinType.C (n + 1)).rank → ℤ) =
      Pi.single i 1 := by
  simp only [chevalleyDatum_weightLatticeBasis, Module.Basis.map_apply,
    LinearEquiv.coe_ofTop_symm_apply, Pi.basisFun_apply]

/-- The coordinate weights of the datum are the standard-module weights, without a change of
basis. -/
@[simp]
theorem chevalleyDatum_coordinateWeight :
    (chevalleyDatum n ht).coordinateWeight = basisWeight n :=
  (chevalleyDatum n ht).coordinateWeight_eq_of_coe_weightLatticeBasis
    (coe_chevalleyDatum_weightLatticeBasis n ht)

/-- Restriction from the full weight lattice is the identity on torus parameters of the
datum. -/
@[simp↓]
theorem chevalleyDatum_fullWeightTorusRestriction {A : Type v} [CommRing A]
    (s : Fin (DynkinType.C (n + 1)).rank → Aˣ) :
    (chevalleyDatum n ht).fullWeightTorusRestriction A s = s :=
  (chevalleyDatum n ht).fullWeightTorusRestriction_eq_of_coe_weightLatticeBasis A
    (coe_chevalleyDatum_weightLatticeBasis n ht) s

/-- The coordinate roots of the datum are the roots of the simply connected root datum of type
`C_(n+1)` in fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateRoot (γ : Fin (DynkinType.C (n + 1)).numRoots) :
    (chevalleyDatum n ht).coordinateRoot γ =
      ((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root γ :=
  (chevalleyDatum n ht).coordinateRoot_eq_of_coe_weightLatticeBasis
    (coe_chevalleyDatum_weightLatticeBasis n ht) γ

end

end TauCeti.SpStd
