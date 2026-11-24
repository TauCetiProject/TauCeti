/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Pinned
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootNormalization

/-!
# The rank-two symplectic Chevalley datum of type B₂

Pulling the four-dimensional standard symplectic representation `TauCeti.SpStd.rep 1` back along
`TauCeti.SpStd.b2PinnedLieEquiv` makes the standard rational module `(Fin 2 ⊕ Fin 2) → ℚ` and its
coordinate `ℤ`-lattice `TauCeti.SpStd.lattice 1` an admissible faithful representation of the
pinned rational Lie algebra of type `B₂`. Reading the four coordinate weights across the Bourbaki
node swap `TauCeti.lengthPermRankTwo` gives a full-weight Chevalley datum
`TauCeti.SpStd.b2ChevalleyDatum` for `TauCeti.DynkinType.B 2`.

Because the four weights `(0, ±1)` and `(±1, ∓1)` span the entire fundamental-weight lattice
`Fin (DynkinType.B 2).rank → ℤ`, the chosen basis of `b2ChevalleyDatum.weightLattice` is the
standard basis of fundamental weights, the coordinate weights equal `b2BasisWeight` with no
lattice-index correction, and `fullWeightTorusRestriction` is the identity on torus parameters.
This file constructs the datum and its weight-lattice coordinates; the comparison of its integral
group scheme and point functor with `TauCeti.SpStd.groupScheme 1` and `TauCeti.SpStd.points 1` is
proved in `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Realization`.

## Main definitions

* `TauCeti.SpStd.b2PinnedRepresentation`: the enveloping-algebra representation of the pinned `B₂`
  Lie algebra on the four-dimensional symplectic module.
* `TauCeti.SpStd.b2Weight` and `TauCeti.SpStd.b2BasisWeight`: the coordinate weights of the
  standard symplectic basis, read in Bourbaki `B₂` fundamental-weight coordinates.
* `TauCeti.SpStd.b2ChevalleyDatum`: the full-weight Chevalley datum of type `B₂` on the
  four-dimensional symplectic lattice.

## Main results

* `TauCeti.SpStd.b2PinnedRepresentation_ι_injective`: faithfulness of the four-dimensional
  representation on the pinned `B₂` Lie algebra.
* `TauCeti.SpStd.b2PinnedRepresentation_kostantForm_mem_lattice`: stability of the standard
  coordinate lattice under the pinned `B₂` Kostant integral form.
* `TauCeti.SpStd.span_range_b2BasisWeight_eq_top` and
  `TauCeti.SpStd.b2ChevalleyDatum_weightLattice`: the weights span the full weight lattice.
* `TauCeti.SpStd.b2ChevalleyDatum_coordinateWeight`,
  `TauCeti.SpStd.b2ChevalleyDatum_fullWeightTorusRestriction`, and
  `TauCeti.SpStd.b2ChevalleyDatum_coordinateRoot`: torus parameters and root characters act
  without lattice-index adjustment.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plates II and III.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The datum assembly and full-weight character-lattice equations adapt
`TauCeti.Algebra.Lie.G2.ShortRoot.Datum` and
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.Datum`.
-/

public section

namespace TauCeti.SpStd

open _root_.Matrix _root_.LieAlgebra.Symplectic

universe v

noncomputable section

/-- The standard four-dimensional representation of the pinned rational `B₂` Lie algebra, extended
to its universal enveloping algebra via `TauCeti.SpStd.b2PinnedLieEquiv`. -/
def b2PinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ
      ((DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl)) →ₐ[ℚ]
        Module.End ℚ ((Fin (1 + 1) ⊕ Fin (1 + 1)) → ℚ) :=
  (rep 1).comp (UniversalEnvelopingAlgebra.map ℚ b2PinnedLieEquiv.toLieHom)

/-- `b2PinnedRepresentation` factors `TauCeti.SpStd.rep 1` through the enveloping-algebra map of
`TauCeti.SpStd.b2PinnedLieEquiv`. -/
theorem b2PinnedRepresentation_def :
    b2PinnedRepresentation =
      (rep 1).comp (UniversalEnvelopingAlgebra.map ℚ b2PinnedLieEquiv.toLieHom) :=
  (rfl)

/-- On an element of the pinned `B₂` Lie algebra, `b2PinnedRepresentation` acts as `rep 1` at the
corresponding `sp₄` matrix. -/
theorem b2PinnedRepresentation_ι
    (x : (DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl)) :
    b2PinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (b2PinnedLieEquiv x)) := by
  rw [b2PinnedRepresentation_def, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieEquiv.coe_toLieHom]

/-- Applying `b2PinnedRepresentation` on the Lie algebra multiplies a coordinate vector by the
`4 × 4` symplectic matrix `b2PinnedLieEquiv x`. -/
theorem b2PinnedRepresentation_ι_apply
    (x : (DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl))
    (v : (Fin (1 + 1) ⊕ Fin (1 + 1)) → ℚ) :
    b2PinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      (b2PinnedLieEquiv x :
        Matrix (Fin (1 + 1) ⊕ Fin (1 + 1)) (Fin (1 + 1) ⊕ Fin (1 + 1)) ℚ) *ᵥ v := by
  rw [b2PinnedRepresentation_ι, rep_ι_apply]

/-- A pinned `B₂` Cartan generator acts as the standard symplectic Cartan operator at the swapped
node. -/
@[simp↓]
theorem b2PinnedRepresentation_ι_h {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedRepresentation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.B 2).lieBasis ht).h i)) =
      rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator 1 (lengthPermRankTwo i))) := by
  rw [b2PinnedRepresentation_ι, b2PinnedLieEquiv_lieBasis_h]

/-- A pinned `B₂` raising generator acts as the standard symplectic raising operator at the swapped
node. -/
@[simp↓]
theorem b2PinnedRepresentation_ι_e {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedRepresentation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.B 2).lieBasis ht).e i)) =
      rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator 1 (.inl (lengthPermRankTwo i)))) := by
  rw [b2PinnedRepresentation_ι, b2PinnedLieEquiv_lieBasis_e]

/-- A pinned `B₂` lowering generator acts as the standard symplectic lowering operator at the
swapped node. -/
@[simp↓]
theorem b2PinnedRepresentation_ι_f {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) :
    b2PinnedRepresentation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.B 2).lieBasis ht).f i)) =
      rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator 1 (.inr (lengthPermRankTwo i)))) := by
  rw [b2PinnedRepresentation_ι, b2PinnedLieEquiv_lieBasis_f]

/-- On the signed simple-root family, `b2PinnedRepresentation` acts as `rep 1` on the signed
symplectic generators reindexed by `lengthPermRankTwo`. -/
@[simp↓]
theorem b2PinnedRepresentation_ι_rootGenerator {ht : (DynkinType.B 2).Valid}
    (k : Fin (DynkinType.B 2).rank ⊕ Fin (DynkinType.B 2).rank) :
    b2PinnedRepresentation
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (((DynkinType.B 2).lieBasis ht).rootGenerator k)) =
      rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator 1 (Sum.map lengthPermRankTwo lengthPermRankTwo k))) := by
  rw [b2PinnedRepresentation_ι, b2PinnedLieEquiv_lieBasis_rootGenerator]

/-- **The four-dimensional symplectic representation of the pinned `B₂` Lie algebra is
faithful.** -/
theorem b2PinnedRepresentation_ι_injective :
    Function.Injective fun x : (DynkinType.B 2).lieAlgebra (DynkinType.valid_B.mpr le_rfl) =>
      b2PinnedRepresentation (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  intro x y hxy
  apply EquivLike.injective b2PinnedLieEquiv
  apply Subtype.ext
  ext a b
  have hcol := congrFun (DFunLike.congr_fun hxy (Pi.single b 1)) a
  simpa only [b2PinnedRepresentation_ι_apply, mulVec_single_one, col_apply] using hcol

/-- **The standard coordinate lattice is stable under the Kostant integral form of the pinned `B₂`
generators.** -/
theorem b2PinnedRepresentation_kostantForm_mem_lattice :
    ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
        ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).rootGenerator
        ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h,
      ∀ v ∈ (lattice 1).toAddSubgroup,
        b2PinnedRepresentation u v ∈ (lattice 1).toAddSubgroup := by
  intro u hu v hv
  rw [b2PinnedRepresentation_def, AlgHom.comp_apply]
  refine rep_kostantForm_mem_lattice 1 _ ?_ v hv
  have hmap := TauCeti.UniversalEnvelopingAlgebra.map_kostantForm_of_root_units
    b2PinnedLieEquiv.toLieHom
    ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).rootGenerator
    ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h
    (rootGenerator 1) (cartanGenerator 1)
    (Sum.map lengthPermRankTwo lengthPermRankTwo) lengthPermRankTwo (fun _ => 1) (fun _ => 1)
    (lengthPermRankTwo.sumCongr lengthPermRankTwo).surjective lengthPermRankTwo.surjective
    (fun k => by
      rw [LieEquiv.coe_toLieHom, Units.val_one, one_smul]
      exact b2PinnedLieEquiv_lieBasis_rootGenerator k)
    (fun i => by simp)
  rw [← hmap]
  exact Subring.mem_map.mpr ⟨u, hu, rfl⟩

/-! ## Coordinate weights in Bourbaki `B₂` numbering -/

/-- The integral weight of a standard symplectic coordinate in Bourbaki `B₂` fundamental-weight
coordinates, obtained by reindexing `TauCeti.SpStd.weight 1` along `TauCeti.lengthPermRankTwo`. -/
def b2Weight (a : Fin (1 + 1) ⊕ Fin (1 + 1)) (i : Fin (DynkinType.B 2).rank) : ℤ :=
  weight 1 a (lengthPermRankTwo i)

@[simp]
theorem b2Weight_apply (a : Fin (1 + 1) ⊕ Fin (1 + 1)) (i : Fin (DynkinType.B 2).rank) :
    b2Weight a i = weight 1 a (lengthPermRankTwo i) :=
  (rfl)

/-- `b2Weight` is `weight 1` postcomposed with `LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo`. -/
theorem b2Weight_eq_comp_lengthPermRankTwo :
    b2Weight = LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo ∘ weight 1 := by
  funext a
  ext i
  rw [Function.comp_apply, LinearEquiv.funCongrLeft_apply, b2Weight_apply]
  exact (LinearMap.funLeft_apply ℤ ℤ lengthPermRankTwo (weight 1 a) i).symm

/-- The integral weight attached to the enumerated coordinate basis `latticeBasis 1` in Bourbaki
`B₂` fundamental-weight coordinates. -/
def b2BasisWeight (a : Fin ((1 + 1) + (1 + 1))) : Fin (DynkinType.B 2).rank → ℤ :=
  b2Weight (finSumFinEquiv.symm a)

@[simp]
theorem b2BasisWeight_apply (a : Fin ((1 + 1) + (1 + 1))) :
    b2BasisWeight a = b2Weight (finSumFinEquiv.symm a) :=
  (rfl)

theorem b2BasisWeight_apply_apply (a : Fin ((1 + 1) + (1 + 1))) (i : Fin (DynkinType.B 2).rank) :
    b2BasisWeight a i = basisWeight 1 a (lengthPermRankTwo i) := by
  rw [b2BasisWeight_apply, b2Weight_apply, basisWeight_apply]

/-- `b2BasisWeight` applies `LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo` to `basisWeight 1`. -/
theorem b2BasisWeight_eq_funCongrLeft :
    b2BasisWeight =
      fun a => (LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo).toLinearMap (basisWeight 1 a) := by
  funext a
  ext i
  rw [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, b2BasisWeight_apply_apply]
  exact (LinearMap.funLeft_apply ℤ ℤ lengthPermRankTwo (basisWeight 1 a) i).symm

/-- Every standard coordinate vector is a Cartan weight vector of weight `b2Weight a` for the
pinned `B₂` Cartan generators. -/
theorem isCartanWeightVector_b2PinnedRepresentation_single (a : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h
      b2PinnedRepresentation (b2Weight a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr fun i => ?_
  rw [b2PinnedRepresentation_ι_h, b2Weight_apply]
  exact (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_single 1 a) (lengthPermRankTwo i)

/-- Every vector of `latticeBasis 1` is a Cartan weight vector of weight `b2BasisWeight a` for the
pinned `B₂` Cartan generators. -/
theorem isCartanWeightVector_b2PinnedRepresentation_latticeBasis
    (a : Fin ((1 + 1) + (1 + 1))) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h
      b2PinnedRepresentation (b2BasisWeight a)
      ((latticeBasis 1 a : (lattice 1).toAddSubgroup) :
        (Fin (1 + 1) ⊕ Fin (1 + 1)) → ℚ) := by
  rw [coe_latticeBasis, b2BasisWeight_apply]
  exact isCartanWeightVector_b2PinnedRepresentation_single (finSumFinEquiv.symm a)

/-- **The four coordinate weights of the symplectic module span the full `B₂` character
lattice.** -/
theorem span_range_b2Weight_eq_top : Submodule.span ℤ (Set.range b2Weight) = ⊤ := by
  let e := LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo
  let w : Fin 2 ⊕ Fin 2 → Fin 2 → ℤ := weight 1
  have hspan : Submodule.span ℤ (Set.range (e ∘ w)) = ⊤ := by
    have hw : Submodule.span ℤ (Set.range w) = ⊤ := span_range_weight_eq_top 1
    rw [Set.range_comp, Submodule.span_image_linearEquiv, hw, Submodule.map_top,
      LinearEquiv.range]
  exact (congrArg (Submodule.span ℤ ∘ Set.range) b2Weight_eq_comp_lengthPermRankTwo).trans hspan

/-- **The weights of `latticeBasis 1` span the full `B₂` character lattice.** -/
theorem span_range_b2BasisWeight_eq_top : Submodule.span ℤ (Set.range b2BasisWeight) = ⊤ := by
  have h : b2BasisWeight = b2Weight ∘ finSumFinEquiv.symm := funext b2BasisWeight_apply
  rw [h, finSumFinEquiv.symm.surjective.range_comp]
  exact span_range_b2Weight_eq_top

/-! ## The full-weight Chevalley datum of type `B₂` -/

/-- **The full-weight Chevalley datum of type `B₂` on the four-dimensional symplectic lattice**,
with `TauCeti.SpStd.latticeBasis 1` as its weight basis and the fundamental weights of `B₂` as the
basis of its weight lattice. -/
-- The carrier, lattice, and dimension are exposed so that dependent equations on representations,
-- basis vectors, and matrix-valued points match `TauCeti.SpStd` at `n = 1` directly.
@[expose] def b2ChevalleyDatum :
    (DynkinType.B 2).ChevalleyDatum (DynkinType.valid_B.mpr le_rfl) where
  carrier := (Fin (1 + 1) ⊕ Fin (1 + 1)) → ℚ
  representation := b2PinnedRepresentation
  injective_representation_ι := b2PinnedRepresentation_ι_injective
  lattice := (lattice 1).toAddSubgroup
  representation_mem_lattice := b2PinnedRepresentation_kostantForm_mem_lattice
  span_lattice_eq_top := by
    simpa only [Submodule.coe_toAddSubgroup] using (instIsFullLatticeLattice 1).span_eq_top
  dim := (1 + 1) + (1 + 1)
  basis := latticeBasis 1
  weight := b2BasisWeight
  isCartanWeightVector_basis := isCartanWeightVector_b2PinnedRepresentation_latticeBasis
  weightLatticeBasis := (Pi.basisFun ℤ (Fin (DynkinType.B 2).rank)).map
    (LinearEquiv.ofTop _ span_range_b2BasisWeight_eq_top).symm

/-- The rank-two symplectic datum has dimension four. -/
theorem b2ChevalleyDatum_dim : b2ChevalleyDatum.dim = 4 :=
  (rfl)

/-- The representation of the datum is `TauCeti.SpStd.b2PinnedRepresentation`. -/
@[simp]
theorem b2ChevalleyDatum_representation :
    b2ChevalleyDatum.representation = b2PinnedRepresentation :=
  (rfl)

/-- The admissible lattice of the datum is `(TauCeti.SpStd.lattice 1).toAddSubgroup`. -/
@[simp]
theorem b2ChevalleyDatum_lattice : b2ChevalleyDatum.lattice = (lattice 1).toAddSubgroup :=
  (rfl)

/-- The weight basis of the datum is `TauCeti.SpStd.latticeBasis 1`. -/
@[simp]
theorem b2ChevalleyDatum_basis : b2ChevalleyDatum.basis = latticeBasis 1 :=
  (rfl)

/-- Each basis vector of the datum is the corresponding standard coordinate vector. -/
@[simp↓]
theorem coe_b2ChevalleyDatum_basis (a : Fin ((1 + 1) + (1 + 1))) :
    (b2ChevalleyDatum.basis a : b2ChevalleyDatum.carrier) =
      Pi.single (finSumFinEquiv.symm a) 1 :=
  coe_latticeBasis 1 a

/-- The basis weights of the datum are `TauCeti.SpStd.b2BasisWeight`. -/
@[simp]
theorem b2ChevalleyDatum_weight : b2ChevalleyDatum.weight = b2BasisWeight :=
  (rfl)

/-- **The rank-two symplectic datum has the full weight lattice.** -/
@[simp]
theorem b2ChevalleyDatum_weightLattice : b2ChevalleyDatum.weightLattice = ⊤ :=
  b2ChevalleyDatum.weightLattice_def.trans span_range_b2BasisWeight_eq_top

/-- The character-lattice basis of `b2ChevalleyDatum` is transported from `Pi.basisFun`. -/
theorem b2ChevalleyDatum_weightLatticeBasis :
    b2ChevalleyDatum.weightLatticeBasis =
      (Pi.basisFun ℤ (Fin (DynkinType.B 2).rank)).map
        (LinearEquiv.ofTop _ b2ChevalleyDatum_weightLattice).symm :=
  (rfl)

/-- The chosen weight-lattice basis of `b2ChevalleyDatum` is the standard basis of fundamental
weights. -/
@[simp↓]
theorem coe_b2ChevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.B 2).rank) :
    (b2ChevalleyDatum.weightLatticeBasis i : Fin (DynkinType.B 2).rank → ℤ) = Pi.single i 1 := by
  simp only [b2ChevalleyDatum_weightLatticeBasis, Module.Basis.map_apply,
    LinearEquiv.coe_ofTop_symm_apply, Pi.basisFun_apply]

/-- The coordinate weights of `b2ChevalleyDatum` equal `b2BasisWeight`, without a lattice-index
correction. -/
@[simp]
theorem b2ChevalleyDatum_coordinateWeight : b2ChevalleyDatum.coordinateWeight = b2BasisWeight :=
  b2ChevalleyDatum.coordinateWeight_eq_of_coe_weightLatticeBasis
    coe_b2ChevalleyDatum_weightLatticeBasis

/-- Restriction from the full weight lattice is the identity on torus parameters of
`b2ChevalleyDatum`. -/
@[simp↓]
theorem b2ChevalleyDatum_fullWeightTorusRestriction {A : Type v} [CommRing A]
    (s : Fin (DynkinType.B 2).rank → Aˣ) :
    b2ChevalleyDatum.fullWeightTorusRestriction A s = s :=
  b2ChevalleyDatum.fullWeightTorusRestriction_eq_of_coe_weightLatticeBasis A
    coe_b2ChevalleyDatum_weightLatticeBasis s

/-- The coordinate roots of `b2ChevalleyDatum` are the roots of the pinned `B₂` root datum in
fundamental-weight coordinates. -/
@[simp]
theorem b2ChevalleyDatum_coordinateRoot (γ : Fin (DynkinType.B 2).numRoots) :
    b2ChevalleyDatum.coordinateRoot γ =
      ((DynkinType.B 2).simplyConnectedRootDatum (DynkinType.valid_B.mpr le_rfl)).root γ :=
  b2ChevalleyDatum.coordinateRoot_eq_of_coe_weightLatticeBasis
    coe_b2ChevalleyDatum_weightLatticeBasis γ

end

end TauCeti.SpStd
