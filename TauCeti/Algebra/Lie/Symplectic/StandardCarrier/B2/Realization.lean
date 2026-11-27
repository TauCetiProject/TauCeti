/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Datum
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Restriction

/-!
# Realizing the pinned B₂ Chevalley datum on the rank-two symplectic carrier

The full-weight Chevalley datum `TauCeti.SpStd.b2ChevalleyDatum` and the rank-two standard
symplectic carrier `TauCeti.SpStd.groupScheme 1` act on the same four-dimensional lattice
`TauCeti.SpStd.lattice 1` in the same coordinate basis `TauCeti.SpStd.latticeBasis 1`. Their signed
simple-root operators are reindexed by `TauCeti.lengthPermRankTwo`, and their coordinate weights
are pushed forward along the invertible character-lattice map induced by `lengthPermRankTwo`.

Consequently, their integral toral defining Hopf ideals inside `O(GL₄)` are equal over `ℤ`
(`TauCeti.SpStd.kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal`), so their affine
group schemes over `ℤ` and their subgroups of `GL₄(A)` for every commutative ring `A` coincide at
the integral scheme level without passing to reduced subschemes or field points, retaining points
over nonreduced rings and rings of characteristic two.

`TauCeti.SpStd.b2ChevalleyDatumPointsEquiv` packages the resulting group isomorphism
`b2ChevalleyDatum.points A ≃* points 1 A`. Across this identification:
* positive and negative simple root subgroups match the numbered raising and lowering subgroups of
  `SpStd 1` across `lengthPermRankTwo`, with the additive parameter unchanged;
* torus points `b2ChevalleyDatum.torusPoints A s` match
  `weightTorusPoints 1 A (s ∘ lengthPermRankTwo)`;
* functorial ring-change maps and `p ^ k`-power Frobenius endomorphisms commute with the
  identification; and
* every root subgroup `b2ChevalleyDatum.rootSubgroupPoints γ A` (across all eight roots of `B₂`) is
  injective over every commutative ring `A`.

## Main definitions

* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv`: the canonical multiplicative isomorphism between
  `b2ChevalleyDatum.points A` and `SpStd.points 1 A` over any commutative ring `A`.

## Main results

* `TauCeti.SpStd.kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal`,
  `TauCeti.SpStd.b2ChevalleyDatum_groupScheme`, and `TauCeti.SpStd.b2ChevalleyDatum_points`: exact
  equality of the integral defining Hopf ideals, affine group schemes over `ℤ`, and matrix-point
  subgroups over every commutative ring.
* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex`,
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex`,
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_torusPoints`, and their `*_symm_*` inverses: the
  forward and inverse transport equations on simple root subgroups and torus points.
* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_map` and
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_frobenius`: naturality in the value ring and
  intertwining of Frobenius endomorphisms.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.

The `ChevalleyDatumPointsEquiv` realization API and theorem layout follow
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Geck.Realization`.
-/

public section

namespace TauCeti.SpStd

open AlgebraicGeometry CategoryTheory _root_.Matrix
open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

/-! ## Equality of the integral defining ideals, group schemes, and point subgroups -/

/-- **The integral defining Hopf ideal of `b2ChevalleyDatum` is `definingIdeal 1`.** Reindexing the
signed simple-root operators by `lengthPermRankTwo` permutes the root-subgroup coordinate maps, and
reindexing the character lattice by `lengthPermRankTwo` preserves the kernel of the weight-torus
coordinate map. -/
theorem kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal :
    kostantToralDefiningIdeal
        ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).rootGenerator
        ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h
        b2ChevalleyDatum.representation b2ChevalleyDatum.lattice
        b2ChevalleyDatum.representation_mem_lattice
        b2ChevalleyDatum.isNilpotent_representation_rootGenerator
        b2ChevalleyDatum.basis b2ChevalleyDatum.coordinateWeight =
      definingIdeal 1 := by
  rw [b2ChevalleyDatum_coordinateWeight, definingIdeal_def]
  have hn := b2ChevalleyDatum.isNilpotent_representation_rootGenerator
  dsimp only [b2ChevalleyDatum] at hn ⊢
  exact kostantToralDefiningIdeal_eq_of_operator_equiv_linearMap
    ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).rootGenerator
    ((DynkinType.B 2).lieBasis (DynkinType.valid_B.mpr le_rfl)).h
    b2PinnedRepresentation (lattice 1).toAddSubgroup
    b2PinnedRepresentation_kostantForm_mem_lattice (latticeBasis 1)
    (rootGenerator 1) (cartanGenerator 1) (rep 1) (rep_kostantForm_mem_lattice 1)
    (lengthPermRankTwo.sumCongr lengthPermRankTwo)
    hn (isNilpotent_rep_rootGenerator 1)
    b2BasisWeight (basisWeight 1)
    (fun k => (b2PinnedRepresentation_ι_rootGenerator k).trans
      (congrArg (fun j => rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator 1 j)))
        (Equiv.sumCongr_apply lengthPermRankTwo lengthPermRankTwo k).symm))
    (LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo).injective
    b2BasisWeight_eq_funCongrLeft

/-- **The integral group scheme of `b2ChevalleyDatum` is `SpStd.groupScheme 1`.** -/
theorem b2ChevalleyDatum_groupScheme : b2ChevalleyDatum.groupScheme = groupScheme 1 := by
  have h := kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal
  rw [DynkinType.ChevalleyDatum.groupScheme, kostantToralGroupScheme, groupScheme_def]
  dsimp only [b2ChevalleyDatum] at h ⊢
  rw [h]

/-- The closed immersion of `b2ChevalleyDatum.groupScheme` into `GL₄` agrees with `carrierι 1`
across `b2ChevalleyDatum_groupScheme`. -/
theorem b2ChevalleyDatum_groupSchemeι :
    b2ChevalleyDatum.groupSchemeι = eqToHom b2ChevalleyDatum_groupScheme ≫ carrierι 1 := by
  have h := kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal.trans (definingIdeal_def 1)
  rw [DynkinType.ChevalleyDatum.groupSchemeι_def, carrierι_def,
    kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def, ← Category.assoc]
  exact congrArg (· ≫ eqToHom (GeneralLinear.groupScheme_def ℤ ((1 + 1) + (1 + 1))).symm)
    (CommHopfAlgCat.eqToHom_comp_quotientSpecι _ h).symm

/-- **The point subgroup of `b2ChevalleyDatum` over any commutative ring `A` is `points 1 A`.** -/
theorem b2ChevalleyDatum_points (A : Type v) [CommRing A] :
    b2ChevalleyDatum.points A = points 1 A := by
  have h := kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal
  rw [DynkinType.ChevalleyDatum.points_def, points_def]
  dsimp only [b2ChevalleyDatum] at h ⊢
  rw [h]

/-! ## The bundled isomorphism on points and its action on generators -/

/-- **The canonical group isomorphism between `b2ChevalleyDatum.points A` and `SpStd.points 1 A`**
over any commutative ring `A`, induced by the equality of matrix subgroups in `GL₄(A)`. -/
def b2ChevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    b2ChevalleyDatum.points A ≃* points 1 A :=
  MulEquiv.subgroupCongr (b2ChevalleyDatum_points A)

/-- `b2ChevalleyDatumPointsEquiv` is the identity on underlying invertible `4 × 4` matrices. -/
@[simp]
theorem coe_b2ChevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : b2ChevalleyDatum.points A) :
    (b2ChevalleyDatumPointsEquiv A g : GeneralLinearGroup (Fin ((1 + 1) + (1 + 1))) A) =
      (g : GeneralLinearGroup (Fin b2ChevalleyDatum.dim) A) :=
  (rfl)

/-- The inverse of `b2ChevalleyDatumPointsEquiv` is the identity on underlying invertible `4 × 4`
matrices. -/
@[simp]
theorem coe_b2ChevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A] (g : points 1 A) :
    ((b2ChevalleyDatumPointsEquiv A).symm g : GeneralLinearGroup (Fin b2ChevalleyDatum.dim) A) =
      (g : GeneralLinearGroup (Fin ((1 + 1) + (1 + 1))) A) :=
  (rfl)

/-- **Positive simple root subgroups of `b2ChevalleyDatum` correspond to the numbered raising
subgroups of `SpStd 1` across `lengthPermRankTwo`.** -/
@[simp↓]
theorem b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex {ht : (DynkinType.B 2).Valid}
    (i : Fin (DynkinType.B 2).rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    b2ChevalleyDatumPointsEquiv A
        (b2ChevalleyDatum.rootSubgroupPoints ((DynkinType.B 2).simpleIndex ht i) A u) =
      rootSubgroupPoints 1 (.inl (lengthPermRankTwo i)) A u := by
  apply Subtype.ext
  rw [coe_b2ChevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_simpleIndex, coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (b2PinnedRepresentation_ι_rootGenerator (.inl i)) _

/-- The inverse point isomorphism carries the `i`-th raising subgroup of `SpStd 1` to the positive
simple root subgroup of `b2ChevalleyDatum` at `lengthPermRankTwo i`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl
    (i : Fin (1 + 1)) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (b2ChevalleyDatumPointsEquiv A).symm (rootSubgroupPoints 1 (.inl i) A u) =
      b2ChevalleyDatum.rootSubgroupPoints
        ((DynkinType.B 2).simpleIndex (DynkinType.valid_B.mpr le_rfl)
          (lengthPermRankTwo i)) A u := by
  rw [MulEquiv.symm_apply_eq]
  exact ((b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex
    (lengthPermRankTwo i) A u).trans
    (congrArg (fun j => rootSubgroupPoints 1 (.inl j) A u)
      (lengthPermRankTwo_lengthPermRankTwo i))).symm

/-- **Negative simple root subgroups of `b2ChevalleyDatum` correspond to the numbered lowering
subgroups of `SpStd 1` across `lengthPermRankTwo`.** -/
@[simp↓]
theorem b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    b2ChevalleyDatumPointsEquiv A
        (b2ChevalleyDatum.rootSubgroupPoints
          (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
            ((DynkinType.B 2).simpleIndex ht i) ((DynkinType.B 2).simpleIndex ht i)) A u) =
      rootSubgroupPoints 1 (.inr (lengthPermRankTwo i)) A u := by
  apply Subtype.ext
  rw [coe_b2ChevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex,
    coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (b2PinnedRepresentation_ι_rootGenerator (.inr i)) _

/-- The inverse point isomorphism carries the `i`-th lowering subgroup of `SpStd 1` to the negative
simple root subgroup of `b2ChevalleyDatum` at `lengthPermRankTwo i`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr
    (i : Fin (1 + 1)) (A : Type v) [CommRing A] (u : Multiplicative A) :
    (b2ChevalleyDatumPointsEquiv A).symm (rootSubgroupPoints 1 (.inr i) A u) =
      b2ChevalleyDatum.rootSubgroupPoints
        (((DynkinType.B 2).simplyConnectedRootDatum (DynkinType.valid_B.mpr le_rfl)).reflectionPerm
          ((DynkinType.B 2).simpleIndex (DynkinType.valid_B.mpr le_rfl) (lengthPermRankTwo i))
          ((DynkinType.B 2).simpleIndex (DynkinType.valid_B.mpr le_rfl) (lengthPermRankTwo i)))
        A u := by
  rw [MulEquiv.symm_apply_eq]
  exact ((b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex
    (lengthPermRankTwo i) A u).trans
    (congrArg (fun j => rootSubgroupPoints 1 (.inr j) A u)
      (lengthPermRankTwo_lengthPermRankTwo i))).symm

/-- **Torus points of `b2ChevalleyDatum` correspond to `weightTorusPoints 1` with the two
fundamental-weight parameters swapped by `lengthPermRankTwo`.** -/
@[simp↓]
theorem b2ChevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin (DynkinType.B 2).rank → Aˣ) :
    b2ChevalleyDatumPointsEquiv A (b2ChevalleyDatum.torusPoints A s) =
      weightTorusPoints 1 A (s ∘ lengthPermRankTwo) := by
  apply Subtype.ext
  rw [coe_b2ChevalleyDatumPointsEquiv, DynkinType.ChevalleyDatum.coe_torusPoints,
    b2ChevalleyDatum_coordinateWeight, coe_weightTorusPoints]
  have hsymm : lengthPermRankTwo.symm = lengthPermRankTwo :=
    Equiv.ext fun i =>
      (Equiv.symm_apply_eq lengthPermRankTwo).mpr (lengthPermRankTwo_lengthPermRankTwo i).symm
  have htpm : torusPointMap (LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo).toLinearMap s =
      s ∘ lengthPermRankTwo := by
    refine (torusPointMap_funCongrLeft lengthPermRankTwo s).trans ?_
    rw [hsymm]
    rfl
  exact (congrArg (fun w => kostantTorusMatrix (lattice 1).toAddSubgroup (latticeBasis 1) w s)
    b2BasisWeight_eq_funCongrLeft).trans
    ((kostantTorusMatrix_torusPointMap (lattice 1).toAddSubgroup (latticeBasis 1)
      (basisWeight 1) (LinearEquiv.funCongrLeft ℤ ℤ lengthPermRankTwo).toLinearMap s).symm.trans
      (congrArg (kostantTorusMatrix (lattice 1).toAddSubgroup (latticeBasis 1) (basisWeight 1))
        htpm))

/-- The inverse point isomorphism sends `weightTorusPoints 1 A s` to `b2ChevalleyDatum.torusPoints`
with parameters reindexed by `lengthPermRankTwo`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin (1 + 1) → Aˣ) :
    (b2ChevalleyDatumPointsEquiv A).symm (weightTorusPoints 1 A s) =
      b2ChevalleyDatum.torusPoints A (s ∘ lengthPermRankTwo) := by
  rw [MulEquiv.symm_apply_eq, b2ChevalleyDatumPointsEquiv_torusPoints A (s ∘ lengthPermRankTwo)]
  congr 1
  funext j
  exact congrArg s (lengthPermRankTwo_lengthPermRankTwo j).symm

/-! ## Functoriality in the value ring and Frobenius compatibility -/

/-- `b2ChevalleyDatumPointsEquiv` is natural with respect to ring homomorphisms `A →+* B`. -/
theorem b2ChevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumPointsEquiv B
        ((b2ChevalleyDatum.pointsPresentation A).map
          (b2ChevalleyDatum.pointsPresentation B) f g) =
      (pointsPresentation 1 A).map (pointsPresentation 1 B) f
        (b2ChevalleyDatumPointsEquiv A g) := by
  apply Subtype.ext
  rw [coe_b2ChevalleyDatumPointsEquiv, GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map, coe_b2ChevalleyDatumPointsEquiv]
  -- Match the exposed datum dimension `b2ChevalleyDatum.dim` with `(1 + 1) + (1 + 1)`.
  rfl

/-- **The point isomorphism intertwines the `p ^ k`-power Frobenius endomorphism of
`b2ChevalleyDatum` with `SpStd.frobenius 1 p k A`.** -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumPointsEquiv A (b2ChevalleyDatum.frobenius p k A g) =
      frobenius 1 p k A (b2ChevalleyDatumPointsEquiv A g) := by
  rw [DynkinType.ChevalleyDatum.frobenius_def, frobenius_eq_map, b2ChevalleyDatumPointsEquiv_map]

/-- The inverse point isomorphism intertwines `SpStd.frobenius 1 p k A` with the Frobenius of
`b2ChevalleyDatum`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type v) [CommRing A]
    [ExpChar A p] (g : points 1 A) :
    (b2ChevalleyDatumPointsEquiv A).symm (frobenius 1 p k A g) =
      b2ChevalleyDatum.frobenius p k A ((b2ChevalleyDatumPointsEquiv A).symm g) := by
  rw [MulEquiv.symm_apply_eq, b2ChevalleyDatumPointsEquiv_frobenius, MulEquiv.apply_symm_apply]

end

end TauCeti.SpStd
