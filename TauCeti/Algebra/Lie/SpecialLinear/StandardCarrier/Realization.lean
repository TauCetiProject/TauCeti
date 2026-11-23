/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Datum
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius
import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr

/-!
# Realizing the standard type-`A_r` Chevalley datum on the explicit carrier

The Chevalley datum `TauCeti.SlStd.chevalleyDatum r ht` and the explicit full-weight carrier
`TauCeti.SlStd.groupScheme r` act on the same lattice `TauCeti.SlStd.lattice r`, in the same
coordinate basis, with the same weights `TauCeti.SlStd.weight r` and, by
`TauCeti.SlStd.pinnedRepresentation_ι_rootGenerator`, with the same numbered root operators.
Consequently their integral toral defining Hopf ideals inside `O(GL_{r+1})` are equal over `ℤ`
(`TauCeti.SlStd.kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal`). Their group schemes
over `ℤ` and their subgroups of `GL_{r+1}(A)` therefore coincide for every commutative ring `A`,
including nonreduced rings and rings of positive characteristic.

`TauCeti.SlStd.chevalleyDatumPointsEquiv` packages the resulting group isomorphism
`(chevalleyDatum r ht).points A ≃* points r A`, which is the identity on matrices. Across it,
the positive and negative simple root subgroups of the datum are the numbered raising and lowering
subgroups of the carrier with the same number and the same additive parameter, the torus of the
datum is the weight torus of the carrier with the same parameters, and the functorial maps along
ring homomorphisms and the `p ^ k`-power Frobenius maps of the two sides agree. Every root subgroup
of the datum, at every root of `A_r`, is injective over every commutative ring.

This is the type-`A_r` input to Chevalley's comparison theorem for the standard special linear
model: the explicit carrier is the group scheme of a full-weight Chevalley datum of type `A_r`,
with matching pinning, torus and Frobenius.

## Main definitions

* `TauCeti.SlStd.chevalleyDatumPointsEquiv`: the isomorphism between the points of the datum and
  the points of the explicit carrier over any commutative ring.

## Main results

* `TauCeti.SlStd.kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal`,
  `TauCeti.SlStd.chevalleyDatum_groupScheme` and `TauCeti.SlStd.chevalleyDatum_points`: equality
  of the integral defining Hopf ideals, of the group schemes over `ℤ` and of the point subgroups.
* `TauCeti.SlStd.chevalleyDatum_groupSchemeι`: the closed immersion of the datum into `GL_{r+1}`
  is `TauCeti.SlStd.carrierι r`.
* `TauCeti.SlStd.chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex`,
  `TauCeti.SlStd.chevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex` and
  `TauCeti.SlStd.chevalleyDatumPointsEquiv_torusPoints`, with their inverse forms: the pinning
  and torus equations.
* `TauCeti.SlStd.chevalleyDatumPointsEquiv_map` and
  `TauCeti.SlStd.chevalleyDatumPointsEquiv_frobenius`: naturality in the value ring and
  compatibility with Frobenius.
* `TauCeti.SlStd.chevalleyDatum_rootSubgroupPoints_injective`: injectivity of every root
  subgroup of the datum.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.

The realization API follows `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Realization`.
-/

public section

namespace TauCeti.SlStd

open AlgebraicGeometry CategoryTheory
open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

variable (r : ℕ) (ht : (DynkinType.A r).Valid)

/-! ## Equality of the integral defining ideals, group schemes and point subgroups -/

/-- **The integral defining Hopf ideal of the standard type-`A_r` datum is `definingIdeal r`.**
Both are toral closures on the same lattice, basis and weights, whose numbered root operators
agree. -/
theorem kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal :
    kostantToralDefiningIdeal ((DynkinType.A r).lieBasis ht).rootGenerator
        ((DynkinType.A r).lieBasis ht).h (chevalleyDatum r ht).representation
        (chevalleyDatum r ht).lattice (chevalleyDatum r ht).representation_mem_lattice
        (chevalleyDatum r ht).isNilpotent_representation_rootGenerator
        (chevalleyDatum r ht).basis (chevalleyDatum r ht).coordinateWeight =
      definingIdeal r := by
  rw [chevalleyDatum_coordinateWeight, definingIdeal_def]
  have hn := (chevalleyDatum r ht).isNilpotent_representation_rootGenerator
  dsimp only [chevalleyDatum] at hn ⊢
  exact kostantToralDefiningIdeal_eq_of_operator_eq
    (e := ((DynkinType.A r).lieBasis ht).rootGenerator) (h := ((DynkinType.A r).lieBasis ht).h)
    (ρ := pinnedRepresentation r ht) (M := (lattice r).toAddSubgroup)
    (hM := pinnedRepresentation_kostantForm_mem_lattice r ht) (b := latticeBasis r)
    (e' := rootGenerator r) (h' := cartanGenerator r) (ρ' := rep r)
    (hM' := rep_kostantForm_mem_lattice r) (hnil := hn)
    (hnil' := isNilpotent_rep_rootGenerator r) (wt := weight r)
    (hop := pinnedRepresentation_ι_rootGenerator r ht)

/-- **The integral group scheme of the standard type-`A_r` datum is `SlStd.groupScheme r`.** -/
theorem chevalleyDatum_groupScheme : (chevalleyDatum r ht).groupScheme = groupScheme r := by
  have h := kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal r ht
  rw [DynkinType.ChevalleyDatum.groupScheme, kostantToralGroupScheme, groupScheme,
    kostantToralGroupScheme]
  dsimp only [chevalleyDatum] at h ⊢
  rw [h]

/-- The closed immersion of the group scheme of the standard type-`A_r` datum into `GL_{r+1}`
agrees with `carrierι r` across `chevalleyDatum_groupScheme`. -/
theorem chevalleyDatum_groupSchemeι :
    (chevalleyDatum r ht).groupSchemeι =
      eqToHom (chevalleyDatum_groupScheme r ht) ≫ carrierι r := by
  have h := (kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal r ht).trans
    (definingIdeal_def r)
  rw [DynkinType.ChevalleyDatum.groupSchemeι_def, carrierι_def,
    kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def, ← Category.assoc]
  exact congrArg (· ≫ eqToHom (GeneralLinear.groupScheme_def ℤ (r + 1)).symm)
    (CommHopfAlgCat.eqToHom_comp_quotientSpecι _ h).symm

/-- **The point subgroup of the standard type-`A_r` datum over any commutative ring `A` is
`points r A`.** -/
theorem chevalleyDatum_points (A : Type v) [CommRing A] :
    (chevalleyDatum r ht).points A = points r A := by
  have h := kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal r ht
  rw [DynkinType.ChevalleyDatum.points_def, points_def]
  dsimp only [chevalleyDatum] at h ⊢
  rw [h]

/-! ## The isomorphism on points and its action on generators -/

/-- **The group isomorphism between the points of the standard type-`A_r` datum and
`SlStd.points r A`** over any commutative ring `A`, induced by the equality of matrix subgroups
of `GL_{r+1}(A)`. -/
def chevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    (chevalleyDatum r ht).points A ≃* points r A :=
  MulEquiv.subgroupCongr (chevalleyDatum_points r ht A)

/-- `chevalleyDatumPointsEquiv` is the identity on underlying invertible matrices. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : (chevalleyDatum r ht).points A) :
    (chevalleyDatumPointsEquiv r ht A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      (g : Matrix.GeneralLinearGroup (Fin (chevalleyDatum r ht).dim) A) :=
  (rfl)

/-- The inverse of `chevalleyDatumPointsEquiv` is the identity on underlying invertible
matrices. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A] (g : points r A) :
    ((chevalleyDatumPointsEquiv r ht A).symm g :
        Matrix.GeneralLinearGroup (Fin (chevalleyDatum r ht).dim) A) =
      (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :=
  (rfl)

/-- **The positive simple root subgroup of the datum at node `i` is the raising subgroup of the
carrier at node `i`.** -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex (i : Fin (DynkinType.A r).rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv r ht A
        ((chevalleyDatum r ht).rootSubgroupPoints ((DynkinType.A r).simpleIndex ht i) A u) =
      rootSubgroupPoints r (.inl i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_simpleIndex, coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pinnedRepresentation_ι_rootGenerator r ht (.inl i)) _

/-- **The negative simple root subgroup of the datum at node `i` is the lowering subgroup of the
carrier at node `i`.** -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex
    (i : Fin (DynkinType.A r).rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv r ht A
        ((chevalleyDatum r ht).rootSubgroupPoints
          (((DynkinType.A r).simplyConnectedRootDatum ht).reflectionPerm
            ((DynkinType.A r).simpleIndex ht i) ((DynkinType.A r).simpleIndex ht i)) A u) =
      rootSubgroupPoints r (.inr i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex,
    coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pinnedRepresentation_ι_rootGenerator r ht (.inr i)) _

/-- The inverse point isomorphism carries the raising subgroup of the carrier at node `i` to the
positive simple root subgroup of the datum at node `i`. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl (i : Fin r) (A : Type v)
    [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv r ht A).symm (rootSubgroupPoints r (.inl i) A u) =
      (chevalleyDatum r ht).rootSubgroupPoints ((DynkinType.A r).simpleIndex ht i) A u := by
  rw [MulEquiv.symm_apply_eq]
  exact (chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex r ht i A u).symm

/-- The inverse point isomorphism carries the lowering subgroup of the carrier at node `i` to the
negative simple root subgroup of the datum at node `i`. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr (i : Fin r) (A : Type v)
    [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv r ht A).symm (rootSubgroupPoints r (.inr i) A u) =
      (chevalleyDatum r ht).rootSubgroupPoints
        (((DynkinType.A r).simplyConnectedRootDatum ht).reflectionPerm
          ((DynkinType.A r).simpleIndex ht i) ((DynkinType.A r).simpleIndex ht i)) A u := by
  rw [MulEquiv.symm_apply_eq]
  exact (chevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex r ht i A u).symm

/-- **The torus point of the datum with parameter `s` is the weight-torus point of the carrier
with the same parameter.** -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin (DynkinType.A r).rank → Aˣ) :
    chevalleyDatumPointsEquiv r ht A ((chevalleyDatum r ht).torusPoints A s) =
      weightTorusPoints r A s := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, DynkinType.ChevalleyDatum.coe_torusPoints,
    kostantTorusMatrix_apply, chevalleyDatum_coordinateWeight]
  -- The datum torus is the same diagonal matrix, written with the datum's dimension `r + 1`, so
  -- the carrier equation is applied rather than rewritten into the goal.
  exact (coe_weightTorusPoints r A s).symm

/-- The inverse point isomorphism carries the weight-torus point of the carrier with parameter
`s` to the torus point of the datum with the same parameter. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin r → Aˣ) :
    (chevalleyDatumPointsEquiv r ht A).symm (weightTorusPoints r A s) =
      (chevalleyDatum r ht).torusPoints A s := by
  rw [MulEquiv.symm_apply_eq]
  exact (chevalleyDatumPointsEquiv_torusPoints r ht A s).symm

/-! ## Functoriality in the value ring and Frobenius -/

/-- `chevalleyDatumPointsEquiv` is natural with respect to ring homomorphisms `A →+* B`. -/
theorem chevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : (chevalleyDatum r ht).points A) :
    chevalleyDatumPointsEquiv r ht B
        (((chevalleyDatum r ht).pointsPresentation A).map
          ((chevalleyDatum r ht).pointsPresentation B) f g) =
      (pointsPresentation r A).map (pointsPresentation r B) f
        (chevalleyDatumPointsEquiv r ht A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map, coe_chevalleyDatumPointsEquiv]
  -- Match the exposed datum dimension `(chevalleyDatum r ht).dim` with `r + 1`.
  rfl

/-- **The point isomorphism intertwines the `p ^ k`-power Frobenius of the datum with
`SlStd.frobenius r p k A`.** -/
@[simp]
theorem chevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : (chevalleyDatum r ht).points A) :
    chevalleyDatumPointsEquiv r ht A ((chevalleyDatum r ht).frobenius p k A g) =
      frobenius r p k A (chevalleyDatumPointsEquiv r ht A g) := by
  rw [DynkinType.ChevalleyDatum.frobenius_def, frobenius_eq_map, chevalleyDatumPointsEquiv_map]

/-- The inverse point isomorphism intertwines `SlStd.frobenius r p k A` with the Frobenius of the
datum. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type v) [CommRing A]
    [ExpChar A p] (g : points r A) :
    (chevalleyDatumPointsEquiv r ht A).symm (frobenius r p k A g) =
      (chevalleyDatum r ht).frobenius p k A ((chevalleyDatumPointsEquiv r ht A).symm g) := by
  rw [MulEquiv.symm_apply_eq, chevalleyDatumPointsEquiv_frobenius, MulEquiv.apply_symm_apply]

/-! ## Injectivity of every root subgroup -/

/-- **Every root subgroup of the standard type-`A_r` datum is injective**, at every root of
`A_r` and over every commutative ring. -/
theorem chevalleyDatum_rootSubgroupPoints_injective (γ : Fin (DynkinType.A r).numRoots)
    (A : Type v) [CommRing A] :
    Function.Injective ((chevalleyDatum r ht).rootSubgroupPoints γ A) := by
  refine (chevalleyDatum r ht).rootSubgroupPoints_injective_of_simple A (fun i => ?_) γ
  intro u v huv
  have h := congrArg (fun g => (chevalleyDatumPointsEquiv r ht A g :
    Matrix.GeneralLinearGroup (Fin (r + 1)) A)) huv
  simp only [chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex,
    coe_rootSubgroupPoints_eq_transvectionUnit] at h
  exact Multiplicative.toAdd.injective
    (transvectionUnit_injective (rootTarget_ne_rootSource r (.inl i)) h)

end

end TauCeti.SlStd
