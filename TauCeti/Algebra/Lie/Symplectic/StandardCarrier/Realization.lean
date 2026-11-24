/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Datum
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.OperatorCongr

/-!
# Realizing the standard symplectic Chevalley datum on the explicit carrier

The Chevalley datum `TauCeti.SpStd.chevalleyDatum n ht` of type `C_(n+1)` and the explicit
full-weight carrier `TauCeti.SpStd.groupScheme n` act on the same lattice
`TauCeti.SpStd.lattice n`, in the same coordinate basis, with the same weights
`TauCeti.SpStd.basisWeight n` and, by `TauCeti.SpStd.pinnedRepresentation_ι_rootGenerator`, with
the same numbered root operators. Consequently their integral toral defining Hopf ideals inside
`O(GL_(2n+2))` are equal over `ℤ`
(`TauCeti.SpStd.kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal`). Their group schemes
over `ℤ` and their subgroups of `GL_(2n+2)(A)` therefore coincide for every commutative ring `A`,
including nonreduced rings and rings of positive characteristic.

`TauCeti.SpStd.chevalleyDatumPointsEquiv` packages the resulting group isomorphism
`(chevalleyDatum n ht).points A ≃* points n A`, which is the identity on matrices. Across it, the
positive and negative simple root subgroups of the datum are the numbered raising and lowering
subgroups of the carrier with the same Bourbaki node and the same additive parameter, the torus of
the datum is the weight torus of the carrier with the same parameters, and the functorial maps
along ring homomorphisms and the `p ^ k`-power Frobenius maps of the two sides agree. Every root
subgroup of the datum, at every root of `C_(n+1)`, is injective over every commutative ring.

Thus the explicit symplectic carrier is the group scheme of a full-weight Chevalley datum of type
`C_(n+1)`, with matching pinning, torus and Frobenius: the form in which Chevalley's comparison
theorem for data with the same weight lattice applies to it.

## Main definitions

* `TauCeti.SpStd.chevalleyDatumPointsEquiv`: the isomorphism between the points of the datum and
  the points of the explicit carrier over any commutative ring.

## Main results

* `TauCeti.SpStd.kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal`,
  `TauCeti.SpStd.chevalleyDatum_groupScheme` and `TauCeti.SpStd.chevalleyDatum_points`: equality
  of the integral defining Hopf ideals, of the group schemes over `ℤ` and of the point subgroups.
* `TauCeti.SpStd.chevalleyDatum_groupSchemeι`: the closed immersion of the datum into
  `GL_(2n+2)` is `TauCeti.SpStd.carrierι n`.
* `TauCeti.SpStd.chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex`,
  `TauCeti.SpStd.chevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex` and
  `TauCeti.SpStd.chevalleyDatumPointsEquiv_torusPoints`, with their inverse forms: the pinning
  and torus equations.
* `TauCeti.SpStd.chevalleyDatumPointsEquiv_map` and
  `TauCeti.SpStd.chevalleyDatumPointsEquiv_frobenius`: naturality in the value ring and
  compatibility with Frobenius.
* `TauCeti.SpStd.chevalleyDatum_rootSubgroupPoints_injective`: injectivity of every root
  subgroup of the datum.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.

The realization API follows `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Realization`.
-/

public section

namespace TauCeti.SpStd

open AlgebraicGeometry CategoryTheory
open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

variable (n : ℕ) (ht : (DynkinType.C (n + 1)).Valid)

/-! ## Equality of the integral defining ideals, group schemes and point subgroups -/

/-- **The integral defining Hopf ideal of the standard symplectic datum of type `C_(n+1)` is
`definingIdeal n`.** Both are toral closures on the same lattice, basis and weights, whose numbered
root operators agree. -/
theorem kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal :
    kostantToralDefiningIdeal ((DynkinType.C (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.C (n + 1)).lieBasis ht).h (chevalleyDatum n ht).representation
        (chevalleyDatum n ht).lattice (chevalleyDatum n ht).representation_mem_lattice
        (chevalleyDatum n ht).isNilpotent_representation_rootGenerator
        (chevalleyDatum n ht).basis (chevalleyDatum n ht).coordinateWeight =
      definingIdeal n := by
  rw [chevalleyDatum_coordinateWeight, definingIdeal_def]
  have hn := (chevalleyDatum n ht).isNilpotent_representation_rootGenerator
  dsimp only [chevalleyDatum] at hn ⊢
  exact kostantToralDefiningIdeal_eq_of_operator_eq
    (e := ((DynkinType.C (n + 1)).lieBasis ht).rootGenerator)
    (h := ((DynkinType.C (n + 1)).lieBasis ht).h)
    (ρ := pinnedRepresentation n ht) (M := (lattice n).toAddSubgroup)
    (hM := pinnedRepresentation_kostantForm_mem_lattice n ht) (b := latticeBasis n)
    (e' := rootGenerator n) (h' := cartanGenerator n) (ρ' := rep n)
    (hM' := rep_kostantForm_mem_lattice n) (hnil := hn)
    (hnil' := isNilpotent_rep_rootGenerator n) (wt := basisWeight n)
    (hop := pinnedRepresentation_ι_rootGenerator n ht)

/-- **The integral group scheme of the standard symplectic datum of type `C_(n+1)` is
`SpStd.groupScheme n`.** -/
theorem chevalleyDatum_groupScheme : (chevalleyDatum n ht).groupScheme = groupScheme n := by
  have h := kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal n ht
  rw [DynkinType.ChevalleyDatum.groupScheme, kostantToralGroupScheme, groupScheme_def]
  dsimp only [chevalleyDatum] at h ⊢
  rw [h]

/-- The closed immersion of the group scheme of the standard symplectic datum into `GL_(2n+2)`
agrees with `carrierι n` across `chevalleyDatum_groupScheme`. -/
theorem chevalleyDatum_groupSchemeι :
    (chevalleyDatum n ht).groupSchemeι =
      eqToHom (chevalleyDatum_groupScheme n ht) ≫ carrierι n := by
  have h := (kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal n ht).trans
    (definingIdeal_def n)
  rw [DynkinType.ChevalleyDatum.groupSchemeι_def, carrierι_def,
    kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def, ← Category.assoc]
  exact congrArg (· ≫ eqToHom (GeneralLinear.groupScheme_def ℤ ((n + 1) + (n + 1))).symm)
    (CommHopfAlgCat.eqToHom_comp_quotientSpecι _ h).symm

/-- **The point subgroup of the standard symplectic datum of type `C_(n+1)` over any commutative
ring `A` is `points n A`.** -/
theorem chevalleyDatum_points (A : Type v) [CommRing A] :
    (chevalleyDatum n ht).points A = points n A := by
  have h := kostantToralDefiningIdeal_chevalleyDatum_eq_definingIdeal n ht
  rw [DynkinType.ChevalleyDatum.points_def, points_def]
  dsimp only [chevalleyDatum] at h ⊢
  rw [h]

/-! ## The isomorphism on points and its action on generators -/

/-- **The group isomorphism between the points of the standard symplectic datum of type `C_(n+1)`
and `SpStd.points n A`** over any commutative ring `A`, induced by the equality of matrix subgroups
of `GL_(2n+2)(A)`. -/
def chevalleyDatumPointsEquiv (A : Type v) [CommRing A] :
    (chevalleyDatum n ht).points A ≃* points n A :=
  MulEquiv.subgroupCongr (chevalleyDatum_points n ht A)

/-- `chevalleyDatumPointsEquiv` is the identity on underlying invertible matrices. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv (A : Type v) [CommRing A]
    (g : (chevalleyDatum n ht).points A) :
    (chevalleyDatumPointsEquiv n ht A g :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      (g : Matrix.GeneralLinearGroup (Fin (chevalleyDatum n ht).dim) A) :=
  (rfl)

/-- The inverse of `chevalleyDatumPointsEquiv` is the identity on underlying invertible
matrices. -/
@[simp]
theorem coe_chevalleyDatumPointsEquiv_symm (A : Type v) [CommRing A] (g : points n A) :
    ((chevalleyDatumPointsEquiv n ht A).symm g :
        Matrix.GeneralLinearGroup (Fin (chevalleyDatum n ht).dim) A) =
      (g : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :=
  (rfl)

/-- **The positive simple root subgroup of the datum at node `i` is the raising subgroup of the
carrier at node `i`.** -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex
    (i : Fin (DynkinType.C (n + 1)).rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv n ht A
        ((chevalleyDatum n ht).rootSubgroupPoints ((DynkinType.C (n + 1)).simpleIndex ht i) A u) =
      rootSubgroupPoints n (.inl i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_simpleIndex, coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pinnedRepresentation_ι_rootGenerator n ht (.inl i)) _

/-- **The negative simple root subgroup of the datum at node `i` is the lowering subgroup of the
carrier at node `i`.** -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex
    (i : Fin (DynkinType.C (n + 1)).rank) (A : Type v) [CommRing A] (u : Multiplicative A) :
    chevalleyDatumPointsEquiv n ht A
        ((chevalleyDatum n ht).rootSubgroupPoints
          (((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).reflectionPerm
            ((DynkinType.C (n + 1)).simpleIndex ht i)
            ((DynkinType.C (n + 1)).simpleIndex ht i)) A u) =
      rootSubgroupPoints n (.inr i) A u := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv,
    DynkinType.ChevalleyDatum.coe_rootSubgroupPoints_reflectionPerm_simpleIndex,
    coe_rootSubgroupPoints]
  exact kostantRootSubgroupMatrix_eq_of_operator_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pinnedRepresentation_ι_rootGenerator n ht (.inr i)) _

/-- The inverse point isomorphism carries the raising subgroup of the carrier at node `i` to the
positive simple root subgroup of the datum at node `i`. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inl (i : Fin (n + 1)) (A : Type v)
    [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv n ht A).symm (rootSubgroupPoints n (.inl i) A u) =
      (chevalleyDatum n ht).rootSubgroupPoints ((DynkinType.C (n + 1)).simpleIndex ht i) A u := by
  rw [MulEquiv.symm_apply_eq]
  exact (chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex n ht i A u).symm

/-- The inverse point isomorphism carries the lowering subgroup of the carrier at node `i` to the
negative simple root subgroup of the datum at node `i`. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_rootSubgroupPoints_inr (i : Fin (n + 1)) (A : Type v)
    [CommRing A] (u : Multiplicative A) :
    (chevalleyDatumPointsEquiv n ht A).symm (rootSubgroupPoints n (.inr i) A u) =
      (chevalleyDatum n ht).rootSubgroupPoints
        (((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).reflectionPerm
          ((DynkinType.C (n + 1)).simpleIndex ht i) ((DynkinType.C (n + 1)).simpleIndex ht i))
        A u := by
  rw [MulEquiv.symm_apply_eq]
  exact (chevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex n ht i A u).symm

/-- **The torus point of the datum with parameter `s` is the weight-torus point of the carrier
with the same parameter.** -/
@[simp↓]
theorem chevalleyDatumPointsEquiv_torusPoints (A : Type v) [CommRing A]
    (s : Fin (DynkinType.C (n + 1)).rank → Aˣ) :
    chevalleyDatumPointsEquiv n ht A ((chevalleyDatum n ht).torusPoints A s) =
      weightTorusPoints n A s := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, DynkinType.ChevalleyDatum.coe_torusPoints,
    chevalleyDatum_coordinateWeight]
  -- The datum torus is the same diagonal matrix, written with the datum's dimension
  -- `(n + 1) + (n + 1)`, so the carrier equation is applied rather than rewritten into the goal.
  exact (coe_weightTorusPoints n A s).symm

/-- The inverse point isomorphism carries the weight-torus point of the carrier with parameter
`s` to the torus point of the datum with the same parameter. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin (n + 1) → Aˣ) :
    (chevalleyDatumPointsEquiv n ht A).symm (weightTorusPoints n A s) =
      (chevalleyDatum n ht).torusPoints A s := by
  rw [MulEquiv.symm_apply_eq]
  exact (chevalleyDatumPointsEquiv_torusPoints n ht A s).symm

/-! ## Functoriality in the value ring and Frobenius -/

/-- `chevalleyDatumPointsEquiv` is natural with respect to ring homomorphisms `A →+* B`. -/
theorem chevalleyDatumPointsEquiv_map {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) (g : (chevalleyDatum n ht).points A) :
    chevalleyDatumPointsEquiv n ht B
        (((chevalleyDatum n ht).pointsPresentation A).map
          ((chevalleyDatum n ht).pointsPresentation B) f g) =
      (pointsPresentation n A).map (pointsPresentation n B) f
        (chevalleyDatumPointsEquiv n ht A g) := by
  apply Subtype.ext
  rw [coe_chevalleyDatumPointsEquiv, GeneralLinear.IntegralPointsPresentation.coe_map,
    GeneralLinear.IntegralPointsPresentation.coe_map, coe_chevalleyDatumPointsEquiv]
  -- Match the exposed datum dimension `(chevalleyDatum n ht).dim` with `(n + 1) + (n + 1)`.
  rfl

/-- **The point isomorphism intertwines the `p ^ k`-power Frobenius of the datum with
`SpStd.frobenius n p k A`.** -/
@[simp]
theorem chevalleyDatumPointsEquiv_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (g : (chevalleyDatum n ht).points A) :
    chevalleyDatumPointsEquiv n ht A ((chevalleyDatum n ht).frobenius p k A g) =
      frobenius n p k A (chevalleyDatumPointsEquiv n ht A g) := by
  rw [DynkinType.ChevalleyDatum.frobenius_def, frobenius_eq_map, chevalleyDatumPointsEquiv_map]

/-- The inverse point isomorphism intertwines `SpStd.frobenius n p k A` with the Frobenius of the
datum. -/
@[simp]
theorem chevalleyDatumPointsEquiv_symm_frobenius (p k : ℕ) (A : Type v) [CommRing A]
    [ExpChar A p] (g : points n A) :
    (chevalleyDatumPointsEquiv n ht A).symm (frobenius n p k A g) =
      (chevalleyDatum n ht).frobenius p k A ((chevalleyDatumPointsEquiv n ht A).symm g) := by
  rw [MulEquiv.symm_apply_eq, chevalleyDatumPointsEquiv_frobenius, MulEquiv.apply_symm_apply]

/-! ## Injectivity of every root subgroup -/

/-- **Every root subgroup of the standard symplectic datum of type `C_(n+1)` is injective**, at
every root of `C_(n+1)` and over every commutative ring. -/
theorem chevalleyDatum_rootSubgroupPoints_injective (γ : Fin (DynkinType.C (n + 1)).numRoots)
    (A : Type v) [CommRing A] :
    Function.Injective ((chevalleyDatum n ht).rootSubgroupPoints γ A) := by
  refine (chevalleyDatum n ht).rootSubgroupPoints_injective_of_simple A (fun i => ?_) γ
  intro u v huv
  exact rootSubgroupPoints_injective n (.inl i) A (by
    simpa only [chevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex] using
      congrArg (chevalleyDatumPointsEquiv n ht A) huv)

end

end TauCeti.SpStd
