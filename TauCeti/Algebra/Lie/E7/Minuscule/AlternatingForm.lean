/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.AlternatingForm
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.ConstantForm
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic

/-!
# The invariant alternating form of the full-weight type-E7 minuscule carrier

The negation index of the type-`E₇` minuscule weight table pairs each of the fifty-six weights
with its negative, and the alternating sign of the weight graph, normalized to `1` at `ϖ₇`,
supplies the entries: the form `J` has entry `e7MinusculeSign a` at `(a, indexNeg a)` and zero
elsewhere. It is skew, alternating in every characteristic, and squares to `-1`, so it is
unimodular over every commutative ring.

The numbered root subgroups and the weight torus of `TauCeti.E7Minuscule.groupScheme` preserve
`J`, so the form relations lie in the defining Hopf ideal of the carrier. This gives a closed
immersion of the carrier into `ConstantForm.groupScheme ℤ 56 (alternatingForm ℤ)`, the subgroup
scheme of `GL₅₆` preserving `J`, whose composite with the inclusion into `GL₅₆` is `carrierι`.
On matrix points, `g J gᵀ = J` and `gᵀ J g = J` for every point `g` of the carrier, and a scalar
point `c • 1` has `c ^ 2 = 1`. Nothing here identifies the carrier with the symplectic group of
`J`, asserts reductivity, or computes the centre of the carrier.

## Main definitions

* `TauCeti.E7Minuscule.signedNegation`: the negation index and the signs of the weight table.
* `TauCeti.E7Minuscule.alternatingForm`: the integral form `J`, read in any coefficient ring.
* `TauCeti.E7Minuscule.toConstantForm`: the closed immersion of the carrier into the subgroup
  scheme of `GL₅₆` preserving `J`.

## Main results

* `TauCeti.E7Minuscule.alternatingForm_transpose`, `alternatingForm_mul_self` and
  `dotProduct_alternatingForm_mulVec_self`: `J` is skew, squares to `-1` and is alternating.
* `TauCeti.E7Minuscule.isUnit_alternatingForm`: the minuscule form is a unit.
* `TauCeti.E7Minuscule.alternatingFormDefiningHopfIdeal_le_definingIdeal`: the form relations
  lie in the defining ideal of the carrier.
* `TauCeti.E7Minuscule.mul_alternatingForm_mul_transpose_of_mem_points` and
  `transpose_mul_alternatingForm_mul_of_mem_points`: every point preserves `J` in the row and in
  the column convention.
* `TauCeti.E7Minuscule.scalar_sq_eq_one_of_mem_points`: a scalar point has scalar of square one.
* `TauCeti.E7Minuscule.toConstantForm_comp_inclusion`: the closed immersion recovers `carrierι`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
* The formal organization follows `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.AlternatingForm`:
  root and torus invariance of the generic matrices, the inclusion of defining Hopf ideals, the
  points criterion, and the closed immersion with its composite into the ambient group.
-/

public section

open scoped Matrix
open TauCeti.DynkinType CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.E7Minuscule

/-- The negation index of the type-`E₇` minuscule weight table, with the alternating signs of
the weight graph. -/
noncomputable def signedNegation : weightTable.SignedNegation where
  indexNeg a := (exists_e7MinusculeWeight_eq_neg a).choose
  weight_indexNeg a i := by
    simpa only [weightTable_weight, Pi.neg_apply] using
      congrFun (exists_e7MinusculeWeight_eq_neg a).choose_spec i
  sign := e7MinusculeSign
  sign_mul_self := e7MinusculeSign_mul_self
  sign_indexNeg a := e7MinusculeSign_eq_neg_of_weight_eq_neg a _
    (exists_e7MinusculeWeight_eq_neg a).choose_spec
  sign_reflection i a h := by
    simpa only [weightTable_reflection] using
      e7MinusculeSign_reflection i a (by simpa only [weightTable_weight] using h)

@[simp]
theorem signedNegation_sign : signedNegation.sign = e7MinusculeSign := by
  rfl

/-- The weight at the negation index of `a` is the negative of the weight at `a`. -/
@[simp]
theorem e7MinusculeWeight_signedNegation_indexNeg (a : Fin 56) :
    e7MinusculeWeight (signedNegation.indexNeg a) = -e7MinusculeWeight a := by
  simpa only [weightTable_weight] using
    (signedNegation.indexNeg_eq_iff_weight_eq_neg a _).mp rfl

/-- The sign at the negation index of `a` is the negative of the sign at `a`. -/
@[simp]
theorem e7MinusculeSign_signedNegation_indexNeg (a : Fin 56) :
    e7MinusculeSign (signedNegation.indexNeg a) = -e7MinusculeSign a := by
  rw [← signedNegation_sign]
  exact signedNegation.sign_indexNeg a

/-- The integral minuscule alternating form, read in any coefficient ring. -/
noncomputable def alternatingForm (R : Type*) [CommRing R] : Matrix (Fin 56) (Fin 56) R :=
  signedNegation.form R

variable (R : Type*) [CommRing R]

/-- The minuscule alternating form is the form of the signed negation of the weight table. -/
theorem alternatingForm_def : alternatingForm R = signedNegation.form R := by
  rfl

@[simp]
theorem alternatingForm_apply_indexNeg (a : Fin 56) :
    alternatingForm R a (signedNegation.indexNeg a) = (e7MinusculeSign a : R) := by
  rw [alternatingForm_def, signedNegation.form_apply_indexNeg, signedNegation_sign]

@[simp]
theorem alternatingForm_apply_of_ne {a b : Fin 56} (h : b ≠ signedNegation.indexNeg a) :
    alternatingForm R a b = 0 := by
  rw [alternatingForm_def, signedNegation.form_apply_of_ne R h]

/-- The minuscule form vanishes on the diagonal. -/
@[simp]
theorem alternatingForm_apply_self (a : Fin 56) : alternatingForm R a a = 0 := by
  rw [alternatingForm_def, signedNegation.form_apply_self]

/-- The minuscule form is skew: `Jᵀ = -J`. -/
@[simp]
theorem alternatingForm_transpose : (alternatingForm R)ᵀ = -alternatingForm R :=
  signedNegation.form_transpose R

/-- The minuscule form is unimodular, with `J * J = -1`. -/
@[simp]
theorem alternatingForm_mul_self : alternatingForm R * alternatingForm R = -1 :=
  signedNegation.form_mul_self R

/-- The minuscule form is a unit, with inverse its negative. -/
theorem isUnit_alternatingForm : IsUnit (alternatingForm R) := by
  rw [alternatingForm_def]
  exact signedNegation.isUnit_form R

/-- The minuscule form is alternating, including in characteristic two. -/
@[simp]
theorem dotProduct_alternatingForm_mulVec_self (x : Fin 56 → R) :
    dotProduct x ((alternatingForm R).mulVec x) = 0 :=
  signedNegation.dotProduct_form_mulVec_self R x

@[simp]
theorem alternatingForm_map {S : Type*} [CommRing S] (f : R →+* S) :
    (alternatingForm R).map f = alternatingForm S :=
  signedNegation.form_map R f

/-- All numbered root-subgroup points preserve the minuscule form. -/
private theorem rootSubgroupPoints_preserves_alternatingForm (k : Fin 7 ⊕ Fin 7)
    (u : Multiplicative R) :
    ((rootSubgroupPoints k R u : Matrix.GeneralLinearGroup (Fin 56) R) :
        Matrix (Fin 56) (Fin 56) R) * alternatingForm R *
      ((rootSubgroupPoints k R u : Matrix.GeneralLinearGroup (Fin 56) R) :
        Matrix (Fin 56) (Fin 56) R)ᵀ = alternatingForm R := by
  cases k with
  | inl i =>
      rw [coe_rootSubgroupPoints_inl]
      simpa only [weightTable_raisingMatrix, alternatingForm] using
        signedNegation.one_add_smul_raisingMatrix_preserves_form R i (Multiplicative.toAdd u)
  | inr i =>
      rw [coe_rootSubgroupPoints_inr]
      simpa only [weightTable_loweringMatrix, alternatingForm] using
        signedNegation.one_add_smul_loweringMatrix_preserves_form R i (Multiplicative.toAdd u)

/-! ## Universal root and torus identities -/

local notation "rootGen" => TauCeti.serreRootGenerator (CartanMatrix.E 7)
local notation "cartanGen" => TauCeti.serreH ℚ (CartanMatrix.E 7)

private theorem rootMatrix_preserves_alternatingForm (A : Type*) [CommRing A]
    (k : Fin 7 ⊕ Fin 7) (p : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ((UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix rootGen cartanGen rep
        lattice.toAddSubgroup rep_kostantForm_mem_lattice k
        (isNilpotent_rep_serreRootGenerator k) latticeBasis p) : Matrix (Fin 56) (Fin 56) A) *
      alternatingForm A *
      ((UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix rootGen cartanGen rep
        lattice.toAddSubgroup rep_kostantForm_mem_lattice k
        (isNilpotent_rep_serreRootGenerator k) latticeBasis p) : Matrix (Fin 56) (Fin 56) A)ᵀ =
      alternatingForm A := by
  have h := rootSubgroupPoints_preserves_alternatingForm A k
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ)) p)
  rwa [coe_rootSubgroupPoints,
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ)).symm_apply_apply p] at h

private theorem rootCoordinateMap_preserves_alternatingForm (k : Fin 7 ⊕ Fin 7) :
    (GeneralLinear.genericMatrix ℤ 56).map
        (UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap rootGen cartanGen rep
          lattice.toAddSubgroup rep_kostantForm_mem_lattice k
          (isNilpotent_rep_serreRootGenerator k) latticeBasis).hom.toAlgHom *
      (alternatingForm ℤ).map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) *
      ((GeneralLinear.genericMatrix ℤ 56).map
        (UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap rootGen cartanGen rep
          lattice.toAddSubgroup rep_kostantForm_mem_lattice k
          (isNilpotent_rep_serreRootGenerator k) latticeBasis).hom.toAlgHom)ᵀ =
      (alternatingForm ℤ).map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) := by
  rw [alternatingForm_map,
    UniversalEnvelopingAlgebra.map_genericMatrix_eq_kostantRootSubgroupMatrix]
  exact rootMatrix_preserves_alternatingForm _ k _

private theorem torusCoordinateMap_preserves_alternatingForm :
    (GeneralLinear.genericMatrix ℤ 56).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) e7MinusculeWeight).hom.toAlgHom *
      (alternatingForm ℤ).map (algebraMap ℤ
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin 7))).obj) *
      ((GeneralLinear.genericMatrix ℤ 56).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) e7MinusculeWeight).hom.toAlgHom)ᵀ =
      (alternatingForm ℤ).map (algebraMap ℤ
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin 7))).obj) := by
  rw [alternatingForm_map, GeneralLinear.map_genericMatrix_weightTorusCoordinateMap]
  refine Matrix.diagonal_mul_mul_transpose_diagonal _ _ fun a b ↦ ?_
  by_cases h : b = signedNegation.indexNeg a
  · subst h
    rw [alternatingForm_apply_indexNeg, mul_right_comm, e7MinusculeWeight_signedNegation_indexNeg,
      SplitTorus.single_weightCharacter_mul_single_weightCharacter_neg, one_mul]
  · rw [alternatingForm_apply_of_ne _ h, mul_zero, zero_mul]

/-! ## The full carrier preserves the form -/

/-- The alternating-form relations belong to the defining ideal of the carrier. -/
theorem alternatingFormDefiningHopfIdeal_le_definingIdeal :
    ConstantForm.definingHopfIdeal ℤ 56 (alternatingForm ℤ) ≤ definingIdeal := by
  rw [definingIdeal_def]
  exact UniversalEnvelopingAlgebra.constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal
    _ _ _ _ _ _ _ _ _ rootCoordinateMap_preserves_alternatingForm
    torusCoordinateMap_preserves_alternatingForm

/-- Every point of the carrier preserves the alternating form: `g J gᵀ = J`. -/
theorem mul_alternatingForm_mul_transpose_of_mem_points
    {g : Matrix.GeneralLinearGroup (Fin 56) R} (hg : g ∈ points R) :
    (g : Matrix (Fin 56) (Fin 56) R) * alternatingForm R *
      (g : Matrix (Fin 56) (Fin 56) R)ᵀ = alternatingForm R := by
  rw [points_def] at hg
  simpa only [alternatingForm_map] using
    ConstantForm.mul_mul_transpose_of_mem_hopfIdealPointsSubgroup
      alternatingFormDefiningHopfIdeal_le_definingIdeal hg

/-- The column convention gives the same invariant form for every carrier point:
`gᵀ J g = J`. -/
theorem transpose_mul_alternatingForm_mul_of_mem_points
    {g : Matrix.GeneralLinearGroup (Fin 56) R} (hg : g ∈ points R) :
    (g : Matrix (Fin 56) (Fin 56) R)ᵀ * alternatingForm R *
      (g : Matrix (Fin 56) (Fin 56) R) = alternatingForm R :=
  Matrix.transpose_mul_mul_eq_of_mul_mul_transpose_eq (alternatingForm_mul_self R) g.inv_mul
    (mul_alternatingForm_mul_transpose_of_mem_points R hg)

/-- A scalar point of the carrier has scalar whose square is one. -/
theorem scalar_sq_eq_one_of_mem_points {g : Matrix.GeneralLinearGroup (Fin 56) R}
    (hg : g ∈ points R) (c : R)
    (hc : (g : Matrix (Fin 56) (Fin 56) R) = c • 1) : c ^ 2 = 1 := by
  have h := mul_alternatingForm_mul_transpose_of_mem_points R hg
  rw [hc] at h
  have : Nonempty (Fin 56) := ⟨0⟩
  exact Matrix.sq_eq_one_of_smul_one_mul_mul_transpose_eq (isUnit_alternatingForm R) h

/-- The carrier maps to the subgroup scheme of `GL₅₆` preserving the minuscule form. -/
noncomputable def toConstantForm :
    groupScheme ⟶ ConstantForm.groupScheme ℤ 56 (alternatingForm ℤ) :=
  CommHopfAlgCat.quotientSpecMapOfLe (GeneralLinear.coordinateHopfAlgebra ℤ 56)
    (alternatingFormDefiningHopfIdeal_le_definingIdeal.trans (le_of_eq definingIdeal_def))

/-- The morphism to the form-preserving subgroup scheme is a closed immersion. -/
instance isClosedImmersion_toConstantForm :
    IsClosedImmersion toConstantForm.hom.hom.left := by
  rw [toConstantForm]
  infer_instance

/-- Including the carrier into the form-preserving subgroup scheme and then into `GL₅₆`
recovers the carrier inclusion. -/
@[simp]
theorem toConstantForm_comp_inclusion :
    toConstantForm ≫ ConstantForm.inclusion ℤ 56 (alternatingForm ℤ) = carrierι := by
  rw [toConstantForm, ConstantForm.inclusion_def, GeneralLinear.hopfIdealInclusion_def,
    carrierι_def, UniversalEnvelopingAlgebra.kostantToralGroupSchemeι_def,
    ← Category.assoc, CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

end TauCeti.E7Minuscule
