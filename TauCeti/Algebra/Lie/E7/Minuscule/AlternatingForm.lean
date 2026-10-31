/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.AlternatingForm
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic

/-!
# The invariant alternating form of the E7 minuscule carrier

The signs of the existing minuscule weight graph pair each weight with its negative.
Their matrix is alternating and has square `-1` over every commutative ring. The root
subgroups and weight torus preserve this form, so the full native toral carrier does too.
In particular, a scalar point of the carrier has scalar whose square is one.
-/

public section

open scoped Matrix
open TauCeti.DynkinType CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.E7Minuscule

/-- Signed opposition of the E7 minuscule table, using its existing parent-tree signs. -/
noncomputable def signedOpposition : weightTable.SignedOpposition where
  opposition a := (exists_e7MinusculeWeight_eq_neg a).choose
  weight_opposition a i := by
    simpa only [weightTable_weight, Pi.neg_apply] using
      congrFun (exists_e7MinusculeWeight_eq_neg a).choose_spec i
  sign := e7MinusculeSign
  sign_mul_self := e7MinusculeSign_mul_self
  sign_opposition a := e7MinusculeSign_eq_neg_of_weight_eq_neg a _
    (exists_e7MinusculeWeight_eq_neg a).choose_spec
  sign_reflection i a h := by
    simpa only [weightTable_reflection] using
      e7MinusculeSign_reflection i a (by simpa only [weightTable_weight] using h)

@[simp]
theorem signedOpposition_sign : signedOpposition.sign = e7MinusculeSign := by
  rfl

/-- The integral minuscule alternating form, read in any coefficient ring. -/
noncomputable def alternatingForm (R : Type*) [CommRing R] : Matrix (Fin 56) (Fin 56) R :=
  signedOpposition.form R

variable (R : Type*) [CommRing R]

/-- The native alternating form is the form of the signed minuscule opposition. -/
theorem alternatingForm_def : alternatingForm R = signedOpposition.form R := by
  rfl

@[simp]
theorem alternatingForm_apply_opposition (a : Fin 56) :
    alternatingForm R a (signedOpposition.opposition a) = (e7MinusculeSign a : R) := by
  rw [alternatingForm_def, signedOpposition.form_apply_opposition, signedOpposition_sign]

@[simp]
theorem alternatingForm_apply_of_ne {a b : Fin 56} (h : b ≠ signedOpposition.opposition a) :
    alternatingForm R a b = 0 := by
  rw [alternatingForm_def, signedOpposition.form_apply_of_ne R h]

@[simp]
theorem alternatingForm_transpose : (alternatingForm R)ᵀ = -alternatingForm R :=
  signedOpposition.form_transpose R

@[simp]
theorem alternatingForm_mul_self : alternatingForm R * alternatingForm R = -1 :=
  signedOpposition.form_mul_self R

/-- The minuscule form is alternating, including in characteristic two. -/
theorem dotProduct_alternatingForm_mulVec_self (x : Fin 56 → R) :
    dotProduct x ((alternatingForm R).mulVec x) = 0 :=
  signedOpposition.dotProduct_form_mulVec_self R x

@[simp]
theorem alternatingForm_map {S : Type*} [CommRing S] (f : R →+* S) :
    (alternatingForm R).map f = alternatingForm S :=
  signedOpposition.form_map R f

/-- The highest weight pairs with its opposite with coefficient one. -/
theorem alternatingForm_zero_opposition :
    alternatingForm R 0 (signedOpposition.opposition 0) = 1 := by
  rw [alternatingForm_apply_opposition]
  simp

/-- All numbered root-subgroup points preserve the minuscule form. -/
theorem rootSubgroupPoints_preserves_alternatingForm (k : Fin 7 ⊕ Fin 7)
    (u : Multiplicative R) :
    let M := ((rootSubgroupPoints k R u : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R)
    M * alternatingForm R * Mᵀ = alternatingForm R := by
  dsimp only
  cases k with
  | inl i =>
      rw [coe_rootSubgroupPoints_inl]
      simpa only [weightTable_raisingMatrix, alternatingForm] using
        signedOpposition.one_add_smul_raisingMatrix_preserves_form R i (Multiplicative.toAdd u)
  | inr i =>
      rw [coe_rootSubgroupPoints_inr]
      have hM : weightTable.loweringMatrix i = loweringMatrix i := by
        ext a b
        simp
      simpa only [hM, alternatingForm] using
        signedOpposition.one_add_smul_loweringMatrix_preserves_form R i (Multiplicative.toAdd u)

/-! ## Universal root and torus identities -/

local notation "rootGen" => TauCeti.serreRootGenerator (CartanMatrix.E 7)
local notation "cartanGen" => TauCeti.serreH ℚ (CartanMatrix.E 7)

private theorem rootMatrix_preserves_alternatingForm (A : Type*) [CommRing A]
    (k : Fin 7 ⊕ Fin 7) (p : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    let M := ((UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix rootGen cartanGen rep
      lattice.toAddSubgroup rep_kostantForm_mem_lattice k
      (isNilpotent_rep_serreRootGenerator k) latticeBasis p) :
        Matrix (Fin 56) (Fin 56) A)
    M * alternatingForm A * Mᵀ = alternatingForm A := by
  have h := rootSubgroupPoints_preserves_alternatingForm A k
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ)) p)
  dsimp only at h ⊢
  rw [coe_rootSubgroupPoints,
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ)).symm_apply_apply p] at h
  exact h

private theorem rootCoordinateMap_preserves_alternatingForm (k : Fin 7 ⊕ Fin 7) :
    let X := (GeneralLinear.genericMatrix ℤ 56).map
      (UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap rootGen cartanGen rep
        lattice.toAddSubgroup rep_kostantForm_mem_lattice k
        (isNilpotent_rep_serreRootGenerator k) latticeBasis).hom.toAlgHom
    X * (alternatingForm ℤ).map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) * Xᵀ =
      (alternatingForm ℤ).map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) := by
  dsimp only
  rw [alternatingForm_map,
    UniversalEnvelopingAlgebra.map_genericMatrix_eq_kostantRootSubgroupMatrix]
  exact rootMatrix_preserves_alternatingForm _ k _

private theorem map_genericMatrix_weightTorusCoordinateMap :
    (GeneralLinear.genericMatrix ℤ 56).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) e7MinusculeWeight).hom.toAlgHom =
      Matrix.diagonal (fun a ↦ MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (e7MinusculeWeight a))) (1 : ℤ)) := by
  ext a b
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply]
  simp only [BialgHom.coe_toAlgHom]
  rw [GeneralLinear.weightTorusCoordinateMap_X, Matrix.diagonal_apply]

private theorem torusCharacter_mul_opposition (a : Fin 56) :
    MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (e7MinusculeWeight a))) (1 : ℤ) *
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm
        (e7MinusculeWeight (signedOpposition.opposition a)))) (1 : ℤ) = 1 := by
  rw [MonoidAlgebra.single_mul_single, mul_one, ← ofAdd_add]
  have hz : Finsupp.equivFunOnFinite.symm (e7MinusculeWeight a) +
      Finsupp.equivFunOnFinite.symm (e7MinusculeWeight (signedOpposition.opposition a)) = 0 := by
    ext i
    have hw := signedOpposition.weight_opposition a i
    simp only [weightTable_weight] at hw
    simp [hw]
  rw [hz]
  rfl

private theorem torusCoordinateMap_preserves_alternatingForm :
    let X := (GeneralLinear.genericMatrix ℤ 56).map
      (GeneralLinear.weightTorusCoordinateMap (R := ℤ) e7MinusculeWeight).hom.toAlgHom
    let S := (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin 7))).obj
    X * (alternatingForm ℤ).map (algebraMap ℤ S) * Xᵀ =
      (alternatingForm ℤ).map (algebraMap ℤ S) := by
  dsimp only
  rw [alternatingForm_map, map_genericMatrix_weightTorusCoordinateMap,
    Matrix.diagonal_transpose]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : b = signedOpposition.opposition a
  · subst b
    simp only [alternatingForm, MinusculeWeightTable.SignedOpposition.form_apply_opposition]
    rw [mul_right_comm, torusCharacter_mul_opposition, one_mul]
  · simp only [alternatingForm, signedOpposition.form_apply_of_ne _ h, mul_zero, zero_mul]

/-! ## The full carrier preserves the form -/

/-- The alternating-form relations belong to the defining ideal of the full native carrier. -/
theorem alternatingFormDefiningHopfIdeal_le_definingIdeal :
    ConstantForm.definingHopfIdeal ℤ 56 (alternatingForm ℤ) ≤ definingIdeal := by
  rw [definingIdeal_def, UniversalEnvelopingAlgebra.le_kostantToralDefiningIdeal_iff]
  refine ⟨fun k ↦ ?_, ?_⟩
  · exact (ConstantForm.definingHopfIdeal_toIdeal_le_ker_iff ℤ _ _ _).mpr
      (rootCoordinateMap_preserves_alternatingForm k)
  · exact (ConstantForm.definingHopfIdeal_toIdeal_le_ker_iff ℤ _ _ _).mpr
      torusCoordinateMap_preserves_alternatingForm

/-- Every point of the full native E7 carrier preserves the alternating form. -/
theorem mul_alternatingForm_transpose_of_mem_points
    {g : Matrix.GeneralLinearGroup (Fin 56) R} (hg : g ∈ points R) :
    (g : Matrix (Fin 56) (Fin 56) R) * alternatingForm R *
      (g : Matrix (Fin 56) (Fin 56) R)ᵀ = alternatingForm R := by
  rw [points_def] at hg
  have h := GeneralLinear.hopfIdealPointsSubgroup_le_of_le 56
    alternatingFormDefiningHopfIdeal_le_definingIdeal R hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at h
  have hmem : (GeneralLinear.pointsMulEquiv (R := ℤ) 56).symm g ∈
      CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra ℤ 56)
        (ConstantForm.definingHopfIdeal ℤ 56 (alternatingForm ℤ)) (CommAlgCat.of ℤ R) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr h
  rw [ConstantForm.mem_definingPointsSubgroup_iff, alternatingForm_map,
    MulEquiv.apply_symm_apply] at hmem
  exact hmem

/-- The column convention gives the same invariant form for every carrier point. -/
theorem transpose_mul_alternatingForm_of_mem_points
    {g : Matrix.GeneralLinearGroup (Fin 56) R} (hg : g ∈ points R) :
    (g : Matrix (Fin 56) (Fin 56) R)ᵀ * alternatingForm R *
      (g : Matrix (Fin 56) (Fin 56) R) = alternatingForm R := by
  let M : Matrix (Fin 56) (Fin 56) R := g
  let N : Matrix (Fin 56) (Fin 56) R := g⁻¹
  have hNM : N * M = 1 := by simp [N, M]
  have h : M * alternatingForm R * Mᵀ = alternatingForm R :=
    mul_alternatingForm_transpose_of_mem_points R hg
  have hleft : alternatingForm R * Mᵀ = N * alternatingForm R := by
    calc
      _ = (N * M) * alternatingForm R * Mᵀ := by rw [hNM, Matrix.one_mul]
      _ = N * (M * alternatingForm R * Mᵀ) := by simp only [Matrix.mul_assoc]
      _ = N * alternatingForm R := by rw [h]
  have haux : alternatingForm R * (Mᵀ * alternatingForm R * M) =
      alternatingForm R * alternatingForm R := by
    calc
      _ = (alternatingForm R * Mᵀ) * alternatingForm R * M := by
        simp only [Matrix.mul_assoc]
      _ = (N * alternatingForm R) * alternatingForm R * M := by rw [hleft]
      _ = -1 := by
        rw [Matrix.mul_assoc N, alternatingForm_mul_self, Matrix.mul_neg, Matrix.mul_one,
          Matrix.neg_mul, hNM]
      _ = _ := (alternatingForm_mul_self R).symm
  have hcancel := congrArg (fun X ↦ alternatingForm R * X) haux
  simpa only [← Matrix.mul_assoc, alternatingForm_mul_self, Matrix.neg_mul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.mul_one, neg_inj, M] using hcancel

/-- A scalar point of the full minuscule carrier has scalar whose square is one. -/
theorem scalar_sq_eq_one_of_mem_points {g : Matrix.GeneralLinearGroup (Fin 56) R}
    (hg : g ∈ points R) (c : R)
    (hc : (g : Matrix (Fin 56) (Fin 56) R) = c • 1) : c ^ 2 = 1 := by
  have h := mul_alternatingForm_transpose_of_mem_points R hg
  rw [hc, Matrix.smul_mul, Matrix.one_mul, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.mul_smul, Matrix.mul_one] at h
  have hentry := congrFun (congrFun h 0) (signedOpposition.opposition 0)
  simpa only [Matrix.smul_apply, smul_eq_mul, alternatingForm_zero_opposition, mul_one,
    pow_two] using hentry

/-- The native carrier maps to the group scheme preserving its minuscule form. -/
noncomputable def toConstantForm :
    groupScheme ⟶ ConstantForm.groupScheme ℤ 56 (alternatingForm ℤ) :=
  CommHopfAlgCat.quotientSpecMapOfLe (GeneralLinear.coordinateHopfAlgebra ℤ 56)
    (alternatingFormDefiningHopfIdeal_le_definingIdeal.trans (le_of_eq definingIdeal_def))

instance isClosedImmersion_toConstantForm :
    IsClosedImmersion toConstantForm.hom.hom.left := by
  rw [toConstantForm]
  infer_instance

/-- The form-preserving inclusion recovers the native ambient inclusion. -/
@[simp]
theorem toConstantForm_comp_inclusion :
    toConstantForm ≫ ConstantForm.inclusion ℤ 56 (alternatingForm ℤ) = carrierι := by
  rw [toConstantForm, ConstantForm.inclusion_def, GeneralLinear.hopfIdealInclusion_def,
    carrierι_def, UniversalEnvelopingAlgebra.kostantToralGroupSchemeι_def,
    ← Category.assoc, CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

end TauCeti.E7Minuscule
