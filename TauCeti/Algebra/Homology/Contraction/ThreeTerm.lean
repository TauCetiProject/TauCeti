/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Cancelling two identity blocks in a three-term cochain complex

Let a cochain complex in a preadditive category with a zero object and binary biproducts
be supported in degrees `-1`, `0`, and `1`, with terms identified as `U`, `Z ⊞ (W ⊞ U)`,
and `W`. Suppose the differential from `U` projects to the identity on the last middle
summand, and the differential to `W` is the identity on the second middle summand.
These two identity blocks cancel, leaving a contraction onto `Z` concentrated in degree zero.

In these coordinates write the differentials as `(δ, x, id)` and `(ε, id, y)`.
Their composite vanishes, so `δ ≫ ε + x + y = 0`. The corrected projection is
`(id, 0, -δ)` and the corrected inclusion is `(id, -ε, 0)`. The homotopy projects from
degree zero to its `U` summand and includes degree one into its `W` summand. Thus the
construction allows nonzero off-diagonal components; it does not assume the displayed
splitting is already a direct sum of complexes.

`Contraction.ThreeTermCancellationData.toContraction` packages these maps in the existing
`Contraction` interface, whose `homotopyEquiv` then supplies the homotopy equivalence.
The degree-zero projection and inclusion are `projectionZero` and `inclusionZero`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace TauCeti.Contraction
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (K : CochainComplex C ℤ) (U Z W : C)
/-- Component identifications for a three-term complex with two cancellable identity blocks. -/
structure ThreeTermCancellationData where
  /-- Identify the lowest nonzero term. -/
  minusIso : K.X (-1) ≅ U
  /-- Split the middle term into the surviving object and the two cancellable objects. -/
  zeroIso : K.X 0 ≅ Z ⊞ (W ⊞ U)
  /-- Identify the highest nonzero term. -/
  oneIso : K.X 1 ≅ W
  /-- The complex vanishes outside these three consecutive degrees. -/
  vanish : ∀ n, n ≠ -1 → n ≠ 0 → n ≠ 1 → IsZero (K.X n)
  /-- The bottom differential has identity component in the last middle summand. -/
  d_snd_snd : K.d (-1) 0 ≫ zeroIso.hom ≫ biprod.snd ≫ biprod.snd = minusIso.hom
  /-- The top differential restricts to the identity on the second middle summand. -/
  inl_inr_d : (biprod.inl : W ⟶ W ⊞ U) ≫ biprod.inr ≫ zeroIso.inv ≫
    K.d 0 1 ≫ oneIso.hom = 𝟙 W
namespace ThreeTermCancellationData

variable {K U Z W} (h : ThreeTermCancellationData K U Z W)
private abbrev pU : Z ⊞ (W ⊞ U) ⟶ U := biprod.snd ≫ biprod.snd
private abbrev iW : W ⟶ Z ⊞ (W ⊞ U) := biprod.inl ≫ biprod.inr
private def delta : U ⟶ Z :=
  h.minusIso.inv ≫ K.d (-1) 0 ≫ h.zeroIso.hom ≫ biprod.fst

omit [HasZeroObject C] in
private theorem d_fst : K.d (-1) 0 ≫ h.zeroIso.hom ≫ biprod.fst =
    h.minusIso.hom ≫ (delta h) := by
  simp only [delta, Iso.hom_inv_id_assoc]

private def epsilon : Z ⟶ W :=
  biprod.inl ≫ h.zeroIso.inv ≫ K.d 0 1 ≫ h.oneIso.hom
/-- The degree-zero projection after eliminating the two identity blocks. -/
def projectionZero : K.X 0 ⟶ Z :=
  h.zeroIso.hom ≫ (biprod.fst - (biprod.snd ≫ biprod.snd) ≫
    (h.minusIso.inv ≫ K.d (-1) 0 ≫ h.zeroIso.hom ≫ biprod.fst))
omit [HasZeroObject C] in
/-- The corrected projection subtracts the bottom differential's surviving component. -/
theorem projectionZero_def :
    projectionZero h = h.zeroIso.hom ≫
      (biprod.fst - (biprod.snd ≫ biprod.snd) ≫
        (h.minusIso.inv ≫ K.d (-1) 0 ≫ h.zeroIso.hom ≫ biprod.fst)) := (rfl)

/-- The degree-zero inclusion corrected by the differential into the upper identity block. -/
def inclusionZero : Z ⟶ K.X 0 :=
  (biprod.inl - (biprod.inl ≫ h.zeroIso.inv ≫ K.d 0 1 ≫ h.oneIso.hom) ≫
    (biprod.inl ≫ biprod.inr)) ≫ h.zeroIso.inv
omit [HasZeroObject C] in
/-- The corrected inclusion subtracts the surviving component of the top differential. -/
theorem inclusionZero_def :
    inclusionZero h =
      (biprod.inl - (biprod.inl ≫ h.zeroIso.inv ≫ K.d 0 1 ≫ h.oneIso.hom) ≫
        (biprod.inl ≫ biprod.inr)) ≫ h.zeroIso.inv := (rfl)

omit [HasZeroObject C] in
private theorem d_projectionZero : K.d (-1) 0 ≫ projectionZero h = 0 := by
  rw [projectionZero_def]
  have hu := h.d_snd_snd
  simp only [← Category.assoc] at hu
  simp only [Category.assoc, Preadditive.comp_sub]
  simp only [← Category.assoc, hu, Iso.hom_inv_id, Category.id_comp, sub_self]

omit [HasZeroObject C] in
private theorem inclusionZero_d : inclusionZero h ≫ K.d 0 1 = 0 := by
  rw [← cancel_mono h.oneIso.hom, zero_comp]
  have hw := h.inl_inr_d
  simp only [inclusionZero, Preadditive.sub_comp, Category.assoc, hw,
    Category.comp_id, sub_self]
omit [HasZeroObject C] in
private theorem inclusionZero_projectionZero : inclusionZero h ≫ projectionZero h = 𝟙 Z := by
  simp [inclusionZero, projectionZero, Category.assoc]
private def projection : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z :=
  HomologicalComplex.mkHomToSingle (projectionZero h) (by
    intro n hn
    have hn' : n = -1 := by
      rw [ComplexShape.up_Rel] at hn
      omega
    subst n
    exact d_projectionZero h)
private def inclusion : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z ⟶ K :=
  HomologicalComplex.mkHomFromSingle (inclusionZero h) (by
    intro n hn
    have hn' : n = 1 := by
      rw [ComplexShape.up_Rel] at hn
      omega
    subst n
    exact inclusionZero_d h)
private theorem inclusion_projection : inclusion h ≫ projection h = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, inclusion, projection,
    HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.id_f]
  rw [← Category.assoc, Category.assoc _ (inclusionZero h), inclusionZero_projectionZero,
    Category.comp_id, Iso.hom_inv_id]
private def normalFirst : U ⟶ Z ⊞ (W ⊞ U) :=
  h.minusIso.inv ≫ K.d (-1) 0 ≫ h.zeroIso.hom
private def normalLast : Z ⊞ (W ⊞ U) ⟶ W :=
  h.zeroIso.inv ≫ K.d 0 1 ≫ h.oneIso.hom
private def crossFirst : U ⟶ W := normalFirst h ≫ biprod.snd ≫ biprod.fst
private def crossLast : U ⟶ W := biprod.inr ≫ biprod.inr ≫ normalLast h
omit [HasZeroObject C] in
private theorem normalFirst_eq : normalFirst h =
    biprod.lift (delta h) (biprod.lift (crossFirst h) (𝟙 U)) := by
  apply biprod.hom_ext
  · simp only [normalFirst, Category.assoc, biprod.lift_fst]
    rw [d_fst h, Iso.inv_hom_id_assoc]
  · apply biprod.hom_ext
    · simp [crossFirst, Category.assoc]
    · simp only [normalFirst, Category.assoc, biprod.lift_snd]
      rw [h.d_snd_snd, Iso.inv_hom_id]
omit [HasZeroObject C] in
private theorem normalLast_eq : normalLast h =
    biprod.desc (epsilon h) (biprod.desc (𝟙 W) (crossLast h)) := by
  apply biprod.hom_ext'
  · simp [normalLast, epsilon]
  · apply biprod.hom_ext'
    · simp only [normalLast, biprod.inr_desc, biprod.inl_desc]
      exact h.inl_inr_d
    · simp [crossLast]
omit [HasZeroObject C] in
private theorem cross_relation : (delta h) ≫ epsilon h + (crossFirst h + crossLast h) = 0 := by
  have hs : normalFirst h ≫ normalLast h = 0 := by
    simp [normalFirst, normalLast, Category.assoc]
  rw [normalFirst_eq, normalLast_eq] at hs
  simpa only [biprod.lift_desc, Category.id_comp, Category.comp_id] using hs
omit [HasZeroObject C] in
private theorem normal_contraction :
    normalLast h ≫ iW + pU ≫ normalFirst h +
      (biprod.fst - pU ≫ (delta h)) ≫ (biprod.inl - epsilon h ≫ iW) =
        𝟙 (Z ⊞ (W ⊞ U)) := by
  rw [normalFirst_eq, normalLast_eq]
  ext <;> simp [pU, iW, Category.assoc]
  simpa [add_comm, add_left_comm, add_assoc] using cross_relation h

private def s0 : K.X 0 ⟶ K.X (-1) := h.zeroIso.hom ≫ pU ≫ h.minusIso.inv
private def s1 : K.X 1 ⟶ K.X 0 := h.oneIso.hom ≫ iW ≫ h.zeroIso.inv
omit [HasZeroObject C] in
private theorem bottom_contract : K.d (-1) 0 ≫ s0 h = 𝟙 _ := by
  simpa only [s0, pU, Category.assoc, Iso.hom_inv_id] using
    congrArg (fun f ↦ f ≫ h.minusIso.inv) h.d_snd_snd
omit [HasZeroObject C] in
private theorem top_contract : s1 h ≫ K.d 0 1 = 𝟙 _ := by
  rw [← cancel_mono h.oneIso.hom, Category.id_comp]
  simp only [s1, iW, Category.assoc, h.inl_inr_d, Category.comp_id]
omit [HasZeroObject C] in
private theorem middle_contract : K.d 0 1 ≫ s1 h + s0 h ≫ K.d (-1) 0 +
    projectionZero h ≫ inclusionZero h = 𝟙 _ := by
  have hn := congrArg (fun f ↦ h.zeroIso.hom ≫ f ≫ h.zeroIso.inv)
    (normal_contraction h)
  simpa only [s0, s1, normalFirst, normalLast, projectionZero, inclusionZero,
    delta, epsilon, iW, pU,
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] using hn
private def homFamily (i j : ℤ) : K.X i ⟶ K.X j := by
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = -1
    · subst j
      exact s0 h
    · exact 0
  · by_cases hi' : i = 1
    · subst i
      by_cases hj : j = 0
      · subst j
        exact s1 h
      · exact 0
    · exact 0
private def contraction : Homotopy (𝟙 K) (projection h ≫ inclusion h) where
  hom := homFamily h
  zero i j hn := by
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = -1
      · subst j
        exact (hn (by simp)).elim
      · simp [homFamily, hj]
    · by_cases hi' : i = 1
      · subst i
        by_cases hj : j = 0
        · subst j
          exact (hn (by simp)).elim
        · simp [homFamily, hj]
      · simp [homFamily, hi, hi']
  comm i := by
    by_cases hi : i = -1
    · subst i
      rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel (-1) 0),
        prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (-2) (-1))]
      have hp : (projection h).f (-1) = 0 :=
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Z (-1)
          (by decide)).eq_of_tgt _ _
      simpa [homFamily, HomologicalComplex.comp_f, hp] using (bottom_contract h).symm
    · by_cases hi' : i = 0
      · subst i
        rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel 0 1),
          prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (-1) 0)]
        have hp : (projection h ≫ inclusion h).f 0 = projectionZero h ≫ inclusionZero h := by
          simp [projection, inclusion, Category.assoc]
        simpa [homFamily, hp] using (middle_contract h).symm
      · by_cases hi'' : i = 1
        · subst i
          rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel 1 2),
            prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel 0 1)]
          have hp : (projection h).f 1 = 0 :=
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Z 1
              (by decide)).eq_of_tgt _ _
          simpa [homFamily, HomologicalComplex.comp_f, hp] using (top_contract h).symm
        · exact (h.vanish i hi hi' hi'').eq_of_src _ _
/-- Cancel the lower and upper identity blocks and retract onto `Z` in degree zero. -/
def toContraction : TauCeti.Contraction K
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z) where
  proj := projection h
  incl := inclusion h
  incl_comp_proj := inclusion_projection h
  homotopy := Cochain.ofHomotopy (contraction h)
  δ_homotopy := by
    rw [Cochain.ofHom_sub]
    exact δ_ofHomotopy (contraction h)

/-- The degree-zero projection is the corrected projection to the surviving summand. -/
@[simp]
theorem toContraction_proj_f_zero :
    (h.toContraction.proj).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom =
      h.projectionZero := by
  simp only [toContraction, projection, HomologicalComplex.mkHomToSingle_f,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The contraction's degree-zero inclusion is the corrected inclusion of the surviving summand. -/
@[simp]
theorem toContraction_incl_f_zero :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv ≫
      (h.toContraction.incl).f 0 = h.inclusionZero := by
  simp only [toContraction, inclusion, HomologicalComplex.mkHomFromSingle_f,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end ThreeTermCancellationData

end TauCeti.Contraction
