/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic

/-!
# The linear Hom complex out of a mapping cone

For a cochain map `f : X ⟶ Y`, restriction to the two summands identifies
`linearHomComplex R (mappingCone f) Z` with the mapping cocone of precomposition by `f`.
In degree `n` the coordinates are restriction to `Y` and `(-1)^(n+1)` times restriction
to the degree-minus-one inclusion of `X`. The sign makes this an isomorphism for Mathlib's
mapping-cone and shifted-cone differentials.

The comparison describes maps and null homotopies out of a cone at the level of the entire
Hom complex. It is natural in the target and in commutative squares of cochain maps.

The construction uses Joël Riou's `mappingCone.descCochain` and `δ_descCochain` in Mathlib,
and the projections of Mathlib's mapping cocone.
-/

public section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u w

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (Z : CochainComplex C ℤ)
  [HasHomotopyCofiber f]

-- Keeping the predecessor explicit lets the differential proof use matching graded types.
private noncomputable def conePrecompEquiv (n m : ℤ) (hm : m + 1 = n) :
    Cochain (mappingCone f) Z n ≃ₗ[R]
      (mappingCocone (linearHomComplexPrecomp R f Z)).X n where
  toFun z :=
    ((mappingCocone.inl (linearHomComplexPrecomp R f Z)).v n n (add_zero n)).hom
      ((Cochain.ofHom (mappingCone.inr f)).comp z (zero_add n)) +
    ((mappingCocone.inr (linearHomComplexPrecomp R f Z)).val.v m n (by omega)).hom
      ((n + 1).negOnePow • (mappingCone.inl f).comp z (by omega))
  invFun z := mappingCone.descCochain f
    ((n + 1).negOnePow •
      ((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v n m (by omega)).hom z)
    (((mappingCocone.fst (linearHomComplexPrecomp R f Z)).f n).hom z) (by omega)
  left_inv z := by
    apply (mappingCone.ext_cochain_from_iff f m n (by omega)).2
    constructor
    · simp only [mappingCone.inl_descCochain, map_add, smul_add, linearHomComplex_X]
      rw [← ModuleCat.comp_apply, mappingCocone.inl_v_snd_v, ← ModuleCat.comp_apply,
        mappingCocone.inr_v_snd_v]
      simp [smul_smul]
    · simp only [mappingCone.inr_descCochain, map_add, linearHomComplex_X]
      rw [← ModuleCat.comp_apply, mappingCocone.inl_v_fst_f, ← ModuleCat.comp_apply,
        mappingCocone.inr_v_fst_f]
      simp
  right_inv z := by
    have h := congrArg (fun g ↦ ModuleCat.Hom.hom g z)
      (mappingCocone.id_X (linearHomComplexPrecomp R f Z) n m (by omega))
    simpa [ModuleCat.comp_apply, smul_smul] using h
  map_add' z z' := by
    simp only [Cochain.comp_add, smul_add, map_add]
    abel
  map_smul' r z := by
    simp [Cochain.comp_smul, smul_add, smul_comm r]

private lemma conePrecompEquiv_symm_d (n : ℤ)
    (z : (mappingCocone (linearHomComplexPrecomp R f Z)).X n) :
    (conePrecompEquiv R f Z (n + 1) (n + 1 + -1) (by omega)).symm
        (((mappingCocone (linearHomComplexPrecomp R f Z)).d n (n + 1)) z) =
      δ n (n + 1) ((conePrecompEquiv R f Z n (n + -1) (by omega)).symm z) := by
  have he : conePrecompEquiv R f Z (n + 1) (n + 1 + -1) (by omega) =
      conePrecompEquiv R f Z (n + 1) n rfl := by
    congr 1; omega
  rw [he]
  apply (mappingCone.ext_cochain_from_iff f n (n + 1) rfl).2
  constructor
  · simp only [conePrecompEquiv, LinearEquiv.coe_symm_mk,
      mappingCone.inl_descCochain,
      mappingCone.δ_descCochain (m := n + -1) (n := n) f _ _ _ (n + 1) rfl,
      Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero]
    have h := congrArg (fun g ↦ ModuleCat.Hom.hom g z)
      (mappingCocone.d_snd_v (linearHomComplexPrecomp R f Z) n)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_neg, ModuleCat.hom_sub, LinearMap.comp_apply,
      LinearMap.neg_apply, LinearMap.sub_apply, linearHomComplex_X,
      linearHomComplexPrecomp_f_apply, linearHomComplex_d_hom_apply] at h
    rw [h]
    simp [δ_units_smul, Int.negOnePow_add, Int.negOnePow_one, smul_add,
      sub_eq_add_neg, add_comm]
  · simp only [conePrecompEquiv, LinearEquiv.coe_symm_mk,
      mappingCone.inr_descCochain,
      mappingCone.δ_descCochain (m := n + -1) (n := n) f _ _ _ (n + 1) rfl,
      Cochain.comp_add, mappingCone.inr_fst_assoc, mappingCone.inr_snd_assoc, zero_add]
    have h := congrArg (fun g ↦ ModuleCat.Hom.hom g z)
      ((mappingCocone.fst (linearHomComplexPrecomp R f Z)).comm n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, linearHomComplex_X,
      linearHomComplex_d_hom_apply] at h
    exact h.symm

/-- Restriction to `Y` and signed restriction to the shifted `X` summand identify the linear
Hom complex out of `mappingCone f` with the mapping cocone of precomposition by `f`. -/
noncomputable def linearHomComplexMappingConePrecompIso :
    linearHomComplex R (mappingCone f) Z ≅ mappingCocone (linearHomComplexPrecomp R f Z) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (conePrecompEquiv R f Z n (n + -1) (by omega)).toModuleIso) (by
      intro n m hnm
      obtain rfl : m = n + 1 := hnm.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply (conePrecompEquiv R f Z (n + 1) (n + 1 + -1) (by omega)).symm.injective
      simpa using conePrecompEquiv_symm_d R f Z n
        (conePrecompEquiv R f Z n (n + -1) (by omega) z))

private lemma linearHomComplexMappingConePrecompIso_hom_f_apply (n : ℤ)
    (z : Cochain (mappingCone f) Z n) :
    dsimp% only [linearHomComplex_X]
      (((linearHomComplexMappingConePrecompIso R f Z).hom.f n).hom z =
        conePrecompEquiv R f Z n (n + -1) (by omega) z) :=
  (rfl)

/-- The first coordinate is restriction along the right inclusion of the cone. -/
@[simp]
lemma linearHomComplexMappingConePrecompIso_hom_f_fst (n : ℤ)
    (z : Cochain (mappingCone f) Z n) :
    dsimp% only [linearHomComplex_X]
      (((mappingCocone.fst (linearHomComplexPrecomp R f Z)).f n).hom
        (((linearHomComplexMappingConePrecompIso R f Z).hom.f n).hom z) =
      (Cochain.ofHom (mappingCone.inr f)).comp z (zero_add n)) := by
  -- Apply the restriction to the inverse law, reusing the reconstruction formula.
  have h := (conePrecompEquiv R f Z n (n + -1) (by omega)).symm_apply_apply z
  simpa only [linearHomComplexMappingConePrecompIso_hom_f_apply,
    conePrecompEquiv, LinearEquiv.coe_symm_mk,
    mappingCone.inr_descCochain] using
    congrArg (fun w ↦ (Cochain.ofHom (mappingCone.inr f)).comp w (zero_add n)) h

/-- The second coordinate is signed restriction along the left inclusion of the cone. -/
@[simp]
lemma linearHomComplexMappingConePrecompIso_hom_f_snd (n m : ℤ) (hm : n + -1 = m)
    (z : Cochain (mappingCone f) Z n) :
    dsimp% only [linearHomComplex_X]
      (((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v n m hm).hom
        (((linearHomComplexMappingConePrecompIso R f Z).hom.f n).hom z) =
      (n + 1).negOnePow • (mappingCone.inl f).comp z (by omega)) := by
  subst m
  -- Apply the restriction to the inverse law, reusing the reconstruction formula.
  have h := (conePrecompEquiv R f Z n (n + -1) (by omega)).symm_apply_apply z
  simpa only [linearHomComplexMappingConePrecompIso_hom_f_apply,
    conePrecompEquiv, LinearEquiv.coe_symm_mk,
    mappingCone.inl_descCochain, smul_smul, Int.units_mul_self, one_smul] using
    congrArg (fun w ↦ (n + 1).negOnePow • (mappingCone.inl f).comp w
      (show -1 + n = n + -1 by omega)) h

/-- Reconstruct a cochain using the two coordinates of the mapping cocone. -/
@[simp]
lemma linearHomComplexMappingConePrecompIso_inv_f_apply (n : ℤ)
    (z : (mappingCocone (linearHomComplexPrecomp R f Z)).X n) :
    dsimp% only [linearHomComplex_X]
      (((linearHomComplexMappingConePrecompIso R f Z).inv.f n).hom z =
      mappingCone.descCochain f
        ((n + 1).negOnePow •
          ((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v n (n + -1) (by omega)).hom z)
        (((mappingCocone.fst (linearHomComplexPrecomp R f Z)).f n).hom z) (by omega)) :=
  (rfl)

/-- For a cochain map out of the cone, the second coordinate is the negative of the
canonical null homotopy of its restriction along `f`. -/
lemma linearHomComplexMappingConePrecompIso_hom_f_snd_ofHom (g : mappingCone f ⟶ Z) :
    dsimp% only [linearHomComplex_X]
      (((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v 0 (-1) (by omega)).hom
        (((linearHomComplexMappingConePrecompIso R f Z).hom.f 0).hom (Cochain.ofHom g)) =
      -Cochain.ofHomotopy ((mappingCone.inrCompHomotopy f).compRight g)) := by
  rw [linearHomComplexMappingConePrecompIso_hom_f_snd]
  simp only [Int.reduceAdd, Int.negOnePow_one, Units.neg_smul, one_smul]
  congr 1
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHomotopy,
    Cochain.mk_v, Homotopy.compRight_hom]
  rw [mappingCone.inrCompHomotopy_hom f p q (by omega)]

-- Both naturality squares follow from compatibility with the two signed restrictions.
private lemma linearHomComplexMappingConePrecompIso_inv_map_of_components
    {X' Y' Z' : CochainComplex C ℤ} (f' : X' ⟶ Y') [HasHomotopyCofiber f']
    (a : linearHomComplex R Y Z ⟶ linearHomComplex R Y' Z')
    (b : linearHomComplex R X Z ⟶ linearHomComplex R X' Z')
    (comm : linearHomComplexPrecomp R f Z ≫ b = a ≫ linearHomComplexPrecomp R f' Z')
    (ψ : linearHomComplex R (mappingCone f) Z ⟶ linearHomComplex R (mappingCone f') Z')
    (hfst : dsimp% only [linearHomComplex_X] (∀ (n : ℤ) (z : Cochain (mappingCone f) Z n),
      (Cochain.ofHom (mappingCone.inr f')).comp ((ψ.f n).hom z) (zero_add n) =
        (a.f n).hom ((Cochain.ofHom (mappingCone.inr f)).comp z (zero_add n))))
    (hsnd : dsimp% only [linearHomComplex_X] (∀ (n : ℤ) (z : Cochain (mappingCone f) Z n),
      (n + 1).negOnePow • (mappingCone.inl f').comp ((ψ.f n).hom z) (by omega) =
        (b.f (n + -1)).hom ((n + 1).negOnePow • (mappingCone.inl f).comp z (by omega)))) :
    (mappingCone.map (linearHomComplexPrecomp R f Z) (linearHomComplexPrecomp R f' Z')
        a b comm)⟦(-1 : ℤ)⟧' ≫ (linearHomComplexMappingConePrecompIso R f' Z').inv =
      (linearHomComplexMappingConePrecompIso R f Z).inv ≫ ψ := by
  let φ : mappingCocone (linearHomComplexPrecomp R f Z) ⟶
      mappingCocone (linearHomComplexPrecomp R f' Z') :=
    (mappingCone.map (linearHomComplexPrecomp R f Z) (linearHomComplexPrecomp R f' Z')
      a b comm)⟦(-1 : ℤ)⟧'
  -- The shifted cone map has source and target expressed as shifts, whereas the isomorphisms
  -- use mappingCocone. A dependent rewrite cannot replace those objects inside composition;
  -- the typed map φ puts every composition in the same cocone objects before cancellation.
  change φ ≫ (linearHomComplexMappingConePrecompIso R f' Z').inv =
    (linearHomComplexMappingConePrecompIso R f Z).inv ≫ ψ
  apply (Iso.comp_inv_eq _).2
  apply (cancel_epi (linearHomComplexMappingConePrecompIso R f Z).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  apply mappingCocone.ext_to (linearHomComplexPrecomp R f' Z') n (n + -1) rfl
  · have hφ : φ ≫ mappingCocone.fst (linearHomComplexPrecomp R f' Z') =
        mappingCocone.fst (linearHomComplexPrecomp R f Z) ≫ a :=
      mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ comm
    rw [Category.assoc, ← HomologicalComplex.comp_f, hφ, HomologicalComplex.comp_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, linearHomComplex_X,
      linearHomComplexMappingConePrecompIso_hom_f_fst] using (hfst n z).symm
  · have hφ : φ.f n ≫ (mappingCocone.snd (linearHomComplexPrecomp R f' Z')).v
        n (n + -1) rfl =
      (mappingCocone.snd (linearHomComplexPrecomp R f Z)).v n (n + -1) rfl ≫ b.f (n + -1) :=
        mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v _ _ _ _ comm n
    rw [Category.assoc, hφ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, linearHomComplex_X,
      linearHomComplexMappingConePrecompIso_hom_f_snd] using (hsnd n z).symm

/-- The comparison is natural under postcomposition in the target complex. -/
@[reassoc]
lemma linearHomComplexMappingConePrecompIso_inv_naturality
    {Z' : CochainComplex C ℤ} (g : Z ⟶ Z') :
    (mappingCone.map (linearHomComplexPrecomp R f Z) (linearHomComplexPrecomp R f Z')
        (linearHomComplexPostcomp R Y g) (linearHomComplexPostcomp R X g)
        (linearHomComplexPrecomp_postcomp_comm R f g))⟦(-1 : ℤ)⟧' ≫
      (linearHomComplexMappingConePrecompIso R f Z').inv =
    (linearHomComplexMappingConePrecompIso R f Z).inv ≫
      linearHomComplexPostcomp R (mappingCone f) g := by
  apply linearHomComplexMappingConePrecompIso_inv_map_of_components
  · intro n z
    simp only [linearHomComplexPostcomp_f_apply,
      Cochain.comp_assoc_of_first_is_zero_cochain]
  · intro n z
    simp only [linearHomComplexPostcomp_f_apply, Cochain.units_smul_comp,
      Cochain.comp_assoc_of_third_is_zero_cochain]

section Squares

variable [HasBinaryBiproducts C] {X₁ Y₁ X₂ Y₂ : CochainComplex C ℤ}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
  (comm : f₁ ≫ b = a ≫ f₂)

/-- A commutative square of cochain maps induces the contravariant square of outgoing
Hom-cone comparisons. -/
@[reassoc]
lemma linearHomComplexMappingConePrecompIso_inv_map :
    (mappingCone.map (linearHomComplexPrecomp R f₂ Z) (linearHomComplexPrecomp R f₁ Z)
        (linearHomComplexPrecomp R b Z) (linearHomComplexPrecomp R a Z)
        (by simp only [← linearHomComplexPrecomp_comp, comm]))⟦(-1 : ℤ)⟧' ≫
      (linearHomComplexMappingConePrecompIso R f₁ Z).inv =
    (linearHomComplexMappingConePrecompIso R f₂ Z).inv ≫
      linearHomComplexPrecomp R (mappingCone.map f₁ f₂ a b comm) Z := by
  apply linearHomComplexMappingConePrecompIso_inv_map_of_components
  · intro n z
    ext p q hpq
    simp [mappingCone.inr_f_map_f_assoc]
  · intro n z
    simp only [linearHomComplexPrecomp_f_apply, Cochain.comp_units_smul]
    congr 1
    ext p q hpq
    rw [Cochain.comp_v _ _ _ p (p + -1) q rfl (by omega)]
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      mappingCone.inl_v_map_f_assoc]
    rw [Cochain.comp_v _ _ _ p (p + -1) q rfl (by omega)]

end Squares

end TauCeti
