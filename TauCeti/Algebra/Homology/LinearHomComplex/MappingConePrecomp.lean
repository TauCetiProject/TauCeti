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
    · simp only [mappingCone.inl_descCochain, map_add, smul_add]
      erw [← ModuleCat.comp_apply, mappingCocone.inl_v_snd_v, ← ModuleCat.comp_apply,
        mappingCocone.inr_v_snd_v]
      simp [smul_smul]
    · simp only [mappingCone.inr_descCochain, map_add]
      erw [← ModuleCat.comp_apply, mappingCocone.inl_v_fst_f, ← ModuleCat.comp_apply,
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
    erw [h]
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

/-- The first coordinate is restriction along the right inclusion of the cone. -/
@[simp]
lemma linearHomComplexMappingConePrecompIso_hom_f_fst (n : ℤ)
    (z : Cochain (mappingCone f) Z n) :
    dsimp% only [linearHomComplex_X]
      (((mappingCocone.fst (linearHomComplexPrecomp R f Z)).f n).hom
        (((linearHomComplexMappingConePrecompIso R f Z).hom.f n).hom z) =
      (Cochain.ofHom (mappingCone.inr f)).comp z (zero_add n)) := by
  -- The component chosen by `isoOfComponents` is the degreewise equivalence.
  change ((mappingCocone.fst (linearHomComplexPrecomp R f Z)).f n).hom
    (conePrecompEquiv R f Z n (n + -1) (by omega) z) = _
  simp only [conePrecompEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    map_add]
  erw [← ModuleCat.comp_apply, mappingCocone.inl_v_fst_f, ← ModuleCat.comp_apply,
    mappingCocone.inr_v_fst_f]
  simp

/-- The second coordinate is signed restriction along the left inclusion of the cone. -/
@[simp]
lemma linearHomComplexMappingConePrecompIso_hom_f_snd (n : ℤ)
    (z : Cochain (mappingCone f) Z n) :
    dsimp% only [linearHomComplex_X]
      (((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v n (n + -1) (by omega)).hom
        (((linearHomComplexMappingConePrecompIso R f Z).hom.f n).hom z) =
      (n + 1).negOnePow • (mappingCone.inl f).comp z (by omega)) := by
  -- The component chosen by `isoOfComponents` is the degreewise equivalence.
  change ((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v n (n + -1) (by omega)).hom
    (conePrecompEquiv R f Z n (n + -1) (by omega) z) = _
  simp only [conePrecompEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    map_add]
  erw [← ModuleCat.comp_apply, mappingCocone.inl_v_snd_v, ← ModuleCat.comp_apply,
    mappingCocone.inr_v_snd_v]
  simp

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
@[simp]
lemma linearHomComplexMappingConePrecompIso_hom_f_snd_ofHom (g : mappingCone f ⟶ Z) :
    dsimp% only [linearHomComplex_X]
      (((mappingCocone.snd (linearHomComplexPrecomp R f Z)).v 0 (-1) (by omega)).hom
        (((linearHomComplexMappingConePrecompIso R f Z).hom.f 0).hom (Cochain.ofHom g)) =
      -Cochain.ofHomotopy ((mappingCone.inrCompHomotopy f).compRight g)) := by
  erw [linearHomComplexMappingConePrecompIso_hom_f_snd]
  simp only [Int.reduceAdd, Int.negOnePow_one, Units.neg_smul, one_smul]
  congr 1
  refine Cochain.ext _ _ fun p q hpq ↦ ?_
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHomotopy,
    Cochain.mk_v, Homotopy.compRight_hom]
  rw [mappingCone.inrCompHomotopy_hom f p q (by omega)]

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
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  -- The native cocone is a shifted cone only after unfolding. Restate the component
  -- applications so rewriting does not pass through the composite's dependent source type.
  change ((linearHomComplexMappingConePrecompIso R f Z').inv.f n).hom
      ((((mappingCone.map (linearHomComplexPrecomp R f Z) (linearHomComplexPrecomp R f Z')
        (linearHomComplexPostcomp R Y g) (linearHomComplexPostcomp R X g)
        (linearHomComplexPrecomp_postcomp_comm R f g))⟦(-1 : ℤ)⟧').f n).hom z) =
    ((linearHomComplexPostcomp R (mappingCone f) g).f n).hom
      (((linearHomComplexMappingConePrecompIso R f Z).inv.f n).hom z)
  erw [linearHomComplexMappingConePrecompIso_inv_f_apply,
    linearHomComplexPostcomp_f_apply, linearHomComplexMappingConePrecompIso_inv_f_apply]
  apply (mappingCone.ext_cochain_from_iff f (n + -1) n (by omega)).2
  constructor
  · ext p q hpq
    rw [Cochain.comp_v _ _ _ p (p + -1) q rfl (by omega)]
    simp only [mappingCone.inl_v_descCochain_v]
    rw [Cochain.comp_v _ _ _ p (p + -1) q rfl (by omega),
      Cochain.comp_zero_cochain_v, mappingCone.inl_v_descCochain_v_assoc]
    have h := congrArg (fun k ↦ ModuleCat.Hom.hom k z)
      (mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v
        (linearHomComplexPrecomp R f Z) (linearHomComplexPrecomp R f Z')
        (linearHomComplexPostcomp R Y g) (linearHomComplexPostcomp R X g)
        (linearHomComplexPrecomp_postcomp_comm R f g) n)
    erw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, linearHomComplexPostcomp_f_apply] at h
    convert congrArg (fun k ↦ (n + 1).negOnePow • k) (Cochain.congr_v h p q hpq) using 1 <;>
      first | rfl | simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    rw [← Linear.units_smul_comp]
    congr 1
  · ext p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      mappingCone.inr_f_descCochain_v]
    rw [Cochain.comp_zero_cochain_v, mappingCone.inr_f_descCochain_v_assoc]
    have h := congrArg (fun k ↦ ModuleCat.Hom.hom k z)
      (HomologicalComplex.congr_hom
        (mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst
          (linearHomComplexPrecomp R f Z) (linearHomComplexPrecomp R f Z')
          (linearHomComplexPostcomp R Y g) (linearHomComplexPostcomp R X g)
          (linearHomComplexPrecomp_postcomp_comm R f g)) n)
    erw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      linearHomComplexPostcomp_f_apply] at h
    convert Cochain.congr_v h p q hpq using 1;
      simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]; rfl

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
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  -- Restate the component applications across the native cocone's shifted-cone model.
  change ((linearHomComplexMappingConePrecompIso R f₁ Z).inv.f n).hom
      ((((mappingCone.map (linearHomComplexPrecomp R f₂ Z) (linearHomComplexPrecomp R f₁ Z)
        (linearHomComplexPrecomp R b Z) (linearHomComplexPrecomp R a Z)
        (by simp only [← linearHomComplexPrecomp_comp, comm]))⟦(-1 : ℤ)⟧').f n).hom z) =
    ((linearHomComplexPrecomp R (mappingCone.map f₁ f₂ a b comm) Z).f n).hom
      (((linearHomComplexMappingConePrecompIso R f₂ Z).inv.f n).hom z)
  erw [linearHomComplexMappingConePrecompIso_inv_f_apply,
    linearHomComplexPrecomp_f_apply, linearHomComplexMappingConePrecompIso_inv_f_apply]
  apply (mappingCone.ext_cochain_from_iff f₁ (n + -1) n (by omega)).2
  constructor <;> ext p q hpq
  · rw [Cochain.comp_v _ _ _ p (p + -1) q rfl (by omega)]
    simp only [mappingCone.inl_v_descCochain_v]
    rw [Cochain.comp_v _ _ _ p (p + -1) q rfl (by omega)]
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      mappingCone.inl_v_map_f_assoc, mappingCone.inl_v_descCochain_v]
    have h := congrArg (fun k ↦ ModuleCat.Hom.hom k z)
      (mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v
        (linearHomComplexPrecomp R f₂ Z) (linearHomComplexPrecomp R f₁ Z)
        (linearHomComplexPrecomp R b Z) (linearHomComplexPrecomp R a Z)
        (by simp only [← linearHomComplexPrecomp_comp, comm]) n)
    erw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, linearHomComplexPrecomp_f_apply] at h
    convert congrArg (fun k ↦ (n + 1).negOnePow • k) (Cochain.congr_v h p q hpq) using 1 <;>
      first | rfl | simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    rw [← Linear.comp_units_smul]
    congr 1
  · simp only [Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, mappingCone.inr_f_descCochain_v,
      mappingCone.inr_f_map_f_assoc, mappingCone.inr_f_descCochain_v]
    have h := congrArg (fun k ↦ ModuleCat.Hom.hom k z)
      (HomologicalComplex.congr_hom
        (mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst
          (linearHomComplexPrecomp R f₂ Z) (linearHomComplexPrecomp R f₁ Z)
          (linearHomComplexPrecomp R b Z) (linearHomComplexPrecomp R a Z)
          (by simp only [← linearHomComplexPrecomp_comp, comm])) n)
    erw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      linearHomComplexPrecomp_f_apply] at h
    convert Cochain.congr_v h p q hpq using 1;
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]; rfl

end Squares

end TauCeti
