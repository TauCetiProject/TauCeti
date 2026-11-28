/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Decalage.Basic

/-!
# Composition of principal décalage

For scalars `f` and `g` acting injectively on each term of a cochain complex `C`,
`CochainComplex.principalDecalageMulIso` identifies the successive principal décalage
`E_g(E_f(C))` with `E_{f * g}(C)`. Both have the same underlying elements and divide
the differential by `f * g`. The comparison commutes with cochain maps by
`CochainComplex.principalDecalageMulHom_naturality`.

This is the principal complex calculation in Bhatt–Morrow–Scholze, *Integral
`p`-adic Hodge theory*, Lemma 6.11. It uses `CochainComplex.smul_principalDecalage_d`
to characterize division and `IsSMulRegular.mul` to cancel the product.
-/

public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℤ) (f g : R)

variable (hf : ∀ n, IsSMulRegular (C.X n) f) (hg : ∀ n, IsSMulRegular (C.X n) g)

variable {C f g} in
/-- Divisibility by `g` in `E_f(C)` amounts to divisibility by `f * g` in `C`.
For this degreewise test, `g` needs to act injectively only in degree `n + 2`. -/
@[simp]
lemma mem_decalageSubmodule_principalDecalage_iff {n : ℤ} {x : C.decalageSubmodule f n}
    (hg₂ : IsSMulRegular (C.X (n + 1 + 1)) g) :
    x ∈ (C.principalDecalage f hf).decalageSubmodule g n ↔
      x.val ∈ C.decalageSubmodule (f * g) n := by
  rw [(C.principalDecalage f hf).mem_decalageSubmodule_iff g, principalDecalage_d_apply,
    C.mem_decalageSubmodule_iff (f * g)]
  constructor
  · rintro ⟨y, hy⟩
    have hyVal : g • y.val = (principalDecalageD hf n x : C.X (n + 1)) :=
      congrArg Subtype.val hy
    refine ⟨y.val, ?_⟩
    rw [mul_smul, hyVal, smul_principalDecalageD]
  · rintro ⟨y, hy⟩
    have hδ : (principalDecalageD hf n x : C.X (n + 1)) = g • y :=
      (principalDecalageD_eq_iff hf).2 (by simpa only [mul_smul] using hy)
    have hyCycle : C.d (n + 1) (n + 1 + 1) y = 0 := by
      refine hg₂ ?_
      beta_reduce
      rw [smul_zero, ← map_smul, ← hδ, d_principalDecalageD]
    exact ⟨⟨y, C.mem_decalageSubmodule_of_d_eq_zero f hyCycle⟩, Subtype.ext hδ.symm⟩

/-- The canonical cochain map from successive principal décalage to décalage by the product.
Its components forget the intermediate divisibility witness. -/
noncomputable def principalDecalageMulHom :
    (C.principalDecalage f hf).principalDecalage g
        (fun n ↦ (hg n).of_injective (C.decalageSubmodule f n).subtype Subtype.val_injective) ⟶
      C.principalDecalage (f * g) (fun n ↦ (hf n).mul (hg n)) :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom
      (((C.decalageSubmodule f n).subtype ∘ₗ
        ((C.principalDecalage f hf).decalageSubmodule g n).subtype).codRestrict _ fun x ↦
          (mem_decalageSubmodule_principalDecalage_iff hf (hg _)).1 x.property))
    (fun n ↦ by
      ext x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
      refine ((hf (n + 1)).mul (hg (n + 1))) ?_
      beta_reduce
      rw [smul_principalDecalage_d, mul_smul]
      exact ((congrArg (fun y : C.decalageSubmodule f (n + 1) ↦ f • y.val)
        (smul_principalDecalage_d
          (fun i ↦ (hg i).of_injective (C.decalageSubmodule f i).subtype Subtype.val_injective)
          n (n + 1) x)).trans
        (smul_principalDecalage_d hf n (n + 1) x.val)).symm)

/-- The comparison map preserves the underlying element of `C.X n`. -/
@[simp]
lemma principalDecalageMulHom_f_apply (n : ℤ)
    (x : (C.principalDecalage f hf).decalageSubmodule g n) :
    ((C.principalDecalageMulHom f g hf hg).f n x).val = x.val.val :=
  (rfl)

/-- The comparison map is bijective in every degree. -/
instance isIso_principalDecalageMulHom : IsIso (C.principalDecalageMulHom f g hf hg) := by
  have (n : ℤ) : IsIso ((C.principalDecalageMulHom f g hf hg).f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      have hVal : ((C.principalDecalageMulHom f g hf hg).f n x).val =
          ((C.principalDecalageMulHom f g hf hg).f n y).val := congrArg Subtype.val h
      rw [principalDecalageMulHom_f_apply, principalDecalageMulHom_f_apply] at hVal
      exact hVal
    · intro x
      have hx : x.val ∈ C.decalageSubmodule f n := by
        obtain ⟨y, hy⟩ := (C.mem_decalageSubmodule_iff (f * g)).1 x.property
        exact mem_decalageSubmodule_of_smul_eq ((mul_smul f g y).symm.trans hy)
      refine ⟨⟨⟨x.val, hx⟩, ?_⟩, ?_⟩
      · exact (mem_decalageSubmodule_principalDecalage_iff hf (hg _)).2 x.property
      · exact Subtype.ext (C.principalDecalageMulHom_f_apply f g hf hg n _)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Successive principal décalage agrees with principal décalage by the product of the two
scalars when both act injectively in each degree. The isomorphism preserves the underlying
element in each integer degree (Bhatt–Morrow–Scholze, Lemma 6.11). -/
noncomputable def principalDecalageMulIso :
    (C.principalDecalage f hf).principalDecalage g
        (fun n ↦ (hg n).of_injective (C.decalageSubmodule f n).subtype Subtype.val_injective) ≅
      C.principalDecalage (f * g) (fun n ↦ (hf n).mul (hg n)) :=
  asIso (C.principalDecalageMulHom f g hf hg)

@[simp]
lemma principalDecalageMulIso_hom :
    (C.principalDecalageMulIso f g hf hg).hom = C.principalDecalageMulHom f g hf hg :=
  (rfl)

/-- The inverse comparison preserves the underlying element of `C.X n`. -/
@[simp]
lemma principalDecalageMulIso_inv_f_apply (n : ℤ) (x : C.decalageSubmodule (f * g) n) :
    ((C.principalDecalageMulIso f g hf hg).inv.f n x).val.val = x.val := by
  rw [← C.principalDecalageMulHom_f_apply f g hf hg]
  rw [← C.principalDecalageMulIso_hom f g hf hg, ← ModuleCat.comp_apply,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply]

variable {C} {D : CochainComplex (ModuleCat.{v} R) ℤ}
  (hfD : ∀ n, IsSMulRegular (D.X n) f) (hgD : ∀ n, IsSMulRegular (D.X n) g)

/-- The comparison of successive décalage with décalage by the product commutes with cochain
maps. -/
@[reassoc (attr := simp)]
lemma principalDecalageMulHom_naturality (φ : C ⟶ D) :
    principalDecalageMap
        (fun n ↦ (hg n).of_injective (C.decalageSubmodule f n).subtype Subtype.val_injective)
        (fun n ↦ (hgD n).of_injective (D.decalageSubmodule f n).subtype Subtype.val_injective)
        (principalDecalageMap hf hfD φ) ≫
        D.principalDecalageMulHom f g hfD hgD =
      C.principalDecalageMulHom f g hf hg ≫
        principalDecalageMap (fun n ↦ (hf n).mul (hg n)) (fun n ↦ (hfD n).mul (hgD n)) φ := by
  ext n x
  simp only [HomologicalComplex.comp_f]
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  -- Evaluate the two paths in the ambient term of `D`.
  rw [principalDecalageMulHom_f_apply, principalDecalageMap_f_apply, principalDecalageMap_f_apply]
  rw [principalDecalageMap_f_apply, principalDecalageMulHom_f_apply]

end CochainComplex
