/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Localization
public import TauCeti.Algebra.Homology.ModuleCat.Decalage.Basic

/-!
# Décalage inside the localized complex

Inside the termwise localization `C[1/f]` of a cochain complex of modules, the classical
décalage `η_f C` consists in degree `n` of the elements of `fⁿ Cⁿ` whose differential is in
`fⁿ⁺¹ Cⁿ⁺¹`. Here both submodules are images in the localization, so the construction works
in negative degrees and the differential is the restriction of the localized differential.

When multiplication by `f` is injective on the terms of `C`,
`CochainComplex.principalDecalageIsoLocalizedDecalage` identifies the normalized décalage
with this subcomplex. It sends `x` in degree `n` to `fⁿ • (x/1)`.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Construction 2.1.3.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Definition 6.2.
-/

public section

open CategoryTheory ModuleCat

universe v u

namespace CochainComplex

variable {R : Type u} [CommRing R] [Small.{v} R]
variable (C : CochainComplex (ModuleCat.{v} R) ℤ) (f : R)

local notation "locChains" => Functor.mapHomologicalComplex
  (localizedModuleFunctor (Submonoid.powers f) ⋙
    restrictScalars (algebraMap R (Localization.Away f)))
  (ComplexShape.up ℤ)
local notation "locC" => Functor.obj (locChains) C

/-- The degree-`n` term of the classical décalage inside `C[1/f]`. -/
noncomputable def localizedDecalageSubmodule (n : ℤ) : Submodule R ((locC).X n) :=
  LinearMap.range ((toLocalizedModuleZPow f n).app (C.X n)).hom ⊓
    (LinearMap.range ((toLocalizedModuleZPow f (n + 1)).app (C.X (n + 1))).hom).comap
      ((locC).d n (n + 1)).hom

/-- Membership in `η_f Cⁿ` amounts to lifting the element and its differential to
`Cⁿ` and `Cⁿ⁺¹` with respective factors `fⁿ` and `fⁿ⁺¹`. -/
@[simp]
lemma mem_localizedDecalageSubmodule_iff {n : ℤ} {z : (locC).X n} :
    z ∈ C.localizedDecalageSubmodule f n ↔
      (∃ x, (toLocalizedModuleZPow f n).app (C.X n) x = z) ∧
      ∃ y, (toLocalizedModuleZPow f (n + 1)).app (C.X (n + 1)) y = (locC).d n (n + 1) z :=
  Iff.rfl

/-- The localized differential preserves the décalage submodules. -/
lemma d_mem_localizedDecalageSubmodule {i j : ℤ} {z : (locC).X i}
    (hz : z ∈ C.localizedDecalageSubmodule f i) :
    (locC).d i j z ∈ C.localizedDecalageSubmodule f j := by
  by_cases hij : i + 1 = j
  · subst j
    refine (C.mem_localizedDecalageSubmodule_iff f).2 ⟨hz.2, 0, ?_⟩
    rw [map_zero, (locC).d_comp_d_apply]
  · rw [(locC).shape i j hij]
    exact Submodule.zero_mem _

/-- The classical décalage `η_f C ⊆ C[1/f]`, with the ambient differential. -/
noncomputable abbrev localizedDecalage : CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (C.localizedDecalageSubmodule f i)
  d i j := ModuleCat.ofHom (((locC).d i j).hom.restrict fun _ ↦
    C.d_mem_localizedDecalageSubmodule f)
  shape i j hij := ModuleCat.hom_ext (LinearMap.ext fun x ↦
    Subtype.ext (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((locC).shape i j hij)) x.val))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦
    Subtype.ext ((locC).d_comp_d_apply i j k x.val))

/-- The inclusion of the classical décalage in the termwise localization of `C`. -/
noncomputable def localizedDecalageι : C.localizedDecalage f ⟶ locC where
  f i := ModuleCat.ofHom (X := (C.localizedDecalage f).X i) (Y := (locC).X i)
    (C.localizedDecalageSubmodule f i).subtype
  comm' _ _ _ := rfl

@[simp]
lemma localizedDecalageι_f_apply (i : ℤ) (x : C.localizedDecalageSubmodule f i) :
    dsimp% only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj]
      (C.localizedDecalageι f).f i x = x.val := (rfl)

instance : Mono (C.localizedDecalageι f) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

section Map

variable {C} {D K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- Localizing a cochain map carries the décalage submodule into the décalage submodule. -/
lemma map_mem_localizedDecalageSubmodule (φ : C ⟶ D) {n : ℤ} {z : (locC).X n}
    (hz : z ∈ C.localizedDecalageSubmodule f n) :
    ((locChains).map φ).f n z ∈ D.localizedDecalageSubmodule f n := by
  obtain ⟨⟨x, rfl⟩, y, hy⟩ := (C.mem_localizedDecalageSubmodule_iff f).1 hz
  refine (D.mem_localizedDecalageSubmodule_iff f).2 ⟨⟨φ.f n x, ?_⟩, φ.f (n + 1) y, ?_⟩
  · exact (toLocalizedModuleZPow f n).naturality_apply (φ.f n) x
  · rw [HomologicalComplex.Hom.comm_apply ((locChains).map φ), ← hy]
    exact (toLocalizedModuleZPow f (n + 1)).naturality_apply (φ.f (n + 1)) y

/-- The map of classical décalages induced by restricting the localized cochain map. -/
noncomputable def localizedDecalageMap (φ : C ⟶ D) :
    C.localizedDecalage f ⟶ D.localizedDecalage f where
  f n := ModuleCat.ofHom ((((locChains).map φ).f n).hom.restrict fun _ ↦
    map_mem_localizedDecalageSubmodule f φ)
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦
    Subtype.ext (((locChains).map φ).comm_apply i j x.val))

@[simp]
lemma localizedDecalageMap_f_apply (φ : C ⟶ D) (n : ℤ) (x : C.localizedDecalageSubmodule f n) :
    dsimp% only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj]
      Subtype.val ((localizedDecalageMap f φ).f n x) = ((locChains).map φ).f n x.val := (rfl)

/-- The inclusion of the classical décalage into the localization is natural. -/
@[reassoc (attr := simp)]
lemma localizedDecalageMap_ι (φ : C ⟶ D) :
    localizedDecalageMap f φ ≫ D.localizedDecalageι f =
      C.localizedDecalageι f ≫ (locChains).map φ := by
  ext n x
  rfl

@[simp]
lemma localizedDecalageMap_id : localizedDecalageMap f (𝟙 C) = 𝟙 _ := by
  rw [← cancel_mono (C.localizedDecalageι f)]
  simp

@[simp]
lemma localizedDecalageMap_comp (φ : C ⟶ D) (ψ : D ⟶ K) :
    localizedDecalageMap f (φ ≫ ψ) = localizedDecalageMap f φ ≫ localizedDecalageMap f ψ := by
  rw [← cancel_mono (K.localizedDecalageι f)]
  simp

end Map

/-- The image of the normalized degree-`n` term under `x ↦ fⁿ • (x/1)` is precisely
the classical degree-`n` term. Regularity is needed only in degree `n + 1`. -/
lemma map_decalageSubmodule_toLocalizedModuleZPow (n : ℤ) (h : IsSMulRegular (C.X (n + 1)) f) :
    (C.decalageSubmodule f n).map ((toLocalizedModuleZPow f n).app (C.X n)).hom =
      C.localizedDecalageSubmodule f n := by
  have hd (x : C.X n) : (locC).d n (n + 1) ((toLocalizedModuleZPow f n).app (C.X n) x) =
      (toLocalizedModuleZPow f n).app (C.X (n + 1)) (C.d n (n + 1) x) :=
    ((toLocalizedModuleZPow f n).naturality_apply (C.d n (n + 1)) x).symm
  ext z
  rw [mem_localizedDecalageSubmodule_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (C.mem_decalageSubmodule_iff f).1 hx
    exact ⟨⟨x, rfl⟩, y, by rw [hd, toLocalizedModuleZPow_succ_apply, hy]⟩
  · rintro ⟨⟨x, rfl⟩, y, hy⟩
    rw [hd, toLocalizedModuleZPow_succ_apply] at hy
    exact ⟨x, mem_decalageSubmodule_of_smul_eq (toLocalizedModuleZPow_injective f h n hy), rfl⟩

variable {C f}

private noncomputable def localizedDecalageEquiv (n : ℤ) (hi : IsSMulRegular (C.X n) f)
    (hj : IsSMulRegular (C.X (n + 1)) f) :
    C.decalageSubmodule f n ≃ₗ[R] C.localizedDecalageSubmodule f n :=
  (Submodule.equivMapOfInjective ((toLocalizedModuleZPow f n).app (C.X n)).hom
    (toLocalizedModuleZPow_injective f hi n) _).trans
    (LinearEquiv.ofEq _ _ (C.map_decalageSubmodule_toLocalizedModuleZPow f n hj))

private lemma coe_localizedDecalageEquiv (n : ℤ) (hi : IsSMulRegular (C.X n) f)
    (hj : IsSMulRegular (C.X (n + 1)) f) (x : C.decalageSubmodule f n) :
    Subtype.val (localizedDecalageEquiv n hi hj x) =
      (toLocalizedModuleZPow f n).app (C.X n) x.val :=
  rfl

variable (hC : ∀ n, IsSMulRegular (C.X n) f)

/-- Multiplication by `fⁿ` in degree `n` identifies the normalized décalage with the
classical décalage inside `C[1/f]`. -/
noncomputable def principalDecalageIsoLocalizedDecalage :
    C.principalDecalage f hC ≅ C.localizedDecalage f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (localizedDecalageEquiv n (hC n) (hC (n + 1))).toModuleIso)
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      -- Evaluate the component isomorphisms as the scaled localization maps.
      change (locC).d i (i + 1) (localizedDecalageEquiv i (hC i) (hC (i + 1)) x).val =
        (localizedDecalageEquiv (i + 1) (hC _) (hC _)
          ((C.principalDecalage f hC).d i (i + 1) x)).val
      rw [coe_localizedDecalageEquiv, coe_localizedDecalageEquiv, toLocalizedModuleZPow_succ_apply,
        smul_principalDecalage_d]
      exact ((toLocalizedModuleZPow f i).naturality_apply (C.d i (i + 1)) x.val).symm

/-- In the ambient localization the comparison isomorphism sends `x` to `fⁿ • (x/1)`. -/
@[simp]
lemma principalDecalageIsoLocalizedDecalage_hom_f_apply (n : ℤ) (x : C.decalageSubmodule f n) :
    dsimp% only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj]
      Subtype.val ((principalDecalageIsoLocalizedDecalage hC).hom.f n x) =
      (toLocalizedModuleZPow f n).app (C.X n) x.val :=
  (rfl)

/-- Rescaling the element recovered by the inverse comparison gives the original fraction. -/
@[simp]
lemma zpow_smul_principalDecalageIsoLocalizedDecalage_inv_f_apply (n : ℤ)
    (z : C.localizedDecalageSubmodule f n) :
    dsimp% only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj]
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).unit ^ n) •
        (C.X n).localizedModuleMkLinearMap (.powers f)
          ((principalDecalageIsoLocalizedDecalage hC).inv.f n z).val = z.val := by
  rw [← toLocalizedModuleZPow_app_apply, ← principalDecalageIsoLocalizedDecalage_hom_f_apply hC]
  exact congrArg Subtype.val ((HomologicalComplex.Hom.isoApp
    (principalDecalageIsoLocalizedDecalage hC) n).inv_hom_id_apply z)

/-- The isomorphism between normalized and classical décalage is natural in the complex. -/
@[reassoc]
lemma principalDecalageIsoLocalizedDecalage_naturality {D : CochainComplex (ModuleCat.{v} R) ℤ}
    (hD : ∀ n, IsSMulRegular (D.X n) f) (φ : C ⟶ D) :
    principalDecalageMap hC hD φ ≫ (principalDecalageIsoLocalizedDecalage hD).hom =
      (principalDecalageIsoLocalizedDecalage hC).hom ≫ localizedDecalageMap f φ := by
  ext n x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [principalDecalageIsoLocalizedDecalage_hom_f_apply,
    localizedDecalageMap_f_apply, principalDecalageMap_f_apply,
    principalDecalageIsoLocalizedDecalage_hom_f_apply]
  exact (toLocalizedModuleZPow f n).naturality_apply (φ.f n) x.val

end CochainComplex
