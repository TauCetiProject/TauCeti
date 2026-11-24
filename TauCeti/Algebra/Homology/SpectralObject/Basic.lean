/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Spectral objects: vanishing of `H^n` and isomorphisms

For a spectral object `X` in an abelian category, over any index category, `H^n(f₁ ≫ f₂ ≫ f₃)`
vanishes as soon as `H^n(f₁ ≫ f₂)` and `H^n(f₂ ≫ f₃)` do
(`CategoryTheory.Abelian.SpectralObject.isZero_H_obj_mk₁_of_isZero_of_isZero`). For composable
`f`, `g`, the map `H^{n₁}(f) ⟶ H^{n₁}(f ≫ g)` is a monomorphism when `H^{n₀}(g)` vanishes
(`n₀ + 1 = n₁`), an epimorphism when `H^{n₁}(g)` vanishes, and an isomorphism when both do
(`CategoryTheory.Abelian.SpectralObject.isIso_H_map_twoδ₂Toδ₁`); this complements Mathlib's
`CategoryTheory.Abelian.SpectralObject.isIso_H_map_twoδ₁Toδ₀` for the other face map.

A morphism `φ` of spectral objects is an isomorphism exactly when it is one on every `H^n(f)`
(`CategoryTheory.Abelian.SpectralObject.isIso_iff_isIso_hom_app`); its components `φ.hom n` are
then isomorphisms, with inverses the components of `inv φ`
(`CategoryTheory.Abelian.SpectralObject.inv_hom`).
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι] (X : SpectralObject C ι)

/-- For three composable morphisms `f₁`, `f₂`, `f₃`, if `H^n(f₁ ≫ f₂)` and `H^n(f₂ ≫ f₃)` vanish
then so does `H^n(f₁ ≫ f₂ ≫ f₃)`. -/
lemma isZero_H_obj_mk₁_of_isZero_of_isZero {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
    (f₃ : i₂ ⟶ i₃) (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃) (f₁₂₃ : i₀ ⟶ i₃) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (h₂₃ : f₂ ≫ f₃ = f₂₃) (h₁₂₃ : f₁ ≫ f₂₃ = f₁₂₃) (n : ℤ)
    (h₁₂_zero : IsZero ((X.H n).obj (mk₁ f₁₂))) (h₂₃_zero : IsZero ((X.H n).obj (mk₁ f₂₃))) :
    IsZero ((X.H n).obj (mk₁ f₁₂₃)) := by
  have h₁₂₃' : f₁₂ ≫ f₃ = f₁₂₃ := by rw [← h₁₂, Category.assoc, h₂₃, h₁₂₃]
  -- `H^n(f₁) ⟶ H^n(f₁ ≫ f₂ ≫ f₃)` is epi by exactness, since `H^n(f₂ ≫ f₃) = 0`
  have hepi : Epi ((X.H n).map (twoδ₂Toδ₁ f₁ f₂₃ f₁₂₃ h₁₂₃)) :=
    (X.exact₂ f₁ f₂₃ f₁₂₃ h₁₂₃ n).epi_f (h₂₃_zero.eq_of_tgt _ _)
  refine IsZero.of_epi_eq_zero ((X.H n).map (twoδ₂Toδ₁ f₁ f₂₃ f₁₂₃ h₁₂₃)) ?_
  -- it factors through `H^n(f₁ ≫ f₂) = 0`
  have hfac : twoδ₂Toδ₁ f₁ f₂₃ f₁₂₃ h₁₂₃ =
      twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂ ≫ twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃' := by
    ext <;> simp [h₂₃]
  rw [hfac, Functor.map_comp, h₁₂_zero.eq_of_tgt ((X.H n).map _) 0, zero_comp]

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i₀ i₁ i₂ : ι}
  (f : i₀ ⟶ i₁) (g : i₁ ⟶ i₂) (fg : i₀ ⟶ i₂) (hfg : f ≫ g = fg)
  (h₁ : IsZero ((X.H n₀).obj (mk₁ g))) (h₂ : IsZero ((X.H n₁).obj (mk₁ g)))

include h₁ hn₁ in
/-- `H^{n₁}(f) ⟶ H^{n₁}(f ≫ g)` is a monomorphism when `H^{n₀}(g)` vanishes, for
`n₀ + 1 = n₁`. -/
lemma mono_H_map_twoδ₂Toδ₁ : Mono ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) :=
  (X.exact₁ f g fg hfg n₀ n₁ hn₁).mono_g (h₁.eq_of_src _ _)

include h₂ in
/-- `H^{n₁}(f) ⟶ H^{n₁}(f ≫ g)` is an epimorphism when `H^{n₁}(g)` vanishes. -/
lemma epi_H_map_twoδ₂Toδ₁ : Epi ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) :=
  (X.exact₂ f g fg hfg n₁).epi_f (h₂.eq_of_tgt _ _)

include h₁ h₂ hn₁ in
/-- `H^{n₁}(f) ⟶ H^{n₁}(f ≫ g)` is an isomorphism when `H^{n₀}(g)` and `H^{n₁}(g)` vanish, for
`n₀ + 1 = n₁`. -/
lemma isIso_H_map_twoδ₂Toδ₁ : IsIso ((X.H n₁).map (twoδ₂Toδ₁ f g fg hfg)) := by
  have := X.mono_H_map_twoδ₂Toδ₁ n₀ n₁ hn₁ f g fg hfg h₁
  have := X.epi_H_map_twoδ₂Toδ₁ n₁ f g fg hfg h₂
  exact isIso_of_mono_of_epi _

end

section

variable {ι' : Type*} [Preorder ι'] (X' : SpectralObject C ι')
  (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (i₀ i₁ i₂ : ι') (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂)
  (h₁ : IsZero ((X'.H n₀).obj (mk₁ (homOfLE h₁₂))))
  (h₂ : IsZero ((X'.H n₁).obj (mk₁ (homOfLE h₁₂))))

include h₁ hn₁ in
/-- Variant of `mono_H_map_twoδ₂Toδ₁` for preorders. -/
lemma mono_H_map_twoδ₂Toδ₁' : Mono ((X'.H n₁).map (twoδ₂Toδ₁' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.mono_H_map_twoδ₂Toδ₁ _ _ hn₁ _ _ _ _ h₁

include h₂ in
/-- Variant of `epi_H_map_twoδ₂Toδ₁` for preorders. -/
lemma epi_H_map_twoδ₂Toδ₁' : Epi ((X'.H n₁).map (twoδ₂Toδ₁' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.epi_H_map_twoδ₂Toδ₁ _ _ _ _ _ h₂

include h₁ h₂ hn₁ in
/-- Variant of `isIso_H_map_twoδ₂Toδ₁` for preorders. -/
lemma isIso_H_map_twoδ₂Toδ₁' : IsIso ((X'.H n₁).map (twoδ₂Toδ₁' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.isIso_H_map_twoδ₂Toδ₁ _ _ hn₁ _ _ _ _ h₁ h₂

end

section IsIso

variable {X} {Y : SpectralObject C ι} (φ : X ⟶ Y)

/-- The components of an isomorphism of spectral objects are isomorphisms. -/
instance isIso_hom [IsIso φ] (n : ℤ) : IsIso (φ.hom n) :=
  ⟨(inv φ).hom n, by rw [← comp_hom, IsIso.hom_inv_id, id_hom],
    by rw [← comp_hom, IsIso.inv_hom_id, id_hom]⟩

/-- The components of the inverse of an isomorphism of spectral objects are the inverses of its
components. -/
@[simp]
lemma inv_hom [IsIso φ] (n : ℤ) : (inv φ).hom n = inv (φ.hom n) :=
  IsIso.eq_inv_of_hom_inv_id (by rw [← comp_hom, IsIso.hom_inv_id, id_hom])

/-- A morphism of spectral objects is an isomorphism as soon as it is one on every `H^n(f)`. -/
lemma isIso_of_isIso_hom_app
    (h : ∀ (n : ℤ) {i j : ι} (f : i ⟶ j), IsIso ((φ.hom n).app (mk₁ f))) : IsIso φ := by
  have hφ (n : ℤ) : IsIso (φ.hom n) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro D
    obtain ⟨_, _, f, rfl⟩ := mk₁_surjective D
    exact h n f
  refine ⟨⟨fun n ↦ inv (φ.hom n), fun n₀ n₁ hn₁ i j k f g ↦ ?_⟩, ?_, ?_⟩
  · rw [← cancel_epi ((φ.hom n₀).app (mk₁ g)), ← φ.comm_assoc]
    simp
  all_goals exact Hom.ext (funext fun n ↦ by simp)

/-- A morphism of spectral objects is an isomorphism exactly when it is one on every `H^n(f)`. -/
lemma isIso_iff_isIso_hom_app :
    IsIso φ ↔ ∀ (n : ℤ) {i j : ι} (f : i ⟶ j), IsIso ((φ.hom n).app (mk₁ f)) :=
  ⟨fun _ _ _ _ _ ↦ inferInstance, isIso_of_isIso_hom_app φ⟩

end IsIso

end CategoryTheory.Abelian.SpectralObject
