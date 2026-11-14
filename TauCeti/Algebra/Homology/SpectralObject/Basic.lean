/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Vanishing of `H^n` for a composite of three morphisms

For a spectral object `X` in an abelian category, over any index category, `H^n(f₁ ≫ f₂ ≫ f₃)`
vanishes as soon as `H^n(f₁ ≫ f₂)` and `H^n(f₂ ≫ f₃)` do
(`CategoryTheory.Abelian.SpectralObject.isZero_H_obj_mk₁_of_isZero_of_isZero`).
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

end CategoryTheory.Abelian.SpectralObject
