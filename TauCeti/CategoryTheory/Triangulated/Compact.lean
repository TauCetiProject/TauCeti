/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import TauCeti.CategoryTheory.Preadditive.Compact

import Mathlib.Algebra.FiveLemma
import TauCeti.Algebra.DirectSum.Exact

/-!
# Triangulated subcategory of compact objects

In a pretriangulated category `T` (with morphisms in `Type v`), the property
`TauCeti.compactForCoproducts T` of objects compact for coproducts is closed under extensions in
distinguished triangles (`TauCeti.IsCompactForCoproducts.of_distTriang`, via the five lemma) and
hence forms a triangulated subcategory (`(TauCeti.compactForCoproducts T).IsTriangulated`).

## Main results

* `TauCeti.IsCompactForCoproducts.of_distTriang`, `TauCeti.IsCompactForCoproducts.of_distTriang₁`,
  `TauCeti.IsCompactForCoproducts.of_distTriang₂`
* `(TauCeti.compactForCoproducts T).IsTriangulated`
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CategoryTheory.Pretriangulated
open scoped DirectSum

universe v u

namespace TauCeti

section Pretriangulated

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- If the first two objects of a distinguished triangle are compact for coproducts, then so is the
third object. -/
theorem IsCompactForCoproducts.of_distTriang {t : Triangle T} (ht : t ∈ distTriang T)
    (h₁ : IsCompactForCoproducts t.obj₁) (h₂ : IsCompactForCoproducts t.obj₂) :
    IsCompactForCoproducts t.obj₃ := by
  rw [isCompactForCoproducts_iff]
  intro J _ f _
  have ht₁ : t.rotate ∈ distTriang T := rot_of_distTriang _ ht
  have ht₂ : t.rotate.rotate ∈ distTriang T := rot_of_distTriang _ ht₁
  have hcomm {A B : T} (u : A ⟶ B) :
      (Preadditive.leftComp (∐ f) u).toIntLinearMap.comp
          (coprodComparisonAddHom B f).toIntLinearMap =
        (coprodComparisonAddHom A f).toIntLinearMap.comp
          (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) u).toIntLinearMap) :=
    DirectSum.linearMap_ext _ fun j ↦ LinearMap.ext fun g ↦ by
      simp [DirectSum.lof_eq_of, Preadditive.leftComp, Category.assoc]
  have hex {s : Triangle T} (hs : s ∈ distTriang T) (W : T) :
      Function.Exact (Preadditive.leftComp W s.mor₂).toIntLinearMap
        (Preadditive.leftComp W s.mor₁).toIntLinearMap := fun g ↦
    ⟨fun hg ↦ let ⟨h, hh⟩ := s.yoneda_exact₂ hs g hg; ⟨h, hh.symm⟩,
      fun ⟨h, hh⟩ ↦ hh ▸ (comp_distTriang_mor_zero₁₂_assoc _ hs h).trans zero_comp⟩
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (DirectSum.lmap (R := ℤ) fun j ↦
      (Preadditive.leftComp (f j) (-t.mor₁⟦(1 : ℤ)⟧')).toIntLinearMap)
    (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) t.mor₃).toIntLinearMap)
    (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) t.mor₂).toIntLinearMap)
    (DirectSum.lmap (R := ℤ) fun j ↦ (Preadditive.leftComp (f j) t.mor₁).toIntLinearMap)
    (Preadditive.leftComp (∐ f) (-t.mor₁⟦(1 : ℤ)⟧')).toIntLinearMap
    (Preadditive.leftComp (∐ f) t.mor₃).toIntLinearMap
    (Preadditive.leftComp (∐ f) t.mor₂).toIntLinearMap
    (Preadditive.leftComp (∐ f) t.mor₁).toIntLinearMap
    (coprodComparisonAddHom (t.obj₂⟦(1 : ℤ)⟧) f).toIntLinearMap
    (coprodComparisonAddHom (t.obj₁⟦(1 : ℤ)⟧) f).toIntLinearMap
    (coprodComparisonAddHom t.obj₃ f).toIntLinearMap
    (coprodComparisonAddHom t.obj₂ f).toIntLinearMap
    (coprodComparisonAddHom t.obj₁ f).toIntLinearMap
    (hcomm (-t.mor₁⟦(1 : ℤ)⟧')) (hcomm t.mor₃) (hcomm t.mor₂) (hcomm t.mor₁)
    (DirectSum.exact_lmap_iff.2 fun j ↦ hex ht₂ (f j))
    (DirectSum.exact_lmap_iff.2 fun j ↦ hex ht₁ (f j))
    (DirectSum.exact_lmap_iff.2 fun j ↦ hex ht (f j))
    (hex ht₂ (∐ f)) (hex ht₁ (∐ f)) (hex ht (∐ f))
    ((isCompactForCoproducts_iff _).1 (h₂.shift (1 : ℤ)) J f).2
    ((isCompactForCoproducts_iff _).1 (h₁.shift (1 : ℤ)) J f)
    ((isCompactForCoproducts_iff _).1 h₂ J f)
    ((isCompactForCoproducts_iff _).1 h₁ J f).1

/-- If the first and third objects of a distinguished triangle are compact for coproducts, then so
is the second object. -/
theorem IsCompactForCoproducts.of_distTriang₂ {t : Triangle T} (ht : t ∈ distTriang T)
    (h₁ : IsCompactForCoproducts t.obj₁) (h₃ : IsCompactForCoproducts t.obj₃) :
    IsCompactForCoproducts t.obj₂ :=
  (h₃.shift (-1 : ℤ)).of_distTriang (inv_rot_of_distTriang _ ht) h₁

/-- If the second and third objects of a distinguished triangle are compact for coproducts, then so
is the first object. -/
theorem IsCompactForCoproducts.of_distTriang₁ {t : Triangle T} (ht : t ∈ distTriang T)
    (h₂ : IsCompactForCoproducts t.obj₂) (h₃ : IsCompactForCoproducts t.obj₃) :
    IsCompactForCoproducts t.obj₁ :=
  (isCompactForCoproducts_shift_iff t.obj₁ (1 : ℤ)).1 (h₂.of_distTriang (rot_of_distTriang _ ht) h₃)

instance : (compactForCoproducts T).IsTriangulated where
  exists_zero := ⟨0, isZero_zero T, (compactForCoproducts_iff _).2 isCompactForCoproducts_zero⟩
  isStableUnderShiftBy a :=
    ⟨fun _ h ↦ (compactForCoproducts_iff _).2 (((compactForCoproducts_iff _).1 h).shift a)⟩
  toIsTriangulatedClosed₂ := .mk' fun _ ht h₁ h₃ ↦
    (compactForCoproducts_iff _).2
      (((compactForCoproducts_iff _).1 h₁).of_distTriang₂ ht ((compactForCoproducts_iff _).1 h₃))

end Pretriangulated

end TauCeti
