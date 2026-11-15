/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Lifting obstructions in distinguished triangles and triangulated functors

Let `A ⟶ B ⟶ Q ⟶ A⟦1⟧` be a distinguished triangle `T` in a pretriangulated category. A morphism
`s : M ⟶ Q` lifts along `B ⟶ Q` exactly when its obstruction `s ≫ T.mor₃ : M ⟶ A⟦1⟧` vanishes
(`CategoryTheory.Pretriangulated.Triangle.exists_comp_mor₂_eq_iff`), and `B ⟶ Q` is a split
epimorphism exactly when the connecting morphism `T.mor₃` vanishes
(`CategoryTheory.Pretriangulated.Triangle.isSplitEpi_mor₂_iff`). These restate Mathlib's
`Triangle.coyoneda_exact₃` and `Triangle.mor₃_eq_zero_iff_epi₂` as characterizations.

A triangulated functor `F` carries the obstruction of `s` to the obstruction of `F.map s` for the
image triangle `F.mapTriangle.obj T`, up to the isomorphism expressing that `F` commutes with the
shift. Consequently, if `F` is injective on `M ⟶ A⟦1⟧`, then `s` lifts as soon as `F.map s` lifts
(`CategoryTheory.Functor.exists_comp_map_mor₂_eq_iff_of_injective`), and if `F` is injective on
`Q ⟶ A⟦1⟧`, then `B ⟶ Q` splits as soon as its image does
(`CategoryTheory.Functor.isSplitEpi_map_mor₂_iff_of_injective`). This is how
a splitting is certified by computing in a target category in which obstructions are easier to
control, as in Bhatt's proof of the derived direct summand conjecture. The injectivity hypothesis
cannot be dropped: a functor may kill a nonzero obstruction, and then the image triangle splits
although the original one does not.

## References

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212
  (2018), proof of Theorem 5.4.
-/

public section

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Pretriangulated

variable {T : Triangle C} (hT : T ∈ distTriang C)
include hT

/-- A morphism into the third object of a distinguished triangle lifts along the second
morphism exactly when its composite with the connecting morphism vanishes. -/
theorem Triangle.exists_comp_mor₂_eq_iff {M : C} (s : M ⟶ T.obj₃) :
    (∃ g : M ⟶ T.obj₂, g ≫ T.mor₂ = s) ↔ s ≫ T.mor₃ = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    rw [assoc, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]
  · obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT s h
    exact ⟨g, hg.symm⟩

/-- The second morphism of a distinguished triangle is a split epimorphism exactly when the
connecting morphism vanishes. -/
theorem Triangle.isSplitEpi_mor₂_iff : IsSplitEpi T.mor₂ ↔ T.mor₃ = 0 := by
  rw [T.mor₃_eq_zero_iff_epi₂ hT]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ isSplitEpi_of_epi _⟩

end Pretriangulated

namespace Functor

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] {T : Triangle C} (hT : T ∈ distTriang C)
include hT

/-- Let `F` be a triangulated functor and `T` a distinguished triangle. If `F` is injective on
morphisms `M ⟶ T.obj₁⟦1⟧`, then a morphism `s : M ⟶ T.obj₃` lifts along `T.mor₂` exactly when
`F.map s` lifts along `F.map T.mor₂`. -/
theorem exists_comp_map_mor₂_eq_iff_of_injective {M : C} (s : M ⟶ T.obj₃)
    (hF : Function.Injective (F.map : (M ⟶ T.obj₁⟦(1 : ℤ)⟧) → _)) :
    (∃ g : F.obj M ⟶ F.obj T.obj₂, g ≫ F.map T.mor₂ = F.map s) ↔
      ∃ g : M ⟶ T.obj₂, g ≫ T.mor₂ = s := by
  rw [Triangle.exists_comp_mor₂_eq_iff hT]
  refine (Triangle.exists_comp_mor₂_eq_iff (F.map_distinguished T hT) (F.map s)).trans ?_
  dsimp only [mapTriangle_obj, Triangle.mk_mor₃]
  rw [← F.map_comp_assoc, IsIso.comp_right_eq_zero, ← F.map_zero, hF.eq_iff]

/-- Let `F` be a triangulated functor and `T` a distinguished triangle. If `F` is injective on
morphisms `T.obj₃ ⟶ T.obj₁⟦1⟧`, then `T.mor₂` is a split epimorphism exactly when
`F.map T.mor₂` is. -/
theorem isSplitEpi_map_mor₂_iff_of_injective
    (hF : Function.Injective (F.map : (T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧) → _)) :
    IsSplitEpi (F.map T.mor₂) ↔ IsSplitEpi T.mor₂ := by
  rw [Triangle.isSplitEpi_mor₂_iff hT]
  refine (Triangle.isSplitEpi_mor₂_iff (F.map_distinguished T hT)).trans ?_
  rw [mapTriangle_obj, Triangle.mk_mor₃, IsIso.comp_right_eq_zero, ← F.map_zero, hF.eq_iff]

end Functor

end CategoryTheory
