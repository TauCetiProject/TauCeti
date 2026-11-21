/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.CategoryTheory.Triangulated.Biproduct
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Split `K₀` and dense subcategories of a pretriangulated category

Let `C` be an essentially small pretriangulated category and `A` an isomorphism-closed property of
objects of `C` which is *dense*: `A.retractClosure = ⊤`, so that every object of `C` is a direct
summand of an object satisfying `A`
(`CategoryTheory.ObjectProperty.prop_retractClosure_iff_exists_biprod`).

Two objects have the same class in split `K₀` of `C` exactly when `X ⊞ W ≅ Y ⊞ W` for some `W`.
Density lets one choose `W` in `A`: pick `W'` with `W ⊞ W'` in `A` and add `W'` on both sides.
Consequently, when `A` is moreover a triangulated subcategory, two objects of `A` with the same
class in split `K₀` of `C` already have the same class in split `K₀` of `A`, so the inclusion
induces an injection of split `K₀` groups.

## Main results

* `TauCeti.SplitK0.of_eq_of_iff_of_retractClosure_eq_top`: for dense `A`, `[X] = [Y]` in split
  `K₀` of `C` if and only if `X ⊞ B ≅ Y ⊞ B` for some `B` satisfying `A`.
* `TauCeti.SplitK0.map_ι_injective_of_retractClosure_eq_top`: for a dense triangulated
  subcategory `A`, the map from split `K₀` of `A` to split `K₀` of `C` is injective.

## References

* R. W. Thomason, *The classification of triangulated subcategories*, Compositio Mathematica
  **105** (1997), 1–27, Lemma 2.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe w w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]

namespace SplitK0

variable (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms]

/-- **Stable isomorphisms are realised in a dense subcategory**: if `A` is dense, two objects have
the same class in split `K₀` exactly when they become isomorphic after adding an object of `A`. -/
theorem of_eq_of_iff_of_retractClosure_eq_top (hA : A.retractClosure = ⊤) {X Y : C} :
    (of X : SplitK0 C) = of Y ↔ ∃ B : C, A B ∧ Nonempty (X ⊞ B ≅ Y ⊞ B) := by
  refine ⟨fun h => ?_, fun ⟨B, _, h⟩ => of_eq_of_iff.2 ⟨B, h⟩⟩
  obtain ⟨W, ⟨e⟩⟩ := of_eq_of_iff.1 h
  obtain ⟨W', hW'⟩ := (A.prop_retractClosure_iff_exists_biprod W).1 (by rw [hA]; trivial)
  exact ⟨W ⊞ W', hW', ⟨(biprod.associator _ _ _).symm ≪≫ biprod.mapIso e (Iso.refl _) ≪≫
    biprod.associator _ _ _⟩⟩

variable [A.IsTriangulated] [EssentiallySmall.{w'} A.FullSubcategory]

/-- For a dense triangulated subcategory `A`, the inclusion is injective on split `K₀`: two objects
of `A` which become isomorphic after adding an object of `C` already become isomorphic after
adding an object of `A`. -/
theorem map_ι_injective_of_retractClosure_eq_top (hA : A.retractClosure = ⊤) :
    Function.Injective (map A.ι) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨P, Q, rfl⟩ := exists_eq_sub s
  rw [map_sub, map_of, map_of, sub_eq_zero, of_eq_of_iff_of_retractClosure_eq_top A hA] at hs
  obtain ⟨W, hW, ⟨e⟩⟩ := hs
  have : PreservesBinaryBiproducts A.ι := preservesBinaryBiproducts_of_preservesBiproducts _
  let B : A.FullSubcategory := ⟨W, hW⟩
  have h := of_congr (C := A.FullSubcategory) (A.fullyFaithfulι.preimageIso
    (A.ι.mapBiprod P B ≪≫ e ≪≫ (A.ι.mapBiprod Q B).symm))
  rw [of_biprod, of_biprod] at h
  rw [add_right_cancel h, sub_self]

end SplitK0

end TauCeti
