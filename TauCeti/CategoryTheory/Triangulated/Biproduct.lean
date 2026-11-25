/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Direct summands and sums of triangles in a pretriangulated category

Facts about binary biproducts in a pretriangulated category `C`.

* A retract is a direct summand: if `X` is a retract of `Y`, then `Y ≅ X ⊞ Z` for some `Z`.
  The pretriangulated category need not be idempotent complete; the complement `Z` is the cone of
  the split monomorphism `X ⟶ Y`, whose distinguished triangle has zero connecting morphism.
  Consequently, for an isomorphism-closed property `P`, an object `X` satisfies
  `P.retractClosure` exactly when `X ⊞ Y` satisfies `P` for some `Y`. If `P` is dense, that is
  `P.retractClosure = ⊤`, every object has such a complement `Y`.
* Distinguished triangles are closed under binary direct sums, up to isomorphism of vertices: for
  distinguished `T₁` and `T₂` there is a distinguished triangle whose vertices are the biproducts
  of the corresponding vertices of `T₁` and `T₂`. It is the product triangle of the pair.

Both are used to manipulate objects up to direct summands in a dense triangulated subcategory,
where every object is a summand of an object of the subcategory.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_biprod_of_mono`: every monomorphism in a
  pretriangulated category splits as a binary biproduct summand.
* `CategoryTheory.Retract.exists_iso_biprod`: a retract of `Y` is a biproduct summand of `Y`.
* `CategoryTheory.ObjectProperty.prop_retractClosure_iff_exists_biprod`: the retract closure of
  an isomorphism-closed property consists of the summands of its objects.
* `CategoryTheory.ObjectProperty.exists_prop_biprod_of_retractClosure_eq_top`: for a dense
  isomorphism-closed property, every object has a complement whose biproduct with it lies in the
  property.
* `CategoryTheory.Pretriangulated.exists_distTriang_iso_biprod`: there is a distinguished triangle
  whose vertices are isomorphic to the vertexwise biproducts of two distinguished triangles.
-/

public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Splitting of monomorphisms in a pretriangulated category**: every monomorphism `f : X ⟶ Y`
identifies `Y` with a binary biproduct `X ⊞ Z` compatibly with `biprod.inl`. -/
theorem Pretriangulated.exists_iso_biprod_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), f ≫ e.hom = biprod.inl := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT
    (Triangle.mor₃_eq_zero_of_mono₁ _ hT ‹_›)
  exact ⟨Z, e, he⟩

/-- **A retract is a direct summand** in a pretriangulated category: if `X` is a retract of `Y`,
then `Y` is isomorphic to `X ⊞ Z` for some object `Z`. -/
theorem Retract.exists_iso_biprod {X Y : C} (h : Retract X Y) :
    ∃ Z : C, Nonempty (Y ≅ X ⊞ Z) := by
  obtain ⟨Z, e, -⟩ := Pretriangulated.exists_iso_biprod_of_mono h.i
  exact ⟨Z, ⟨e⟩⟩

/-- In a pretriangulated category, an object lies in the retract closure of an
isomorphism-closed property `P` exactly when it becomes an object satisfying `P` after adding a
direct summand. -/
theorem ObjectProperty.prop_retractClosure_iff_exists_biprod (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (X : C) : P.retractClosure X ↔ ∃ Y : C, P (X ⊞ Y) := by
  refine ⟨fun ⟨Y, hY, ⟨r⟩⟩ => ?_, fun ⟨Y, hY⟩ => P.prop_retractClosure hY
    { i := biprod.inl, r := biprod.fst }⟩
  obtain ⟨Z, ⟨e⟩⟩ := r.exists_iso_biprod
  exact ⟨Z, P.prop_of_iso e hY⟩

/-- In a pretriangulated category, every object has a complement for a dense isomorphism-closed
property `P`: a summand whose biproduct with the object satisfies `P`. -/
theorem ObjectProperty.exists_prop_biprod_of_retractClosure_eq_top (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (hP : P.retractClosure = ⊤) (X : C) : ∃ Y : C, P (X ⊞ Y) :=
  (P.prop_retractClosure_iff_exists_biprod X).1 (by rw [hP]; trivial)

namespace Pretriangulated

/-- **Direct sums of distinguished triangles**: for distinguished triangles `T₁` and `T₂` there is
a distinguished triangle whose three vertices are isomorphic to `T₁.obj₁ ⊞ T₂.obj₁`,
`T₁.obj₂ ⊞ T₂.obj₂` and `T₁.obj₃ ⊞ T₂.obj₃`. -/
theorem exists_distTriang_iso_biprod (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ distTriang C)
    (h₂ : T₂ ∈ distTriang C) :
    ∃ T ∈ distTriang C, Nonempty (T.obj₁ ≅ T₁.obj₁ ⊞ T₂.obj₁) ∧
      Nonempty (T.obj₂ ≅ T₁.obj₂ ⊞ T₂.obj₂) ∧ Nonempty (T.obj₃ ≅ T₁.obj₃ ⊞ T₂.obj₃) := by
  -- A product over `WalkingPair` is the binary biproduct of its two factors.
  let e (F : WalkingPair → C) : ∏ᶜ F ≅ F .left ⊞ F .right :=
    HasLimit.isoOfNatIso (diagramIsoPair (Discrete.functor F)) ≪≫ (biprod.isoProd _ _).symm
  refine ⟨productTriangle (pairFunction T₁ T₂), productTriangle_distinguished _ ?_,
    ⟨e _⟩, ⟨e _⟩, ⟨e _⟩⟩
  rintro (_ | _)
  exacts [h₁, h₂]

end Pretriangulated

end CategoryTheory
