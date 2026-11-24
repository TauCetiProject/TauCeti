/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Images of the structure maps of a binary biproduct

For a functor `F` preserving zero morphisms and a binary biproduct `X ⊞ Y`, the comparison maps
`biprod.lift (F.map biprod.fst) (F.map biprod.snd) : F(X ⊞ Y) ⟶ F(X) ⊞ F(Y)` and
`biprod.desc (F.map biprod.inl) (F.map biprod.inr) : F(X) ⊞ F(Y) ⟶ F(X ⊞ Y)` carry `F` of the
inclusions to the inclusions and the projections to `F` of the projections. These are the simp
normal forms of the two components of `CategoryTheory.Functor.mapBiprod`, so the lemmas below
let `simp` move the structure maps of a binary biproduct through that comparison. No preservation
hypothesis is needed: only the existence of the biproduct `F(X) ⊞ F(Y)`.

When `F` preserves the biproduct and its target is preadditive, an automorphism of `F(X ⊞ Y)`
which fixes `F` of the first inclusion and induces the identity along `F` of the second projection
becomes, under `F(X ⊞ Y) ≅ F(X) ⊞ F(Y)`, the unipotent automorphism given by its off-diagonal
block.

## Main results

* `CategoryTheory.Limits.biprod.map_inl_comp_lift_map`,
  `CategoryTheory.Limits.biprod.map_inr_comp_lift_map`: `F(inl)` and `F(inr)` followed by the
  comparison `F(X ⊞ Y) ⟶ F(X) ⊞ F(Y)` are the inclusions.
* `CategoryTheory.Limits.biprod.desc_map_comp_map_fst`,
  `CategoryTheory.Limits.biprod.desc_map_comp_map_snd`: the comparison `F(X) ⊞ F(Y) ⟶ F(X ⊞ Y)`
  followed by `F(fst)` and `F(snd)` is the projection.
* `CategoryTheory.Functor.mapBiprod_symm_trans_trans_eq_unipotentLower`: a triangular
  automorphism of `F(X ⊞ Y)` with identity diagonal is unipotent under `F.mapBiprod X Y`.
-/

public section

namespace CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (X Y : C) [HasBinaryBiproduct X Y]
  [HasBinaryBiproduct (F.obj X) (F.obj Y)]

/-- `F` of the first inclusion, followed by the comparison `F(X ⊞ Y) ⟶ F(X) ⊞ F(Y)`, is the first
inclusion. -/
@[reassoc (attr := simp)]
theorem biprod.map_inl_comp_lift_map :
    F.map (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.lift (F.map biprod.fst) (F.map biprod.snd) =
      biprod.inl := by
  ext <;> simp [← F.map_comp]

/-- `F` of the second inclusion, followed by the comparison `F(X ⊞ Y) ⟶ F(X) ⊞ F(Y)`, is the second
inclusion. -/
@[reassoc (attr := simp)]
theorem biprod.map_inr_comp_lift_map :
    F.map (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.lift (F.map biprod.fst) (F.map biprod.snd) =
      biprod.inr := by
  ext <;> simp [← F.map_comp]

/-- The comparison `F(X) ⊞ F(Y) ⟶ F(X ⊞ Y)`, followed by `F` of the first projection, is the first
projection. -/
@[reassoc (attr := simp)]
theorem biprod.desc_map_comp_map_fst :
    biprod.desc (F.map (biprod.inl : X ⟶ X ⊞ Y)) (F.map biprod.inr) ≫ F.map biprod.fst =
      biprod.fst := by
  ext <;> simp [← F.map_comp]

/-- The comparison `F(X) ⊞ F(Y) ⟶ F(X ⊞ Y)`, followed by `F` of the second projection, is the
second projection. -/
@[reassoc (attr := simp)]
theorem biprod.desc_map_comp_map_snd :
    biprod.desc (F.map (biprod.inl : X ⟶ X ⊞ Y)) (F.map biprod.inr) ≫ F.map biprod.snd =
      biprod.snd := by
  ext <;> simp [← F.map_comp]

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [Preadditive D]
  [HasBinaryBiproducts D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {X Y : C} [HasBinaryBiproduct X Y]
  [PreservesBinaryBiproduct X Y F]

/-- Under `F(X ⊞ Y) ≅ F(X) ⊞ F(Y)`, an automorphism of `F(X ⊞ Y)` fixing `F` of the first
inclusion and inducing the identity along `F` of the second projection is the unipotent
automorphism given by its off-diagonal block `F(Y) ⟶ F(X)`. -/
theorem mapBiprod_symm_trans_trans_eq_unipotentLower (u : F.obj (X ⊞ Y) ≅ F.obj (X ⊞ Y))
    (h₁ : F.map biprod.inl ≫ u.hom = F.map biprod.inl)
    (h₂ : u.hom ≫ F.map biprod.snd = F.map biprod.snd) :
    (F.mapBiprod X Y).symm ≪≫ u ≪≫ F.mapBiprod X Y =
      Biprod.unipotentLower (F.map biprod.inr ≫ u.hom ≫ F.map biprod.fst) := by
  ext
  · simp [Biprod.ofComponents, reassoc_of% h₁]
  · simp [Biprod.ofComponents, reassoc_of% h₁]
  · simp [Biprod.ofComponents]
  · simp [Biprod.ofComponents, h₂, ← F.map_comp]

end CategoryTheory.Functor
