/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of ideal sheaves

This file identifies the closed subscheme of an ideal sheaf pulled back along a fibre-product
projection with the corresponding base change. It also records the resulting preservation of
flatness for the closed subscheme.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S T X : Scheme.{u}}

/-- The closed subscheme cut out by the pullback of an ideal sheaf along a fibre-product
projection is the base change of its original closed subscheme. -/
noncomputable def comapPullbackFstIso (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comap (pullback.fst f g)).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
  I.comapIso (pullback.fst f g) ≪≫
    pullbackSymmetry (pullback.fst f g) I.subschemeι ≪≫
      pullbackRightPullbackFstIso f g I.subschemeι

/-- The base-change comparison preserves the projection to the original closed subscheme. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_hom_fst (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).hom ≫ pullback.fst (I.subschemeι ≫ f) g =
      subschemeMap _ _ (pullback.fst f g) (I.le_map_comap _) := by
  simp [comapPullbackFstIso, Category.assoc]

/-- The inverse base-change comparison preserves the projection to the original closed
subscheme. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_inv_fst (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).inv ≫
        subschemeMap _ _ (pullback.fst f g) (I.le_map_comap _) =
      pullback.fst (I.subschemeι ≫ f) g := by
  rw [← comapPullbackFstIso_hom_fst, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The base-change comparison preserves the projection to the new base. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_hom_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).hom ≫ pullback.snd (I.subschemeι ≫ f) g =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g := by
  simp [comapPullbackFstIso, Category.assoc]

/-- Flatness of the closed subscheme over the base is preserved by arbitrary base change. -/
theorem flat_comap_subschemeι_comp_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) [Flat (I.subschemeι ≫ f)] :
    Flat ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  rw [← comapPullbackFstIso_hom_snd]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
