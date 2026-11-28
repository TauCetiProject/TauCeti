/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Transport of a differential comparison along a complex isomorphism

A morphism identified with a multiple of an opposite differential retains that description
when the object identifications are composed with an isomorphism of complexes. This is used
when comparing the first differentials of Čech spectral sequences on localized sites.
-/

public section

open CategoryTheory Opposite

namespace HomologicalComplex

/-- Transport an identification with a multiple of an opposite differential along an
isomorphism of complexes. -/
lemma transport_op_d {A : Type*} [Category* A] [Preadditive A] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex A c} (e : K ≅ L) (i j : ι)
    {X Y : Aᵒᵖ} (a : X ≅ op (L.X j)) (b : Y ≅ op (L.X i)) (d : X ⟶ Y) (n : ℤ)
    (h : a.inv ≫ d ≫ b.hom = n • (L.d i j).op) :
    (a ≪≫ (Hom.isoApp e j).op).inv ≫ d ≫ (b ≪≫ (Hom.isoApp e i).op).hom =
      n • (K.d i j).op := by
  have hd : e.hom.f i ≫ L.d i j ≫ e.inv.f j = K.d i j := by
    rw [e.hom.comm_assoc]
    simp only [← comp_f, e.hom_inv_id, id_f, Category.comp_id]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% h, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  simpa only [Hom.isoApp, Functor.mapIso_hom, Functor.mapIso_inv, eval_map,
    Iso.op_inv, Iso.op_hom, ← op_comp, Category.assoc] using congrArg Quiver.Hom.op hd

end HomologicalComplex
