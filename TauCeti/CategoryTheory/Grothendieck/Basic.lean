/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Grothendieck

/-!
# Canonical transport in a Grothendieck construction

Every morphism factors as canonical transport to the target fiber followed by a morphism
inside that fiber. Successive transports agree with transport along the composite, after
the canonical identification of the fiber objects. These identities allow naturality
conditions on the total category to be checked using fiber inclusions and base arrows.

Adapted from `Mei/CategoryTheory/Grothendieck/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0).
-/

public section

namespace CategoryTheory.Grothendieck

universe v u w z

variable {D : Type u} [Category.{v} D] {C : D ⥤ Cat.{w, z}}

/-- A morphism is canonical transport followed by its fiber morphism. -/
theorem ιNatTrans_app_comp_ι_map {X Y : Grothendieck C} (h : X ⟶ Y) :
    (ιNatTrans h.base).app X.fiber ≫ (ι C Y.base).map h.fiber = h := by
  cases X with | mk d x =>
  cases Y with | mk e y =>
  dsimp [Grothendieck.ιNatTrans, Grothendieck.ι]
  refine Grothendieck.ext _ _ (by simp [Grothendieck.comp_base]) ?_
  -- Retype the fiber composite after expanding the dependent inclusion maps.
  change (eqToHom _ ≫ eqToHom _ ≫ (C.map (𝟙 e)).toFunctor.map (𝟙 _) ≫
    eqToHom _ ≫ h.fiber : (C.map h.base).toFunctor.obj x ⟶ y) = h.fiber
  simp only [comp_base, Functor.map_id, Category.id_comp, eqToHom_trans_assoc]
  erw [eqToHom_trans_assoc (C := C.obj e)]
  erw [eqToHom_refl (C := C.obj e), Category.id_comp (obj := C.obj e)]

/-- Successive canonical transports agree with transport along the composite after identifying
the iterated image with the image of the composite in the target fiber. -/
theorem ιNatTrans_app_comp {d e b : D} (f : d ⟶ e) (g : e ⟶ b) (x : C.obj d) :
    (ιNatTrans f).app x ≫ (ιNatTrans g).app ((C.map f).toFunctor.obj x) ≫
      (ι C b).map (eqToHom (by simp)) = (ιNatTrans (f ≫ g)).app x := by
  let h : (⟨e, (C.map f).toFunctor.obj x⟩ : Grothendieck C) ⟶
      ⟨b, (C.map (f ≫ g)).toFunctor.obj x⟩ :=
    ⟨g, eqToHom (by simp)⟩
  rw [ιNatTrans_app_comp_ι_map h]
  symm
  refine Grothendieck.ext _ _ (by
    dsimp [Grothendieck.ιNatTrans, Grothendieck.comp, h]
    rfl) ?_
  dsimp [Grothendieck.ιNatTrans, Grothendieck.ι, h]
  erw [(C.map g).toFunctor.map_id]
  erw [Category.comp_id (obj := C.obj b), Category.id_comp (obj := C.obj b),
    eqToHom_trans (C := C.obj b)]
  rfl

end CategoryTheory.Grothendieck
