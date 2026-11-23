/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import TauCeti.AlgebraicTopology.SimplexCategory.Endpoint
public import TauCeti.Order.Hom.Adjoint
import TauCeti.Order.Fin.Basic

/-!
# Top/bottom duality (`Δ_topᵒᵖ ≅ Δ_bot`)

This file constructs the strict category duality between `TauCeti.SimplexCategory.LastPreservingᵒᵖ`
(`Δ_topᵒᵖ`) and `TauCeti.SimplexCategory.ZeroPreserving` (`Δ_bot`) via finite-order Galois
adjoints (`OrderHom.leftAdjoint` and `OrderHom.rightAdjoint`):

* `TauCeti.SimplexCategory.lastPreservingOpToZeroPreserving`: `Δ_topᵒᵖ ⥤ Δ_bot`.
* `TauCeti.SimplexCategory.zeroPreservingToLastPreservingOp`: `Δ_bot ⥤ Δ_topᵒᵖ`.
* `TauCeti.SimplexCategory.lastPreservingOpIsoZeroPreserving`:
  `Cat.of LastPreservingᵒᵖ ≅ Cat.of ZeroPreserving`.

## References

* S. Schanuel and R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques **27** (1986), 81–83.
* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Proposition 3.3.4.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- The duality functor `Δ_topᵒᵖ ⥤ Δ_bot` taking each top-preserving map to its left adjoint. -/
@[expose] def lastPreservingOpToZeroPreserving : LastPreservingᵒᵖ ⥤ ZeroPreserving where
  obj x := ⟨x.unop.obj⟩
  map f := ZeroPreserving.homMk
    (Hom.mk (f.unop.hom.toOrderHom.leftAdjoint (LastPreserving.toOrderHom_last f.unop)))
    (f.unop.hom.toOrderHom.leftAdjoint_bot (LastPreserving.toOrderHom_last f.unop))
  map_id _ := WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    erw [ZeroPreserving.homMk_hom, Hom.toOrderHom_mk]
    exact OrderHom.leftAdjoint_id
  map_comp f g := WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp only [WideSubcategory.comp_def, comp_toOrderHom]
    conv_lhs => erw [ZeroPreserving.homMk_hom, Hom.toOrderHom_mk]
    conv_rhs =>
      arg 1
      erw [ZeroPreserving.homMk_hom, Hom.toOrderHom_mk]
    conv_rhs =>
      arg 2
      erw [ZeroPreserving.homMk_hom, Hom.toOrderHom_mk]
    exact OrderHom.leftAdjoint_comp (LastPreserving.toOrderHom_last g.unop)
      (LastPreserving.toOrderHom_last f.unop)

/-- The duality functor `Δ_bot ⥤ Δ_topᵒᵖ` taking each bottom-preserving map to its right
adjoint. -/
@[expose] def zeroPreservingToLastPreservingOp : ZeroPreserving ⥤ LastPreservingᵒᵖ where
  obj x := op ⟨x.obj⟩
  map f := Quiver.Hom.op <| LastPreserving.homMk
    (Hom.mk (f.hom.toOrderHom.rightAdjoint (ZeroPreserving.toOrderHom_zero f)))
    (f.hom.toOrderHom.rightAdjoint_top (ZeroPreserving.toOrderHom_zero f))
  map_id _ := Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    erw [Quiver.Hom.unop_op, LastPreserving.homMk_hom, Hom.toOrderHom_mk]
    exact OrderHom.rightAdjoint_id
  map_comp f g := Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp only [unop_comp, WideSubcategory.comp_def, comp_toOrderHom]
    conv_lhs => erw [Quiver.Hom.unop_op, LastPreserving.homMk_hom, Hom.toOrderHom_mk]
    conv_rhs =>
      arg 1
      erw [Quiver.Hom.unop_op, LastPreserving.homMk_hom, Hom.toOrderHom_mk]
    conv_rhs =>
      arg 2
      erw [Quiver.Hom.unop_op, LastPreserving.homMk_hom, Hom.toOrderHom_mk]
    exact OrderHom.rightAdjoint_comp (ZeroPreserving.toOrderHom_zero f)
      (ZeroPreserving.toOrderHom_zero g)

/-- Object map of `lastPreservingOpToZeroPreserving`. -/
@[simp]
theorem lastPreservingOpToZeroPreserving_obj (x : LastPreservingᵒᵖ) :
    lastPreservingOpToZeroPreserving.obj x = ⟨x.unop.obj⟩ := (rfl)

/-- Object map of `zeroPreservingToLastPreservingOp`. -/
@[simp]
theorem zeroPreservingToLastPreservingOp_obj (x : ZeroPreserving) :
    zeroPreservingToLastPreservingOp.obj x = op ⟨x.obj⟩ := (rfl)

/-- Underlying monotone map of `lastPreservingOpToZeroPreserving.map f`. -/
@[simp]
theorem lastPreservingOpToZeroPreserving_map_toOrderHom {x y : LastPreservingᵒᵖ} (f : x ⟶ y) :
    (lastPreservingOpToZeroPreserving.map f).hom.toOrderHom =
      f.unop.hom.toOrderHom.leftAdjoint (LastPreserving.toOrderHom_last f.unop) := by
  erw [ZeroPreserving.homMk_hom, Hom.toOrderHom_mk]

/-- Underlying monotone map of `(zeroPreservingToLastPreservingOp.map f).unop`. -/
@[simp]
theorem zeroPreservingToLastPreservingOp_map_toOrderHom {x y : ZeroPreserving} (f : x ⟶ y) :
    (zeroPreservingToLastPreservingOp.map f).unop.hom.toOrderHom =
      f.hom.toOrderHom.rightAdjoint (ZeroPreserving.toOrderHom_zero f) := by
  erw [Quiver.Hom.unop_op, LastPreserving.homMk_hom, Hom.toOrderHom_mk]

/-- `lastPreservingOpToZeroPreserving` sends the restricted coface `LastPreserving.δ i`
(omitting `i.castSucc`) to the restricted codegeneracy `ZeroPreserving.σ i`. -/
@[simp]
theorem lastPreservingOpToZeroPreserving_map_δ {n : ℕ} (i : Fin (n + 1)) :
    lastPreservingOpToZeroPreserving.map (LastPreserving.δ i).op = ZeroPreserving.σ i :=
  WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    rw [lastPreservingOpToZeroPreserving_map_toOrderHom]
    erw [ZeroPreserving.σ_hom]
    refine OrderHom.leftAdjoint_eq_of_galoisConnection _ ?_
    erw [Quiver.Hom.unop_op, LastPreserving.δ_hom]
    exact Fin.galoisConnection_predAbove_castSucc_succAbove i

/-- `lastPreservingOpToZeroPreserving` sends the restricted codegeneracy `LastPreserving.σ i`
to the restricted coface `ZeroPreserving.δ i` (omitting `i.succ`). -/
@[simp]
theorem lastPreservingOpToZeroPreserving_map_σ {n : ℕ} (i : Fin (n + 1)) :
    lastPreservingOpToZeroPreserving.map (LastPreserving.σ i).op = ZeroPreserving.δ i :=
  WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    rw [lastPreservingOpToZeroPreserving_map_toOrderHom]
    erw [ZeroPreserving.δ_hom]
    refine OrderHom.leftAdjoint_eq_of_galoisConnection _ ?_
    erw [Quiver.Hom.unop_op, LastPreserving.σ_hom]
    exact Fin.galoisConnection_succ_succAbove_predAbove i

/-- `zeroPreservingToLastPreservingOp` sends the restricted coface `ZeroPreserving.δ i`
(omitting `i.succ`) to the opposite restricted codegeneracy `(LastPreserving.σ i).op`. -/
@[simp]
theorem zeroPreservingToLastPreservingOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    zeroPreservingToLastPreservingOp.map (ZeroPreserving.δ i) = (LastPreserving.σ i).op :=
  Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    rw [zeroPreservingToLastPreservingOp_map_toOrderHom]
    erw [Quiver.Hom.unop_op, LastPreserving.σ_hom]
    refine OrderHom.rightAdjoint_eq_of_galoisConnection _ ?_
    erw [ZeroPreserving.δ_hom]
    exact Fin.galoisConnection_succ_succAbove_predAbove i

/-- `zeroPreservingToLastPreservingOp` sends the restricted codegeneracy `ZeroPreserving.σ i`
to the opposite restricted coface `(LastPreserving.δ i).op` (omitting `i.castSucc`). -/
@[simp]
theorem zeroPreservingToLastPreservingOp_map_σ {n : ℕ} (i : Fin (n + 1)) :
    zeroPreservingToLastPreservingOp.map (ZeroPreserving.σ i) = (LastPreserving.δ i).op :=
  Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    rw [zeroPreservingToLastPreservingOp_map_toOrderHom]
    erw [Quiver.Hom.unop_op, LastPreserving.δ_hom]
    refine OrderHom.rightAdjoint_eq_of_galoisConnection _ ?_
    erw [ZeroPreserving.σ_hom]
    exact Fin.galoisConnection_predAbove_castSucc_succAbove i

/-- `lastPreservingOpToZeroPreserving` and `zeroPreservingToLastPreservingOp` are strict
left/right inverses on `Δ_topᵒᵖ`. -/
@[simp]
theorem lastPreservingOpToZeroPreserving_comp_zeroPreservingToLastPreservingOp :
    lastPreservingOpToZeroPreserving ⋙ zeroPreservingToLastPreservingOp =
      𝟭 LastPreservingᵒᵖ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
      simp only [Functor.comp_map, Functor.id_map,
        zeroPreservingToLastPreservingOp_map_toOrderHom,
        lastPreservingOpToZeroPreserving_map_toOrderHom]
      exact OrderHom.rightAdjoint_leftAdjoint f.unop.hom.toOrderHom
        (LastPreserving.toOrderHom_last f.unop)

/-- `zeroPreservingToLastPreservingOp` and `lastPreservingOpToZeroPreserving` are strict
left/right inverses on `Δ_bot`. -/
@[simp]
theorem zeroPreservingToLastPreservingOp_comp_lastPreservingOpToZeroPreserving :
    zeroPreservingToLastPreservingOp ⋙ lastPreservingOpToZeroPreserving =
      𝟭 ZeroPreserving :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
      simp only [Functor.comp_map, Functor.id_map,
        lastPreservingOpToZeroPreserving_map_toOrderHom,
        zeroPreservingToLastPreservingOp_map_toOrderHom]
      exact OrderHom.leftAdjoint_rightAdjoint f.hom.toOrderHom (ZeroPreserving.toOrderHom_zero f)

/-- Strict isomorphism of categories `Δ_topᵒᵖ ≅ Δ_bot`. -/
def lastPreservingOpIsoZeroPreserving :
    Cat.of LastPreservingᵒᵖ ≅ Cat.of ZeroPreserving where
  hom := lastPreservingOpToZeroPreserving.toCatHom
  inv := zeroPreservingToLastPreservingOp.toCatHom
  hom_inv_id := Cat.ext lastPreservingOpToZeroPreserving_comp_zeroPreservingToLastPreservingOp
  inv_hom_id := Cat.ext zeroPreservingToLastPreservingOp_comp_lastPreservingOpToZeroPreserving

/-- Underlying forward functor of `lastPreservingOpIsoZeroPreserving`. -/
@[simp]
theorem lastPreservingOpIsoZeroPreserving_hom_toFunctor :
    lastPreservingOpIsoZeroPreserving.hom.toFunctor = lastPreservingOpToZeroPreserving :=
  (rfl)

/-- Underlying inverse functor of `lastPreservingOpIsoZeroPreserving`. -/
@[simp]
theorem lastPreservingOpIsoZeroPreserving_inv_toFunctor :
    lastPreservingOpIsoZeroPreserving.inv.toFunctor = zeroPreservingToLastPreservingOp :=
  (rfl)

end TauCeti.SimplexCategory
