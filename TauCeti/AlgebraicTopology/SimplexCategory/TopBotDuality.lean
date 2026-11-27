/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.IsoCat
public import TauCeti.AlgebraicTopology.SimplexCategory.EndpointPreserving
public import TauCeti.Order.Hom.Adjoint
import TauCeti.Order.Fin.Basic

/-!
# Top/bottom duality (`Δ_⊤ᵒᵖ ≅ Δ_⊥`)

This file constructs the strict category duality between `TauCeti.SimplexCategory.TopPreservingᵒᵖ`
(`Δ_⊤ᵒᵖ`) and `TauCeti.SimplexCategory.BotPreserving` (`Δ_⊥`) via finite-order Galois adjoints
(`OrderHom.leftAdjoint` and `OrderHom.rightAdjoint`):

* `TauCeti.SimplexCategory.topPreservingOpToBotPreserving`: `Δ_⊤ᵒᵖ ⥤ Δ_⊥`.
* `TauCeti.SimplexCategory.botPreservingToTopPreservingOp`: `Δ_⊥ ⥤ Δ_⊤ᵒᵖ`.
* `TauCeti.SimplexCategory.topBotIsoCat`: `IsoCat TopPreservingᵒᵖ BotPreserving` (whose underlying
  equivalence is `topBotIsoCat.toEquivalence`).

## References

* S. Schanuel and R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques **27** (1986), 81–83.
* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Proposition 3.3.4.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- The duality functor `Δ_⊤ᵒᵖ ⥤ Δ_⊥` taking each top-preserving map to its left adjoint. -/
@[expose] def topPreservingOpToBotPreserving : TopPreservingᵒᵖ ⥤ BotPreserving where
  obj x := ⟨x.unop.obj⟩
  map f := ⟨Hom.mk (f.unop.hom.toOrderHom.leftAdjoint (TopPreserving.hom_toOrderHom_last f.unop)),
    (preservesBot_iff _).mpr
      (f.unop.hom.toOrderHom.leftAdjoint_bot (TopPreserving.hom_toOrderHom_last f.unop))⟩
  map_id _ := BotPreserving.hom_ext' <| by
    dsimp only
    rw [Hom.toOrderHom_mk]
    exact OrderHom.leftAdjoint_id
  map_comp _ _ := BotPreserving.hom_ext' <| by
    dsimp only
    simp only [WideSubcategory.comp_def, comp_toOrderHom, Hom.toOrderHom_mk]
    exact OrderHom.leftAdjoint_comp _ _

/-- The duality functor `Δ_⊥ ⥤ Δ_⊤ᵒᵖ` taking each bottom-preserving map to its right adjoint. -/
@[expose] def botPreservingToTopPreservingOp : BotPreserving ⥤ TopPreservingᵒᵖ where
  obj x := op ⟨x.obj⟩
  map f := Quiver.Hom.op
    ⟨Hom.mk (f.hom.toOrderHom.rightAdjoint (BotPreserving.hom_toOrderHom_zero f)),
      (preservesTop_iff _).mpr
        (f.hom.toOrderHom.rightAdjoint_top (BotPreserving.hom_toOrderHom_zero f))⟩
  map_id _ := Quiver.Hom.unop_inj <| TopPreserving.hom_ext' <| by
    dsimp only
    rw [Quiver.Hom.unop_op, Hom.toOrderHom_mk]
    exact OrderHom.rightAdjoint_id
  map_comp _ _ := Quiver.Hom.unop_inj <| TopPreserving.hom_ext' <| by
    dsimp only
    simp only [unop_comp, WideSubcategory.comp_def, comp_toOrderHom, Quiver.Hom.unop_op,
      Hom.toOrderHom_mk]
    exact OrderHom.rightAdjoint_comp _ _

/-- Object map of `topPreservingOpToBotPreserving`. -/
@[simp]
theorem topPreservingOpToBotPreserving_obj (x : TopPreservingᵒᵖ) :
    topPreservingOpToBotPreserving.obj x = ⟨x.unop.obj⟩ := (rfl)

/-- Object map of `botPreservingToTopPreservingOp`. -/
@[simp]
theorem botPreservingToTopPreservingOp_obj (x : BotPreserving) :
    botPreservingToTopPreservingOp.obj x = op ⟨x.obj⟩ := (rfl)

/-- Underlying monotone map of `topPreservingOpToBotPreserving.map f`. -/
@[simp]
theorem topPreservingOpToBotPreserving_map_toOrderHom {x y : TopPreservingᵒᵖ} (f : x ⟶ y) :
    (topPreservingOpToBotPreserving.map f).hom.toOrderHom =
      f.unop.hom.toOrderHom.leftAdjoint (TopPreserving.hom_toOrderHom_last f.unop) :=
  (rfl)

/-- Underlying monotone map of `(botPreservingToTopPreservingOp.map f).unop`. -/
@[simp]
theorem botPreservingToTopPreservingOp_map_toOrderHom {x y : BotPreserving} (f : x ⟶ y) :
    (botPreservingToTopPreservingOp.map f).unop.hom.toOrderHom =
      f.hom.toOrderHom.rightAdjoint (BotPreserving.hom_toOrderHom_zero f) :=
  (rfl)

/-- `topPreservingOpToBotPreserving` sends the restricted coface `TopPreserving.δ i`
(omitting `i.castSucc`) to the restricted codegeneracy `BotPreserving.σ i`. -/
@[simp]
theorem topPreservingOpToBotPreserving_map_δ {n : ℕ} (i : Fin (n + 1)) :
    topPreservingOpToBotPreserving.map (TopPreserving.δ i).op = BotPreserving.σ i :=
  BotPreserving.hom_ext' <| by
    rw [topPreservingOpToBotPreserving_map_toOrderHom, BotPreserving.σ_hom]
    refine OrderHom.leftAdjoint_eq_of_galoisConnection _ ?_
    rw [Quiver.Hom.unop_op, TopPreserving.δ_hom]
    exact Fin.galoisConnection_predAbove_castSucc_succAbove i

/-- `topPreservingOpToBotPreserving` sends the restricted codegeneracy `TopPreserving.σ i`
to the restricted coface `BotPreserving.δ i` (omitting `i.succ`). -/
@[simp]
theorem topPreservingOpToBotPreserving_map_σ {n : ℕ} (i : Fin (n + 1)) :
    topPreservingOpToBotPreserving.map (TopPreserving.σ i).op = BotPreserving.δ i :=
  BotPreserving.hom_ext' <| by
    rw [topPreservingOpToBotPreserving_map_toOrderHom, BotPreserving.δ_hom]
    refine OrderHom.leftAdjoint_eq_of_galoisConnection _ ?_
    rw [Quiver.Hom.unop_op, TopPreserving.σ_hom]
    exact Fin.galoisConnection_succ_succAbove_predAbove i

/-- `botPreservingToTopPreservingOp` sends the restricted coface `BotPreserving.δ i`
(omitting `i.succ`) to the opposite restricted codegeneracy `(TopPreserving.σ i).op`. -/
@[simp]
theorem botPreservingToTopPreservingOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    botPreservingToTopPreservingOp.map (BotPreserving.δ i) = (TopPreserving.σ i).op :=
  Quiver.Hom.unop_inj <| TopPreserving.hom_ext' <| by
    rw [botPreservingToTopPreservingOp_map_toOrderHom]
    -- `((TopPreserving.σ i).op).unop` has implicit endpoints
    -- `botPreservingToTopPreservingOp.obj _`, which must be unfolded to `op _` before
    -- `Quiver.Hom.unop_op` can match.
    dsimp only [botPreservingToTopPreservingOp]
    rw [Quiver.Hom.unop_op, TopPreserving.σ_hom]
    refine OrderHom.rightAdjoint_eq_of_galoisConnection _ ?_
    rw [BotPreserving.δ_hom]
    exact Fin.galoisConnection_succ_succAbove_predAbove i

/-- `botPreservingToTopPreservingOp` sends the restricted codegeneracy `BotPreserving.σ i`
to the opposite restricted coface `(TopPreserving.δ i).op` (omitting `i.castSucc`). -/
@[simp]
theorem botPreservingToTopPreservingOp_map_σ {n : ℕ} (i : Fin (n + 1)) :
    botPreservingToTopPreservingOp.map (BotPreserving.σ i) = (TopPreserving.δ i).op :=
  Quiver.Hom.unop_inj <| TopPreserving.hom_ext' <| by
    rw [botPreservingToTopPreservingOp_map_toOrderHom]
    -- Same object-endpoint unfolding as in `botPreservingToTopPreservingOp_map_δ`.
    dsimp only [botPreservingToTopPreservingOp]
    rw [Quiver.Hom.unop_op, TopPreserving.δ_hom]
    refine OrderHom.rightAdjoint_eq_of_galoisConnection _ ?_
    rw [BotPreserving.σ_hom]
    exact Fin.galoisConnection_predAbove_castSucc_succAbove i

/-- `topPreservingOpToBotPreserving` and `botPreservingToTopPreservingOp` are strict
left/right inverses on `Δ_⊤ᵒᵖ`. -/
@[simp]
theorem topPreservingOpToBotPreserving_comp_botPreservingToTopPreservingOp :
    topPreservingOpToBotPreserving ⋙ botPreservingToTopPreservingOp =
      𝟭 TopPreservingᵒᵖ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    Quiver.Hom.unop_inj <| TopPreserving.hom_ext' <| by
      simp only [Functor.comp_map, Functor.id_map,
        botPreservingToTopPreservingOp_map_toOrderHom,
        topPreservingOpToBotPreserving_map_toOrderHom]
      exact OrderHom.rightAdjoint_leftAdjoint f.unop.hom.toOrderHom
        (TopPreserving.hom_toOrderHom_last f.unop)

/-- `botPreservingToTopPreservingOp` and `topPreservingOpToBotPreserving` are strict
left/right inverses on `Δ_⊥`. -/
@[simp]
theorem botPreservingToTopPreservingOp_comp_topPreservingOpToBotPreserving :
    botPreservingToTopPreservingOp ⋙ topPreservingOpToBotPreserving =
      𝟭 BotPreserving :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    BotPreserving.hom_ext' <| by
      simp only [Functor.comp_map, Functor.id_map,
        topPreservingOpToBotPreserving_map_toOrderHom,
        botPreservingToTopPreservingOp_map_toOrderHom]
      exact OrderHom.leftAdjoint_rightAdjoint f.hom.toOrderHom
        (BotPreserving.hom_toOrderHom_zero f)

/-- Strict isomorphism of categories `Δ_⊤ᵒᵖ ≅ Δ_⊥`. The underlying equivalence is
`topBotIsoCat.toEquivalence`. -/
@[expose, simps functor inverse]
def topBotIsoCat : IsoCat TopPreservingᵒᵖ BotPreserving where
  functor := topPreservingOpToBotPreserving
  inverse := botPreservingToTopPreservingOp
  unit_eq := topPreservingOpToBotPreserving_comp_botPreservingToTopPreservingOp.symm
  counit_eq := botPreservingToTopPreservingOp_comp_topPreservingOpToBotPreserving

end TauCeti.SimplexCategory
