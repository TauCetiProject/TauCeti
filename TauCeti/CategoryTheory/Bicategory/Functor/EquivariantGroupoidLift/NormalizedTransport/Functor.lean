/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Normalization

/-!
# The normalization pseudofunctor

Normalization sends the bicategory of equivariant lifts to the locally discrete bicategory
of normalized transports. Its morphism map retains the coherent equivariant comparison on
the prescribed fibers. Compatible modifications become equalities of those comparisons.

This is the forward normalization construction. The target is locally discrete because the
prescribed fiber comparisons leave no independent modification components after normalization.
The conventions follow Johnson–Yau, *2-Dimensional Categories*, Chapter 4.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- Normalize equivariant lifts, their morphisms and compatible modifications on the
prescribed fibers. The target has only identity `2`-morphisms between equal comparisons. -/
-- The map and map₂ characteristic equations use the literal prescribed endpoints.
-- Keeping these carriers opaque would require conjugation by object equalities.
@[expose] noncomputable def normalizationPseudofunctor :
    EquivariantGroupoidLift Γ actions ⥤ᵖ LocallyDiscrete (NormalizedTransport Γ actions) where
  obj L := ⟨L.normalizedTransport⟩
  map φ := φ.normalizedTransportHom.toLoc
  map₂ Θ := eqToHom (congrArg Quiver.Hom.toLoc Θ.normalizedTransportHom_eq)
  mapId L := eqToIso (congrArg Quiver.Hom.toLoc (Hom.id_normalizedTransportHom L))
  mapComp φ ψ := eqToIso (congrArg Quiver.Hom.toLoc (Hom.comp_normalizedTransportHom φ ψ))
  map₂_id _ := Subsingleton.elim _ _
  map₂_comp _ _ := Subsingleton.elim _ _
  map₂_whisker_left := by intros; exact Subsingleton.elim _ _
  map₂_whisker_right := by intros; exact Subsingleton.elim _ _
  map₂_associator _ _ _ := Subsingleton.elim _ _
  map₂_left_unitor _ := Subsingleton.elim _ _
  map₂_right_unitor _ := Subsingleton.elim _ _

@[simp]
lemma normalizationPseudofunctor_obj_as (L : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).obj L).as = L.normalizedTransport := (rfl)

lemma normalizationPseudofunctor_map_as {L L' : EquivariantGroupoidLift Γ actions}
    (φ : L ⟶ L') :
    ((normalizationPseudofunctor actions).map φ).as = φ.normalizedTransportHom := (rfl)

lemma normalizationPseudofunctor_map₂ {L L' : EquivariantGroupoidLift Γ actions}
    {φ ψ : L ⟶ L'} (Θ : φ ⟶ ψ) :
    (normalizationPseudofunctor actions).map₂ Θ =
      eqToHom (congrArg Quiver.Hom.toLoc Θ.normalizedTransportHom_eq) := (rfl)

/-- Normalization uses the equality expressing preservation of identity as its unit cell. -/
lemma normalizationPseudofunctor_mapId (L : EquivariantGroupoidLift Γ actions) :
    (normalizationPseudofunctor actions).mapId L =
      eqToIso (congrArg Quiver.Hom.toLoc (Hom.id_normalizedTransportHom L)) := (rfl)

/-- Normalization uses the equality expressing preservation of composition as its compositor. -/
lemma normalizationPseudofunctor_mapComp {L L' L'' : EquivariantGroupoidLift Γ actions}
    (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (normalizationPseudofunctor actions).mapComp φ ψ =
      eqToIso (congrArg Quiver.Hom.toLoc (Hom.comp_normalizedTransportHom φ ψ)) := (rfl)

end TauCeti.EquivariantGroupoidLift
