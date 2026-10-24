/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme

/-!
# Functoriality of locally closed orbit schemes

An equivariant morphism carrying one rational point to another restricts uniquely to
a morphism of their locally closed orbit schemes. These restrictions preserve identities
and composition, intertwine orbit factorizations and rational translations, and carry
equivariant isomorphisms to isomorphisms. Moving the base point by a rational group point
gives a canonical isomorphism over the ambient scheme, with right translation on the
orbit parametrization. The construction retains the scheme structures
supplied by the orbit morphisms, including nilpotents; no reducedness or smoothness is needed.

The construction uses `SchemeAction.orbitScheme` and
`Scheme.Hom.existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X Y Z : Over (Spec (.of k))}
  [GrpObj G] [ModObj G X] [ModObj G Y] [ModObj G Z]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left]
  [LocallyOfFiniteType Z.hom] [CompactSpace Z.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
  (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
  (f : X ⟶ Y) [IsModHom G f] (h : x ≫ f = y)

include h in
private theorem toOrbit_orbitι_comp_left :
    toOrbit G x ≫ orbitι G x ≫ f.left = (orbitMap G y).left := by
  rw [toOrbit_ι_assoc, ← Over.comp_left, orbitMap_comp, h]

include h in
private theorem existsUnique_orbitSchemeMap :
    ∃! l : orbitScheme G x ⟶ orbitScheme G y,
      l ≫ orbitι G y = orbitι G x ≫ f.left := by
  refine (orbitι G y).existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (orbitι G x ≫ f.left) (toOrbit G x) (toOrbit G y) ?_
  rw [toOrbit_ι]
  exact toOrbit_orbitι_comp_left G x y f h

/-- The restriction of an equivariant morphism to the orbit schemes of specified
rational points that it carries to one another. -/
def orbitSchemeMap : orbitScheme G x ⟶ orbitScheme G y :=
  (existsUnique_orbitSchemeMap G x y f h).exists.choose

/-- The restricted morphism commutes with the orbit immersions. -/
@[reassoc (attr := simp)]
theorem orbitSchemeMap_ι :
    orbitSchemeMap G x y f h ≫ orbitι G y = orbitι G x ≫ f.left :=
  (existsUnique_orbitSchemeMap G x y f h).exists.choose_spec

/-- The orbit immersion uniquely characterizes the restriction. -/
theorem orbitSchemeMap_unique (l : orbitScheme G x ⟶ orbitScheme G y)
    (hl : l ≫ orbitι G y = orbitι G x ≫ f.left) :
    l = orbitSchemeMap G x y f h := by
  apply (cancel_mono (orbitι G y)).mp
  rw [hl, orbitSchemeMap_ι]

/-- Restricting an equivariant morphism commutes with the maps from the acting group. -/
@[reassoc (attr := simp)]
theorem toOrbit_orbitSchemeMap :
    toOrbit G x ≫ orbitSchemeMap G x y f h = toOrbit G y := by
  apply (cancel_mono (orbitι G y)).mp
  rw [Category.assoc, orbitSchemeMap_ι, toOrbit_orbitι_comp_left G x y f h, toOrbit_ι]

/-- The restriction is a morphism over the ground field. -/
@[reassoc (attr := simp)]
theorem orbitSchemeMap_toBase :
    orbitSchemeMap G x y f h ≫ orbitToBase G y = orbitToBase G x := by
  simp only [orbitToBase_def, orbitSchemeMap_ι_assoc, Over.w]

/-- The restricted morphism intertwines rational translations. -/
@[reassoc]
theorem orbitTranslation_hom_orbitSchemeMap
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitTranslation G x g).hom ≫ orbitSchemeMap G x y f h =
      orbitSchemeMap G x y f h ≫ (orbitTranslation G y g).hom := by
  apply (cancel_mono (orbitι G y)).mp
  simp only [Category.assoc, orbitSchemeMap_ι, orbitTranslation_hom_ι,
    orbitTranslation_hom_ι_assoc, orbitSchemeMap_ι_assoc]
  rw [← Over.comp_left, translation_hom_comp, Over.comp_left]

variable {x y f h}

/-- Restriction of the identity is the identity of the orbit scheme. -/
@[simp]
theorem orbitSchemeMap_id :
    orbitSchemeMap G x x (𝟙 X) (Category.comp_id x) = 𝟙 (orbitScheme G x) := by
  apply (cancel_mono (orbitι G x)).mp
  simp

/-- Restriction preserves composition, with the specified images of the base points. -/
@[reassoc (attr := simp)]
theorem orbitSchemeMap_comp
    {z : 𝟙_ (Over (Spec (.of k))) ⟶ Z}
    {f' : Y ⟶ Z} [IsModHom G f'] (h' : y ≫ f' = z) :
    orbitSchemeMap G x y f h ≫ orbitSchemeMap G y z f' h' =
      orbitSchemeMap G x z (f ≫ f') (by rw [← Category.assoc, h, h']) := by
  apply (cancel_mono (orbitι G z)).mp
  simp

variable (x y)

/-- An equivariant isomorphism induces an isomorphism of orbit schemes. -/
def orbitSchemeIso (e : X ≅ Y) [IsModHom G e.hom] (h : x ≫ e.hom = y) :
    orbitScheme G x ≅ orbitScheme G y where
  hom := orbitSchemeMap G x y e.hom h
  inv := orbitSchemeMap G y x e.inv (by rw [← h]; simp)
  hom_inv_id := by
    apply (cancel_mono (orbitι G x)).mp
    simp
  inv_hom_id := by
    apply (cancel_mono (orbitι G y)).mp
    simp

/-- The forward orbit isomorphism is the restriction of the ambient one. -/
@[simp]
theorem orbitSchemeIso_hom (e : X ≅ Y) [IsModHom G e.hom] (h : x ≫ e.hom = y) :
    (orbitSchemeIso G x y e h).hom = orbitSchemeMap G x y e.hom h := (rfl)

/-- The inverse orbit isomorphism restricts the inverse ambient isomorphism. -/
@[simp]
theorem orbitSchemeIso_inv (e : X ≅ Y) [IsModHom G e.hom] (h : x ≫ e.hom = y) :
    (orbitSchemeIso G x y e h).inv =
      orbitSchemeMap G y x e.inv (by rw [← h]; simp) := (rfl)

section ChangeBasePoint

private theorem existsUnique_orbitSchemeSmulMap
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (h : g • x = y) :
    ∃! l : orbitScheme G y ⟶ orbitScheme G x,
      l ≫ orbitι G x = orbitι G y := by
  refine (orbitι G x).existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (orbitι G y) (toOrbit G y) ((rightTranslation g).hom.left ≫ toOrbit G x) ?_
  rw [Category.assoc, toOrbit_ι, toOrbit_ι, ← Over.comp_left, ← orbitMap_smul, h]

/-- The ambient identity restricted to the orbit schemes of two translated base points. -/
private def orbitSchemeSmulMap
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (h : g • x = y) :
    orbitScheme G y ⟶ orbitScheme G x :=
  (existsUnique_orbitSchemeSmulMap G x g y h).exists.choose

@[reassoc]
private theorem orbitSchemeSmulMap_ι
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ X) (h : g • x = y) :
    orbitSchemeSmulMap G x g y h ≫ orbitι G x = orbitι G y :=
  (existsUnique_orbitSchemeSmulMap G x g y h).exists.choose_spec

/-- Changing the rational base point by a group point canonically identifies the
locally closed orbit schemes over the original acted-on scheme. -/
def orbitSchemeIsoSmul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    orbitScheme G (g • x) ≅ orbitScheme G x where
  hom := orbitSchemeSmulMap G x g (g • x) rfl
  inv := orbitSchemeSmulMap G (g • x) g⁻¹ x (inv_smul_smul g x)
  hom_inv_id := by
    apply (cancel_mono (orbitι G (g • x))).mp
    simp only [Category.assoc, orbitSchemeSmulMap_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (orbitι G x)).mp
    simp only [Category.assoc, orbitSchemeSmulMap_ι, Category.id_comp]

/-- The canonical base-point change leaves the immersion into the ambient scheme fixed. -/
@[reassoc (attr := simp)]
theorem orbitSchemeIsoSmul_hom_ι (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitSchemeIsoSmul G x g).hom ≫ orbitι G x = orbitι G (g • x) :=
  orbitSchemeSmulMap_ι G x g (g • x) rfl

/-- The inverse base-point change also leaves the ambient immersion fixed. -/
@[reassoc (attr := simp)]
theorem orbitSchemeIsoSmul_inv_ι (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitSchemeIsoSmul G x g).inv ≫ orbitι G (g • x) = orbitι G x := by
  rw [Iso.inv_comp_eq, orbitSchemeIsoSmul_hom_ι]

/-- Changing the base point reparametrizes the orbit morphism by right translation. -/
@[reassoc]
theorem toOrbit_orbitSchemeIsoSmul_hom (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    toOrbit G (g • x) ≫ (orbitSchemeIsoSmul G x g).hom =
      (rightTranslation g).hom.left ≫ toOrbit G x := by
  apply (cancel_mono (orbitι G x)).mp
  simp only [Category.assoc, orbitSchemeIsoSmul_hom_ι, toOrbit_ι]
  rw [← Over.comp_left, ← orbitMap_smul]

/-- Base-point change respects the ground-field structure. -/
@[reassoc (attr := simp)]
theorem orbitSchemeIsoSmul_hom_toBase (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitSchemeIsoSmul G x g).hom ≫ orbitToBase G x = orbitToBase G (g • x) := by
  simp only [orbitToBase_def, orbitSchemeIsoSmul_hom_ι_assoc]

/-- The inverse base-point change also respects the ground-field structure. -/
@[reassoc (attr := simp)]
theorem orbitSchemeIsoSmul_inv_toBase (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (orbitSchemeIsoSmul G x g).inv ≫ orbitToBase G (g • x) = orbitToBase G x := by
  simp only [orbitToBase_def, orbitSchemeIsoSmul_inv_ι_assoc]

end ChangeBasePoint

end TauCeti.SchemeAction
