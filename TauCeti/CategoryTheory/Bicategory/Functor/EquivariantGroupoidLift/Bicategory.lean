/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom

/-!
# The bicategory of equivariant groupoid lifts

Fix a category `Γ`, a monoid `H` and a family `actions p` of categorical actions of `H`, presented
as pseudofunctors `LocallyDiscrete (SingleObj H) ⥤ᵖ Cat`. This file makes the coherent
equivariant lifts `EquivariantGroupoidLift Γ actions` of these actions into a bicategory, whose
`1`-morphisms are the morphisms of lifts `EquivariantGroupoidLift.Hom` and whose `2`-morphisms
are the compatible modifications `EquivariantGroupoidLift.Hom.Hom₂`, with the identities
`Hom.id` and composites `Hom.comp`.

Whiskerings, associators and unitors are those of the bicategory of pseudofunctors
`LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat` on the joint strong transformations. Their
compatibility with the fiber isomorphisms is checked componentwise, where it follows from the
compatibility of the whiskered `2`-morphism and the coherence theorem for bicategories. A
`2`-morphism is determined by its joint modification, so the coherence axioms are inherited from
the bicategory of pseudofunctors.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.whiskerLeft`,
  `TauCeti.EquivariantGroupoidLift.Hom.whiskerRight`: whiskering of compatible modifications by
  morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.Hom.associator`,
  `TauCeti.EquivariantGroupoidLift.Hom.leftUnitor`,
  `TauCeti.EquivariantGroupoidLift.Hom.rightUnitor`: the associator and unitors of morphisms of
  lifts;
* `TauCeti.EquivariantGroupoidLift.instBicategory`: the bicategory of lifts, with the
  characterizing lemmas `comp_joint`, `comp_fiberIso`, `whiskerLeft_joint`,
  `associator_hom_joint` and their siblings.

## References

* Niles Johnson and Donald Yau, [2-Dimensional Categories](https://arxiv.org/abs/2002.06055),
  Oxford University Press (2021): the bicategory of pseudofunctors, strong transformations and
  modifications.
* Mathlib's bicategory of adjunctions, `Mathlib/CategoryTheory/Bicategory/Adjunction/Adj.lean`:
  the pattern of 2-morphisms carrying a compatibility condition, with a bicategory structure
  whose axioms are checked on the underlying 2-morphisms.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, with their loop group actions.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

namespace Hom

variable {L L' L'' L''' : EquivariantGroupoidLift Γ actions}

/-- Left whiskering of a `2`-morphism of lifts by a morphism of lifts. -/
def whiskerLeft (φ : L.Hom L') {ψ ψ' : L'.Hom L''} (Θ : ψ ⟶ ψ') : φ.comp ψ ⟶ φ.comp ψ' :=
  ⟨φ.joint ◁ Θ.joint, fun p a => by
    simp only [comp_fiberIso_hom_as_app, whiskerLeft_as_app]
    rw [← Θ.comm p a]
    bicategory⟩

/-- Right whiskering of a `2`-morphism of lifts by a morphism of lifts. -/
def whiskerRight {φ φ' : L.Hom L'} (Θ : φ ⟶ φ') (ψ : L'.Hom L'') : φ.comp ψ ⟶ φ'.comp ψ :=
  ⟨Θ.joint ▷ ψ.joint, fun p a => by
    simp only [comp_fiberIso_hom_as_app, whiskerRight_as_app]
    rw [← Θ.comm p a]
    -- Exchange the whiskerings by `Θ` and by the fiber isomorphism of `ψ`. The fiber comparison
    -- is typed by the restriction of `L''.joint`, so this step is a term rather than a rewrite.
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (whisker_exchange_assoc _ _ _).symm)
    bicategory⟩

/-- The associator of morphisms of lifts, whose joint modification is the associator of strong
transformations. -/
noncomputable def associator (φ : L.Hom L') (ψ : L'.Hom L'') (χ : L''.Hom L''') :
    (φ.comp ψ).comp χ ≅ φ.comp (ψ.comp χ) where
  hom := ⟨(α_ φ.joint ψ.joint χ.joint).hom, fun p a => by
    simp only [comp_fiberIso_hom_as_app, associator_hom_as_app]
    bicategory⟩
  inv := ⟨(α_ φ.joint ψ.joint χ.joint).inv, fun p a => by
    simp only [comp_fiberIso_hom_as_app, associator_inv_as_app]
    bicategory⟩
  hom_inv_id := hom₂_ext (α_ φ.joint ψ.joint χ.joint).hom_inv_id
  inv_hom_id := hom₂_ext (α_ φ.joint ψ.joint χ.joint).inv_hom_id

/-- The left unitor of a morphism of lifts, whose joint modification is the left unitor of strong
transformations. -/
noncomputable def leftUnitor (φ : L.Hom L') : (id L).comp φ ≅ φ where
  hom := ⟨(λ_ φ.joint).hom, fun p a => by
    simp only [comp_fiberIso_hom_as_app, id_fiberIso_hom_as_app, leftUnitor_hom_as_app]
    bicategory⟩
  inv := ⟨(λ_ φ.joint).inv, fun p a => by
    simp only [comp_fiberIso_hom_as_app, id_fiberIso_hom_as_app, leftUnitor_inv_as_app]
    bicategory⟩
  hom_inv_id := hom₂_ext (λ_ φ.joint).hom_inv_id
  inv_hom_id := hom₂_ext (λ_ φ.joint).inv_hom_id

/-- The right unitor of a morphism of lifts, whose joint modification is the right unitor of
strong transformations. -/
noncomputable def rightUnitor (φ : L.Hom L') : φ.comp (id L') ≅ φ where
  hom := ⟨(ρ_ φ.joint).hom, fun p a => by
    simp only [comp_fiberIso_hom_as_app, id_fiberIso_hom_as_app, rightUnitor_hom_as_app]
    bicategory⟩
  inv := ⟨(ρ_ φ.joint).inv, fun p a => by
    simp only [comp_fiberIso_hom_as_app, id_fiberIso_hom_as_app, rightUnitor_inv_as_app]
    bicategory⟩
  hom_inv_id := hom₂_ext (ρ_ φ.joint).hom_inv_id
  inv_hom_id := hom₂_ext (ρ_ φ.joint).inv_hom_id

end Hom

/-- The bicategory of coherent equivariant lifts of a family of categorical actions. Its
`1`-morphisms are the morphisms of lifts `EquivariantGroupoidLift.Hom` and its `2`-morphisms are
the compatible modifications `EquivariantGroupoidLift.Hom.Hom₂`. Since a `2`-morphism is
determined by its joint modification, the coherence axioms are those of the bicategory of
pseudofunctors. -/
noncomputable instance instBicategory : Bicategory (EquivariantGroupoidLift Γ actions) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  whiskerLeft := Hom.whiskerLeft
  whiskerRight := Hom.whiskerRight
  associator := Hom.associator
  leftUnitor := Hom.leftUnitor
  rightUnitor := Hom.rightUnitor
  whiskerLeft_id φ ψ := Hom.hom₂_ext (by exact Bicategory.whiskerLeft_id φ.joint ψ.joint)
  whiskerLeft_comp φ _ _ _ Θ Ξ :=
    Hom.hom₂_ext (by
      exact Bicategory.whiskerLeft_comp φ.joint (Hom.Hom₂.joint Θ) (Hom.Hom₂.joint Ξ))
  id_whiskerLeft Θ := Hom.hom₂_ext (by exact Bicategory.id_whiskerLeft (Hom.Hom₂.joint Θ))
  comp_whiskerLeft φ ψ _ _ Θ :=
    Hom.hom₂_ext (by exact Bicategory.comp_whiskerLeft φ.joint ψ.joint (Hom.Hom₂.joint Θ))
  id_whiskerRight φ ψ := Hom.hom₂_ext (by exact Bicategory.id_whiskerRight φ.joint ψ.joint)
  comp_whiskerRight Θ Ξ χ :=
    Hom.hom₂_ext (by
      exact Bicategory.comp_whiskerRight (Hom.Hom₂.joint Θ) (Hom.Hom₂.joint Ξ) χ.joint)
  whiskerRight_id Θ := Hom.hom₂_ext (by exact Bicategory.whiskerRight_id (Hom.Hom₂.joint Θ))
  whiskerRight_comp Θ ψ χ :=
    Hom.hom₂_ext (by exact Bicategory.whiskerRight_comp (Hom.Hom₂.joint Θ) ψ.joint χ.joint)
  whisker_assoc φ _ _ Θ χ :=
    Hom.hom₂_ext (by exact Bicategory.whisker_assoc φ.joint (Hom.Hom₂.joint Θ) χ.joint)
  whisker_exchange Θ Ξ :=
    Hom.hom₂_ext (by exact Bicategory.whisker_exchange (Hom.Hom₂.joint Θ) (Hom.Hom₂.joint Ξ))
  pentagon φ ψ χ ω := Hom.hom₂_ext (by exact Bicategory.pentagon φ.joint ψ.joint χ.joint ω.joint)
  triangle φ ψ := Hom.hom₂_ext (by exact Bicategory.triangle φ.joint ψ.joint)

section API

variable {L L' L'' L''' : EquivariantGroupoidLift Γ actions}

/-- `2`-morphisms of the bicategory of lifts are determined by their joint modifications. -/
@[ext]
lemma hom₂_ext {φ ψ : L ⟶ L'} {Θ Ξ : φ ⟶ ψ} (h : Θ.joint = Ξ.joint) : Θ = Ξ :=
  Hom.hom₂_ext h

@[simp]
lemma hom₂_id_joint (φ : L ⟶ L') : Hom.Hom₂.joint (𝟙 φ) = 𝟙 φ.joint :=
  (rfl)

@[simp]
lemma hom₂_comp_joint {φ ψ χ : L ⟶ L'} (Θ : φ ⟶ ψ) (Ξ : ψ ⟶ χ) :
    Hom.Hom₂.joint (Θ ≫ Ξ) = Hom.Hom₂.joint Θ ≫ Hom.Hom₂.joint Ξ :=
  (rfl)

@[simp]
lemma id_joint (L : EquivariantGroupoidLift Γ actions) : Hom.joint (𝟙 L) = 𝟙 L.joint :=
  (rfl)

@[simp]
lemma comp_joint (φ : L ⟶ L') (ψ : L' ⟶ L'') : (φ ≫ ψ).joint = φ.joint ≫ ψ.joint :=
  (rfl)

/-- The fiber isomorphisms of the identity `1`-morphism are those of `Hom.id`. -/
lemma id_fiberIso (L : EquivariantGroupoidLift Γ actions) (p : Γ) :
    Hom.fiberIso (𝟙 L) p = (Hom.id L).fiberIso p :=
  rfl

/-- The fiber isomorphisms of a composite `1`-morphism are those of `Hom.comp`. -/
lemma comp_fiberIso (φ : L ⟶ L') (ψ : L' ⟶ L'') (p : Γ) :
    (φ ≫ ψ).fiberIso p = (Hom.comp φ ψ).fiberIso p :=
  rfl

@[simp]
lemma whiskerLeft_joint (φ : L ⟶ L') {ψ ψ' : L' ⟶ L''} (Θ : ψ ⟶ ψ') :
    (φ ◁ Θ).joint = φ.joint ◁ Θ.joint :=
  (rfl)

@[simp]
lemma whiskerRight_joint {φ φ' : L ⟶ L'} (Θ : φ ⟶ φ') (ψ : L' ⟶ L'') :
    (Θ ▷ ψ).joint = Θ.joint ▷ ψ.joint :=
  (rfl)

@[simp]
lemma associator_hom_joint (φ : L ⟶ L') (ψ : L' ⟶ L'') (χ : L'' ⟶ L''') :
    (α_ φ ψ χ).hom.joint = (α_ φ.joint ψ.joint χ.joint).hom :=
  (rfl)

@[simp]
lemma associator_inv_joint (φ : L ⟶ L') (ψ : L' ⟶ L'') (χ : L'' ⟶ L''') :
    (α_ φ ψ χ).inv.joint = (α_ φ.joint ψ.joint χ.joint).inv :=
  (rfl)

@[simp]
lemma leftUnitor_hom_joint (φ : L ⟶ L') : (λ_ φ).hom.joint = (λ_ φ.joint).hom :=
  (rfl)

@[simp]
lemma leftUnitor_inv_joint (φ : L ⟶ L') : (λ_ φ).inv.joint = (λ_ φ.joint).inv :=
  (rfl)

@[simp]
lemma rightUnitor_hom_joint (φ : L ⟶ L') : (ρ_ φ).hom.joint = (ρ_ φ.joint).hom :=
  (rfl)

@[simp]
lemma rightUnitor_inv_joint (φ : L ⟶ L') : (ρ_ φ).inv.joint = (ρ_ φ.joint).inv :=
  (rfl)

end API

end TauCeti.EquivariantGroupoidLift
