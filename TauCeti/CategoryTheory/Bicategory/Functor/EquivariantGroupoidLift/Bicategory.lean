/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic

/-!
# The bicategory of equivariant groupoid lifts

Fix a category `Γ`, a monoid `H` and a family `actions p` of categorical actions of `H`, presented
as pseudofunctors `LocallyDiscrete (SingleObj H) ⥤ᵖ Cat`. This file makes the coherent
equivariant lifts `EquivariantGroupoidLift Γ actions` of these actions into a bicategory.

* A 1-morphism `φ : L ⟶ L'` is a strong transformation `φ.joint : L.joint ⟶ L'.joint` of joint
  pseudofunctors, together with, for each `p : Γ`, an invertible modification
  `φ.comparisonIso p : φ.joint|_p ≫ L'.comparison p ≅ L.comparison p`. Here `φ.joint|_p` is the
  restriction of `φ.joint` to the fiber `{p} × SingleObj H`. So `φ` is compatible, up to a
  specified equivariant isomorphism, with the comparisons of both lifts with the prescribed
  fibers and actions.
* A 2-morphism `φ ⟶ ψ` is a modification `φ.joint ⟶ ψ.joint` whose restriction to each fiber
  carries `φ.comparisonIso p` to `ψ.comparisonIso p`.

Identities, composites, whiskerings, associators and unitors are those of the bicategory of
pseudofunctors `LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat`, with the comparison isomorphisms
composed by whiskering. A 2-morphism is determined by its underlying modification, so the
coherence axioms are inherited from that bicategory.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom`: 1-morphisms of lifts, with identities `Hom.id` and
  composites `Hom.comp`;
* `TauCeti.EquivariantGroupoidLift.Hom₂`: 2-morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.Hom₂.isoMk`: an invertible 2-morphism from an invertible
  modification compatible with the comparison isomorphisms;
* `TauCeti.EquivariantGroupoidLift.instBicategory`: the bicategory of lifts, with the
  characterizing lemmas `comp_joint`, `comp_comparisonIso`, `whiskerLeft_joint`,
  `associator_hom_joint` and their siblings.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021):
  the bicategory of pseudofunctors, strong transformations and modifications.
* Mathlib's bicategory of pseudofunctors and strong transformations,
  `Mathlib/CategoryTheory/Bicategory/FunctorBicategory/Pseudo.lean`: the identities,
  composites, whiskerings, associators and unitors of lifts are its operations on the joint
  pseudofunctors, and its coherence axioms are inherited here.
* Mathlib's bicategory of adjunctions, `Mathlib/CategoryTheory/Bicategory/Adjunction/Adj.lean`:
  the pattern of a `Hom₂` structure of 2-morphisms carrying a compatibility condition, with a
  bicategory structure whose axioms are checked on the underlying 2-morphisms.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, with their loop group actions.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- A 1-morphism of equivariant groupoid lifts `L ⟶ L'`: a strong transformation of joint
pseudofunctors, with an invertible modification, for each `p : Γ`, from its restriction to the
fiber over `p` followed by the comparison of `L'` to the comparison of `L`. -/
structure Hom (L L' : EquivariantGroupoidLift Γ actions) where
  /-- The strong transformation of joint pseudofunctors. -/
  joint : L.joint ⟶ L'.joint
  /-- The isomorphism of fiber comparisons over `p`. -/
  comparisonIso (p : Γ) :
    (joint.restrictFiber p ≫ L'.comparison p : L.joint.restrictFiber p ⟶ actions p) ≅
      L.comparison p

/-- A 2-morphism of 1-morphisms of equivariant groupoid lifts: a modification of the strong
transformations of joint pseudofunctors, whose restriction to each fiber is compatible with the
comparison isomorphisms. -/
@[ext]
structure Hom₂ {L L' : EquivariantGroupoidLift Γ actions} (φ ψ : Hom L L') where
  /-- The modification of strong transformations of joint pseudofunctors. -/
  joint : φ.joint ⟶ ψ.joint
  /-- Compatibility with the comparison isomorphisms on each fiber. -/
  comm (p : Γ) :
    restrictFiberMap joint p ▷ L'.comparison p ≫ (ψ.comparisonIso p).hom =
      (φ.comparisonIso p).hom := by cat_disch

attribute [reassoc (attr := simp)] Hom₂.comm

namespace Hom

variable {L L' L'' : EquivariantGroupoidLift Γ actions}

/-! `Hom.id` and `Hom.comp` are exposed: the types of 2-morphisms between composites, and the
statements of the characterizing lemmas such as `whiskerLeft_joint`, only typecheck by unfolding
`(φ ≫ ψ).joint` to `φ.joint ≫ ψ.joint`. -/

variable (L) in
/-- The identity 1-morphism of a lift: the identity strong transformation, with the left unitors
as comparison isomorphisms. -/
@[expose] def id : Hom L L where
  joint := 𝟙 L.joint
  -- The restriction of the identity is the identity, by `Pseudofunctor.whiskerLeft_id`.
  comparisonIso p := (λ_ (L.comparison p) : 𝟙 (L.joint.restrictFiber p) ≫ _ ≅ _)

/-- The composite of 1-morphisms of lifts. Its comparison isomorphism over `p` is the composite
of the associator, the comparison isomorphism of `ψ` whiskered by the restriction of `φ`, and the
comparison isomorphism of `φ`. -/
@[expose] def comp (φ : Hom L L') (ψ : Hom L' L'') : Hom L L'' where
  joint := φ.joint ≫ ψ.joint
  -- The restriction of a composite is the composite of restrictions, by
  -- `Pseudofunctor.whiskerLeft_comp`.
  comparisonIso p :=
    (α_ (φ.joint.restrictFiber p) (ψ.joint.restrictFiber p) (L''.comparison p) ≪≫
      whiskerLeftIso (φ.joint.restrictFiber p) (ψ.comparisonIso p) ≪≫ φ.comparisonIso p :
      (φ.joint.restrictFiber p ≫ ψ.joint.restrictFiber p) ≫ L''.comparison p ≅ L.comparison p)

end Hom

namespace Hom₂

variable {L L' : EquivariantGroupoidLift Γ actions} {φ ψ χ : Hom L L'}

variable (φ) in
/-- The identity 2-morphism. -/
def id : Hom₂ φ φ where
  joint := 𝟙 φ.joint

/-- The vertical composite of 2-morphisms. -/
def vcomp (Θ : Hom₂ φ ψ) (Ξ : Hom₂ ψ χ) : Hom₂ φ χ where
  joint := Θ.joint ≫ Ξ.joint
  comm p := by simp

end Hom₂

/-- The category of 1-morphisms `L ⟶ L'` of lifts and their 2-morphisms. -/
instance homCategory (L L' : EquivariantGroupoidLift Γ actions) : Category (Hom L L') where
  Hom := Hom₂
  id := Hom₂.id
  comp := Hom₂.vcomp
  id_comp Θ := Hom₂.ext (by exact Category.id_comp Θ.joint)
  comp_id Θ := Hom₂.ext (by exact Category.comp_id Θ.joint)
  assoc Θ Ξ Ψ := Hom₂.ext (by exact Category.assoc Θ.joint Ξ.joint Ψ.joint)

namespace Hom₂

variable {L L' : EquivariantGroupoidLift Γ actions} {φ ψ χ : Hom L L'}

/-- An isomorphism of 1-morphisms of lifts from an isomorphism of their strong transformations
of joint pseudofunctors whose forward modification is compatible with the comparison
isomorphisms. -/
def isoMk (e : φ.joint ≅ ψ.joint)
    (comm : ∀ p, restrictFiberMap e.hom p ▷ L'.comparison p ≫ (ψ.comparisonIso p).hom =
      (φ.comparisonIso p).hom) : φ ≅ ψ where
  hom := ⟨e.hom, comm⟩
  inv :=
    { joint := e.inv
      comm p := by
        rw [← comm p, ← comp_whiskerRight_assoc (restrictFiberMap e.inv p)
          (restrictFiberMap e.hom p), ← Pseudofunctor.whiskerLeftMap_comp, e.inv_hom_id,
          Pseudofunctor.whiskerLeftMap_id, id_whiskerRight, Category.id_comp] }
  hom_inv_id := Hom₂.ext e.hom_inv_id
  inv_hom_id := Hom₂.ext e.inv_hom_id

@[simp]
lemma isoMk_hom_joint (e : φ.joint ≅ ψ.joint)
    (comm : ∀ p, restrictFiberMap e.hom p ▷ L'.comparison p ≫ (ψ.comparisonIso p).hom =
      (φ.comparisonIso p).hom) : (isoMk e comm).hom.joint = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_joint (e : φ.joint ≅ ψ.joint)
    (comm : ∀ p, restrictFiberMap e.hom p ▷ L'.comparison p ≫ (ψ.comparisonIso p).hom =
      (φ.comparisonIso p).hom) : (isoMk e comm).inv.joint = e.inv :=
  (rfl)

end Hom₂

section Bicategory

/-! In the proofs below, the restriction of a composite of strong transformations, of a
whiskered modification, of an associator or of a unitor is definitionally the corresponding
composite, whiskering, associator or unitor of restrictions (`Pseudofunctor.whiskerLeft_comp`,
`Pseudofunctor.whiskerLeftMap_whiskerLeft` and their siblings, all proved by `rfl`). These
lemmas cannot be used for rewriting, because the restricted 2-morphisms are typed by the
unrestricted composites. Each proof therefore first states its goal in terms of the
restrictions, then identifies it with the actual goal by `rfl` (in a `calc` step) or by `exact`.
The bicategorical rewrites take explicit arguments, because their metavariables do not unify
with the instances of the scoped bicategory of pseudofunctors at reducible transparency. -/

variable {L L' L'' L''' : EquivariantGroupoidLift Γ actions}

/-- Left whiskering of a 2-morphism of lifts by a 1-morphism. -/
def whiskerLeft (φ : Hom L L') {ψ ψ' : Hom L' L''} (Θ : ψ ⟶ ψ') :
    Hom.comp φ ψ ⟶ Hom.comp φ ψ' where
  joint := φ.joint ◁ Θ.joint
  comm p := calc
    _ = (restrictFiber φ.joint p ◁ restrictFiberMap Θ.joint p) ▷ L''.comparison p ≫
          (α_ (restrictFiber φ.joint p) (restrictFiber ψ'.joint p) (L''.comparison p)).hom ≫
          restrictFiber φ.joint p ◁ (ψ'.comparisonIso p).hom ≫ (φ.comparisonIso p).hom := rfl
    _ = (α_ (restrictFiber φ.joint p) (restrictFiber ψ.joint p) (L''.comparison p)).hom ≫
          restrictFiber φ.joint p ◁ (ψ.comparisonIso p).hom ≫ (φ.comparisonIso p).hom := by
      rw [associator_naturality_middle_assoc (restrictFiber φ.joint p)
          (restrictFiberMap Θ.joint p),
        ← whiskerLeft_comp_assoc (restrictFiber φ.joint p) (restrictFiberMap Θ.joint p ▷ _),
        Θ.comm]

/-- Right whiskering of a 2-morphism of lifts by a 1-morphism. -/
def whiskerRight {φ φ' : Hom L L'} (Θ : φ ⟶ φ') (ψ : Hom L' L'') :
    Hom.comp φ ψ ⟶ Hom.comp φ' ψ where
  joint := Θ.joint ▷ ψ.joint
  comm p := calc
    _ = (restrictFiberMap Θ.joint p ▷ restrictFiber ψ.joint p) ▷ L''.comparison p ≫
          (α_ (restrictFiber φ'.joint p) (restrictFiber ψ.joint p) (L''.comparison p)).hom ≫
          restrictFiber φ'.joint p ◁ (ψ.comparisonIso p).hom ≫ (φ'.comparisonIso p).hom := rfl
    _ = (α_ (restrictFiber φ.joint p) (restrictFiber ψ.joint p) (L''.comparison p)).hom ≫
          restrictFiber φ.joint p ◁ (ψ.comparisonIso p).hom ≫ (φ.comparisonIso p).hom := by
      rw [associator_naturality_left_assoc (restrictFiberMap Θ.joint p),
        ← whisker_exchange_assoc (restrictFiberMap Θ.joint p) (ψ.comparisonIso p).hom, Θ.comm]

/-- The associator of 1-morphisms of lifts, whose underlying modification is the associator of
strong transformations. -/
def associator (φ : Hom L L') (ψ : Hom L' L'') (χ : Hom L'' L''') :
    Hom.comp (Hom.comp φ ψ) χ ≅ Hom.comp φ (Hom.comp ψ χ) :=
  Hom₂.isoMk (α_ φ.joint ψ.joint χ.joint) fun p => calc
    _ = (α_ (restrictFiber φ.joint p) (restrictFiber ψ.joint p)
            (restrictFiber χ.joint p)).hom ▷ L'''.comparison p ≫
          (α_ (restrictFiber φ.joint p) (restrictFiber ψ.joint p ≫ restrictFiber χ.joint p)
            (L'''.comparison p)).hom ≫
          restrictFiber φ.joint p ◁ ((α_ (restrictFiber ψ.joint p) (restrictFiber χ.joint p)
            (L'''.comparison p)).hom ≫
            restrictFiber ψ.joint p ◁ (χ.comparisonIso p).hom ≫ (ψ.comparisonIso p).hom) ≫
          (φ.comparisonIso p).hom := rfl
    _ = (α_ (restrictFiber φ.joint p ≫ restrictFiber ψ.joint p) (restrictFiber χ.joint p)
            (L'''.comparison p)).hom ≫
          (restrictFiber φ.joint p ≫ restrictFiber ψ.joint p) ◁ (χ.comparisonIso p).hom ≫
          (α_ (restrictFiber φ.joint p) (restrictFiber ψ.joint p) (L''.comparison p)).hom ≫
          restrictFiber φ.joint p ◁ (ψ.comparisonIso p).hom ≫ (φ.comparisonIso p).hom := by
      rw [whiskerLeft_comp (restrictFiber φ.joint p), whiskerLeft_comp (restrictFiber φ.joint p),
        Category.assoc, Category.assoc,
        pentagon_assoc (restrictFiber φ.joint p) (restrictFiber ψ.joint p),
        associator_naturality_right_assoc (restrictFiber φ.joint p) (restrictFiber ψ.joint p)]

/-- The left unitor of a 1-morphism of lifts, whose underlying modification is the left unitor of
strong transformations. -/
def leftUnitor (φ : Hom L L') : Hom.comp (Hom.id L) φ ≅ φ :=
  Hom₂.isoMk (λ_ φ.joint) fun p => by
    have h : (λ_ (restrictFiber φ.joint p)).hom ▷ L'.comparison p ≫ (φ.comparisonIso p).hom =
        (α_ (𝟙 (L.joint.restrictFiber p)) (restrictFiber φ.joint p) (L'.comparison p)).hom ≫
          𝟙 (L.joint.restrictFiber p) ◁ (φ.comparisonIso p).hom ≫
          (λ_ (L.comparison p) : 𝟙 (L.joint.restrictFiber p) ≫ _ ≅ _).hom := by
      rw [leftUnitor_naturality (φ.comparisonIso p).hom,
        leftUnitor_whiskerRight (restrictFiber φ.joint p), Category.assoc]
    exact h

/-- The right unitor of a 1-morphism of lifts, whose underlying modification is the right unitor
of strong transformations. -/
def rightUnitor (φ : Hom L L') : Hom.comp φ (Hom.id L') ≅ φ :=
  Hom₂.isoMk (ρ_ φ.joint) fun p => by
    have h : (ρ_ (restrictFiber φ.joint p)).hom ▷ L'.comparison p ≫ (φ.comparisonIso p).hom =
        (α_ (restrictFiber φ.joint p) (𝟙 (L'.joint.restrictFiber p)) (L'.comparison p)).hom ≫
          restrictFiber φ.joint p ◁
            (λ_ (L'.comparison p) : 𝟙 (L'.joint.restrictFiber p) ≫ _ ≅ _).hom ≫
          (φ.comparisonIso p).hom := by
      rw [triangle_assoc (restrictFiber φ.joint p)]
    exact h

end Bicategory

/-- The bicategory of coherent equivariant lifts of a family of categorical actions. Its
1-morphisms are `EquivariantGroupoidLift.Hom` and its 2-morphisms are
`EquivariantGroupoidLift.Hom₂`. Since a 2-morphism is determined by its underlying modification,
the coherence axioms are those of the bicategory of pseudofunctors. -/
instance instBicategory : Bicategory (EquivariantGroupoidLift Γ actions) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  homCategory := homCategory
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id φ ψ := Hom₂.ext (by exact Bicategory.whiskerLeft_id φ.joint ψ.joint)
  whiskerLeft_comp φ _ _ _ Θ Ξ :=
    Hom₂.ext (by exact Bicategory.whiskerLeft_comp φ.joint Θ.joint Ξ.joint)
  id_whiskerLeft Θ := Hom₂.ext (by exact Bicategory.id_whiskerLeft Θ.joint)
  comp_whiskerLeft φ ψ _ _ Θ :=
    Hom₂.ext (by exact Bicategory.comp_whiskerLeft φ.joint ψ.joint Θ.joint)
  id_whiskerRight φ ψ := Hom₂.ext (by exact Bicategory.id_whiskerRight φ.joint ψ.joint)
  comp_whiskerRight Θ Ξ χ :=
    Hom₂.ext (by exact Bicategory.comp_whiskerRight Θ.joint Ξ.joint χ.joint)
  whiskerRight_id Θ := Hom₂.ext (by exact Bicategory.whiskerRight_id Θ.joint)
  whiskerRight_comp Θ ψ χ :=
    Hom₂.ext (by exact Bicategory.whiskerRight_comp Θ.joint ψ.joint χ.joint)
  whisker_assoc φ _ _ Θ χ := Hom₂.ext (by exact Bicategory.whisker_assoc φ.joint Θ.joint χ.joint)
  whisker_exchange Θ Ξ := Hom₂.ext (by exact Bicategory.whisker_exchange Θ.joint Ξ.joint)
  pentagon φ ψ χ ω := Hom₂.ext (by exact Bicategory.pentagon φ.joint ψ.joint χ.joint ω.joint)
  triangle φ ψ := Hom₂.ext (by exact Bicategory.triangle φ.joint ψ.joint)

section API

variable {L L' L'' L''' : EquivariantGroupoidLift Γ actions}

/-- 2-morphisms of lifts are determined by their underlying modifications. -/
@[ext]
lemma Hom₂.hom_ext {φ ψ : L ⟶ L'} {Θ Ξ : φ ⟶ ψ} (h : Θ.joint = Ξ.joint) : Θ = Ξ :=
  Hom₂.ext h

@[simp]
lemma Hom₂.id_joint (φ : L ⟶ L') : Hom₂.joint (𝟙 φ) = 𝟙 φ.joint :=
  (rfl)

@[simp]
lemma Hom₂.comp_joint {φ ψ χ : L ⟶ L'} (Θ : φ ⟶ ψ) (Ξ : ψ ⟶ χ) :
    (Θ ≫ Ξ).joint = Θ.joint ≫ Ξ.joint :=
  (rfl)

@[simp]
lemma id_joint (L : EquivariantGroupoidLift Γ actions) : Hom.joint (𝟙 L) = 𝟙 L.joint :=
  (rfl)

@[simp]
lemma comp_joint (φ : L ⟶ L') (ψ : L' ⟶ L'') : (φ ≫ ψ).joint = φ.joint ≫ ψ.joint :=
  (rfl)

/-- The comparison isomorphisms of the identity 1-morphism are the left unitors. -/
lemma id_comparisonIso (L : EquivariantGroupoidLift Γ actions) (p : Γ) :
    Hom.comparisonIso (𝟙 L) p = (λ_ (L.comparison p) : 𝟙 (L.joint.restrictFiber p) ≫ _ ≅ _) :=
  rfl

/-- The comparison isomorphisms of a composite 1-morphism. -/
lemma comp_comparisonIso (φ : L ⟶ L') (ψ : L' ⟶ L'') (p : Γ) :
    (φ ≫ ψ).comparisonIso p =
      (α_ (φ.joint.restrictFiber p) (ψ.joint.restrictFiber p) (L''.comparison p) ≪≫
        whiskerLeftIso (φ.joint.restrictFiber p) (ψ.comparisonIso p) ≪≫ φ.comparisonIso p :
        (φ.joint.restrictFiber p ≫ ψ.joint.restrictFiber p) ≫ L''.comparison p ≅
          L.comparison p) :=
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
