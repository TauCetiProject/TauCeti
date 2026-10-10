/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Descent data on objects over a base, relative to a morphism

Let `p : S' ⟶ S` be a morphism in a category with pullbacks. A descent datum on an object
`π : X ⟶ S'` over `S'` relative to `p` identifies the fibres of `X` over any two points of `S'`
with the same image in `S`, compatibly with composition. This file records it in *action form*:
a morphism

`act : S' ×_S X ⟶ X`, written `(s, x) ↦ s · x`,

lying over the first projection (`π (s · x) = s`), with `π x · x = x` and the cocycle condition
`s₁ · (s₂ · x) = s₁ · x`. In other words, `act` is an action of the groupoid
`S' ×_S S' ⇉ S'` on `X`.

Mathematically this is the classical notion of a descent datum, an isomorphism
`φ : pr₁^* X ≅ pr₂^* X` over `S' ×_S S'` satisfying `φ₁₃ = φ₂₃ ∘ φ₁₂`: on points, `φ` sends
`x` in the fibre over `s₁` to `s₂ · x` in the fibre over `s₂`, and the normalisation and the
cocycle condition make `s₁ ·` inverse to `s₂ ·` on these fibres. The action form involves only
the pullbacks `S' ×_S X` and `S' ×_S (S' ×_S X)`, so the cocycle condition is a single equation
between two morphisms `S' ×_S (S' ×_S X) ⟶ X`, with no reassociation of iterated pullbacks. It
is the geometric counterpart of the coaction form `TauCeti.Algebra.DescentDatum` of a descent
datum on an algebra: for affine schemes, `act` is `Spec` of the coaction
(`TauCeti.Algebra.DescentDatum.specEquiv`).

Mathlib's `CategoryTheory.Pseudofunctor.DescentData` describes descent data for a pseudofunctor
to `Cat`, relative to a family of morphisms. The structure here is the concrete special case of
the pullback pseudofunctor `X ↦ Over X` and a single morphism `p`, which Mathlib does not
construct.

## Main definitions

* `TauCeti.DescentDatum p X`: a descent datum on `X : Over S'` relative to `p : S' ⟶ S`.
* `TauCeti.DescentDatum.Hom`: a morphism over `S'` intertwining the actions, with `Hom.id`,
  `Hom.comp`, and the inverse `Hom.inv` of a morphism which is an isomorphism over `S'`.
* `TauCeti.DescentDatum.transport e E`: the descent datum transported from `E` along an
  isomorphism `e : X ≅ Y` over `S'`, with the isomorphism `transportHom e E` to `E`.
* `TauCeti.DescentDatum.baseChange p X`: the canonical descent datum on the base change
  `X ×_S S'` of an object `X` over `S`, acting by `s · (x, s₀) = (x, s)`.

A descent datum `D` is *effective* when there are an object `X` over `S` and a morphism
`baseChange p X ⟶ D` of descent data which is an isomorphism over `S'`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)

/-- A descent datum on `X : Over S'` relative to `p : S' ⟶ S`, in action form: a morphism
`act : S' ×_S X ⟶ X`, `(s, x) ↦ s · x`, with `π (s · x) = s`, `π x · x = x` and
`s₁ · (s₂ · x) = s₁ · x`, where `π = X.hom`. -/
@[ext]
structure DescentDatum (X : Over S') where
  /-- The action `S' ×_S X ⟶ X`, `(s, x) ↦ s · x`. -/
  act : pullback p (X.hom ≫ p) ⟶ X.left
  /-- The action moves `x` into the fibre over `s`: `π (s · x) = s`. -/
  act_hom : act ≫ X.hom = pullback.fst p (X.hom ≫ p)
  /-- Normalisation: `π x · x = x`. -/
  lift_act : pullback.lift X.hom (𝟙 X.left) (by simp) ≫ act = 𝟙 X.left
  /-- The cocycle condition: `s₁ · (s₂ · x) = s₁ · x` on `S' ×_S (S' ×_S X)`. -/
  act_assoc :
    pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ act)
        (by rw [Category.assoc, reassoc_of% act_hom]; exact pullback.condition) ≫ act =
      pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ pullback.snd p (X.hom ≫ p))
        (by
          rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
          exact pullback.condition) ≫ act

namespace DescentDatum

attribute [reassoc (attr := simp)] act_hom lift_act

variable {p}

section Hom

variable {X Y Z : Over S'}

/-- A morphism of descent data: a morphism over `S'` which intertwines the actions,
`f (s · x) = s · f x`. -/
@[ext]
structure Hom (D : DescentDatum p X) (E : DescentDatum p Y) where
  /-- The underlying morphism over `S'`. -/
  hom : X ⟶ Y
  /-- The morphism intertwines the actions. -/
  map_act : pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') hom.left (𝟙 S) (by simp)
      (by simp) ≫ E.act = D.act ≫ hom.left

attribute [reassoc] Hom.map_act

variable (D : DescentDatum p X) {E : DescentDatum p Y} {F : DescentDatum p Z}

/-- The identity morphism of a descent datum. -/
def Hom.id : Hom D D where
  hom := 𝟙 X
  map_act := by simp

@[simp]
theorem Hom.id_hom : (Hom.id D).hom = 𝟙 X :=
  (rfl)

variable {D} in
/-- The composite of two morphisms of descent data. -/
def Hom.comp (g : Hom E F) (f : Hom D E) : Hom D F where
  hom := f.hom ≫ g.hom
  map_act := by
    have : pullback.map p (X.hom ≫ p) p (Z.hom ≫ p) (𝟙 S') (f.hom ≫ g.hom).left (𝟙 S) (by simp)
        (by simp) =
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S) (by simp) (by simp) ≫
          pullback.map p (Y.hom ≫ p) p (Z.hom ≫ p) (𝟙 S') g.hom.left (𝟙 S) (by simp)
            (by simp) := by
      ext <;> simp
    rw [this, Category.assoc, g.map_act, f.map_act_assoc, Over.comp_left]

variable {D} in
@[simp]
theorem Hom.comp_hom (g : Hom E F) (f : Hom D E) : (g.comp f).hom = f.hom ≫ g.hom :=
  (rfl)

variable {D} in
@[simp]
theorem Hom.id_comp (f : Hom D E) : (Hom.id E).comp f = f :=
  Hom.ext (Category.comp_id _)

variable {D} in
@[simp]
theorem Hom.comp_id (f : Hom D E) : f.comp (Hom.id D) = f :=
  Hom.ext (Category.id_comp _)

variable {D} in
@[simp]
theorem Hom.comp_assoc {W : Over S'} {G : DescentDatum p W} (h : Hom F G) (g : Hom E F)
    (f : Hom D E) : (h.comp g).comp f = h.comp (g.comp f) :=
  Hom.ext (Category.assoc _ _ _).symm

section Inv

variable {D} (f : Hom D E) [IsIso f.hom]

/-- The inverse of a morphism of descent data whose underlying morphism over `S'` is an
isomorphism. -/
noncomputable def Hom.inv : Hom E D where
  hom := CategoryTheory.inv f.hom
  map_act := by
    rw [← cancel_mono f.hom.left, Category.assoc, Category.assoc, ← Over.comp_left,
      IsIso.inv_hom_id, Over.id_left, Category.comp_id, ← f.map_act, ← Category.assoc]
    convert Category.id_comp E.act using 2
    ext <;> simp [← Over.comp_left]

@[simp]
theorem Hom.inv_hom : f.inv.hom = CategoryTheory.inv f.hom :=
  (rfl)

instance Hom.isIso_inv_hom : IsIso f.inv.hom := by
  rw [Hom.inv_hom]
  infer_instance

@[simp]
theorem Hom.inv_comp_self : f.inv.comp f = Hom.id D :=
  Hom.ext (IsIso.hom_inv_id _)

@[simp]
theorem Hom.comp_inv_self : f.comp f.inv = Hom.id E :=
  Hom.ext (IsIso.inv_hom_id _)

end Inv

/-- The descent datum on `X` transported from a descent datum on `Y` along an isomorphism
`e : X ≅ Y` over `S'`: a point `s` of `S'` acts by `s · x = e⁻¹ (s · e x)`. -/
noncomputable def transport (e : X ≅ Y) (E : DescentDatum p Y) : DescentDatum p X where
  act := pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') e.hom.left (𝟙 S) (by simp)
      (by simp) ≫ E.act ≫ e.inv.left
  act_hom := by simp
  lift_act := by
    have : pullback.lift X.hom (𝟙 X.left) (by simp) ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') e.hom.left (𝟙 S) (by simp) (by simp) =
        e.hom.left ≫ pullback.lift Y.hom (𝟙 Y.left) (by simp) := by
      ext <;> simp
    rw [reassoc_of% this, E.lift_act_assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left]
  act_assoc := by
    have key := pullback.map p (pullback.fst p (X.hom ≫ p) ≫ p) p
      (pullback.fst p (Y.hom ≫ p) ≫ p) (𝟙 S') (pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S')
        e.hom.left (𝟙 S) (by simp) (by simp)) (𝟙 S) (by simp) (by simp) ≫= E.act_assoc
    rw [← cancel_mono e.hom.left]
    simp only [Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]
    simp only [← Category.assoc] at key ⊢
    convert key using 2 <;> ext <;> simp

/-- The isomorphism `e : X ≅ Y` over `S'` is a morphism from the transported descent datum
`transport e E` to `E`. -/
noncomputable def transportHom (e : X ≅ Y) (E : DescentDatum p Y) : Hom (transport e E) E where
  hom := e.hom
  map_act := by simp [transport, ← Over.comp_left]

@[simp]
theorem transportHom_hom (e : X ≅ Y) (E : DescentDatum p Y) : (transportHom e E).hom = e.hom :=
  (rfl)

end Hom

variable (p) in
/-- The canonical descent datum on the base change `X ×_S S'` of an object `X` over `S`: a point
`s` of `S'` acts by `s · (x, s₀) = (x, s)`. -/
noncomputable def baseChange (X : Over S) : DescentDatum p ((Over.pullback p).obj X) where
  act := pullback.lift (pullback.snd _ _ ≫ pullback.fst X.hom p) (pullback.fst _ _) <| by
    simp [pullback.condition]
  act_hom := by simp
  lift_act := by refine pullback.hom_ext ?_ ?_ <;> simp
  act_assoc := by refine pullback.hom_ext ?_ ?_ <;> simp

variable (p) in
/-- The canonical action keeps the point of `X`: `s · (x, s₀)` has first coordinate `x`. -/
@[reassoc (attr := simp)]
theorem baseChange_act_fst (X : Over S) :
    (baseChange p X).act ≫ pullback.fst X.hom p =
      pullback.snd _ _ ≫ pullback.fst X.hom p := by
  simp [baseChange]

variable (p) in
/-- The canonical action moves into the fibre over `s`: `s · (x, s₀)` has second coordinate
`s`. -/
@[reassoc (attr := simp)]
theorem baseChange_act_snd (X : Over S) :
    (baseChange p X).act ≫ pullback.snd X.hom p = pullback.fst _ _ := by
  simp [baseChange]

end DescentDatum

end TauCeti
