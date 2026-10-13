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
* `TauCeti.DescentDatum.pullbackAlong D q`: the descent datum obtained from `D` after an arbitrary
  base change `q : T ⟶ S`, functorial on morphisms of descent data.
* `TauCeti.DescentDatum.baseChange p X`: the canonical descent datum on the base change
  `X ×_S S'` of an object `X` over `S`, acting by `s · (x, s₀) = (x, s)`, with the morphism
  `baseChangeHom p f : Hom (baseChange p X) (baseChange p Y)` induced by `f : X ⟶ Y` over `S`.

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

section Pullback

variable {T : C} (q : T ⟶ S) {X Y Z : Over S'}

/-- The object over `T ×_S S'` obtained by pulling an object over `S'` back along the second
projection `T ×_S S' ⟶ S'`. This is the carrier on which a base-changed descent datum acts. -/
noncomputable abbrev pullbackAlongObj (X : Over S') : Over (pullback q p) :=
  (Over.pullback (pullback.snd q p)).obj X

/-- The comparison from the action space of the base-changed datum to the action space of the
original datum. On points it sends `((t, s₁), (x, (t, s₂)))` to `(s₁, x)`. -/
noncomputable def pullbackAlongActionComparison (X : Over S') :
    pullback (pullback.fst q p) ((pullbackAlongObj (p := p) q X).hom ≫ pullback.fst q p) ⟶
      pullback p (X.hom ≫ p) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.snd q p)
    (pullback.snd _ _ ≫ pullback.fst X.hom (pullback.snd q p)) <| by
      simp only [Category.assoc]
      slice_lhs 2 3 => rw [← pullback.condition]
      slice_rhs 2 3 => rw [pullback.condition]
      slice_rhs 3 4 => rw [← pullback.condition]
      simpa only [pullbackAlongObj, Over.pullback_obj_hom, Category.assoc] using
        pullback.condition_assoc
        (f := pullback.fst q p)
        (g := (pullbackAlongObj (p := p) q X).hom ≫ pullback.fst q p) q

/-- The action-space comparison preserves the first `S'`-coordinate. -/
@[reassoc (attr := simp)]
theorem pullbackAlongActionComparison_fst (X : Over S') :
    pullbackAlongActionComparison (p := p) q X ≫ pullback.fst p (X.hom ≫ p) =
      pullback.fst _ _ ≫ pullback.snd q p :=
  pullback.lift_fst _ _ _

/-- The action-space comparison preserves the point of `X`. -/
@[reassoc (attr := simp)]
theorem pullbackAlongActionComparison_snd (X : Over S') :
    pullbackAlongActionComparison (p := p) q X ≫ pullback.snd p (X.hom ≫ p) =
      pullback.snd _ _ ≫ pullback.fst X.hom (pullback.snd q p) :=
  pullback.lift_snd _ _ _

/-- The comparison from the twice-iterated action space after base change to the original
twice-iterated action space. -/
private noncomputable def pullbackAlongActionAssocComparison (X : Over S') :
    pullback (pullback.fst q p)
        (pullback.fst (pullback.fst q p)
          ((pullbackAlongObj (p := p) q X).hom ≫ pullback.fst q p) ≫ pullback.fst q p) ⟶
      pullback p (pullback.fst p (X.hom ≫ p) ≫ p) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.snd q p)
    (pullback.snd _ _ ≫ pullbackAlongActionComparison (p := p) q X) <| by
      simp only [Category.assoc]
      slice_lhs 2 3 => rw [← pullback.condition]
      rw [pullbackAlongActionComparison_fst_assoc]
      slice_rhs 3 4 => rw [← pullback.condition]
      simpa only [pullbackAlongObj, Over.pullback_obj_hom, Category.assoc] using
        pullback.condition_assoc
        (f := pullback.fst q p)
        (g := pullback.fst (pullback.fst q p)
          ((pullbackAlongObj (p := p) q X).hom ≫ pullback.fst q p) ≫ pullback.fst q p) q

private theorem pullbackAlongNormalizationComparison (X : Over S') :
    pullback.lift (pullbackAlongObj (p := p) q X).hom (𝟙 _) (by simp) ≫
        pullbackAlongActionComparison (p := p) q X =
      pullback.fst X.hom (pullback.snd q p) ≫
        pullback.lift X.hom (𝟙 X.left) (by simp) := by
  apply pullback.hom_ext
  · simpa [pullbackAlongActionComparison, pullbackAlongObj] using
      (pullback.condition (f := X.hom) (g := pullback.snd q p)).symm
  · simp [pullbackAlongActionComparison, pullbackAlongObj]

private theorem pullbackAlongActionAssocComparison_act (D : DescentDatum p X) :
    pullback.lift (pullback.fst _ _)
          (pullback.snd _ _ ≫
            pullback.lift (pullbackAlongActionComparison (p := p) q X ≫ D.act)
              (pullback.fst _ _) (by simp))
          (by
            simp only [pullbackAlongObj, Over.pullback_obj_hom, Category.assoc,
              pullback.lift_snd_assoc]
            exact pullback.condition) ≫
        pullbackAlongActionComparison (p := p) q X =
      pullbackAlongActionAssocComparison (p := p) q X ≫
        pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
          (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ D.act)
          (by rw [Category.assoc, reassoc_of% D.act_hom]; exact pullback.condition) := by
  apply pullback.hom_ext
  · simp [pullbackAlongActionAssocComparison, pullbackAlongActionComparison, pullbackAlongObj]
  · simp only [Category.assoc]
    dsimp only [pullbackAlongActionAssocComparison]
    slice_lhs 2 3 => rw [pullbackAlongActionComparison_snd]
    slice_lhs 1 2 => rw [pullback.lift_snd]
    slice_lhs 2 3 => rw [pullback.lift_fst]
    slice_rhs 2 3 => rw [pullback.lift_snd]
    slice_rhs 1 2 => rw [pullback.lift_snd]
    exact (Category.assoc _ _ _).symm

private theorem pullbackAlongActionAssocComparison_snd (X : Over S') :
    pullback.lift (pullback.fst _ _)
          (pullback.snd _ _ ≫ pullback.snd _ _)
          (by
            simp only [pullbackAlongObj, Over.pullback_obj_hom, Category.assoc]
            slice_rhs 2 4 => rw [← pullback.condition]
            exact pullback.condition) ≫
        pullbackAlongActionComparison (p := p) q X =
      pullbackAlongActionAssocComparison (p := p) q X ≫
        pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
          (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫
            pullback.snd p (X.hom ≫ p))
          (by
            rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
            exact pullback.condition) := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    dsimp only [pullbackAlongActionAssocComparison]
    slice_lhs 2 3 => rw [pullbackAlongActionComparison_fst]
    slice_lhs 1 2 => rw [pullback.lift_fst]
    slice_rhs 2 3 => rw [pullback.lift_fst]
    slice_rhs 1 2 => rw [pullback.lift_fst]
  · simp only [Category.assoc]
    dsimp only [pullbackAlongActionAssocComparison]
    slice_lhs 2 3 => rw [pullbackAlongActionComparison_snd]
    slice_lhs 1 2 => rw [pullback.lift_snd]
    slice_rhs 2 3 => rw [pullback.lift_snd]
    slice_rhs 1 2 => rw [pullback.lift_snd]
    slice_rhs 2 3 => rw [pullbackAlongActionComparison_snd]
    exact Category.assoc _ _ _

private theorem pullbackAlongActionComparison_naturality (f : X ⟶ Y) :
    pullback.map (pullback.fst q p) _ (pullback.fst q p) _ (𝟙 _)
          ((Over.pullback (pullback.snd q p)).map f).left (𝟙 _) (by simp) (by simp) ≫
        pullbackAlongActionComparison (p := p) q Y =
      pullbackAlongActionComparison (p := p) q X ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S)
          (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp [pullbackAlongActionComparison, pullbackAlongObj, Over.pullback_map_left]

/-- Base change of a descent datum along an arbitrary morphism `q : T ⟶ S`. If `D` acts on
`X ⟶ S'` relative to `p : S' ⟶ S`, then `D.pullbackAlong q` acts on
`X ×_{S'} (T ×_S S') ⟶ T ×_S S'` relative to the base change of `p` to `T`. -/
noncomputable def pullbackAlong (D : DescentDatum p X) :
    DescentDatum (pullback.fst q p) (pullbackAlongObj (p := p) q X) where
  act := pullback.lift (pullbackAlongActionComparison (p := p) q X ≫ D.act)
    (pullback.fst _ _) <| by simp
  act_hom := by simp
  lift_act := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullbackAlongNormalizationComparison, Category.assoc, D.lift_act,
        Category.comp_id, Category.id_comp]
    · simp
  act_assoc := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      -- Compare both sides with the original twice-iterated action space, where `D.act_assoc`
      -- applies directly.
      calc
        _ = (pullbackAlongActionAssocComparison (p := p) q X ≫
              pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
                (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ D.act)
                (by rw [Category.assoc, reassoc_of% D.act_hom]; exact pullback.condition)) ≫
              D.act := by rw [← Category.assoc, pullbackAlongActionAssocComparison_act]
        _ = pullbackAlongActionAssocComparison (p := p) q X ≫
              (pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
                (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ D.act)
                (by rw [Category.assoc, reassoc_of% D.act_hom]; exact pullback.condition) ≫
              D.act) := Category.assoc _ _ _
        _ = pullbackAlongActionAssocComparison (p := p) q X ≫
              (pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
                (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫
                  pullback.snd p (X.hom ≫ p))
                (by
                  rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
                  exact pullback.condition) ≫ D.act) := congrArg _ D.act_assoc
        _ = (pullbackAlongActionAssocComparison (p := p) q X ≫
              pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
                (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫
                  pullback.snd p (X.hom ≫ p))
                (by
                  rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
                  exact pullback.condition)) ≫ D.act := (Category.assoc _ _ _).symm
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (· ≫ D.act) (pullbackAlongActionAssocComparison_snd (p := p) q X).symm
    · simp

/-- The underlying map of the base-changed action, followed by the projection to `X`, is the
original action applied after forgetting the base-change coordinates. -/
@[reassoc (attr := simp)]
theorem pullbackAlong_act_fst (D : DescentDatum p X) :
    (D.pullbackAlong q).act ≫ pullback.fst X.hom (pullback.snd q p) =
      pullbackAlongActionComparison (p := p) q X ≫ D.act :=
  pullback.lift_fst _ _ _

/-- The base-changed action moves a point into the fibre over its first
`T ×_S S'`-coordinate. -/
@[reassoc (attr := simp)]
theorem pullbackAlong_act_snd (D : DescentDatum p X) :
    (D.pullbackAlong q).act ≫ pullback.snd X.hom (pullback.snd q p) = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

variable {q}

/-- Base change of a morphism of descent data. -/
noncomputable def Hom.pullbackAlong {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    (q : T ⟶ S) : Hom (D.pullbackAlong q) (E.pullbackAlong q) where
  hom := (Over.pullback (pullback.snd q p)).map f.hom
  map_act := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackAlong_act_fst]
      rw [← Category.assoc, pullbackAlongActionComparison_naturality, Category.assoc, f.map_act]
      have hm : ((Over.pullback (pullback.snd q p)).map f.hom).left ≫
          pullback.fst Y.hom (pullback.snd q p) =
          pullback.fst X.hom (pullback.snd q p) ≫ f.hom.left := by simp
      rw [hm, pullbackAlong_act_fst_assoc]
    · simp

/-- The underlying morphism of the base-changed morphism is obtained by pullback in `Over`. -/
@[simp]
theorem Hom.pullbackAlong_hom {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    (q : T ⟶ S) : (f.pullbackAlong q).hom = (Over.pullback (pullback.snd q p)).map f.hom :=
  (rfl)

/-- Base change preserves morphisms of descent data whose underlying morphism is an isomorphism. -/
instance Hom.isIso_pullbackAlong_hom {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [IsIso f.hom] (q : T ⟶ S) : IsIso (f.pullbackAlong q).hom := by
  rw [Hom.pullbackAlong_hom]
  infer_instance

/-- Base change preserves identity morphisms of descent data. -/
@[simp]
theorem Hom.pullbackAlong_id (D : DescentDatum p X) (q : T ⟶ S) :
    (Hom.id D).pullbackAlong q = Hom.id (D.pullbackAlong q) :=
  Hom.ext ((Over.pullback (pullback.snd q p)).map_id X)

/-- Base change preserves composition of morphisms of descent data. -/
@[simp]
theorem Hom.pullbackAlong_comp {D : DescentDatum p X} {E : DescentDatum p Y}
    {F : DescentDatum p Z} (g : Hom E F) (f : Hom D E) (q : T ⟶ S) :
    (g.comp f).pullbackAlong q = (g.pullbackAlong q).comp (f.pullbackAlong q) :=
  Hom.ext ((Over.pullback (pullback.snd q p)).map_comp f.hom g.hom)

end Pullback

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

variable (p) in
/-- The morphism of canonical descent data induced by a morphism `f : X ⟶ Y` over `S`: its
underlying morphism over `S'` is the base change `(x, s) ↦ (f x, s)`. -/
noncomputable def baseChangeHom {X Y : Over S} (f : X ⟶ Y) :
    Hom (baseChange p X) (baseChange p Y) where
  hom := (Over.pullback p).map f
  map_act := by refine pullback.hom_ext ?_ ?_ <;> simp

variable (p) in
@[simp]
theorem baseChangeHom_hom {X Y : Over S} (f : X ⟶ Y) :
    (baseChangeHom p f).hom = (Over.pullback p).map f :=
  (rfl)

variable (p) in
@[simp]
theorem baseChangeHom_id (X : Over S) : baseChangeHom p (𝟙 X) = Hom.id (baseChange p X) :=
  Hom.ext ((Over.pullback p).map_id X)

variable (p) in
@[simp]
theorem baseChangeHom_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChangeHom p (f ≫ g) = (baseChangeHom p g).comp (baseChangeHom p f) :=
  Hom.ext ((Over.pullback p).map_comp f g)

end DescentDatum

end TauCeti
