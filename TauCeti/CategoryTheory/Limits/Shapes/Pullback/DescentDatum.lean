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
* `TauCeti.DescentDatum.baseChangePullbackAlongHom p q X₀`: the isomorphism from the canonical
  descent datum on the base change of `X₀ ×_S T` along `T ×_S S' ⟶ T` to the base change along
  `q : T ⟶ S` of the canonical descent datum on `X₀ ×_S S'`.
* `TauCeti.DescentDatum.transportArrow e D`: the descent datum relative to `q` obtained from a
  descent datum `D` relative to `p` along an isomorphism of arrows `e : Arrow.mk p ≅ Arrow.mk q`,
  functorial on morphisms, inverse to transport along `e.symm` (`transportArrowSymmHom`), and
  compatible with canonical descent data (`baseChangeTransportArrowHom`).

A descent datum `D` is *effective* when there are an object `X` over `S` and a morphism
`baseChange p X ⟶ D` of descent data which is an isomorphism over `S'`.
Effectivity is invariant under isomorphisms of arrows
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_transportArrow`), so an effectivity theorem
proved for a normal form of `p`, such as `Spec` of a ring map, applies to every arrow isomorphic
to it.
Effectivity is also stable under base change along any `q : T ⟶ S`
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_pullbackAlong`).

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

section PullbackBaseChange

variable {T : C} (q : T ⟶ S)

/-- The underlying isomorphism of `baseChangePullbackAlongHom`: on points it sends
`((x, t), (t, s))` to `((x, s), (t, s))`. Both sides are identified with `X₀ ×_S (T ×_S S')` by
pasting pullback squares. -/
private noncomputable def baseChangePullbackAlongIso (X₀ : Over S) :
    pullback (pullback.snd X₀.hom q) (pullback.fst q p) ≅
      pullback (pullback.snd X₀.hom p) (pullback.snd q p) :=
  pullbackLeftPullbackSndIso X₀.hom q (pullback.fst q p) ≪≫
    pullback.congrHom rfl pullback.condition ≪≫
    (pullbackLeftPullbackSndIso X₀.hom p (pullback.snd q p)).symm

variable (p) in
/-- Base change of canonical descent data: for `X₀` over `S` and `q : T ⟶ S`, the canonical
descent datum on the base change of `X₀ ×_S T` along `T ×_S S' ⟶ T` is isomorphic
(`isIso_baseChangePullbackAlongHom_hom`) to the base change along `q` of the canonical descent
datum on `X₀ ×_S S'`. -/
noncomputable def baseChangePullbackAlongHom (X₀ : Over S) :
    Hom (baseChange (pullback.fst q p) ((Over.pullback q).obj X₀))
      ((baseChange p X₀).pullbackAlong q) where
  hom := (Over.isoMk (baseChangePullbackAlongIso q X₀)
    (by simp [baseChangePullbackAlongIso])).hom
  map_act := by
    -- The characteristic lemmas of the two actions, with `Over.pullback` unfolded to the
    -- `pullback` projections in which the goal is stated.
    have h₁ := @pullbackAlong_act_fst_assoc _ _ _ _ _ p _ q _ (baseChange p X₀)
    have h₂ := pullbackAlong_act_snd q (baseChange p X₀)
    have h₃ := @pullbackAlongActionComparison_snd_assoc _ _ _ _ _ p _ q ((Over.pullback p).obj X₀)
    have h₄ := pullbackAlongActionComparison_fst (p := p) q ((Over.pullback p).obj X₀)
    have h₅ := @baseChange_act_fst_assoc _ _ _ _ _ (pullback.fst q p) ((Over.pullback q).obj X₀)
    have h₆ := @baseChange_act_snd_assoc _ _ _ _ _ (pullback.fst q p) ((Over.pullback q).obj X₀)
    have h₇ := baseChange_act_snd (pullback.fst q p) ((Over.pullback q).obj X₀)
    simp only [Over.pullback_obj_hom, Over.pullback_obj_left] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
    · simp [baseChangePullbackAlongIso, h₁, h₃, h₅]
    · simp [baseChangePullbackAlongIso, h₁, h₄, h₆]
    · simp [baseChangePullbackAlongIso, h₂, h₇]

variable (p) in
/-- The comparison `baseChangePullbackAlongHom` keeps the point of `X₀`. -/
@[reassoc (attr := simp)]
theorem baseChangePullbackAlongHom_hom_left_fst_fst (X₀ : Over S) :
    (baseChangePullbackAlongHom p q X₀).hom.left ≫
        pullback.fst (pullback.snd X₀.hom p) (pullback.snd q p) ≫ pullback.fst X₀.hom p =
      pullback.fst (pullback.snd X₀.hom q) (pullback.fst q p) ≫ pullback.fst X₀.hom q := by
  simp [baseChangePullbackAlongHom, baseChangePullbackAlongIso]

variable (p) in
/-- The comparison `baseChangePullbackAlongHom` keeps the point of `S'`. -/
@[reassoc (attr := simp)]
theorem baseChangePullbackAlongHom_hom_left_fst_snd (X₀ : Over S) :
    (baseChangePullbackAlongHom p q X₀).hom.left ≫
        pullback.fst (pullback.snd X₀.hom p) (pullback.snd q p) ≫ pullback.snd X₀.hom p =
      pullback.snd (pullback.snd X₀.hom q) (pullback.fst q p) ≫ pullback.snd q p := by
  simp [baseChangePullbackAlongHom, baseChangePullbackAlongIso]

variable (p) in
/-- The comparison `baseChangePullbackAlongHom` lies over `T ×_S S'`. -/
@[reassoc (attr := simp)]
theorem baseChangePullbackAlongHom_hom_left_snd (X₀ : Over S) :
    (baseChangePullbackAlongHom p q X₀).hom.left ≫
        pullback.snd (pullback.snd X₀.hom p) (pullback.snd q p) =
      pullback.snd (pullback.snd X₀.hom q) (pullback.fst q p) := by
  simp [baseChangePullbackAlongHom, baseChangePullbackAlongIso]

variable (p) in
/-- The comparison `baseChangePullbackAlongHom` is an isomorphism of descent data. -/
instance isIso_baseChangePullbackAlongHom_hom (X₀ : Over S) :
    IsIso (baseChangePullbackAlongHom p q X₀).hom := by
  rw [baseChangePullbackAlongHom]
  infer_instance

variable (p) in
/-- The comparison `baseChangePullbackAlongHom` is natural in the object over `S`. -/
theorem baseChangePullbackAlongHom_naturality {X₀ Y₀ : Over S} (g : X₀ ⟶ Y₀) :
    (baseChangePullbackAlongHom p q Y₀).comp
        (baseChangeHom (pullback.fst q p) ((Over.pullback q).map g)) =
      ((baseChangeHom p g).pullbackAlong q).comp (baseChangePullbackAlongHom p q X₀) := by
  ext
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simp

/-- **Effectivity is stable under base change.** If `D` is isomorphic to the canonical descent
datum on the base change of `X₀` along `p`, then for every `q : T ⟶ S` the base-changed datum
`D.pullbackAlong q` is isomorphic to the canonical descent datum on the base change of
`X₀ ×_S T` along `T ×_S S' ⟶ T`. -/
theorem exists_baseChange_hom_isIso_pullbackAlong {X : Over S'} {D : DescentDatum p X}
    {X₀ : Over S} (f : Hom (baseChange p X₀) D) [IsIso f.hom] :
    ∃ g : Hom (baseChange (pullback.fst q p) ((Over.pullback q).obj X₀)) (D.pullbackAlong q),
      IsIso g.hom :=
  ⟨(f.pullbackAlong q).comp (baseChangePullbackAlongHom p q X₀),
    by simp only [Hom.comp_hom]; infer_instance⟩

end PullbackBaseChange

section ArrowIso

variable {T T' : C} {q : T' ⟶ T} (e : Arrow.mk p ≅ Arrow.mk q) {X Y : Over S'}

/-- The comparison from the action space of a datum transported along
`e : Arrow.mk p ≅ Arrow.mk q` to the original action space. On points it sends `(t, x)` to
`(e⁻¹ t, x)`. -/
noncomputable def transportArrowActionComparison (X : Over S') :
    pullback q (((Over.map e.hom.left).obj X).hom ≫ q) ⟶ pullback p (X.hom ≫ p) :=
  pullback.map q (((Over.map e.hom.left).obj X).hom ≫ q) p (X.hom ≫ p) e.inv.left (𝟙 X.left)
    e.inv.right (Arrow.w_mk_right e.inv).symm (by simp)

/-- The action-space comparison for transport moves the point of `T'` to `S'` along `e⁻¹`. -/
@[reassoc (attr := simp)]
theorem transportArrowActionComparison_fst (X : Over S') :
    transportArrowActionComparison e X ≫ pullback.fst p (X.hom ≫ p) =
      pullback.fst _ _ ≫ e.inv.left :=
  pullback.lift_fst _ _ _

/-- The action-space comparison for transport preserves the point of `X`. -/
@[reassoc (attr := simp)]
theorem transportArrowActionComparison_snd (X : Over S') :
    transportArrowActionComparison e X ≫ pullback.snd p (X.hom ≫ p) = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The transport of a descent datum along an isomorphism of arrows `e : Arrow.mk p ≅ Arrow.mk q`.
If `D` acts on `X ⟶ S'` relative to `p : S' ⟶ S`, then `D.transportArrow e` acts on
`X ⟶ S' ≅ T'` relative to `q : T' ⟶ T`, by `t · x = e⁻¹ t · x`. -/
noncomputable def transportArrow (D : DescentDatum p X) :
    DescentDatum q ((Over.map e.hom.left).obj X) where
  act := transportArrowActionComparison e X ≫ D.act
  act_hom := by simp
  lift_act := by
    refine Eq.trans ?_ D.lift_act
    rw [← Category.assoc]
    congr 1
    ext <;> simp
  act_assoc := by
    dsimp only [Over.map_obj_left, Over.map_obj_hom]
    -- Compare both sides with the original twice-iterated action space, where `D.act_assoc`
    -- applies directly.
    have key := pullback.map q (pullback.fst q ((X.hom ≫ e.hom.left) ≫ q) ≫ q)
      p (pullback.fst p (X.hom ≫ p) ≫ p) e.inv.left (transportArrowActionComparison e X)
      e.inv.right (Arrow.w_mk_right e.inv).symm (by simp) ≫= D.act_assoc
    simp only [← Category.assoc] at key ⊢
    convert key using 2 <;> refine pullback.hom_ext ?_ ?_ <;> simp

/-- The transported action is the original action after moving the point of `T'` to `S'` along
`e⁻¹`: `t · x = e⁻¹ t · x`. -/
theorem transportArrow_act (D : DescentDatum p X) :
    (D.transportArrow e).act = transportArrowActionComparison e X ≫ D.act :=
  (rfl)

/-- The transport of a morphism of descent data along an isomorphism of arrows. -/
noncomputable def Hom.transportArrow {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E) :
    Hom (D.transportArrow e) (E.transportArrow e) where
  hom := (Over.map e.hom.left).map f.hom
  map_act := by
    rw [transportArrow_act, transportArrow_act, Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) f.map_act)
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    ext <;> simp

@[simp]
theorem Hom.transportArrow_hom {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E) :
    (f.transportArrow e).hom = (Over.map e.hom.left).map f.hom :=
  (rfl)

/-- Transport along an isomorphism of arrows preserves identity morphisms of descent data. -/
@[simp]
theorem Hom.transportArrow_id (D : DescentDatum p X) :
    (Hom.id D).transportArrow e = Hom.id (D.transportArrow e) :=
  Hom.ext ((Over.map e.hom.left).map_id X)

/-- Transport along an isomorphism of arrows preserves composition of morphisms of descent
data. -/
@[simp]
theorem Hom.transportArrow_comp {Z : Over S'} {D : DescentDatum p X} {E : DescentDatum p Y}
    {F : DescentDatum p Z} (g : Hom E F) (f : Hom D E) :
    (g.comp f).transportArrow e = (g.transportArrow e).comp (f.transportArrow e) :=
  Hom.ext ((Over.map e.hom.left).map_comp f.hom g.hom)

/-- Transport along an isomorphism of arrows preserves isomorphisms of descent data. -/
instance Hom.isIso_transportArrow_hom {D : DescentDatum p X} {E : DescentDatum p Y}
    (f : Hom D E) [IsIso f.hom] : IsIso (f.transportArrow e).hom := by
  rw [Hom.transportArrow_hom]
  infer_instance

/-- Transporting a descent datum along `e` and back along `e.symm` gives back the original datum:
the identity of `X` is an isomorphism of descent data. -/
noncomputable def transportArrowSymmHom (D : DescentDatum p X) :
    Hom ((D.transportArrow e).transportArrow e.symm) D where
  hom := (Over.isoMk (f := (Over.map e.symm.hom.left).obj ((Over.map e.hom.left).obj X)) (g := X)
    (Iso.refl X.left) (by simp)).hom
  map_act := by
    rw [transportArrow_act, transportArrow_act]
    simp only [Over.isoMk_hom_left, Iso.refl_hom]
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (Category.comp_id _).symm)
    congr 1
    ext <;> simp [transportArrowActionComparison]

@[simp]
theorem transportArrowSymmHom_hom_left (D : DescentDatum p X) :
    (transportArrowSymmHom e D).hom.left = 𝟙 X.left :=
  (rfl)

/-- The round-trip comparison `transportArrowSymmHom` is an isomorphism of descent data. -/
instance isIso_transportArrowSymmHom_hom (D : DescentDatum p X) :
    IsIso (transportArrowSymmHom e D).hom := by
  rw [transportArrowSymmHom]
  infer_instance

/-- Transport along an isomorphism of arrows `e : Arrow.mk p ≅ Arrow.mk q` takes canonical descent
data to canonical descent data: for `Y₀` over `S`, the base change of `Y₀ ⟶ S ≅ T` along `q` is
isomorphic, as a descent datum, to the transport of the base change of `Y₀` along `p`. -/
noncomputable def baseChangeTransportArrowHom (Y₀ : Over S) :
    Hom (baseChange q ((Over.map e.hom.right).obj Y₀)) ((baseChange p Y₀).transportArrow e) where
  hom := (Over.isoMk (asIso (pullback.map (Y₀.hom ≫ e.hom.right) q Y₀.hom p (𝟙 Y₀.left)
    e.inv.left e.inv.right (by simp) (Arrow.w_mk_right e.inv).symm)) (by simp)).hom
  map_act := by
    rw [transportArrow_act]
    refine pullback.hom_ext ?_ ?_ <;> simp [baseChange, transportArrowActionComparison]

@[simp]
theorem baseChangeTransportArrowHom_hom_left (Y₀ : Over S) :
    (baseChangeTransportArrowHom e Y₀).hom.left =
      pullback.map (Y₀.hom ≫ e.hom.right) q Y₀.hom p (𝟙 Y₀.left) e.inv.left e.inv.right
        (by simp) (Arrow.w_mk_right e.inv).symm :=
  (rfl)

/-- The comparison `baseChangeTransportArrowHom` is an isomorphism of descent data. -/
instance isIso_baseChangeTransportArrowHom_hom (Y₀ : Over S) :
    IsIso (baseChangeTransportArrowHom e Y₀).hom := by
  rw [baseChangeTransportArrowHom]
  infer_instance

/-- **Effectivity is invariant under isomorphisms of arrows.** If the transport of `D` along
`e : Arrow.mk p ≅ Arrow.mk q` is isomorphic to the canonical descent datum on the base change of
`Y₀` along `q`, then `D` is isomorphic to the canonical descent datum on the base change of
`Y₀ ⟶ T ≅ S` along `p`. -/
theorem exists_baseChange_hom_isIso_of_transportArrow (D : DescentDatum p X) {Y₀ : Over T}
    (f : Hom (baseChange q Y₀) (D.transportArrow e)) [IsIso f.hom] :
    ∃ g : Hom (baseChange p ((Over.map e.inv.right).obj Y₀)) D, IsIso g.hom :=
  ⟨(transportArrowSymmHom e D).comp ((f.transportArrow e.symm).comp
    (baseChangeTransportArrowHom e.symm Y₀)), by simp only [Hom.comp_hom]; infer_instance⟩

end ArrowIso

end DescentDatum

end TauCeti
