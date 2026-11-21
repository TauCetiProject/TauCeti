/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Cat
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Equivalence
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Categorical.Groupoid

/-!
# The 2-fibre product of pseudofunctors into `Cat`

Let `f : F ⟶ H` and `g : G ⟶ H` be strong transformations between pseudofunctors from a
bicategory `B` to `Cat`. Their 2-fibre product `f.twoFiberProduct g` is the pseudofunctor whose
fibre over `b` is the categorical pullback `f.app b ⊡ g.app b` of Mathlib: its objects are
triples `(x₁, x₂, f.app b x₁ ≅ g.app b x₂)`. A `1`-morphism `φ : b ⟶ b'` acts componentwise
through `F.map φ` and `G.map φ`, the structural isomorphism being transported along the
naturality isomorphisms of `f` and `g`. The identity and composition constraints are those of
`F` and `G`, componentwise.

This is the 2-fibre product in the 2-category of pseudofunctors into `Cat`, and it is the
construction behind 2-fibre products of prestacks and stacks over a site, such as the stacks in
groupoids over schemes, whose fibre over `T` is the 2-fibre product of the fibre groupoids.
It comes with the two projections, the invertible 2-cell `fst ≫ f ≅ snd ≫ g`, and its
2-universal property: strong transformations `a : K ⟶ F` and `c : K ⟶ G` with an invertible
modification `a ≫ f ≅ c ≫ g` lift to `K ⟶ f.twoFiberProduct g` (`twoFiberProduct.lift`), the
2-commutativity isomorphism restricting along the lift to the given one
(`twoFiberProduct.lift_whiskerLeft_iso_hom`), and modifications between strong transformations
into the 2-fibre product correspond to compatible pairs of modifications after composing with the
projections (`twoFiberProduct.homMk`, `twoFiberProduct.isoMk`, `twoFiberProduct.hom_ext`).
The fibres are groupoids when those of `F` and `G` are, and the second projection is a
fibrewise equivalence when `f` is.

The pseudofunctors take values in `Cat.{v, max u v}`: the objects of a categorical pullback
carry an isomorphism, so they live in a universe containing the morphisms. For stacks over
schemes, `Cat.{u, u + 1}`, the universe levels have to be given explicitly.

The objects of the fibres, the projections, the lift and the functors between the fibres are
reducible, so that the components of the objects of the fibres appear directly to `simp` in the
coherence conditions; the bodies are exposed for the same reason. As plain definitions, the
objects they produce would only be definitionally, not reducibly, equal to their components, so
that `simp` lemmas such as `Functor.map_id` no longer apply to the identities in those conditions.
The `simp` lemmas `fst_app_obj`, `lift_app_obj_fst` and their companions name these values.

## Main declarations

* `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct`: the 2-fibre product of `f` and `g`.
* `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.fst`,
  `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.snd`: the two projections.
* `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.iso`: the invertible modification
  `fst f g ≫ f ≅ snd f g ≫ g`.
* `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.lift`, with
  `twoFiberProduct.liftFstIso` and `twoFiberProduct.liftSndIso`: the strong transformation into
  the 2-fibre product induced by a 2-commutative square, and
  `twoFiberProduct.lift_whiskerLeft_iso_hom`, its compatibility with the 2-cells.
* `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.homMk`,
  `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.isoMk`,
  `CategoryTheory.Pseudofunctor.StrongTrans.twoFiberProduct.hom_ext`: modifications and
  invertible modifications into the 2-fibre product.

## References

* [Stacks Project, Section 003O](https://stacks.math.columbia.edu/tag/003O) (2-fibre products)
* [Kerodon, Tag 032Z](https://kerodon.net/tag/032Z) (categorical pullbacks)
-/

@[expose] public section

universe w₁ v₁ u₁ v u

namespace CategoryTheory

open Bicategory Limits CategoricalPullback

namespace Pseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {F G H : Pseudofunctor B Cat.{v, max u v}}

namespace StrongTrans

variable (f : StrongTrans F H) (g : StrongTrans G H)

namespace twoFiberProduct

/-- The functor between the fibres of the 2-fibre product over a `1`-morphism `φ : b ⟶ b'`. -/
@[simps]
abbrev mapFunctor {b b' : B} (φ : b ⟶ b') :
    (f.app b).toFunctor ⊡ (g.app b).toFunctor ⥤ (f.app b').toFunctor ⊡ (g.app b').toFunctor where
  obj x :=
    { fst := (F.map φ).toFunctor.obj x.fst
      snd := (G.map φ).toFunctor.obj x.snd
      iso := (Cat.Hom.toNatIso (f.naturality φ)).app x.fst ≪≫
        (H.map φ).toFunctor.mapIso x.iso ≪≫ (Cat.Hom.toNatIso (g.naturality φ)).symm.app x.snd }
  map u :=
    { fst := (F.map φ).toFunctor.map u.fst
      snd := (G.map φ).toFunctor.map u.snd
      w := by
        have h₁ := (f.naturality φ).hom.toNatTrans.naturality u.fst
        have h₂ := (g.naturality φ).inv.toNatTrans.naturality u.snd
        dsimp at h₁ h₂ ⊢
        simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Category.assoc]
        rw [reassoc_of% h₁, ← Functor.map_comp_assoc, u.w, Functor.map_comp_assoc, h₂] }
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

/-- The natural transformation between the functors `mapFunctor f g φ` and `mapFunctor f g ψ`
induced by a `2`-morphism `η : φ ⟶ ψ`. -/
@[simps!]
def mapNatTrans {b b' : B} {φ ψ : b ⟶ b'} (η : φ ⟶ ψ) : mapFunctor f g φ ⟶ mapFunctor f g ψ where
  app x :=
    { fst := (F.map₂ η).toNatTrans.app x.fst
      snd := (G.map₂ η).toNatTrans.app x.snd
      w := by
        have h₁ := naturality_naturality_app f η x.fst
        have h₂ := naturality_naturality_app g η x.snd
        dsimp only [mapFunctor_obj_iso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Iso.symm_hom]
        simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Category.assoc]
        have h₂' : (H.map₂ η).toNatTrans.app ((g.app b).toFunctor.obj x.snd) ≫
            (g.naturality ψ).inv.toNatTrans.app x.snd = (g.naturality φ).inv.toNatTrans.app x.snd ≫
              (g.app b').toFunctor.map ((G.map₂ η).toNatTrans.app x.snd) := by
          rw [← cancel_epi ((g.naturality φ).hom.toNatTrans.app x.snd), ← reassoc_of% h₂]
          simp
        rw [reassoc_of% h₁, ← NatTrans.naturality_assoc, h₂'] }
  naturality _ _ u := by
    ext
    exacts [(F.map₂ η).toNatTrans.naturality u.fst, (G.map₂ η).toNatTrans.naturality u.snd]

/-- The isomorphism between `mapFunctor f g (𝟙 b)` and the identity functor. -/
@[simps!]
def mapIdIso (b : B) : mapFunctor f g (𝟙 b) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun x ↦ mkIso ((Cat.Hom.toNatIso (F.mapId b)).app x.fst)
    ((Cat.Hom.toNatIso (G.mapId b)).app x.snd) (by
      dsimp only [mapFunctor_obj_iso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Iso.symm_hom, Functor.id_obj]
      simp [StrongTrans.naturality_id_hom_app, StrongTrans.naturality_id_inv_app,
        ← Functor.map_comp, ← Cat.Hom₂.comp_app])) (by
      intro x y u
      ext
      · exact (F.mapId b).hom.toNatTrans.naturality u.fst
      · exact (G.mapId b).hom.toNatTrans.naturality u.snd)

/-- The isomorphism between `mapFunctor f g (φ ≫ ψ)` and the composite of `mapFunctor f g φ`
and `mapFunctor f g ψ`. -/
@[simps!]
def mapCompIso {b₀ b₁ b₂ : B} (φ : b₀ ⟶ b₁) (ψ : b₁ ⟶ b₂) :
    mapFunctor f g (φ ≫ ψ) ≅ mapFunctor f g φ ⋙ mapFunctor f g ψ :=
  NatIso.ofComponents (fun x ↦ mkIso ((Cat.Hom.toNatIso (F.mapComp φ ψ)).app x.fst)
    ((Cat.Hom.toNatIso (G.mapComp φ ψ)).app x.snd) (by
      dsimp only [mapFunctor_obj_iso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Iso.symm_hom, Functor.comp_obj]
      simp [StrongTrans.naturality_comp_hom_app, StrongTrans.naturality_comp_inv_app,
        ← Functor.map_comp, ← Cat.Hom₂.comp_app]
      simp only [Functor.map_comp, Category.assoc])) (by
      intro x y u
      ext
      · exact (F.mapComp φ ψ).hom.toNatTrans.naturality u.fst
      · exact (G.mapComp φ ψ).hom.toNatTrans.naturality u.snd)

end twoFiberProduct

open twoFiberProduct in
/-- The 2-fibre product of strong transformations `f : F ⟶ H` and `g : G ⟶ H` of pseudofunctors
into `Cat`: its fibre over `b` is the categorical pullback of `f.app b` and `g.app b`. -/
@[simps! map_toFunctor map₂_toNatTrans]
abbrev twoFiberProduct : Pseudofunctor B Cat.{v, max u v} where
  obj b := ⟨(f.app b).toFunctor ⊡ (g.app b).toFunctor, inferInstance⟩
  map φ := ⟨mapFunctor f g φ⟩
  map₂ η := ⟨mapNatTrans f g η⟩
  mapId b := Cat.Hom.isoMk (mapIdIso f g b)
  mapComp φ ψ := Cat.Hom.isoMk (mapCompIso f g φ ψ)
  map₂_id φ := by
    ext x : 1
    · exact congr_arg (fun θ ↦ θ.toNatTrans.app x.fst) (F.map₂_id φ)
    · exact congr_arg (fun θ ↦ θ.toNatTrans.app x.snd) (G.map₂_id φ)
  map₂_comp η θ := by
    ext x : 1
    · exact congr_arg (fun θ ↦ θ.toNatTrans.app x.fst) (F.map₂_comp η θ)
    · exact congr_arg (fun θ ↦ θ.toNatTrans.app x.snd) (G.map₂_comp η θ)
  map₂_whisker_left φ ψ ψ' η := by ext x : 1 <;> simp
  map₂_whisker_right η ψ := by ext x : 1 <;> simp
  map₂_associator φ ψ χ := by ext x : 1 <;> simp
  map₂_left_unitor φ := by ext x : 1 <;> simp
  map₂_right_unitor φ := by ext x : 1 <;> simp

namespace twoFiberProduct

/-- The first projection `π₁` out of the fibre of the 2-fibre product over `b`. It is written out,
rather than taken to be `π₁`, so that its values on objects reduce to `x.fst` and `simp` can
match identity morphisms on both sides of the naturality conditions. -/
abbrev fstFunctor (b : B) : (twoFiberProduct f g).obj b ⥤ F.obj b where
  obj x := x.fst
  map u := u.fst

/-- `fstFunctor f g b` is Mathlib's projection `π₁` out of the categorical pullback. -/
lemma fstFunctor_eq_π₁ (b : B) :
    fstFunctor f g b = π₁ (f.app b).toFunctor (g.app b).toFunctor :=
  rfl

/-- The naturality isomorphism of the first projection, whose components are identities. -/
def fstNaturality {b b' : B} (φ : b ⟶ b') :
    (twoFiberProduct f g).map φ ≫ (⟨fstFunctor f g b'⟩ : (twoFiberProduct f g).obj b' ⟶ F.obj b') ≅
      ⟨fstFunctor f g b⟩ ≫ F.map φ :=
  Iso.refl _

@[simp]
lemma fstNaturality_hom_app {b b' : B} (φ : b ⟶ b') (x : (twoFiberProduct f g).obj b) :
    (fstNaturality f g φ).hom.toNatTrans.app x = 𝟙 ((F.map φ).toFunctor.obj x.fst) :=
  (rfl)

@[simp]
lemma fstNaturality_inv_app {b b' : B} (φ : b ⟶ b') (x : (twoFiberProduct f g).obj b) :
    (fstNaturality f g φ).inv.toNatTrans.app x = 𝟙 ((F.map φ).toFunctor.obj x.fst) :=
  (rfl)

/-- The first projection of the 2-fibre product. -/
abbrev fst : twoFiberProduct f g ⟶ F where
  app b := ⟨fstFunctor f g b⟩
  naturality := fstNaturality f g
  naturality_naturality η := by ext x : 3; simp
  naturality_id b := by ext x : 3; simp
  naturality_comp φ ψ := by ext x : 3; simp

@[simp]
lemma fst_app_obj (b : B) (x : (twoFiberProduct f g).obj b) :
    ((fst f g).app b).toFunctor.obj x = x.fst :=
  (rfl)

@[simp]
lemma fst_app_map (b : B) {x y : (twoFiberProduct f g).obj b} (u : x ⟶ y) :
    ((fst f g).app b).toFunctor.map u = u.fst :=
  (rfl)

/-- The second projection `π₂` out of the fibre of the 2-fibre product over `b`. It is written out,
rather than taken to be `π₂`, so that its values on objects reduce to `x.snd` and `simp` can
match identity morphisms on both sides of the naturality conditions. -/
abbrev sndFunctor (b : B) : (twoFiberProduct f g).obj b ⥤ G.obj b where
  obj x := x.snd
  map u := u.snd

/-- `sndFunctor f g b` is Mathlib's projection `π₂` out of the categorical pullback. -/
lemma sndFunctor_eq_π₂ (b : B) :
    sndFunctor f g b = π₂ (f.app b).toFunctor (g.app b).toFunctor :=
  rfl

/-- The naturality isomorphism of the second projection, whose components are identities. -/
def sndNaturality {b b' : B} (φ : b ⟶ b') :
    (twoFiberProduct f g).map φ ≫ (⟨sndFunctor f g b'⟩ : (twoFiberProduct f g).obj b' ⟶ G.obj b') ≅
      ⟨sndFunctor f g b⟩ ≫ G.map φ :=
  Iso.refl _

@[simp]
lemma sndNaturality_hom_app {b b' : B} (φ : b ⟶ b') (x : (twoFiberProduct f g).obj b) :
    (sndNaturality f g φ).hom.toNatTrans.app x = 𝟙 ((G.map φ).toFunctor.obj x.snd) :=
  (rfl)

@[simp]
lemma sndNaturality_inv_app {b b' : B} (φ : b ⟶ b') (x : (twoFiberProduct f g).obj b) :
    (sndNaturality f g φ).inv.toNatTrans.app x = 𝟙 ((G.map φ).toFunctor.obj x.snd) :=
  (rfl)

/-- The second projection of the 2-fibre product. -/
abbrev snd : twoFiberProduct f g ⟶ G where
  app b := ⟨sndFunctor f g b⟩
  naturality := sndNaturality f g
  naturality_naturality η := by ext x : 3; simp
  naturality_id b := by ext x : 3; simp
  naturality_comp φ ψ := by ext x : 3; simp

@[simp]
lemma snd_app_obj (b : B) (x : (twoFiberProduct f g).obj b) :
    ((snd f g).app b).toFunctor.obj x = x.snd :=
  (rfl)

@[simp]
lemma snd_app_map (b : B) {x y : (twoFiberProduct f g).obj b} (u : x ⟶ y) :
    ((snd f g).app b).toFunctor.map u = u.snd :=
  (rfl)

/-- The components of the 2-commutativity isomorphism of the 2-fibre product: over `b`, the
structural isomorphisms `f.app b x.fst ≅ g.app b x.snd` of the objects `x` of the fibre. -/
def isoComponent (b : B) : (fst f g ≫ f).app b ≅ (snd f g ≫ g).app b where
  hom := ⟨{ app x := x.iso.hom, naturality _ _ u := u.w }⟩
  inv := ⟨{ app x := x.iso.inv, naturality _ _ u := Hom.w' u }⟩
  hom_inv_id := Cat.Hom₂.ext (NatTrans.ext (funext fun x ↦ x.iso.hom_inv_id))
  inv_hom_id := Cat.Hom₂.ext (NatTrans.ext (funext fun x ↦ x.iso.inv_hom_id))

@[simp]
lemma isoComponent_hom_app (b : B) (x : (twoFiberProduct f g).obj b) :
    (isoComponent f g b).hom.toNatTrans.app x = x.iso.hom :=
  (rfl)

@[simp]
lemma isoComponent_inv_app (b : B) (x : (twoFiberProduct f g).obj b) :
    (isoComponent f g b).inv.toNatTrans.app x = x.iso.inv :=
  (rfl)

/-- The 2-commutativity isomorphism `fst f g ≫ f ≅ snd f g ≫ g` of the 2-fibre product, given
over `b` by the structural isomorphisms of the objects of the fibre. -/
def iso : fst f g ≫ f ≅ snd f g ≫ g :=
  StrongTrans.isoMk (isoComponent f g) fun φ ↦
    (naturality_app_iff φ _ _).2 fun x ↦ by
      rw [isoComponent_hom_app, isoComponent_hom_app, comp_naturality_hom_app,
        comp_naturality_hom_app]
      simp

@[simp]
lemma iso_hom_as_app_app (b : B) (x : (twoFiberProduct f g).obj b) :
    ((iso f g).hom.as.app b).toNatTrans.app x = x.iso.hom :=
  (rfl)

@[simp]
lemma iso_inv_as_app_app (b : B) (x : (twoFiberProduct f g).obj b) :
    ((iso f g).inv.as.app b).toNatTrans.app x = x.iso.inv :=
  (rfl)

section lift

variable {K : Pseudofunctor B Cat.{v, max u v}} (a : K ⟶ F) (c : K ⟶ G) (e : a ≫ f ≅ c ≫ g)

/-- The functor from the fibre of `K` over `b` to the fibre of the 2-fibre product induced by
strong transformations `a : K ⟶ F` and `c : K ⟶ G` with an invertible modification
`e : a ≫ f ≅ c ≫ g`. -/
abbrev liftFunctor (b : B) : K.obj b ⥤ (twoFiberProduct f g).obj b where
  obj k :=
    { fst := (a.app b).toFunctor.obj k
      snd := (c.app b).toFunctor.obj k
      iso :=
        { hom := (e.hom.as.app b).toNatTrans.app k
          inv := (e.inv.as.app b).toNatTrans.app k
          hom_inv_id := congrArg (fun m ↦ (m.as.app b).toNatTrans.app k) e.hom_inv_id
          inv_hom_id := congrArg (fun m ↦ (m.as.app b).toNatTrans.app k) e.inv_hom_id } }
  map u :=
    { fst := (a.app b).toFunctor.map u
      snd := (c.app b).toFunctor.map u
      w := (e.hom.as.app b).toNatTrans.naturality u }

/-- The naturality isomorphism of `lift f g a c e`, built from those of `a` and `c`. -/
def liftNaturality {b b' : B} (φ : b ⟶ b') :
    K.map φ ≫ (⟨liftFunctor f g a c e b'⟩ : K.obj b' ⟶ (twoFiberProduct f g).obj b') ≅
      ⟨liftFunctor f g a c e b⟩ ≫ (twoFiberProduct f g).map φ :=
  Cat.Hom.isoMk (NatIso.ofComponents
    (fun k ↦ mkIso ((Cat.Hom.toNatIso (a.naturality φ)).app k)
      ((Cat.Hom.toNatIso (c.naturality φ)).app k) (by
        have h := (naturality_app_iff φ _ _).1 (e.hom.as.naturality φ) k
        rw [comp_naturality_hom_app, comp_naturality_hom_app] at h
        dsimp
        simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv]
        rw [← cancel_mono ((g.naturality φ).hom.toNatTrans.app ((c.app b).toFunctor.obj k))]
        simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
        simpa using h.symm))
    (fun u ↦ by
      ext
      · exact (a.naturality φ).hom.toNatTrans.naturality u
      · exact (c.naturality φ).hom.toNatTrans.naturality u))

@[simp]
lemma liftNaturality_hom_app_fst {b b' : B} (φ : b ⟶ b') (k : K.obj b) :
    ((liftNaturality f g a c e φ).hom.toNatTrans.app k).fst =
      (a.naturality φ).hom.toNatTrans.app k :=
  (rfl)

@[simp]
lemma liftNaturality_hom_app_snd {b b' : B} (φ : b ⟶ b') (k : K.obj b) :
    ((liftNaturality f g a c e φ).hom.toNatTrans.app k).snd =
      (c.naturality φ).hom.toNatTrans.app k :=
  (rfl)

@[simp]
lemma liftNaturality_inv_app_fst {b b' : B} (φ : b ⟶ b') (k : K.obj b) :
    ((liftNaturality f g a c e φ).inv.toNatTrans.app k).fst =
      (a.naturality φ).inv.toNatTrans.app k :=
  (rfl)

@[simp]
lemma liftNaturality_inv_app_snd {b b' : B} (φ : b ⟶ b') (k : K.obj b) :
    ((liftNaturality f g a c e φ).inv.toNatTrans.app k).snd =
      (c.naturality φ).inv.toNatTrans.app k :=
  (rfl)

/-- The strong transformation `K ⟶ twoFiberProduct f g` induced by strong transformations
`a : K ⟶ F` and `c : K ⟶ G` with an invertible modification `e : a ≫ f ≅ c ≫ g`. -/
abbrev lift : K ⟶ twoFiberProduct f g where
  app b := ⟨liftFunctor f g a c e b⟩
  naturality := liftNaturality f g a c e
  naturality_naturality η := by
    ext k : 1
    · simpa using naturality_naturality_app a η k
    · simpa using naturality_naturality_app c η k
  naturality_id b := by ext k : 1 <;> simp [naturality_id_hom_app]
  naturality_comp φ ψ := by ext k : 1 <;> simp [naturality_comp_hom_app]

/-- The composite of `lift f g a c e` with the first projection is `a`, with identity
components. -/
def liftFstIso : lift f g a c e ≫ fst f g ≅ a :=
  StrongTrans.isoMk (fun _ ↦ Iso.refl _) fun φ ↦
    (naturality_app_iff φ _ _).2 fun k ↦ by
      rw [comp_naturality_hom_app]
      simp

/-- The composite of `lift f g a c e` with the second projection is `c`, with identity
components. -/
def liftSndIso : lift f g a c e ≫ snd f g ≅ c :=
  StrongTrans.isoMk (fun _ ↦ Iso.refl _) fun φ ↦
    (naturality_app_iff φ _ _).2 fun k ↦ by
      rw [comp_naturality_hom_app]
      simp

@[simp]
lemma lift_app_obj_fst (b : B) (k : K.obj b) :
    (((lift f g a c e).app b).toFunctor.obj k).fst = (a.app b).toFunctor.obj k :=
  (rfl)

@[simp]
lemma lift_app_obj_snd (b : B) (k : K.obj b) :
    (((lift f g a c e).app b).toFunctor.obj k).snd = (c.app b).toFunctor.obj k :=
  (rfl)

@[simp]
lemma lift_app_obj_iso_hom (b : B) (k : K.obj b) :
    (((lift f g a c e).app b).toFunctor.obj k).iso.hom = (e.hom.as.app b).toNatTrans.app k :=
  (rfl)

@[simp]
lemma lift_app_obj_iso_inv (b : B) (k : K.obj b) :
    (((lift f g a c e).app b).toFunctor.obj k).iso.inv = (e.inv.as.app b).toNatTrans.app k :=
  (rfl)

@[simp]
lemma lift_app_map_fst (b : B) {k k' : K.obj b} (u : k ⟶ k') :
    (((lift f g a c e).app b).toFunctor.map u).fst = (a.app b).toFunctor.map u :=
  (rfl)

@[simp]
lemma lift_app_map_snd (b : B) {k k' : K.obj b} (u : k ⟶ k') :
    (((lift f g a c e).app b).toFunctor.map u).snd = (c.app b).toFunctor.map u :=
  (rfl)

@[simp]
lemma liftFstIso_hom_as_app_app (b : B) (k : K.obj b) :
    ((liftFstIso f g a c e).hom.as.app b).toNatTrans.app k = 𝟙 ((a.app b).toFunctor.obj k) :=
  (rfl)

@[simp]
lemma liftFstIso_inv_as_app_app (b : B) (k : K.obj b) :
    ((liftFstIso f g a c e).inv.as.app b).toNatTrans.app k = 𝟙 ((a.app b).toFunctor.obj k) :=
  (rfl)

@[simp]
lemma liftSndIso_hom_as_app_app (b : B) (k : K.obj b) :
    ((liftSndIso f g a c e).hom.as.app b).toNatTrans.app k = 𝟙 ((c.app b).toFunctor.obj k) :=
  (rfl)

@[simp]
lemma liftSndIso_inv_as_app_app (b : B) (k : K.obj b) :
    ((liftSndIso f g a c e).inv.as.app b).toNatTrans.app k = 𝟙 ((c.app b).toFunctor.obj k) :=
  (rfl)

/-- The 2-commutativity isomorphism of the 2-fibre product, whiskered by `lift f g a c e`, is `e`
up to `liftFstIso`, `liftSndIso` and associators. -/
lemma lift_whiskerLeft_iso_hom :
    lift f g a c e ◁ (iso f g).hom =
      (α_ _ _ _).inv ≫ (liftFstIso f g a c e).hom ▷ f ≫ e.hom ≫
        (liftSndIso f g a c e).inv ▷ g ≫ (α_ _ _ _).hom := by
  ext b k
  refine (Cat.whiskerLeft_app _ _ _).trans ?_
  -- On `k`, the right-hand side is definitionally `e` composed with identities.
  refine Eq.symm <| (Category.id_comp _).trans <|
    (congrArg (· ≫ _) ((f.app b).toFunctor.map_id _)).trans <| (Category.id_comp _).trans <|
      (congrArg (_ ≫ ·) <| (congrArg (· ≫ _) ((g.app b).toFunctor.map_id _)).trans
        (Category.id_comp _)).trans (Category.comp_id _)

end lift

section homMk

variable {K : Pseudofunctor B Cat.{v, max u v}} {l₁ l₂ : K ⟶ twoFiberProduct f g}

/-- A modification `l₁ ⟶ l₂` between strong transformations into the 2-fibre product, built from
modifications between their composites with the two projections that are compatible with the
structural isomorphisms of the objects of the fibres. -/
def homMk (α : l₁ ≫ fst f g ⟶ l₂ ≫ fst f g) (β : l₁ ≫ snd f g ⟶ l₂ ≫ snd f g)
    (w : ∀ (b : B) (k : K.obj b),
      (f.app b).toFunctor.map ((α.as.app b).toNatTrans.app k) ≫
          ((l₂.app b).toFunctor.obj k).iso.hom =
        ((l₁.app b).toFunctor.obj k).iso.hom ≫
          (g.app b).toFunctor.map ((β.as.app b).toNatTrans.app k)) :
    l₁ ⟶ l₂ where
  as.app b := ⟨{
    app k := ⟨(α.as.app b).toNatTrans.app k, (β.as.app b).toNatTrans.app k, w b k⟩
    naturality _ _ u := by
      ext
      · exact (α.as.app b).toNatTrans.naturality u
      · exact (β.as.app b).toNatTrans.naturality u }⟩
  as.naturality φ := by
    ext k : 1
    · simpa using (comp_naturality_app_iff φ _ _).1 (α.as.naturality φ) k
    · simpa using (comp_naturality_app_iff φ _ _).1 (β.as.naturality φ) k

@[simp]
lemma homMk_as_app_app_fst (α : l₁ ≫ fst f g ⟶ l₂ ≫ fst f g) (β : l₁ ≫ snd f g ⟶ l₂ ≫ snd f g)
    (w) (b : B) (k : K.obj b) :
    (((homMk f g α β w).as.app b).toNatTrans.app k).fst = (α.as.app b).toNatTrans.app k :=
  (rfl)

@[simp]
lemma homMk_as_app_app_snd (α : l₁ ≫ fst f g ⟶ l₂ ≫ fst f g) (β : l₁ ≫ snd f g ⟶ l₂ ≫ snd f g)
    (w) (b : B) (k : K.obj b) :
    (((homMk f g α β w).as.app b).toNatTrans.app k).snd = (β.as.app b).toNatTrans.app k :=
  (rfl)

variable {f g} in
/-- Modifications between strong transformations into the 2-fibre product are determined by
their composites with the two projections. -/
@[ext]
lemma hom_ext {m m' : l₁ ⟶ l₂}
    (h₁ : ∀ (b : B) (k : K.obj b),
      ((m.as.app b).toNatTrans.app k).fst = ((m'.as.app b).toNatTrans.app k).fst)
    (h₂ : ∀ (b : B) (k : K.obj b),
      ((m.as.app b).toNatTrans.app k).snd = ((m'.as.app b).toNatTrans.app k).snd) :
    m = m' :=
  homCategory.ext fun b ↦ Cat.Hom₂.ext (NatTrans.ext (funext fun k ↦
    CategoricalPullback.hom_ext (h₁ b k) (h₂ b k)))

/-- An isomorphism `l₁ ≅ l₂` between strong transformations into the 2-fibre product, built from
isomorphisms between their composites with the two projections that are compatible with the
structural isomorphisms of the objects of the fibres. -/
def isoMk (α : l₁ ≫ fst f g ≅ l₂ ≫ fst f g) (β : l₁ ≫ snd f g ≅ l₂ ≫ snd f g)
    (w : ∀ (b : B) (k : K.obj b),
      (f.app b).toFunctor.map ((α.hom.as.app b).toNatTrans.app k) ≫
          ((l₂.app b).toFunctor.obj k).iso.hom =
        ((l₁.app b).toFunctor.obj k).iso.hom ≫
          (g.app b).toFunctor.map ((β.hom.as.app b).toNatTrans.app k)) :
    l₁ ≅ l₂ :=
  StrongTrans.isoMk (fun b ↦ Cat.Hom.isoMk (NatIso.ofComponents
    (fun k ↦ mkIso
      { hom := (α.hom.as.app b).toNatTrans.app k
        inv := (α.inv.as.app b).toNatTrans.app k
        hom_inv_id := congrArg (fun m ↦ (m.as.app b).toNatTrans.app k) α.hom_inv_id
        inv_hom_id := congrArg (fun m ↦ (m.as.app b).toNatTrans.app k) α.inv_hom_id }
      { hom := (β.hom.as.app b).toNatTrans.app k
        inv := (β.inv.as.app b).toNatTrans.app k
        hom_inv_id := congrArg (fun m ↦ (m.as.app b).toNatTrans.app k) β.hom_inv_id
        inv_hom_id := congrArg (fun m ↦ (m.as.app b).toNatTrans.app k) β.inv_hom_id } (w b k))
    fun u ↦ ((homMk f g α.hom β.hom w).as.app b).toNatTrans.naturality u))
    fun φ ↦ (homMk f g α.hom β.hom w).as.naturality φ

@[simp]
lemma isoMk_hom (α : l₁ ≫ fst f g ≅ l₂ ≫ fst f g) (β : l₁ ≫ snd f g ≅ l₂ ≫ snd f g) (w) :
    (isoMk f g α β w).hom = homMk f g α.hom β.hom w :=
  (rfl)

end homMk

/-- The fibres of the 2-fibre product of transformations between pseudofunctors with groupoid
fibres are groupoids. -/
instance isGroupoid_obj [∀ b, IsGroupoid (F.obj b)] [∀ b, IsGroupoid (G.obj b)] (b : B) :
    IsGroupoid ((twoFiberProduct f g).obj b) :=
  inferInstanceAs (IsGroupoid ((f.app b).toFunctor ⊡ (g.app b).toFunctor))

/-- The second projection of a 2-fibre product along a fibrewise equivalence `f` is a fibrewise
equivalence: equivalences are stable under 2-base change. -/
instance isEquivalence_snd_app [∀ b, (f.app b).toFunctor.IsEquivalence] (b : B) :
    ((snd f g).app b).toFunctor.IsEquivalence :=
  inferInstanceAs (π₂ (f.app b).toFunctor (g.app b).toFunctor).IsEquivalence

end twoFiberProduct

end StrongTrans

end Pseudofunctor

end CategoryTheory
