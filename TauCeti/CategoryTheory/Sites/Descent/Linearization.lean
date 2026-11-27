/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Linearized objects of a pseudofunctor

Let `C` be a cartesian monoidal category, `G` a monoid object of `C` acting on an object `X` by
`γ : G ⊗ X ⟶ X`, and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` a pseudofunctor, thought of as a fibred
category with pullback functors `f^*`. A `G`-linearization of an object `M` of `F` over `X` is an
isomorphism `φ : γ^* M ≅ pr₂^* M` over `G ⊗ X` satisfying the cocycle condition
`(μ × 1)^* φ = pr₂₃^* φ ∘ (1 × γ)^* φ` over `G ⊗ G ⊗ X` and the unit condition `(η × 1)^* φ = 1`
over `X` (Mumford–Fogarty–Kirwan, Definition 1.6). For `C` the category of schemes over a base
`S`, a group scheme `G` and `F` the pseudofunctor of modules, these are the `G`-linearized, or
`G`-equivariant, modules on `X`; the isomorphism classes of linearized line bundles form the
equivariant Picard group of `X`.

The pullbacks are written with Mathlib's `Pseudofunctor.LocallyDiscreteOpToCat.pullHom`, which
pulls back a morphism `f₁^* M ⟶ f₂^* M` along `g` and identifies the result with a morphism
`gf₁^* M ⟶ gf₂^* M` for chosen factorizations `g ≫ f₁ = gf₁` and `g ≫ f₂ = gf₂`.

Restricting `φ` along a point `(g, x) : Y ⟶ G ⊗ X` gives the linearization at that point,
`LinearizedObject.hom D g x gx h : gx^* M ⟶ x^* M` where `h : g • x = gx`. The cocycle and unit
conditions become multiplicativity `φ(g₁, g₂ • x) ≫ φ(g₂, x) = φ(g₁ * g₂, x)`
(`LinearizedObject.hom_comp`) and `φ(1, x) = 1` (`LinearizedObject.hom_one`), and conversely such
a compatible family of morphisms whose member at the universal point `(pr₁, pr₂)` is an isomorphism
defines a linearization (`LinearizedObject.mk'`); invertibility is automatic when `G` is a group,
but not for a general monoid. This pointwise description gives the two basic constructions:

* `LinearizedObject.ofObj`: an object `M` pulled back from the terminal object along
  `t : X ⟶ 𝟙_ C` carries the trivial linearization, since `γ ≫ t = pr₂ ≫ t`; this is the functor
  `Pseudofunctor.toLinearizedObject`, and `LinearizedObject.ofObj_comm_iff` says which morphisms
  between such objects respect the linearizations;
* `LinearizedObject.pull`: the pullback along a `G`-equivariant morphism `f : X ⟶ Z`, with
  linearization at `(g, x)` that of the object over `Z` at `(g, x ≫ f)`; this is the functor
  `LinearizedObject.pullFunctor`.

Linearized objects form a category (`Pseudofunctor.LinearizedObject.Hom`), whose morphisms are the
morphisms of underlying objects compatible with the linearizations, with a faithful and
conservative forgetful functor `LinearizedObject.forget`.

The pointwise API follows Mathlib's descent data `Pseudofunctor.DescentData` of Joël Riou and
Christian Merten, of which linearizations are the analogue for the action groupoid of `G` on `X`.

## References

* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, 3rd ed., Chapter 1, §3,
  Definition 1.6.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Equivariant quasi-coherent sheaves*.
-/

public noncomputable section

universe v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory MonoidalCategory CartesianMonoidalCategory MonObj LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (G : C) [MonObj G] (X : C) [ModObj G X]

/-- A `G`-linearized object of `F` over `X`: an object `M` of `F` over `X` with an isomorphism
`φ : γ^* M ≅ pr₂^* M` over `G ⊗ X` satisfying the cocycle condition over `G ⊗ G ⊗ X` and the unit
condition over `X`. -/
structure LinearizedObject where
  /-- The underlying object of `F` over `X`. -/
  obj : F.obj (.mk (op X))
  /-- The linearization `γ^* M ≅ pr₂^* M` over `G ⊗ X`. -/
  iso : (F.map γ[G,X].op.toLoc).toFunctor.obj obj ≅ (F.map (snd G X).op.toLoc).toFunctor.obj obj
  /-- The cocycle condition: over `G ⊗ G ⊗ X`, the pullback of `φ` along `μ × 1` is the
  composite of its pullbacks along `1 × γ` and `pr₂₃`. -/
  cocycle :
    pullHom iso.hom (G ◁ γ[G,X]) (G ◁ γ[G,X] ≫ γ[G,X]) (snd G (G ⊗ X) ≫ γ[G,X]) rfl
        (whiskerLeft_snd _ _) ≫
      pullHom iso.hom (snd G (G ⊗ X)) (snd G (G ⊗ X) ≫ γ[G,X]) (snd G (G ⊗ X) ≫ snd G X)
        rfl rfl =
    pullHom iso.hom ((α_ G G X).inv ≫ μ ▷ X) (G ◁ γ[G,X] ≫ γ[G,X])
        (snd G (G ⊗ X) ≫ snd G X) (by rw [Category.assoc, ModObj.mul_smul_self_flip])
        (by simp)
  /-- The unit condition: the pullback of `φ` along `η × 1 : X ⟶ G ⊗ X` is the identity. -/
  unit : pullHom iso.hom ((λ_ X).inv ≫ η[G] ▷ X) (𝟙 X) (𝟙 X) (by simp) (by simp) = 𝟙 _

namespace LinearizedObject

variable {F G X}

section Points

variable (D : F.LinearizedObject G X)

/-- The linearization at a point `(g, x) : Y ⟶ G ⊗ X`: the pullback of `φ` along `(g, x)`, a
morphism `gx^* M ⟶ x^* M` for `gx = g • x`. -/
def hom ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X) (h : g • x = gx) :
    (F.map gx.op.toLoc).toFunctor.obj D.obj ⟶ (F.map x.op.toLoc).toFunctor.obj D.obj :=
  pullHom D.iso.hom (lift g x) gx x ((CategoryTheory.Hom.smul_def _ g x).symm.trans h)
    (lift_snd g x)

/-- The linearization at the universal point `(pr₁, pr₂)` is `φ` itself. -/
@[simp]
lemma hom_fst_snd :
    D.hom (fst G X) (snd G X) γ[G,X] (by simp [CategoryTheory.Hom.smul_def]) =
      D.iso.hom := by
  simp [hom]

instance ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X) (h : g • x = gx) : IsIso (D.hom g x gx h) := by
  unfold hom
  infer_instance

/-- The linearizations at points are compatible with pullback. -/
lemma pullHom_hom ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X) (h : g • x = gx) ⦃Y' : C⦄ (f : Y' ⟶ Y)
    (fg : Y' ⟶ G) (fx fgx : Y' ⟶ X) (hg : f ≫ g = fg) (hx : f ≫ x = fx) (hgx : f ≫ gx = fgx) :
    pullHom (D.hom g x gx h) f fgx fx hgx hx =
      D.hom fg fx fgx (by rw [← hg, ← hx, ← hgx, ← h, ModObj.comp_smul]) := by
  subst hg hx hgx
  simp only [hom, pullHom_pullHom]
  congr 1
  simp

/-- The linearization at a point `(1, x)` is the identity. -/
@[simp]
lemma hom_one ⦃Y : C⦄ (x : Y ⟶ X) : D.hom 1 x x (one_smul _ x) = 𝟙 _ := by
  have h : lift (1 : Y ⟶ G) x = x ≫ (λ_ X).inv ≫ η[G] ▷ X := by
    ext <;> simp [CategoryTheory.Hom.one_def]
  have := congrArg (fun φ ↦ pullHom φ x x x) D.unit
  simp only [pullHom_pullHom, pullHom_id_self] at this
  rw [← this]
  simp only [hom, h]

/-- The linearizations at points are multiplicative: `φ(g₁, g₂ • x) ≫ φ(g₂, x) = φ(g₁ * g₂, x)`. -/
@[reassoc (attr := simp)]
lemma hom_comp ⦃Y : C⦄ (g₁ g₂ : Y ⟶ G) (x₁ x₂ x₃ : Y ⟶ X) (h₁ : g₁ • x₂ = x₁)
    (h₂ : g₂ • x₃ = x₂) :
    D.hom g₁ x₂ x₁ h₁ ≫ D.hom g₂ x₃ x₂ h₂ = D.hom (g₁ * g₂) x₃ x₁ (by rw [mul_smul, h₂, h₁]) := by
  have p₁ : lift g₁ (lift g₂ x₃) ≫ G ◁ γ[G,X] ≫ γ[G,X] = x₁ := by
    subst h₁ h₂; simp [CategoryTheory.Hom.smul_def]
  have p₂ : lift g₁ (lift g₂ x₃) ≫ snd G (G ⊗ X) ≫ γ[G,X] = x₂ := by
    subst h₂; simp [CategoryTheory.Hom.smul_def]
  have p₃ : lift g₁ (lift g₂ x₃) ≫ snd G (G ⊗ X) ≫ snd G X = x₃ := by simp
  have := congrArg (fun φ ↦ pullHom φ (lift g₁ (lift g₂ x₃)) x₁ x₃ p₁ p₃) D.cocycle
  rw [pullHom_comp _ _ _ x₁ x₂ x₃ p₁ p₂ p₃] at this
  simp only [pullHom_pullHom] at this
  convert this using 2
  · simp only [hom]
    congr 1
    subst h₂
    simp [CategoryTheory.Hom.smul_def]
  · simp only [hom]
    congr 1
    simp
  · simp only [hom]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [CategoryTheory.Hom.mul_def]

end Points

section Category

/-- A morphism of linearized objects: a morphism of the underlying objects compatible with the
linearizations. -/
@[ext]
structure Hom (D₁ D₂ : F.LinearizedObject G X) where
  /-- The underlying morphism. -/
  hom : D₁.obj ⟶ D₂.obj
  /-- The compatibility with the linearizations. -/
  comm : (F.map γ[G,X].op.toLoc).toFunctor.map hom ≫ D₂.iso.hom =
      D₁.iso.hom ≫ (F.map (snd G X).op.toLoc).toFunctor.map hom := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (F.LinearizedObject G X) where
  Hom := Hom
  id D := { hom := 𝟙 _ }
  comp φ ψ :=
    { hom := φ.hom ≫ ψ.hom
      comm := by simp only [Functor.map_comp, Category.assoc, Hom.comm, Hom.comm_assoc] }
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

@[ext]
lemma hom_ext {D₁ D₂ : F.LinearizedObject G X} {φ ψ : D₁ ⟶ D₂} (h : φ.hom = ψ.hom) : φ = ψ :=
  Hom.ext h

@[simp]
lemma id_hom (D : F.LinearizedObject G X) : Hom.hom (𝟙 D) = 𝟙 D.obj := rfl

@[simp, reassoc]
lemma comp_hom {D₁ D₂ D₃ : F.LinearizedObject G X} (φ : D₁ ⟶ D₂) (ψ : D₂ ⟶ D₃) :
    (φ ≫ ψ).hom = φ.hom ≫ ψ.hom := rfl

/-- A morphism of linearized objects commutes with the linearizations at every point. -/
@[reassoc]
lemma Hom.comm_hom {D₁ D₂ : F.LinearizedObject G X} (φ : D₁ ⟶ D₂) ⦃Y : C⦄ (g : Y ⟶ G)
    (x gx : Y ⟶ X) (h : g • x = gx) :
    (F.map gx.op.toLoc).toFunctor.map φ.hom ≫ D₂.hom g x gx h =
      D₁.hom g x gx h ≫ (F.map x.op.toLoc).toFunctor.map φ.hom := by
  have := congrArg (fun ψ ↦ pullHom ψ (lift g x) gx x
    ((CategoryTheory.Hom.smul_def _ g x).symm.trans h) (lift_snd g x)) φ.comm
  rwa [pullHom_comp, pullHom_comp, pullHom_map, pullHom_map] at this

/-- An isomorphism of linearized objects, from an isomorphism of the underlying objects compatible
with the linearizations. Exposed so that its `simps` lemmas are definitional. -/
@[expose, simps]
def isoMk {D₁ D₂ : F.LinearizedObject G X} (e : D₁.obj ≅ D₂.obj)
    (comm : (F.map γ[G,X].op.toLoc).toFunctor.map e.hom ≫ D₂.iso.hom =
      D₁.iso.hom ≫ (F.map (snd G X).op.toLoc).toFunctor.map e.hom) : D₁ ≅ D₂ where
  hom := { hom := e.hom }
  inv :=
    { hom := e.inv
      comm := by
        rw [← cancel_mono ((F.map (snd G X).op.toLoc).toFunctor.map e.hom), Category.assoc,
          Category.assoc, Iso.inv_hom_id_map, Category.comp_id,
          ← cancel_epi ((F.map γ[G,X].op.toLoc).toFunctor.map e.hom),
          Iso.hom_inv_id_map_assoc, comm] }

variable (F G X) in
/-- The forgetful functor from linearized objects to objects of `F` over `X`. Exposed so that its
`simps` lemmas are definitional. -/
@[expose, simps]
def forget : F.LinearizedObject G X ⥤ F.obj (.mk (op X)) where
  obj D := D.obj
  map φ := φ.hom

instance : (forget F G X).Faithful where
  map_injective h := hom_ext h

instance : (forget F G X).ReflectsIsomorphisms where
  reflects φ (_ : IsIso φ.hom) :=
    (isoMk (asIso φ.hom) φ.comm).isIso_hom

end Category

section Mk

variable (obj : F.obj (.mk (op X)))
  (φ : ∀ ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X), g • x = gx →
    ((F.map gx.op.toLoc).toFunctor.obj obj ⟶ (F.map x.op.toLoc).toFunctor.obj obj))
  (hφ : IsIso (φ (fst G X) (snd G X) γ[G,X] (by simp [CategoryTheory.Hom.smul_def])))
  (pullHom_φ : ∀ ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X) (h : g • x = gx) ⦃Y' : C⦄ (f : Y' ⟶ Y)
    (fg : Y' ⟶ G) (fx fgx : Y' ⟶ X) (hg : f ≫ g = fg) (hx : f ≫ x = fx) (hgx : f ≫ gx = fgx),
    pullHom (φ g x gx h) f fgx fx hgx hx =
      φ fg fx fgx (by rw [← hg, ← hx, ← hgx, ← h, ModObj.comp_smul]))
  (φ_one : ∀ ⦃Y : C⦄ (x : Y ⟶ X), φ 1 x x (one_smul _ x) = 𝟙 _)
  (φ_comp : ∀ ⦃Y : C⦄ (g₁ g₂ : Y ⟶ G) (x₁ x₂ x₃ : Y ⟶ X) (h₁ : g₁ • x₂ = x₁)
    (h₂ : g₂ • x₃ = x₂),
    φ g₁ x₂ x₁ h₁ ≫ φ g₂ x₃ x₂ h₂ = φ (g₁ * g₂) x₃ x₁ (by rw [mul_smul, h₂, h₁]))

/-- A linearized object from a family of morphisms `(g • x)^* M ⟶ x^* M` indexed by all points
`(g, x)` of `G ⊗ X`, compatible with pullback, trivial at `g = 1` and multiplicative in `g`, whose
member at the universal point `(pr₁, pr₂)` is an isomorphism (`hφ`). For a monoid `G` this last
condition does not follow from the others. -/
abbrev mk' : F.LinearizedObject G X where
  obj := obj
  iso := asIso (φ (fst G X) (snd G X) γ[G,X] (by simp [CategoryTheory.Hom.smul_def]))
  cocycle := by
    simp only [asIso_hom]
    rw [pullHom_φ (fg := fst G (G ⊗ X)) (hg := by simp),
      pullHom_φ (fg := snd G (G ⊗ X) ≫ fst G X) (hg := rfl),
      pullHom_φ (fg := fst G (G ⊗ X) * (snd G (G ⊗ X) ≫ fst G X))
        (hg := by
          rw [CategoryTheory.Hom.mul_def, Category.assoc, whiskerRight_fst, ← Category.assoc]
          congr 1
          apply CartesianMonoidalCategory.hom_ext <;> simp),
      φ_comp]
  unit := by
    simp only [asIso_hom]
    rw [pullHom_φ (fg := 1) (hg := by simp [CategoryTheory.Hom.one_def]), φ_one]

@[simp]
lemma mk'_obj : (mk' obj φ hφ pullHom_φ φ_one φ_comp).obj = obj := rfl

@[simp]
lemma mk'_iso_hom : (mk' obj φ hφ pullHom_φ φ_one φ_comp).iso.hom =
    φ (fst G X) (snd G X) γ[G,X] (by simp [CategoryTheory.Hom.smul_def]) := rfl

/-- The linearization of `mk'` at points is the given family. -/
@[simp]
lemma mk'_hom ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X) (h : g • x = gx) :
    (mk' obj φ hφ pullHom_φ φ_one φ_comp).hom g x gx h = φ g x gx h := by
  exact pullHom_φ (fst G X) (snd G X) γ[G,X] _ (lift g x) g x gx (lift_fst g x) (lift_snd g x)
    ((CategoryTheory.Hom.smul_def _ g x).symm.trans h)

end Mk

end LinearizedObject

section Base

open LinearizedObject

/-- The linearized object `t^* M`, for `t : X ⟶ 𝟙_ C` and an object `M` of `F` over the terminal
object, with the linearization given by the comparison isomorphisms of `F`: both `γ ≫ t` and
`pr₂ ≫ t` are the morphism `G ⊗ X ⟶ 𝟙_ C`. Exposed because the statement of
`LinearizedObject.ofObj_hom` needs its underlying object to reduce to `t^* M`. -/
@[expose]
def LinearizedObject.ofObj (M : F.obj (.mk (op (𝟙_ C)))) : F.LinearizedObject G X :=
  mk' ((F.map (toUnit X).op.toLoc).toFunctor.obj M)
    (fun Y _ x gx _ ↦
      (F.mapComp' (toUnit X).op.toLoc gx.op.toLoc (toUnit Y).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, comp_toUnit])).inv.toNatTrans.app M ≫
        (F.mapComp' (toUnit X).op.toLoc x.op.toLoc (toUnit Y).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, comp_toUnit])).hom.toNatTrans.app M)
    inferInstance
    (fun Y _ x gx _ Y' f _ fx fgx _ hx hgx ↦ by
      rw [pullHom_comp _ _ f fgx (toUnit Y') fx hgx (comp_toUnit _) hx,
        pullHom_mapComp'_inv (hk := comp_toUnit _), pullHom_mapComp'_hom (hk := comp_toUnit _)])
    (fun Y x ↦ by simp)
    (fun Y _ _ _ _ _ _ _ ↦ by simp)

/-- The underlying object of `LinearizedObject.ofObj F G X M` is `t^* M`. -/
@[simp]
lemma LinearizedObject.ofObj_obj (M : F.obj (.mk (op (𝟙_ C)))) :
    (ofObj F G X M).obj = (F.map (toUnit X).op.toLoc).toFunctor.obj M := rfl

/-- The trivial linearization at `(g, x)` is the composite of the comparison isomorphisms
`(g • x)^* t^* M ≅ t^* M ≅ x^* t^* M` of `F`. -/
lemma LinearizedObject.ofObj_hom (M : F.obj (.mk (op (𝟙_ C)))) ⦃Y : C⦄ (g : Y ⟶ G)
    (x gx : Y ⟶ X) (h : g • x = gx) :
    (ofObj F G X M).hom g x gx h =
      (F.mapComp' (toUnit X).op.toLoc gx.op.toLoc (toUnit Y).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, comp_toUnit])).inv.toNatTrans.app M ≫
        (F.mapComp' (toUnit X).op.toLoc x.op.toLoc (toUnit Y).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, comp_toUnit])).hom.toNatTrans.app M := by
  unfold ofObj
  exact mk'_hom _ _ _ _ _ _ _ _ _ _

/-- Pulling back objects of `F` from the terminal object to `X`, with their trivial
linearizations. Exposed so that its `simps` lemmas are definitional. -/
@[expose, simps]
def toLinearizedObject : F.obj (.mk (op (𝟙_ C))) ⥤ F.LinearizedObject G X where
  obj M := .ofObj F G X M
  map {M M'} f :=
    { hom := (F.map (toUnit X).op.toLoc).toFunctor.map f
      comm := by simp [ofObj] }

/-- A morphism `α : t^* M ⟶ t^* M'` between pulled back objects is compatible with their trivial
linearizations exactly when its two pullbacks along `γ` and `pr₂` to `G ⊗ X` agree. -/
lemma LinearizedObject.ofObj_comm_iff {M M' : F.obj (.mk (op (𝟙_ C)))}
    (α : (F.map (toUnit X).op.toLoc).toFunctor.obj M ⟶
      (F.map (toUnit X).op.toLoc).toFunctor.obj M') :
    (F.map γ[G,X].op.toLoc).toFunctor.map α ≫ (ofObj F G X M').iso.hom =
        (ofObj F G X M).iso.hom ≫ (F.map (snd G X).op.toLoc).toFunctor.map α ↔
      pullHom α γ[G,X] (toUnit (G ⊗ X)) (toUnit (G ⊗ X)) (comp_toUnit _) (comp_toUnit _) =
        pullHom α (snd G X) (toUnit (G ⊗ X)) (toUnit (G ⊗ X)) (comp_toUnit _) (comp_toUnit _) := by
  unfold ofObj
  rw [mk'_iso_hom, mk'_iso_hom, pullHom, pullHom, ← cancel_epi
    ((F.mapComp' (toUnit X).op.toLoc γ[G,X].op.toLoc (toUnit (G ⊗ X)).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, comp_toUnit]; rfl)).hom.toNatTrans.app M),
    ← cancel_mono ((F.mapComp' (toUnit X).op.toLoc (snd G X).op.toLoc (toUnit (G ⊗ X)).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, comp_toUnit])).inv.toNatTrans.app M')]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category.comp_id]

end Base

section Pull

open LinearizedObject

variable {F G X} {Z : C} [ModObj G Z] (f : X ⟶ Z) [IsModHom G f]

/-- The pullback `f^* M` of a linearized object `M` along a `G`-equivariant morphism `f`, with the
linearization at `(g, x)` given by that of `M` at `(g, x ≫ f)`. Exposed because the statement of
`LinearizedObject.pull_hom` needs its underlying object to reduce to `f^* M`. -/
@[expose]
def LinearizedObject.pull (D : F.LinearizedObject G Z) : F.LinearizedObject G X :=
  mk' ((F.map f.op.toLoc).toFunctor.obj D.obj)
    (fun Y g x gx h ↦
      (F.mapComp' f.op.toLoc gx.op.toLoc (gx ≫ f).op.toLoc (by simp)).inv.toNatTrans.app D.obj ≫
        D.hom g (x ≫ f) (gx ≫ f) (by rw [← h, IsModHom.map_smul]) ≫
        (F.mapComp' f.op.toLoc x.op.toLoc (x ≫ f).op.toLoc (by simp)).hom.toNatTrans.app D.obj)
    inferInstance
    (fun Y g x gx h Y' k kg kx kgx hg hx hgx ↦ by
      rw [pullHom_comp _ _ k kgx (kgx ≫ f) kx hgx (by rw [← hgx, Category.assoc]) hx,
        pullHom_comp _ _ k (kgx ≫ f) (kx ≫ f) kx (by rw [← hgx, Category.assoc])
          (by rw [← hx, Category.assoc]) hx,
        pullHom_mapComp'_inv (hk := rfl), pullHom_mapComp'_hom (hk := rfl),
        D.pullHom_hom _ _ _ _ _ kg _ _ hg (by rw [← hx, Category.assoc])
          (by rw [← hgx, Category.assoc])])
    (fun Y x ↦ by simp [D.hom_one])
    (fun Y g₁ g₂ x₁ x₂ x₃ h₁ h₂ ↦ by
      simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, D.hom_comp_assoc])

/-- The underlying object of the pullback along `f` is the pullback along `f`. -/
@[simp]
lemma LinearizedObject.pull_obj (D : F.LinearizedObject G Z) :
    (D.pull f).obj = (F.map f.op.toLoc).toFunctor.obj D.obj := rfl

/-- The linearization of the pullback along `f` at `(g, x)` is that of `M` at `(g, x ≫ f)`,
read through the comparison isomorphisms of `F`. -/
lemma LinearizedObject.pull_hom (D : F.LinearizedObject G Z) ⦃Y : C⦄ (g : Y ⟶ G) (x gx : Y ⟶ X)
    (h : g • x = gx) :
    (D.pull f).hom g x gx h =
      (F.mapComp' f.op.toLoc gx.op.toLoc (gx ≫ f).op.toLoc (by simp)).inv.toNatTrans.app D.obj ≫
        D.hom g (x ≫ f) (gx ≫ f) (by rw [← h, IsModHom.map_smul]) ≫
        (F.mapComp' f.op.toLoc x.op.toLoc (x ≫ f).op.toLoc (by simp)).hom.toNatTrans.app D.obj := by
  unfold pull
  exact mk'_hom _ _ _ _ _ _ _ _ _ _

variable (F G) in
/-- Pullback of linearized objects along a `G`-equivariant morphism. Exposed so that its `simps`
lemmas are definitional. -/
@[expose, simps]
def LinearizedObject.pullFunctor : F.LinearizedObject G Z ⥤ F.LinearizedObject G X where
  obj D := D.pull f
  map {D₁ D₂} φ :=
    { hom := (F.map f.op.toLoc).toFunctor.map φ.hom
      comm := by
        rw [← hom_fst_snd, ← hom_fst_snd, pull_hom, pull_hom]
        dsimp only [pull_obj]
        rw [mapComp'_inv_naturality_assoc,
          Hom.comm_hom_assoc, Category.assoc, Category.assoc, mapComp'_hom_naturality] }
  map_id _ := hom_ext (Functor.map_id _ _)
  map_comp _ _ := hom_ext (Functor.map_comp _ _ _)

end Pull

end CategoryTheory.Pseudofunctor
