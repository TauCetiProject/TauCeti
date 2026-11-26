/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct

/-!
# Groupoid objects in sheaves of sets

A groupoid object in the category of `J`-sheaves of sets on a site `(C, J)` consists of a sheaf of
objects `X`, a sheaf of arrows `R`, source and target morphisms `s t : R ⟶ X`, identities
`e : X ⟶ R`, a composition `c : R ×_{t, X, s} R ⟶ R` and inverses `i : R ⟶ R`, such that for
every object `U` the sections `(X(U), R(U))` form a groupoid (Stacks, Definition 39.13.1 (0231),
there for schemes). The sections of the fibre product `R ×_{t, X, s} R` over `U` are the pairs of
sections `(f, g)` of `R` over `U` with `t f = s g`, so a morphism of sheaves out of it is a family
of maps on such pairs which commutes with restriction; the composition is stated in this form.
The arrow `f` goes from `s f` to `t f`, and `c f g` is the composite of `f` followed by `g`.

The groupoid of sections over `U` is `GroupoidObject.Fiber G U`, with objects the sections of `X`
over `U` and morphisms `x ⟶ y` the sections `r` of `R` over `U` with `s r = x` and `t r = y`.
These fibres are the fibres of the prestack of `G`
(`TauCeti.CategoryTheory.GroupoidObject.toPseudofunctor`, in
`TauCeti.CategoryTheory.Sites.Descent.GroupoidPrestack`), whose stackification is the quotient
stack `[X/R]`.

The basic example is the action groupoid `MulActionSheaf.actionGroupoid` of a sheaf of groups `G`
acting on a sheaf of sets `X`: its sheaf of arrows is `G × X`, with `(g, x)` an arrow from `x`
to `g • x` (Stacks, Section 39.15 (0234), there for group schemes).

## Main declarations

* `TauCeti.CategoryTheory.GroupoidObject J`: groupoid objects in `J`-sheaves of sets.
* `TauCeti.CategoryTheory.GroupoidObject.Fiber G U`: the groupoid of sections of `G` over `U`,
  with `Fiber.Hom.arr` the underlying section of `R` of a morphism.
* `CategoryTheory.Sheaf.MulActionSheaf.actionGroupoid X`: the action groupoid of a sheaf of sets
  with an action of a sheaf of groups, with `actionGroupoid.homEquiv` identifying its morphisms
  `x ⟶ y` over `U` with the sections `g` of the group with `g • x = y`.

## References

* [Stacks Project, Definition 39.13.1](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Section 39.15](https://stacks.math.columbia.edu/tag/0234)
-/

public section

universe w' w v u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A groupoid object `(X, R, s, t, e, c, i)` in the category of `J`-sheaves of sets: sheaves `X`
of objects and `R` of arrows, the source and target `s t : R ⟶ X`, the identities `e : X ⟶ R`,
the inverses `i : R ⟶ R` and the composition `c`, defined on the sections `(f, g)` of the fibre
product `R ×_{t, X, s} R` and commuting with restriction, such that the sections over every
object form a groupoid in which `f` is an arrow from `s f` to `t f` and `c f g` is `f` followed
by `g` (Stacks, Definition 39.13.1 (0231)). -/
@[stacks 0231]
structure GroupoidObject (J : GrothendieckTopology C) where
  /-- The sheaf of objects. -/
  X : Sheaf J (Type w)
  /-- The sheaf of arrows. -/
  R : Sheaf J (Type w)
  /-- The source of an arrow. -/
  s : R ⟶ X
  /-- The target of an arrow. -/
  t : R ⟶ X
  /-- The identity arrow of an object. -/
  e : X ⟶ R
  /-- The inverse of an arrow. -/
  i : R ⟶ R
  /-- The composite of an arrow `f` followed by an arrow `g` whose source is the target of `f`. -/
  c ⦃U : Cᵒᵖ⦄ (f g : R.obj.obj U) (h : t.hom.app U f = s.hom.app U g) : R.obj.obj U
  /-- Composition commutes with restriction. -/
  map_c ⦃U V : Cᵒᵖ⦄ (φ : U ⟶ V) (f g : R.obj.obj U) (h : t.hom.app U f = s.hom.app U g) :
    R.obj.map φ (c f g h) = c (R.obj.map φ f) (R.obj.map φ g) (by
      simp only [NatTrans.naturality_apply, h])
  /-- The identity of `x` is an arrow from `x`. -/
  s_e ⦃U : Cᵒᵖ⦄ (x : X.obj.obj U) : s.hom.app U (e.hom.app U x) = x
  /-- The identity of `x` is an arrow to `x`. -/
  t_e ⦃U : Cᵒᵖ⦄ (x : X.obj.obj U) : t.hom.app U (e.hom.app U x) = x
  /-- The source of a composite is the source of its first arrow. -/
  s_c ⦃U : Cᵒᵖ⦄ (f g : R.obj.obj U) (h : t.hom.app U f = s.hom.app U g) :
    s.hom.app U (c f g h) = s.hom.app U f
  /-- The target of a composite is the target of its second arrow. -/
  t_c ⦃U : Cᵒᵖ⦄ (f g : R.obj.obj U) (h : t.hom.app U f = s.hom.app U g) :
    t.hom.app U (c f g h) = t.hom.app U g
  /-- The identity of the source of `f` followed by `f` is `f`. -/
  e_c ⦃U : Cᵒᵖ⦄ (f : R.obj.obj U) : c (e.hom.app U (s.hom.app U f)) f (t_e _) = f
  /-- `f` followed by the identity of the target of `f` is `f`. -/
  c_e ⦃U : Cᵒᵖ⦄ (f : R.obj.obj U) : c f (e.hom.app U (t.hom.app U f)) (s_e _).symm = f
  /-- Composition is associative. -/
  c_assoc ⦃U : Cᵒᵖ⦄ (f g k : R.obj.obj U) (h₁ : t.hom.app U f = s.hom.app U g)
    (h₂ : t.hom.app U g = s.hom.app U k) :
    c (c f g h₁) k ((t_c f g h₁).trans h₂) = c f (c g k h₂) (h₁.trans (s_c g k h₂).symm)
  /-- The inverse of `f` is an arrow from the target of `f`. -/
  s_i ⦃U : Cᵒᵖ⦄ (f : R.obj.obj U) : s.hom.app U (i.hom.app U f) = t.hom.app U f
  /-- The inverse of `f` is an arrow to the source of `f`. -/
  t_i ⦃U : Cᵒᵖ⦄ (f : R.obj.obj U) : t.hom.app U (i.hom.app U f) = s.hom.app U f
  /-- `f` followed by its inverse is the identity of the source of `f`. -/
  c_i ⦃U : Cᵒᵖ⦄ (f : R.obj.obj U) : c f (i.hom.app U f) (s_i f).symm = e.hom.app U (s.hom.app U f)
  /-- The inverse of `f` followed by `f` is the identity of the target of `f`. -/
  i_c ⦃U : Cᵒᵖ⦄ (f : R.obj.obj U) : c (i.hom.app U f) f (t_i f) = e.hom.app U (t.hom.app U f)

namespace GroupoidObject

attribute [simp] s_e t_e s_c t_c s_i t_i c_i i_c

variable {J : GrothendieckTopology C} (G : GroupoidObject.{w} J)

/-- The identity of any object followed by an arrow `f` is `f`. -/
@[simp]
lemma c_e_left {U : Cᵒᵖ} (x : G.X.obj.obj U) (f : G.R.obj.obj U)
    (h : G.t.hom.app U (G.e.hom.app U x) = G.s.hom.app U f) : G.c (G.e.hom.app U x) f h = f := by
  obtain rfl : x = G.s.hom.app U f := (G.t_e x).symm.trans h
  exact G.e_c f

/-- An arrow `f` followed by the identity of any object is `f`. -/
@[simp]
lemma c_e_right {U : Cᵒᵖ} (f : G.R.obj.obj U) (y : G.X.obj.obj U)
    (h : G.t.hom.app U f = G.s.hom.app U (G.e.hom.app U y)) : G.c f (G.e.hom.app U y) h = f := by
  obtain rfl : y = G.t.hom.app U f := (G.s_e y).symm.trans h.symm
  exact G.c_e f

/-- The objects of the groupoid of sections of `G` over `U`: the sections of the sheaf of objects
over `U`, lifted to the universe `max w w'` so that the groupoids can be the fibres of a
pseudofunctor with values in a larger universe of objects. -/
@[ext]
structure Fiber (U : Cᵒᵖ) : Type max w w' where
  /-- The section of the sheaf of objects underlying an object of the groupoid of sections. -/
  as : G.X.obj.obj U

variable {G}

/-- A morphism `x ⟶ y` of the groupoid of sections of `G` over `U`: a section of the sheaf of
arrows over `U` from `x` to `y`. -/
@[ext]
structure Fiber.Hom {U : Cᵒᵖ} (x y : Fiber.{w'} G U) : Type w where
  /-- The section of the sheaf of arrows underlying a morphism. -/
  arr : G.R.obj.obj U
  /-- The source of the underlying arrow. -/
  s_arr : G.s.hom.app U arr = x.as
  /-- The target of the underlying arrow. -/
  t_arr : G.t.hom.app U arr = y.as

attribute [simp] Fiber.Hom.s_arr Fiber.Hom.t_arr

/-- The sections of a groupoid object over `U` form a groupoid: the identity of `x` is `e x`,
the composite of `φ` and `ψ` is `c φ ψ` and the inverse of `φ` is `i φ`. -/
instance (U : Cᵒᵖ) : Groupoid (Fiber.{w'} G U) where
  Hom := Fiber.Hom
  id x := ⟨G.e.hom.app U x.as, G.s_e _, G.t_e _⟩
  comp φ ψ := ⟨G.c φ.arr ψ.arr (φ.t_arr.trans ψ.s_arr.symm), (G.s_c _ _ _).trans φ.s_arr,
    (G.t_c _ _ _).trans ψ.t_arr⟩
  id_comp _ := Fiber.Hom.ext (G.c_e_left _ _ _)
  comp_id _ := Fiber.Hom.ext (G.c_e_right _ _ _)
  assoc _ _ _ := Fiber.Hom.ext (G.c_assoc _ _ _ _ _)
  inv φ := ⟨G.i.hom.app U φ.arr, (G.s_i _).trans φ.t_arr, (G.t_i _).trans φ.s_arr⟩
  inv_comp φ := Fiber.Hom.ext ((G.i_c φ.arr).trans (congrArg _ φ.t_arr))
  comp_inv φ := Fiber.Hom.ext ((G.c_i φ.arr).trans (congrArg _ φ.s_arr))

namespace Fiber

variable {U : Cᵒᵖ}

/-- Morphisms of the groupoid of sections are determined by their underlying arrows. -/
@[ext]
lemma hom_ext {x y : Fiber.{w'} G U} {φ ψ : x ⟶ y} (h : φ.arr = ψ.arr) : φ = ψ :=
  Fiber.Hom.ext h

/-- The identity of `x` is the identity arrow `e x`. -/
@[simp]
lemma id_arr (x : Fiber.{w'} G U) : Hom.arr (𝟙 x) = G.e.hom.app U x.as :=
  (rfl)

/-- The composite of `φ` and `ψ` is the composite `c φ ψ` of the underlying arrows. -/
@[simp]
lemma comp_arr {x y z : Fiber.{w'} G U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (φ ≫ ψ).arr = G.c φ.arr ψ.arr (φ.t_arr.trans ψ.s_arr.symm) :=
  (rfl)

/-- The inverse of `φ` is the inverse `i φ` of the underlying arrow. -/
@[simp]
lemma inv_arr {x y : Fiber.{w'} G U} (φ : x ⟶ y) : (inv φ).arr = G.i.hom.app U φ.arr := by
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- The morphism `eqToHom h` is the identity arrow of its source. -/
@[simp]
lemma eqToHom_arr {x y : Fiber.{w'} G U} (h : x = y) :
    (eqToHom h).arr = G.e.hom.app U x.as := by
  subst h
  rfl

/-- Morphisms with the same underlying arrow between objects which are equal agree up to the
`eqToHom` identifications of their sources and targets. -/
lemma hom_eq_eqToHom_comp {x y x' y' : Fiber.{w'} G U} (φ : x ⟶ y) (ψ : x' ⟶ y') (hx : x = x')
    (hy : y = y') (h : φ.arr = ψ.arr) : φ = eqToHom hx ≫ ψ ≫ eqToHom hy.symm := by
  subst hx hy
  simpa using hom_ext h

end Fiber

end GroupoidObject

end TauCeti.CategoryTheory

namespace CategoryTheory.Sheaf.MulActionSheaf

open TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Sheaf J GrpCat.{w}}
  (X : MulActionSheaf G)

/-- The action groupoid of a sheaf of sets `X` with an action of a sheaf of groups `G`: the
sheaf of objects is `X`, the sheaf of arrows is `G × X`, an arrow `(g, x)` goes from `x` to
`g • x`, the composite of `(g, x)` followed by `(h, g • x)` is `(h * g, x)`, the identity of `x`
is `(1, x)` and the inverse of `(g, x)` is `(g⁻¹, g • x)` (Stacks, Section 39.15 (0234)).

It is an abbreviation because the sections of the sheaves of objects and of arrows are, by
definition, the sections of `X` and the pairs of sections of `G` and `X`; statements about the
action groupoid apply the action and the group operations to them. -/
@[stacks 0234]
abbrev actionGroupoid : GroupoidObject.{w} J where
  X := X.sheaf
  R := (sheafCompose J (forget GrpCat.{w})).obj G ⊗ X.sheaf
  s := snd _ _
  t := ObjectProperty.homMk
    { app U := ↾fun a : G.obj.obj U × X.sheaf.obj.obj U ↦ a.1 • a.2
      naturality _ _ f := by
        ext a
        exact (X.map_smul f a.1 a.2).symm }
  e := ObjectProperty.homMk
    { app U := ↾fun x : X.sheaf.obj.obj U ↦ ((1 : G.obj.obj U), x)
      naturality _ _ f := by
        ext x
        exact Prod.ext (map_one (G.obj.map f).hom).symm rfl }
  i := ObjectProperty.homMk
    { app U := ↾fun a : G.obj.obj U × X.sheaf.obj.obj U ↦ ((a.1⁻¹ : G.obj.obj U), a.1 • a.2)
      naturality _ _ f := by
        ext a
        exact Prod.ext (map_inv (G.obj.map f).hom (G := G.obj.obj _) a.1).symm
          (X.map_smul f a.1 a.2).symm }
  c U := fun (f g : G.obj.obj U × X.sheaf.obj.obj U) _ ↦ (g.1 * f.1, f.2)
  map_c _ _ φ := fun (f g : G.obj.obj _ × X.sheaf.obj.obj _) _ ↦
    Prod.ext (map_mul (G.obj.map φ).hom g.1 f.1) rfl
  s_e _ _ := rfl
  t_e U x := one_smul (G.obj.obj U) x
  s_c _ _ _ _ := rfl
  t_c U := fun (f g : G.obj.obj U × X.sheaf.obj.obj U) (h : f.1 • f.2 = g.2) ↦
    (mul_smul g.1 f.1 f.2).trans (congrArg (g.1 • ·) h)
  e_c U := fun (f : G.obj.obj U × X.sheaf.obj.obj U) ↦ Prod.ext (mul_one f.1) rfl
  c_e U := fun (f : G.obj.obj U × X.sheaf.obj.obj U) ↦ Prod.ext (one_mul f.1) rfl
  c_assoc U := fun (f g k : G.obj.obj U × X.sheaf.obj.obj U) _ _ ↦
    Prod.ext (mul_assoc k.1 g.1 f.1).symm rfl
  s_i _ _ := rfl
  t_i U := fun (f : G.obj.obj U × X.sheaf.obj.obj U) ↦ inv_smul_smul f.1 f.2
  c_i U := fun (f : G.obj.obj U × X.sheaf.obj.obj U) ↦ Prod.ext (inv_mul_cancel f.1) rfl
  i_c U := fun (f : G.obj.obj U × X.sheaf.obj.obj U) ↦ Prod.ext (mul_inv_cancel f.1) rfl

variable {X}

namespace actionGroupoid

/-- A morphism `x ⟶ y` of the groupoid of sections of the action groupoid over `U` is a section
`g` of the group over `U` with `g • x = y`. -/
def homEquiv {U : Cᵒᵖ} (x y : GroupoidObject.Fiber.{w'} X.actionGroupoid U) :
    (x ⟶ y) ≃ {g : G.obj.obj U // g • x.as = y.as} where
  toFun φ := ⟨_root_.Prod.fst (α := G.obj.obj U) (β := X.sheaf.obj.obj U) φ.arr, by
    obtain ⟨⟨g, z⟩, hs, ht⟩ := φ
    exact hs ▸ ht⟩
  invFun g := ⟨(g.val, x.as), rfl, g.property⟩
  left_inv φ := by
    obtain ⟨⟨g, z⟩, hs, ht⟩ := φ
    obtain rfl : z = x.as := hs
    rfl
  right_inv _ := rfl

/-- The element of the group given by a morphism is the first component of the underlying
arrow. -/
lemma homEquiv_apply_coe {U : Cᵒᵖ} {x y : GroupoidObject.Fiber.{w'} X.actionGroupoid U}
    (φ : x ⟶ y) : (homEquiv x y φ : G.obj.obj U) = φ.arr.1 :=
  (rfl)

/-- The morphism given by a section `g` of the group with `g • x = y` has underlying arrow
`(g, x)`. -/
@[simp]
lemma homEquiv_symm_apply_arr {U : Cᵒᵖ} {x y : GroupoidObject.Fiber.{w'} X.actionGroupoid U}
    (g : {g : G.obj.obj U // g • x.as = y.as}) : ((homEquiv x y).symm g).arr = (g.val, x.as) :=
  (rfl)

/-- The identity of `x` corresponds to the unit of the group. -/
@[simp]
lemma homEquiv_id {U : Cᵒᵖ} (x : GroupoidObject.Fiber.{w'} X.actionGroupoid U) :
    (homEquiv x x (𝟙 x) : G.obj.obj U) = 1 :=
  (rfl)

/-- Composition corresponds to multiplication in the group, in the opposite order. -/
@[simp]
lemma homEquiv_comp {U : Cᵒᵖ} {x y z : GroupoidObject.Fiber.{w'} X.actionGroupoid U}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    (homEquiv x z (φ ≫ ψ) : G.obj.obj U) = homEquiv y z ψ * homEquiv x y φ :=
  (rfl)

/-- Inverses correspond to inverses in the group. -/
@[simp]
lemma homEquiv_inv {U : Cᵒᵖ} {x y : GroupoidObject.Fiber.{w'} X.actionGroupoid U}
    (φ : x ⟶ y) : (homEquiv y x (inv φ) : G.obj.obj U) = (homEquiv x y φ : G.obj.obj U)⁻¹ := by
  rw [homEquiv_apply_coe, GroupoidObject.Fiber.inv_arr]
  rfl

end actionGroupoid

end CategoryTheory.Sheaf.MulActionSheaf
