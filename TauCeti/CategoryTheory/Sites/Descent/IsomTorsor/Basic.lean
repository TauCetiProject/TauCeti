/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import TauCeti.CategoryTheory.Sites.Descent.Banding

/-!
# The torsor of isomorphisms of a banded pseudofunctor

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, and let `x` and
`y` be objects of the fibre of `F` over `U`. The coefficients `A(U)` act on the isomorphisms
`x ≅ y` by postcomposition with the band automorphisms of `y`; since the band automorphisms commute
with every isomorphism, this is also precomposition with the band automorphisms of `x`. The action
is free and transitive: any two isomorphisms `p q : x ≅ y` differ by a unique coefficient, their
difference. Hence the isomorphisms `x ≅ y`, when there is one, form an `A(U)`-torsor, and choosing
one identifies them with `A(U)` (Olsson, Lemma 31.3 and Remark 31.5). The action and the difference
are compatible with pullback along arrows `V ⟶ U`, and the action on morphisms `homAct` is
compatible with Mathlib's restriction maps `pullHom` of the presheaves of morphisms
`Pseudofunctor.presheafHom x y`. The torsor structure is built over each object `U` separately; the
sheaf-level torsor of isomorphisms is in `TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Sheaf`.

## Main declarations

* `CategoryTheory.Pseudofunctor.AbelianBanding.act`: the action of a coefficient on an
  isomorphism.
* `CategoryTheory.Pseudofunctor.AbelianBanding.difference`: the coefficient carrying one
  isomorphism to another.
* `CategoryTheory.Pseudofunctor.AbelianBanding.principalEquiv`: the bijection
  `(x ≅ y) × A(U) ≃ (x ≅ y) × (x ≅ y)`, `(p, a) ↦ (p, p • a)`, which needs no isomorphism to
  exist.
* `CategoryTheory.Pseudofunctor.AbelianBanding.isomTorsor`: the isomorphisms `x ≅ y` form a
  torsor under `A(U)` when they are nonempty.
* `CategoryTheory.Pseudofunctor.AbelianBanding.coordinateEquiv`: the identification of `A(U)` with
  the isomorphisms `x ≅ y` given by a chosen isomorphism.
* `CategoryTheory.Pseudofunctor.AbelianBanding.mapIso_act`,
  `CategoryTheory.Pseudofunctor.AbelianBanding.difference_mapIso`: compatibility with pullback.
* `CategoryTheory.Pseudofunctor.AbelianBanding.pullHom_homAct`: compatibility of the action on
  morphisms with the restriction maps of the presheaves of morphisms.
* `CategoryTheory.Pseudofunctor.AbelianBanding.overMapCompPresheafHomIso_hom_app_homAct`: the
  identification of the restriction of `presheafHom x y` to `Over V` with `presheafHom` of the
  pullbacks of `x` and `y` to `V` respects the actions.
* `CategoryTheory.Pseudofunctor.AbelianBanding.homPrincipalEquiv`: the principal comparison
  `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)` on morphisms of a groupoid fibre.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Lemma 31.3 and Remark 31.5
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)
  {U : C} {x y z : F.obj (.mk (op U))}

section Act

/-- The action of a coefficient `a` of `A(U)` on an isomorphism `p : x ≅ y`: the composite of
`p` with the band automorphism of `a` at `y`. -/
def act (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) : x ≅ y :=
  p ≪≫ (b.mulEquiv U y a).asIso

@[simp]
lemma act_hom (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    (b.act p a).hom = p.hom ≫ (b.mulEquiv U y a).asIso.hom :=
  (rfl)

/-- The action of `a` on `p` is also the composite of the band automorphism of `a` at `x` with
`p`. -/
lemma act_eq_trans (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.act p a = (b.mulEquiv U x a).asIso ≪≫ p := by
  ext
  simp [b.mulEquiv_hom_comp p]

/-- The action of `a` on the identity of `x` is the band automorphism of `a` at `x`. -/
@[simp]
lemma act_refl (a : Multiplicative (A.obj.obj (op U))) :
    b.act (Iso.refl x) a = (b.mulEquiv U x a).asIso := by
  ext
  simp

@[simp]
lemma act_one (p : x ≅ y) : b.act p 1 = p := by
  ext
  simp

/-- The action is a left action for the composition convention of `Aut`, in which `a * c` is
`c` followed by `a`. -/
lemma act_mul (p : x ≅ y) (a c : Multiplicative (A.obj.obj (op U))) :
    b.act p (a * c) = b.act (b.act p c) a := by
  ext
  simp

/-- The action commutes with postcomposition: acting on `p` and then composing with `q` is acting
on `p ≪≫ q`. -/
@[simp]
lemma act_trans (p : x ≅ y) (q : y ≅ z) (a : Multiplicative (A.obj.obj (op U))) :
    b.act p a ≪≫ q = b.act (p ≪≫ q) a := by
  ext
  simpa using b.mulEquiv_hom_comp q a

/-- The action commutes with precomposition. -/
@[simp]
lemma trans_act (p : x ≅ y) (q : y ≅ z) (a : Multiplicative (A.obj.obj (op U))) :
    p ≪≫ b.act q a = b.act (p ≪≫ q) a := by
  ext
  simp

/-- The inverse of the action of `a` on `p` is the action of `a⁻¹` on the inverse of `p`. -/
@[simp]
lemma act_symm (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    (b.act p a).symm = b.act p.symm a⁻¹ := by
  rw [act_eq_trans, act]
  ext
  simp [← Aut.inv_asIso, ← map_inv]

end Act

section Difference

/-- The difference of two isomorphisms `p q : x ≅ y`: the coefficient whose band automorphism at
`y` is `p⁻¹ ≫ q`. -/
def difference (p q : x ≅ y) : Multiplicative (A.obj.obj (op U)) :=
  (b.mulEquiv U y).symm (.of (p.symm ≪≫ q))

/-- The band automorphism at `y` of the difference of `p` and `q` is `p⁻¹ ≫ q`. -/
@[simp]
lemma mulEquiv_difference (p q : x ≅ y) :
    b.mulEquiv U y (b.difference p q) = .of (p.symm ≪≫ q) := by
  simp [difference]

@[simp]
lemma act_difference (p q : x ≅ y) : b.act p (b.difference p q) = q := by
  ext
  simp

@[simp]
lemma difference_act (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.difference p (b.act p a) = a := by
  apply (b.mulEquiv U y).injective
  ext
  simp

/-- The difference of `p` and `q` is the unique coefficient carrying `p` to `q`. -/
lemma difference_eq_iff (p q : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.difference p q = a ↔ b.act p a = q :=
  ⟨fun h ↦ h ▸ b.act_difference p q, fun h ↦ h ▸ b.difference_act p a⟩

@[simp]
lemma difference_self (p : x ≅ y) : b.difference p p = 1 := by
  rw [difference_eq_iff, act_one]

/-- The differences of three isomorphisms satisfy the cocycle relation. -/
lemma difference_mul_difference (p q r : x ≅ y) :
    b.difference q r * b.difference p q = b.difference p r := by
  rw [eq_comm, difference_eq_iff, act_mul, act_difference, act_difference]

@[simp]
lemma inv_difference (p q : x ≅ y) : (b.difference p q)⁻¹ = b.difference q p := by
  rw [inv_eq_iff_mul_eq_one, difference_mul_difference, difference_self]

lemma act_injective (p : x ≅ y) : Function.Injective (b.act p) :=
  fun a c h ↦ by rw [← b.difference_act p a, h, difference_act]

/-- The action is free: a coefficient fixes an isomorphism only if it is trivial. -/
@[simp]
lemma act_eq_self_iff (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.act p a = p ↔ a = 1 := by
  rw [← difference_eq_iff, difference_self, eq_comm]

end Difference

section Equivalences

variable (x y) in
/-- The principal comparison `(x ≅ y) × A(U) ≃ (x ≅ y) × (x ≅ y)`, sending `(p, a)` to
`(p, p • a)`. Its inverse sends `(p, q)` to `(p, q - p)`; neither needs an isomorphism `x ≅ y`
to exist. -/
def principalEquiv :
    (x ≅ y) × Multiplicative (A.obj.obj (op U)) ≃ (x ≅ y) × (x ≅ y) where
  toFun pa := (pa.1, b.act pa.1 pa.2)
  invFun pq := (pq.1, b.difference pq.1 pq.2)
  left_inv pa := by simp
  right_inv pq := by simp

@[simp]
lemma principalEquiv_apply (pa : (x ≅ y) × Multiplicative (A.obj.obj (op U))) :
    b.principalEquiv x y pa = (pa.1, b.act pa.1 pa.2) :=
  (rfl)

@[simp]
lemma principalEquiv_symm_apply (pq : (x ≅ y) × (x ≅ y)) :
    (b.principalEquiv x y).symm pq = (pq.1, b.difference pq.1 pq.2) :=
  (rfl)

variable (x y) in
/-- When there is an isomorphism `x ≅ y`, the isomorphisms `x ≅ y` form a torsor under the
coefficients `A(U)`, acting by `AbelianBanding.act` (Olsson, Lemma 31.3 and Remark 31.5). The
division of `p` by `q` is the difference of `q` and `p`. -/
@[implicit_reducible]
def isomTorsor (h : Nonempty (x ≅ y)) : Torsor (Multiplicative (A.obj.obj (op U))) (x ≅ y) where
  smul a p := b.act p a
  one_smul := b.act_one
  mul_smul a c p := b.act_mul p a c
  sdiv p q := b.difference q p
  sdiv_smul' p q := b.act_difference q p
  smul_sdiv' a p := b.difference_act p a
  nonempty := h

lemma isomTorsor_smul (h : Nonempty (x ≅ y)) (a : Multiplicative (A.obj.obj (op U)))
    (p : x ≅ y) :
    letI := b.isomTorsor x y h
    a • p = b.act p a :=
  (rfl)

lemma isomTorsor_sdiv (h : Nonempty (x ≅ y)) (p q : x ≅ y) :
    letI := b.isomTorsor x y h
    p /ₛ q = b.difference q p :=
  (rfl)

/-- The identification of the coefficients `A(U)` with the isomorphisms `x ≅ y` given by a chosen
isomorphism `p`, sending `a` to `p • a`: the map `Equiv.smulConst p` of the torsor
`AbelianBanding.isomTorsor`. -/
def coordinateEquiv (p : x ≅ y) : Multiplicative (A.obj.obj (op U)) ≃ (x ≅ y) :=
  letI := b.isomTorsor x y ⟨p⟩
  Equiv.smulConst p

@[simp]
lemma coordinateEquiv_apply (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.coordinateEquiv p a = b.act p a :=
  (rfl)

@[simp]
lemma coordinateEquiv_symm_apply (p q : x ≅ y) :
    (b.coordinateEquiv p).symm q = b.difference p q :=
  (rfl)

lemma coordinateEquiv_one (p : x ≅ y) : b.coordinateEquiv p 1 = p :=
  b.act_one p

/-- Changing the chosen isomorphism from `p` to `q` multiplies the coordinates by the difference
of `p` and `q`. -/
lemma coordinateEquiv_apply_eq (p q : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.coordinateEquiv q a = b.coordinateEquiv p (a * b.difference p q) := by
  simp [act_mul]

end Equivalences

section Pullback

variable {V : C} (f : V ⟶ U)

/-- Pullback along `f : V ⟶ U` carries the action of `a` on `p` to the action of the restriction
of `a` to `V` on the pullback of `p`. -/
lemma mapIso_act (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    (F.map f.op.toLoc).toFunctor.mapIso (b.act p a) =
      b.act ((F.map f.op.toLoc).toFunctor.mapIso p) (.ofAdd (A.obj.map f.op a.toAdd)) := by
  ext
  simp

/-- The difference of the pullbacks of `p` and `q` along `f : V ⟶ U` is the restriction of the
difference of `p` and `q`. -/
lemma difference_mapIso (p q : x ≅ y) :
    b.difference ((F.map f.op.toLoc).toFunctor.mapIso p) ((F.map f.op.toLoc).toFunctor.mapIso q) =
      .ofAdd (A.obj.map f.op (b.difference p q).toAdd) := by
  rw [difference_eq_iff, ← mapIso_act, act_difference]

end Pullback

section Hom

/-- The action of a coefficient `a` of `A(U)` on a morphism `p : x ⟶ y` of the fibre over `U`:
the composite of `p` with the band automorphism of `a` at `y`. On isomorphisms it is
`AbelianBanding.act`. -/
def homAct (p : x ⟶ y) (a : Multiplicative (A.obj.obj (op U))) : x ⟶ y :=
  p ≫ (b.mulEquiv U y a).asIso.hom

lemma homAct_def (p : x ⟶ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.homAct p a = p ≫ (b.mulEquiv U y a).asIso.hom :=
  (rfl)

@[simp]
lemma homAct_hom (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    b.homAct p.hom a = (b.act p a).hom :=
  (rfl)

@[simp]
lemma homAct_one (p : x ⟶ y) : b.homAct p 1 = p := by
  simp [homAct]

/-- The action on morphisms is a left action for the composition convention of `Aut`, in which
`a * c` is `c` followed by `a`. -/
lemma homAct_mul (p : x ⟶ y) (a c : Multiplicative (A.obj.obj (op U))) :
    b.homAct p (a * c) = b.homAct (b.homAct p c) a := by
  simp [homAct]

/-- The action on morphisms commutes with precomposition. -/
@[simp]
lemma comp_homAct {w : F.obj (.mk (op U))} (f : w ⟶ x) (p : x ⟶ y)
    (a : Multiplicative (A.obj.obj (op U))) : f ≫ b.homAct p a = b.homAct (f ≫ p) a := by
  simp [homAct]

/-- The action on morphisms commutes with postcomposition by an isomorphism. -/
@[simp]
lemma homAct_comp_hom (p : x ⟶ y) (e : y ≅ z) (a : Multiplicative (A.obj.obj (op U))) :
    b.homAct p a ≫ e.hom = b.homAct (p ≫ e.hom) a := by
  simp [homAct, b.mulEquiv_hom_comp e]

/-- The restriction maps `pullHom` of the presheaves of morphisms carry the action of `a` on a
morphism `φ` to the action of the restriction of `a` on the restriction of `φ`. -/
lemma pullHom_homAct ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (a : Multiplicative (A.obj.obj (op Y))) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁)
    (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (b.homAct φ a) g gf₁ gf₂ hgf₁ hgf₂ =
      b.homAct (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) (.ofAdd (A.obj.map g.op a.toAdd)) := by
  let e := Cat.Hom.toNatIso (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop))
  simp only [pullHom, homAct, Functor.map_comp, map_mulEquiv_hom, Category.assoc]
  congr 2
  exact b.mulEquiv_hom_comp (e.app M₂).symm _

/-- Restriction along `q : V ⟶ U` identifies the restriction of `Isom(x, y)` to `Over V` with
`Isom` of the pullbacks of `x` and `y` to `V` (`Pseudofunctor.overMapCompPresheafHomIso`), and this
identification commutes with the actions of the coefficients. -/
lemma overMapCompPresheafHomIso_hom_app_homAct {V : C} (q : V ⟶ U) (T : (Over V)ᵒᵖ)
    (p : (F.presheafHom x y).obj (op ((Over.map q).obj T.unop)))
    (a : Multiplicative (A.obj.obj (op T.unop.left))) :
    (F.overMapCompPresheafHomIso x y q).hom.app T (b.homAct p a) =
      b.homAct ((F.overMapCompPresheafHomIso x y q).hom.app T p) a := by
  -- The component of `overMapCompPresheafHomIso` is conjugation by the comparison isomorphisms
  -- `F.mapComp'` at `x` and `y`.
  exact (congrArg (· ≫ _) (b.comp_homAct _ p a)).trans (b.homAct_comp_hom _
    ((Cat.Hom.toNatIso (F.mapComp' q.op.toLoc T.unop.hom.op.toLoc _)).app y) a)

end Hom

section HomPrincipal

variable [IsGroupoid (F.obj (.mk (op U)))]

/-- In a groupoid fibre, the isomorphism underlying the action of `a` on a morphism `p` is the
action of `a` on the isomorphism underlying `p`. -/
@[simp]
lemma asIso_homAct (p : x ⟶ y) (a : Multiplicative (A.obj.obj (op U))) :
    asIso (b.homAct p a) = b.act (asIso p) a := by
  ext
  simp [homAct_def]

/-- In a groupoid fibre, the difference of `p` and `q` carries `p` to `q`. -/
@[simp]
lemma homAct_difference_asIso (p q : x ⟶ y) :
    b.homAct p (b.difference (asIso p) (asIso q)) = q :=
  (b.homAct_hom (asIso p) _).trans (congrArg Iso.hom (b.act_difference _ _))

variable (x y) in
/-- The principal comparison `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)` of a groupoid fibre, sending
`(p, a)` to `(p, p • a)`; its inverse sends `(p, q)` to `(p, q - p)`. It is
`AbelianBanding.principalEquiv` on the isomorphisms underlying the morphisms, and needs no morphism
`x ⟶ y` to exist.

The body is exposed because it is the component of the sheaf-level principal comparison
`AbelianBanding.principalSheafIso`, whose component lemmas hold by definition. -/
@[expose] noncomputable def homPrincipalEquiv :
    (x ⟶ y) × Multiplicative (A.obj.obj (op U)) ≃ (x ⟶ y) × (x ⟶ y) where
  toFun pa := (pa.1, b.homAct pa.1 pa.2)
  invFun pq := (pq.1, b.difference (asIso pq.1) (asIso pq.2))
  left_inv pa := by simp
  right_inv pq := by simp

@[simp]
lemma homPrincipalEquiv_apply (pa : (x ⟶ y) × Multiplicative (A.obj.obj (op U))) :
    b.homPrincipalEquiv x y pa = (pa.1, b.homAct pa.1 pa.2) :=
  (rfl)

@[simp]
lemma homPrincipalEquiv_symm_apply (pq : (x ⟶ y) × (x ⟶ y)) :
    (b.homPrincipalEquiv x y).symm pq = (pq.1, b.difference (asIso pq.1) (asIso pq.2)) :=
  (rfl)

end HomPrincipal

end CategoryTheory.Pseudofunctor.AbelianBanding
