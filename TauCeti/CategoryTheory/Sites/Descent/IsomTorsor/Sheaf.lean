/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic

/-!
# The principal comparison for the sheaf of isomorphisms of a banded gerbe

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose fibres are
groupoids, for instance a gerbe, and let `x y` be objects over `U`. Mathlib's presheaf of
morphisms `F.presheafHom x y` on `Over U` is then the presheaf of isomorphisms `Isom(x, y)`, and
`A|_U` acts on it by `homAct`. This file shows that the action is principal at the level of
presheaves and of sheaves: the map `(p, a) ↦ (p, p · a)` is an isomorphism from
`Hom(x, y) × A|_U` onto `Hom(x, y) × Hom(x, y)` (`AbelianBanding.principalPresheafIso`), with
inverse `(p, q) ↦ (p, q - p)`, and for a prestack both sides are sheaves for `J.over U`
(`AbelianBanding.principalSheafIso`). Together with the local sections of `Hom(x, y)` in a gerbe
(`IsGerbe.exists_covering_hom`), these are the ingredients of Olsson's condition that `Isom(x, y)`
is an `A|_U`-torsor (Olsson, Definition 31.1, Lemma 31.3 and Remark 31.5); the torsor statement
itself is not formalised here.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `homPrincipalEquiv`: `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)`, `(p, a) ↦ (p, homAct p a)`.
* `coefficientPresheaf`, `actionPresheaf`, `pairPresheaf`: the presheaves `A|_U`,
  `Hom(x, y) × A|_U` and `Hom(x, y) × Hom(x, y)` on `Over U`.
* `principalPresheafIso`: the principal comparison of presheaves.
* `coefficientSheaf`: the sheaf `A|_U` on `J.over U`.
* `principalSheafIso`: the same comparison for the tensor products of sheaves on `J.over U`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Lemma 31.3 and Remark 31.5
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{v'}} (b : F.AbelianBanding J A)
  {U : C} {x y : F.obj (.mk (op U))}

/-! ### The principal equivalence on one fibre -/

variable (x y) in
/-- **The principal equivalence on morphisms.** In a groupoid fibre, `(p, a) ↦ (p, homAct p a)` is
an equivalence `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)`, with inverse
`(p, q) ↦ (p, difference p q)`. No morphism `x ⟶ y` is assumed to exist. -/
noncomputable def homPrincipalEquiv [IsGroupoid (F.obj (.mk (op U)))] :
    (x ⟶ y) × Multiplicative (A.obj.obj (op U)) ≃ (x ⟶ y) × (x ⟶ y) :=
  letI := Groupoid.ofIsGroupoid (C := F.obj (.mk (op U)))
  ((Groupoid.isoEquivHom x y).symm.prodCongr (Equiv.refl _)).trans
    ((b.principalEquiv x y).trans
      ((Groupoid.isoEquivHom x y).prodCongr (Groupoid.isoEquivHom x y)))

@[simp]
theorem homPrincipalEquiv_apply [IsGroupoid (F.obj (.mk (op U)))]
    (pa : (x ⟶ y) × Multiplicative (A.obj.obj (op U))) :
    b.homPrincipalEquiv x y pa = (pa.1, b.homAct pa.1 pa.2) := by
  simp [homPrincipalEquiv, homAct_def]

@[simp]
theorem homPrincipalEquiv_symm_apply [IsGroupoid (F.obj (.mk (op U)))]
    (pq : (x ⟶ y) × (x ⟶ y)) :
    (b.homPrincipalEquiv x y).symm pq = (pq.1, b.difference (asIso pq.1) (asIso pq.2)) := by
  -- the isomorphism with underlying morphism `p` is `asIso p`, as their `hom` fields agree
  have h (p : x ⟶ y) : letI := Groupoid.ofIsGroupoid (C := F.obj (.mk (op U)))
      (Groupoid.isoEquivHom x y).symm p = asIso p := Iso.ext rfl
  simp [homPrincipalEquiv, h]

/-! ### Presheaves on `Over U` -/

variable (A U) in
/-- The coefficient presheaf `A|_U` on `Over U`, with values in types. -/
abbrev coefficientPresheaf : (Over U)ᵒᵖ ⥤ Type v' :=
  (Over.forget U).op ⋙ A.obj ⋙ forget AddCommGrpCat

variable (F x y) in
/-- The presheaf `Hom(x, y) × Hom(x, y)` of pairs of local morphisms. -/
abbrev pairPresheaf : (Over U)ᵒᵖ ⥤ Type v' :=
  F.presheafHom x y ⊗ F.presheafHom x y

variable (A x y) in
/-- The presheaf `Hom(x, y) × A|_U` of local morphisms with a coefficient. -/
abbrev actionPresheaf : (Over U)ᵒᵖ ⥤ Type v' :=
  F.presheafHom x y ⊗ coefficientPresheaf A U

variable (x y) in
/-- **The principal comparison of presheaves** `Hom(x, y) × A|_U ≅ Hom(x, y) × Hom(x, y)`,
`(p, a) ↦ (p, homAct p a)`, when every fibre is a groupoid. -/
noncomputable def principalPresheafIso [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    actionPresheaf A x y ≅ pairPresheaf F x y :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso ((Equiv.prodCongr (Equiv.refl _) Multiplicative.ofAdd).trans
      (b.homPrincipalEquiv _ _)))
    (fun {T₁ T₂} g ↦ by
      ext ⟨p, a⟩
      -- Evaluate both components by `homPrincipalEquiv_apply`. The restriction maps of the
      -- product presheaves act on pairs componentwise, and that of `F.presheafHom x y` is
      -- `pullHom` along `g.unop.left` (Mathlib's `Pseudofunctor.presheafHom_map`, generated by
      -- `@[simps]` on `presheafHom`), so the two sides agree by `pullHom_homAct`.
      refine (b.homPrincipalEquiv_apply _).trans (.trans ?_ (congrArg
        (ConcreteCategory.hom ((pairPresheaf F x y).map g))
        (b.homPrincipalEquiv_apply (p, .ofAdd a))).symm)
      exact Prod.ext rfl (b.pullHom_homAct p (.ofAdd a) g.unop.left T₂.unop.hom T₂.unop.hom
        (Over.w g.unop) (Over.w g.unop)).symm)

/-- The principal comparison sends `(p, a)` to `(p, homAct p a)`. -/
theorem principalPresheafIso_hom_app [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) (pa : (actionPresheaf A x y).obj T) :
    (b.principalPresheafIso x y).hom.app T pa =
      (pa.1, b.homAct pa.1 (.ofAdd pa.2)) :=
  b.homPrincipalEquiv_apply (pa.1, .ofAdd pa.2)

/-- The inverse comparison sends `(p, q)` to `(p, difference p q)`. -/
theorem principalPresheafIso_inv_app [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) (pq : (pairPresheaf F x y).obj T) :
    (b.principalPresheafIso x y).inv.app T pq =
      (pq.1, (b.difference (asIso pq.1) (asIso pq.2)).toAdd) :=
  congrArg (Prod.map _root_.id Multiplicative.toAdd) (b.homPrincipalEquiv_symm_apply pq)

/-! ### Sheaves on `J.over U` -/

variable (J A U) in
/-- The coefficient sheaf `A|_U` on `J.over U`, with values in types. -/
abbrev coefficientSheaf : Sheaf (J.over U) (Type v') :=
  (sheafCompose (J.over U) (forget AddCommGrpCat.{v'})).obj
    ((J.overPullback AddCommGrpCat U).obj A)

variable [F.IsPrestack J]

variable (x y) in
/-- **The principal comparison of sheaves** `Hom(x, y) × A|_U ≅ Hom(x, y) × Hom(x, y)` on
`J.over U`, whose underlying morphism of presheaves is `principalPresheafIso`. -/
noncomputable def principalSheafIso [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    F.sheafHom J x y ⊗ coefficientSheaf J A U ≅ F.sheafHom J x y ⊗ F.sheafHom J x y :=
  (fullyFaithfulSheafToPresheaf (J.over U) (Type v')).preimageIso (b.principalPresheafIso x y)

@[simp]
theorem principalSheafIso_hom_hom [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    (b.principalSheafIso x y).hom.hom = (b.principalPresheafIso x y).hom :=
  (rfl)

@[simp]
theorem principalSheafIso_inv_hom [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    (b.principalSheafIso x y).inv.hom = (b.principalPresheafIso x y).inv :=
  (rfl)

end CategoryTheory.Pseudofunctor.AbelianBanding
