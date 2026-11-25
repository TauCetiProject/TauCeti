/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor

/-!
# The sheaf of isomorphisms of a banded gerbe is a torsor

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose fibres are
groupoids, for instance a gerbe, and let `x y` be objects over `U`. Mathlib's presheaf of
morphisms `F.presheafHom x y` on `Over U` is then the presheaf of isomorphisms `Isom(x, y)`, and
`A|_U` acts on it by `homAct`. This file shows that the action is principal at the level of
presheaves and of sheaves: the map `(p, a) ↦ (p, p · a)` is an isomorphism from
`Hom(x, y) × A|_U` onto `Hom(x, y) × Hom(x, y)` (`AbelianBanding.principalPresheafIso`), with
inverse `(p, q) ↦ (p, q - p)`, and for a prestack both sides are sheaves for `J.over U`
(`AbelianBanding.principalSheafIso`). For a gerbe, `Hom(x, y)` has sections locally
(`AbelianBanding.hom_localNonempty`), so `Isom(x, y)` is an `A|_U`-torsor (Olsson, Definition 31.1,
Lemma 31.3 and Remark 31.5).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `homEquiv`: in a groupoid fibre, `(x ≅ y) ≃ (x ⟶ y)`.
* `homPrincipalEquiv`: `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)`, `(p, a) ↦ (p, homAct p a)`.
* `coefficientPresheaf`, `actionPresheaf`, `pairPresheaf`: the presheaves `A|_U`,
  `Hom(x, y) × A|_U` and `Hom(x, y) × Hom(x, y)` on `Over U`.
* `principalPresheafIso`: the principal comparison of presheaves.
* `pair_isSheaf`, `action_isSheaf`, `pairSheaf`, `actionSheaf`, `principalSheafIso`: the same
  for sheaves on `J.over U`.
* `hom_localNonempty`: for a gerbe, `Hom(x, y)` has a section on every arrow of a covering sieve.

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

/-! ### Principal equivalences on one fibre -/

variable (x y) in
/-- In a groupoid fibre, isomorphisms `x ≅ y` are the morphisms `x ⟶ y`. -/
noncomputable def homEquiv [IsGroupoid (F.obj (.mk (op U)))] : (x ≅ y) ≃ (x ⟶ y) where
  toFun p := p.hom
  invFun p := asIso p
  left_inv _ := Iso.ext rfl
  right_inv _ := rfl

@[simp]
theorem homEquiv_apply [IsGroupoid (F.obj (.mk (op U)))] (p : x ≅ y) : homEquiv x y p = p.hom :=
  (rfl)

@[simp]
theorem homEquiv_symm_apply [IsGroupoid (F.obj (.mk (op U)))] (p : x ⟶ y) :
    (homEquiv x y).symm p = asIso p :=
  (rfl)

variable (x y) in
/-- **The principal equivalence on morphisms.** In a groupoid fibre, `(p, a) ↦ (p, homAct p a)` is
an equivalence `(x ⟶ y) × A(U) ≃ (x ⟶ y) × (x ⟶ y)`, with inverse
`(p, q) ↦ (p, difference p q)`. No morphism `x ⟶ y` is assumed to exist. -/
noncomputable def homPrincipalEquiv [IsGroupoid (F.obj (.mk (op U)))] :
    (x ⟶ y) × Multiplicative (A.obj.obj (op U)) ≃ (x ⟶ y) × (x ⟶ y) where
  toFun pa := (pa.1, b.homAct pa.1 pa.2)
  invFun pq := (pq.1, b.difference (asIso pq.1) (asIso pq.2))
  left_inv := fun ⟨p, a⟩ ↦ by
    refine Prod.ext rfl ?_
    change b.difference (asIso p) (asIso (b.homAct p a)) = a
    have h : asIso (b.homAct p a) = b.act (asIso p) a := Iso.ext (b.homAct_hom (asIso p) a)
    rw [h, difference_act]
  right_inv := fun ⟨p, q⟩ ↦ by
    refine Prod.ext rfl ?_
    change b.homAct p (b.difference (asIso p) (asIso q)) = q
    exact (b.homAct_hom (asIso p) _).trans (congrArg Iso.hom (b.act_difference (asIso p) (asIso q)))

@[simp]
theorem homPrincipalEquiv_apply [IsGroupoid (F.obj (.mk (op U)))]
    (pa : (x ⟶ y) × Multiplicative (A.obj.obj (op U))) :
    b.homPrincipalEquiv x y pa = (pa.1, b.homAct pa.1 pa.2) :=
  (rfl)

@[simp]
theorem homPrincipalEquiv_symm_apply [IsGroupoid (F.obj (.mk (op U)))]
    (pq : (x ⟶ y) × (x ⟶ y)) :
    (b.homPrincipalEquiv x y).symm pq = (pq.1, b.difference (asIso pq.1) (asIso pq.2)) :=
  (rfl)

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
`(p, a) ↦ (p, homAct p a)`, when every fibre is a groupoid. Naturality is `pullHom_homAct`. -/
noncomputable def principalPresheafIso [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    actionPresheaf A x y ≅ pairPresheaf F x y :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso ((Equiv.prodCongr (Equiv.refl _) Multiplicative.ofAdd).trans
      (b.homPrincipalEquiv _ _)))
    (fun {T₁ T₂} g ↦ by
      ext ⟨p, a⟩
      refine Prod.ext rfl ?_
      exact (b.pullHom_homAct p (.ofAdd a) g.unop.left T₂.unop.hom T₂.unop.hom
        (Over.w g.unop) (Over.w g.unop)).symm)

/-- The principal comparison sends `(p, a)` to `(p, homAct p a)`. -/
theorem principalPresheafIso_hom_app [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) (pa : (actionPresheaf A x y).obj T) :
    (b.principalPresheafIso x y).hom.app T pa =
      (pa.1, b.homAct pa.1 (.ofAdd pa.2)) :=
  (rfl)

/-- The inverse comparison sends `(p, q)` to `(p, difference p q)`. -/
theorem principalPresheafIso_inv_app [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) (pq : (pairPresheaf F x y).obj T) :
    (b.principalPresheafIso x y).inv.app T pq =
      (pq.1, (b.difference (asIso pq.1) (asIso pq.2)).toAdd) :=
  (rfl)

/-- **Local sections.** For a gerbe, `Hom(x, y)` has a section over every arrow of some covering
sieve of `U`. No global morphism `x ⟶ y` is asserted. -/
theorem hom_localNonempty [F.IsGerbe J] (x y : F.obj (.mk (op U))) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y) := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) x y
  exact ⟨R, hR, fun _ f hf ↦ (h f hf).map Iso.hom⟩

/-! ### Sheaves on `J.over U` -/

variable [F.IsPrestack J]

variable (F J x y) in
/-- The presheaf of pairs of local morphisms is a sheaf for `J.over U`, as a product of two copies
of the sheaf of morphisms. -/
theorem pair_isSheaf : Presheaf.IsSheaf (J.over U) (pairPresheaf F x y) :=
  Sheaf.tensorProd_isSheaf (J.over U) (F.sheafHom J x y) (F.sheafHom J x y)

include b in
variable (x y) in
/-- The presheaf of local morphisms with a coefficient is a sheaf for `J.over U`, transported
from `pair_isSheaf` through the principal comparison. -/
theorem action_isSheaf [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    Presheaf.IsSheaf (J.over U) (actionPresheaf A x y) :=
  (Presheaf.isSheaf_of_iso_iff (b.principalPresheafIso x y)).2 (pair_isSheaf F J x y)

variable (F J x y) in
/-- The sheaf `Hom(x, y) × Hom(x, y)` on `J.over U`. -/
abbrev pairSheaf : Sheaf (J.over U) (Type v') :=
  ⟨pairPresheaf F x y, pair_isSheaf F J x y⟩

variable (x y) in
/-- The sheaf `Hom(x, y) × A|_U` on `J.over U`. -/
abbrev actionSheaf [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] : Sheaf (J.over U) (Type v') :=
  ⟨actionPresheaf A x y, action_isSheaf b x y⟩

variable (x y) in
/-- **The principal comparison of sheaves** `Hom(x, y) × A|_U ≅ Hom(x, y) × Hom(x, y)` on
`J.over U`, whose underlying morphism of presheaves is `principalPresheafIso`. -/
noncomputable def principalSheafIso [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    b.actionSheaf x y ≅ pairSheaf F J x y :=
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
