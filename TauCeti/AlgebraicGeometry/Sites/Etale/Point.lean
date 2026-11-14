/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Morphisms of points of the small étale site induced by geometric points

Let `S` be a scheme. A morphism `a : Spec Ω' ⟶ Spec Ω` of geometric points of `S` over `S`, that
is with `a ≫ s = s'`, induces a morphism of points `pointSmallEtale s' ⟶ pointSmallEtale s` of
the small étale site (`AlgebraicGeometry.Scheme.pointSmallEtaleHom`): a lift `t` of `s` to an
étale `S`-scheme goes to the lift `a ≫ t` of `s'`. This construction is functorial in `a`.

## Main definitions

* `AlgebraicGeometry.Scheme.pointSmallEtaleHom a h`: the morphism of points of the small étale
  site induced by a morphism `a` of geometric points.

## Main results

* `AlgebraicGeometry.Scheme.pointSmallEtaleHom_id`,
  `AlgebraicGeometry.Scheme.pointSmallEtaleHom_comp`: functoriality in the geometric point.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

section Hom

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω'] [Field Ω''] [IsSepClosed Ω'']

/-- A morphism `a : Spec Ω' ⟶ Spec Ω` of geometric points of `S`, with `a ≫ s = s'`, induces a
morphism of points `pointSmallEtale s' ⟶ pointSmallEtale s` of the small étale site: a lift `t`
of `s` to an étale `S`-scheme goes to the lift `a ≫ t` of `s'`. -/
noncomputable def pointSmallEtaleHom {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') :
    pointSmallEtale s' ⟶ pointSmallEtale s where
  hom := Functor.whiskerLeft (Etale.forget S)
    (coyoneda.map (Over.homMk a h : Over.mk s' ⟶ Over.mk s).op)

/-- The morphism of points induced by `a` is precomposition with `Over.homMk a h` on the fiber
functors. -/
theorem pointSmallEtaleHom_hom {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') :
    (pointSmallEtaleHom a h).hom = Functor.whiskerLeft (Etale.forget S)
      (coyoneda.map (Over.homMk a h : Over.mk s' ⟶ Over.mk s).op) :=
  (rfl)

/-- The morphism of points induced by `a` sends a lift `t` to `a ≫ t`. -/
@[simp]
theorem pointSmallEtaleHom_hom_app_left {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    (a : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : a ≫ s = s') (X : S.Etale)
    (t : (pointSmallEtale s).fiber.obj X) :
    ((pointSmallEtaleHom a h).hom.app X t).left = a ≫ t.left :=
  (rfl)

/-- The identity of a geometric point induces the identity of its point of the small étale
site. -/
@[simp]
theorem pointSmallEtaleHom_id (s : Spec (.of Ω) ⟶ S) (h : 𝟙 _ ≫ s = s) :
    pointSmallEtaleHom (𝟙 _) h = 𝟙 (pointSmallEtale s) := by
  ext X : 3
  refine ConcreteCategory.hom_ext _ _ fun t ↦ Over.OverMorphism.ext ?_
  simp only [pointSmallEtaleHom_hom_app_left, GrothendieckTopology.Point.id_hom, NatTrans.id_app,
    ConcreteCategory.id_apply, Category.id_comp]

/-- The morphism of points induced by a composite of geometric points is the composite of the
induced morphisms. -/
theorem pointSmallEtaleHom_comp {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    {s'' : Spec (.of Ω'') ⟶ S} (a : Spec (.of Ω'') ⟶ Spec (.of Ω'))
    (b : Spec (.of Ω') ⟶ Spec (.of Ω)) (ha : a ≫ s' = s'') (hb : b ≫ s = s')
    (hab : (a ≫ b) ≫ s = s'') :
    pointSmallEtaleHom (a ≫ b) hab = pointSmallEtaleHom a ha ≫ pointSmallEtaleHom b hb := by
  ext X : 3
  refine ConcreteCategory.hom_ext _ _ fun t ↦ Over.OverMorphism.ext ?_
  simp only [pointSmallEtaleHom_hom_app_left, GrothendieckTopology.Point.comp_hom,
    NatTrans.comp_app, ConcreteCategory.comp_apply, Category.assoc]

/-- Equal morphisms of geometric points induce equal morphisms of points. -/
theorem pointSmallEtaleHom_congr {s : Spec (.of Ω) ⟶ S} {s' : Spec (.of Ω') ⟶ S}
    {a b : Spec (.of Ω') ⟶ Spec (.of Ω)} (hab : a = b) (ha : a ≫ s = s') (hb : b ≫ s = s') :
    pointSmallEtaleHom a ha = pointSmallEtaleHom b hb := by
  subst hab
  rfl

end Hom

end AlgebraicGeometry.Scheme
