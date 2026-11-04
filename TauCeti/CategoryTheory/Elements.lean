/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Data.Set.Prod

/-!
# Arrows of the category of elements as pairs of an arrow and a point

A functor `F : C ⥤ Type*` is an action of `C` on the family of fibers `F.obj x` over the objects
of `C`, with total space `F.Elements` and anchor `Functor.Elements.obj : F.Elements → C`. Its
category of elements `F.Elements` is the action category `C ⋉ F.Elements`, an action groupoid
when `C` is a groupoid. An arrow of
`F.Elements` from `z` is determined by its underlying arrow `g` of `C`, whose source is the
object under `z`, and by `z`: its target is the translate `g • z = F.map g z`
(`CategoryTheory.Functor.Elements.act`). So the total arrows of `F.Elements` are the fiber product
of the total arrows of `C` and the total space, along the source and the anchor
(`CategoryTheory.Functor.Elements.totalEquiv`). This is the algebraic description behind the
topology of action categories of families in `TauCeti.Topology.CategoryTheory.Elements.Basic`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
-/

public section

universe v

namespace CategoryTheory

variable {C : Type*} [Category.{v} C]

namespace Functor.Elements

variable (F : C ⥤ Type*)

/-- The translate of a point `z` of the total space by an arrow `g` of `C` with source over `z`:
the action map `Γ₁ ×_{Γ₀} Z → Z` of the family. -/
def act (q : (Quiver.Total.left : Quiver.Total C → C).Pullback (Functor.Elements.obj (F := F))) :
    F.Elements :=
  .mk (F.map (eqToHom q.2.symm ≫ q.1.1.hom) q.1.2.val)

/-- The translate of a point by an arrow lies over the target of the arrow. -/
@[simp]
theorem act_obj
    (q : (Quiver.Total.left : Quiver.Total C → C).Pullback (Functor.Elements.obj (F := F))) :
    (act F q).obj = q.1.1.right := (rfl)

/-- The translate of a point `z` over `x` by an arrow `g : x ⟶ y` is `F.map g z`. -/
@[simp]
theorem act_mk {x y : C} (g : x ⟶ y) (z : F.obj x) :
    act F ⟨(⟨x, y, g⟩, .mk z), rfl⟩ = .mk (F.map g z) := by
  simp [act]

/-- The total arrows of the category of elements are the pairs of an arrow of `C` and a point
of the total space lying over its source. -/
def totalEquiv : Quiver.Total F.Elements ≃
    (Quiver.Total.left : Quiver.Total C → C).Pullback (Functor.Elements.obj (F := F)) where
  toFun a := ⟨(⟨a.left.obj, a.right.obj, a.hom.hom⟩, a.left), rfl⟩
  invFun q := ⟨q.1.2, act F q, homMk (eqToHom q.2.symm ≫ q.1.1.hom) rfl⟩
  left_inv := by
    rintro ⟨x, y, f⟩
    have hy : act F ⟨(⟨x.obj, y.obj, f.hom⟩, x), rfl⟩ = y := by
      obtain ⟨yv⟩ := y
      exact congrArg Functor.Elements.mk (by simpa using f.map_val)
    -- Generalize the target so that it can be identified with `y`.
    have key : ∀ (Y : F.Elements) (g : x ⟶ Y), Y = y → g.hom ≍ f.hom →
        (⟨x, Y, g⟩ : Quiver.Total F.Elements) = ⟨x, y, f⟩ := by
      rintro Y g rfl h
      rw [hom_ext (eq_of_heq h)]
    exact key _ _ hy (heq_of_eq (Category.id_comp _))
  right_inv := by
    rintro ⟨⟨⟨x, y, g⟩, z⟩, h⟩
    dsimp only at h
    subst h
    exact Subtype.ext (Prod.ext (Quiver.Total.ext rfl rfl (heq_of_eq (Category.id_comp _))) rfl)

/-- A total arrow corresponds to its underlying arrow of `C` and its source. -/
@[simp]
theorem totalEquiv_apply (a : Quiver.Total F.Elements) :
    totalEquiv F a = ⟨(⟨a.left.obj, a.right.obj, a.hom.hom⟩, a.left), rfl⟩ := (rfl)

/-- The source of the total arrow corresponding to `(g, z)` is `z`. -/
@[simp]
theorem totalEquiv_symm_apply_left
    (q : (Quiver.Total.left : Quiver.Total C → C).Pullback (Functor.Elements.obj (F := F))) :
    ((totalEquiv F).symm q).left = q.1.2 := (rfl)

/-- The target of the total arrow corresponding to `(g, z)` is the translate of `z` by `g`. -/
@[simp]
theorem totalEquiv_symm_apply_right
    (q : (Quiver.Total.left : Quiver.Total C → C).Pullback (Functor.Elements.obj (F := F))) :
    ((totalEquiv F).symm q).right = act F q := (rfl)

/-- The target of a total arrow of the category of elements is the translate of its source. -/
theorem act_totalEquiv (a : Quiver.Total F.Elements) : act F (totalEquiv F a) = a.right := by
  rw [← totalEquiv_symm_apply_right, Equiv.symm_apply_apply]

section BaseChange

variable {D : Type*} [Category D] (K : D ⥤ C)

/-- The total space of the pulled-back family is the fiber product of the object map and
the original anchor. This uses the native precomposition functor on categories of elements. -/
def precompEquiv : (K ⋙ F).Elements ≃
    K.obj.Pullback (Functor.Elements.obj (F := F)) where
  toFun z := ⟨(z.obj, (precomp K F).obj z), rfl⟩
  invFun q := { obj := q.1.1, val := F.map (eqToHom q.2.symm) q.1.2.val }
  left_inv z := by
    cases z
    simp
  right_inv q := by
    obtain ⟨⟨d, @⟨c, z⟩⟩, h⟩ := q
    dsimp only at h
    subst c
    simp [precomp]

/-- The fiber-product coordinates of a point in a pulled-back family. -/
@[simp]
theorem precompEquiv_apply (z : (K ⋙ F).Elements) :
    precompEquiv F K z = ⟨(z.obj, (precomp K F).obj z), rfl⟩ := (rfl)

/-- The anchor of the point reconstructed from fiber-product coordinates. -/
@[simp]
theorem precompEquiv_symm_apply_obj (q : K.obj.Pullback (Functor.Elements.obj (F := F))) :
    ((precompEquiv F K).symm q).obj = q.1.1 := (rfl)

/-- The original point is recovered by forgetting the new base coordinate. -/
@[simp]
theorem precomp_obj_precompEquiv_symm (q : K.obj.Pullback (Functor.Elements.obj (F := F))) :
    (precomp K F).obj ((precompEquiv F K).symm q) = q.1.2 := by
  exact congrArg (fun p => p.1.2) ((precompEquiv F K).apply_symm_apply q)

end BaseChange

end Functor.Elements

end CategoryTheory
