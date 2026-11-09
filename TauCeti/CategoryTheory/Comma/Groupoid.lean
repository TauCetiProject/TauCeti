/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Comma categories of groupoids

For functors `L : A ⥤ T` and `R : B ⥤ T`, an object of `CategoryTheory.Comma L R` is a triple
`(a, h, b)` with `h : L a ⟶ R b`, and an arrow is a pair of arrows of `A` and `B` making the
evident square commute. When `A` and `B` are groupoids, so is `Comma L R`
(`CategoryTheory.Comma.isGroupoid`); when `T` is a groupoid as well, every structure arrow is
invertible and `Comma L R` is the weak (iso-comma) fiber product of `L` and `R`.

When only `A` is a groupoid, an arrow of `Comma L R` is freely and uniquely determined by its
source `X` and its two components, an arrow of `A` out of `X.left` and an arrow of `B` out of
`X.right`: the structure arrow of the target is forced by commutativity of the square.
`CategoryTheory.Comma.totalEquiv` records this as an equivalence between the total arrows of
`Comma L R` and the fiber product of the objects of `Comma L R` with the total arrows of `A` and
`B` over the objects of `A` and `B`. Over a groupoid `T`, this is the description of the arrows of
a weak fiber product of groupoids used to topologize it.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
-/

public section

namespace CategoryTheory.Comma

variable {A B T : Type*} [Category A] [Category B] [Category T] {L : A ⥤ T} {R : B ⥤ T}

/-- An arrow of a comma category whose two components are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_left_of_isIso_right {X Y : Comma L R} (f : X ⟶ Y) [IsIso f.left]
    [IsIso f.right] : IsIso f :=
  (isoMk (asIso f.left) (asIso f.right) f.w).isIso_hom

/-- The comma category of two functors out of groupoids is a groupoid. When the common target is
a groupoid too, it is their weak fiber product. -/
instance isGroupoid [IsGroupoid A] [IsGroupoid B] : IsGroupoid (Comma L R) where
  all_isIso f := isIso_of_isIso_left_of_isIso_right f

/-- Arrows of a comma category with the same source and equal targets are heterogeneously equal
as soon as their components are. -/
theorem hom_heq_ext {X Y Y' : Comma L R} (h : Y = Y') {f : X ⟶ Y} {g : X ⟶ Y'}
    (hl : f.left ≍ g.left) (hr : f.right ≍ g.right) : f ≍ g := by
  subst h
  exact heq_of_eq (hom_ext _ _ (eq_of_heq hl) (eq_of_heq hr))

/-- An arrow `α` of `A` out of `X.left` and an arrow `β` of `B` out of `X.right` are the components
of a unique arrow of `Comma L R` out of `X`, when `A` is a groupoid. The arrows are given as total
arrows together with the equalities identifying their sources. -/
noncomputable def totalEquiv [IsGroupoid A] :
    Quiver.Total (Comma L R) ≃
      {p : Comma L R × Quiver.Total A × Quiver.Total B //
        p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right} where
  toFun f := ⟨(f.left, ⟨_, _, f.hom.left⟩, ⟨_, _, f.hom.right⟩), rfl, rfl⟩
  invFun p :=
    ⟨p.1.1, ⟨p.1.2.1.right, p.1.2.2.right,
      L.map (inv (eqToHom p.2.1.symm ≫ p.1.2.1.hom)) ≫ p.1.1.hom ≫
        R.map (eqToHom p.2.2.symm ≫ p.1.2.2.hom)⟩,
      { left := eqToHom p.2.1.symm ≫ p.1.2.1.hom
        right := eqToHom p.2.2.symm ≫ p.1.2.2.hom
        w := by simp [← Functor.map_comp_assoc] }⟩
  left_inv := by
    rintro ⟨X, ⟨l, r, h⟩, ⟨α, β, w⟩⟩
    dsimp only at α β w
    obtain rfl : h = L.map (inv α) ≫ X.hom ≫ R.map β := by simp [← w]
    refine Quiver.Total.ext rfl (by simp) (hom_heq_ext ?_ (by simp) (by simp))
    simp
  right_inv := by
    rintro ⟨⟨X, ⟨a, a', α⟩, ⟨b, b', β⟩⟩, ha, hb⟩
    dsimp only at ha hb
    subst ha hb
    simp

/-- `CategoryTheory.Comma.totalEquiv` records the source and the two components of an arrow. -/
@[simp]
theorem totalEquiv_apply_coe [IsGroupoid A] (f : Quiver.Total (Comma L R)) :
    (totalEquiv f : Comma L R × Quiver.Total A × Quiver.Total B) =
      (f.left, ⟨_, _, f.hom.left⟩, ⟨_, _, f.hom.right⟩) := (rfl)

/-- The arrow with prescribed source and components has that source. -/
@[simp]
theorem totalEquiv_symm_apply_left [IsGroupoid A]
    (p : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}) :
    (totalEquiv.symm p).left = p.1.1 := (rfl)

/-- The target of the arrow with prescribed source and components. Its structure arrow is the
composite `L α⁻¹ ≫ X.hom ≫ R β` forced by commutativity of the square. -/
@[simp]
theorem totalEquiv_symm_apply_right [IsGroupoid A]
    (p : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}) :
    (totalEquiv.symm p).right = ⟨p.1.2.1.right, p.1.2.2.right,
      L.map (inv (eqToHom p.2.1.symm ≫ p.1.2.1.hom)) ≫ p.1.1.hom ≫
        R.map (eqToHom p.2.2.symm ≫ p.1.2.2.hom)⟩ := (rfl)

/-- The arrow with prescribed source and components has that left component. -/
@[simp]
theorem totalEquiv_symm_apply_hom_left [IsGroupoid A]
    (p : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}) :
    (⟨_, _, (totalEquiv.symm p).hom.left⟩ : Quiver.Total A) = p.1.2.1 := by
  obtain ⟨⟨X, ⟨a, a', α⟩, ⟨b, b', β⟩⟩, ha, hb⟩ := p
  dsimp only at ha hb
  subst ha hb
  simp [totalEquiv]

/-- The arrow with prescribed source and components has that right component. -/
@[simp]
theorem totalEquiv_symm_apply_hom_right [IsGroupoid A]
    (p : {p : Comma L R × Quiver.Total A × Quiver.Total B //
      p.2.1.left = p.1.left ∧ p.2.2.left = p.1.right}) :
    (⟨_, _, (totalEquiv.symm p).hom.right⟩ : Quiver.Total B) = p.1.2.2 := by
  obtain ⟨⟨X, ⟨a, a', α⟩, ⟨b, b', β⟩⟩, ha, hb⟩ := p
  dsimp only at ha hb
  subst ha hb
  simp [totalEquiv]

end CategoryTheory.Comma
