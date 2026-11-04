/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Composition of total arrows and sums over arrows with a given source

The total arrows `Quiver.Total C` of a category form a space of their own, as for the arrows of a
topological or étale groupoid. Two total arrows `a` and `b` are composable when the target of `a`
is the source of `b`, and then `Quiver.Total.comp` is the total arrow `a ≫ b`. Its continuity on
the subspace of composable pairs is the continuity of composition of a topological groupoid.

A total arrow with identified endpoints is read as a morphism between those endpoints by Mathlib's
`Quiver.homOfEq`, which recovers the total arrow (`Quiver.Total.mk_homOfEq`) and turns composition
of morphisms into composition of total arrows (`Quiver.Total.mk_homOfEq_comp_homOfEq`).

A sum over the total arrows with source `x` is a sum over the arrows `x ⟶ y` for all `y`
(`Quiver.Total.finsum_mem_preimage_left_singleton`). In a category, an isomorphism `x ≅ y` matches
the arrows out of `x` with those out of `y` with the same targets, so the sum of a function of the
target over the arrows with source `x` depends only on the isomorphism class of `x`
(`Quiver.Total.finsum_mem_preimage_left_singleton_eq_of_iso`). Such sums define the cutoff
functions of étale groupoids.

## Main declarations

* `Quiver.Total.comp`: the composite of two composable total arrows of a category.
-/

public section

open CategoryTheory

namespace Quiver.Total

section Quiver

variable {V : Type*} [Quiver V]

/-- A total arrow, read as a morphism between objects equal to its endpoints, is again the
same total arrow. -/
@[simp]
theorem mk_homOfEq (a : Quiver.Total V) {y z : V} (hy : a.left = y) (hz : a.right = z) :
    (⟨y, z, Quiver.homOfEq a.hom hy hz⟩ : Quiver.Total V) = a := by
  subst hy hz
  rfl

/-- The total arrows with source `x` are the arrows `x ⟶ y`, for all objects `y`. -/
theorem preimage_left_singleton (x : V) :
    Quiver.Total.left ⁻¹' {x} =
      Set.range fun p : Σ y, (x ⟶ y) ↦ (⟨x, p.1, p.2⟩ : Quiver.Total V) := by
  ext ⟨a, b, f⟩
  constructor
  · rintro rfl
    exact ⟨⟨b, f⟩, rfl⟩
  · rintro ⟨p, h⟩
    exact congrArg Quiver.Total.left h.symm

/-- A sum over the total arrows with source `x` is a sum over the arrows `x ⟶ y`. -/
theorem finsum_mem_preimage_left_singleton {M : Type*} [AddCommMonoid M]
    (g : Quiver.Total V → M) (x : V) :
    ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, g a = ∑ᶠ p : Σ y, (x ⟶ y), g ⟨x, p.1, p.2⟩ := by
  rw [preimage_left_singleton, finsum_mem_range]
  rintro ⟨y, f⟩ ⟨y', f'⟩ h
  obtain ⟨-, rfl, hf⟩ := Quiver.Total.mk.inj h
  exact Sigma.ext rfl hf

end Quiver

variable {C : Type*} [Category C]

/-- The sum of a function of the target over the total arrows with source `x` only depends on the
isomorphism class of `x`: an isomorphism `x ≅ y` identifies the arrows out of `x` with those out
of `y`, preserving targets. -/
theorem finsum_mem_preimage_left_singleton_eq_of_iso {M : Type*} [AddCommMonoid M] (g : C → M)
    {x y : C} (e : x ≅ y) :
    ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, g a.right = ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {y}, g a.right := by
  rw [finsum_mem_preimage_left_singleton, finsum_mem_preimage_left_singleton]
  exact finsum_comp_equiv (Equiv.sigmaCongrRight fun _ ↦ e.homFromEquiv)
    (f := fun p : Σ z, (y ⟶ z) ↦ g p.1)

/-- The composite of total arrows `a` and `b` of a category with the target of `a` equal to the
source of `b`: the first arrow is followed by the second. -/
def comp (a b : Quiver.Total C) (h : a.right = b.left) : Quiver.Total C :=
  ⟨a.left, b.right, a.hom ≫ eqToHom h ≫ b.hom⟩

theorem comp_def (a b : Quiver.Total C) (h : a.right = b.left) :
    a.comp b h = ⟨a.left, b.right, a.hom ≫ eqToHom h ≫ b.hom⟩ := (rfl)

@[simp]
theorem comp_left (a b : Quiver.Total C) (h : a.right = b.left) : (a.comp b h).left = a.left :=
  (rfl)

@[simp]
theorem comp_right (a b : Quiver.Total C) (h : a.right = b.left) :
    (a.comp b h).right = b.right := (rfl)

@[simp]
theorem mk_comp_mk {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (⟨x, y, f⟩ : Quiver.Total C).comp ⟨y, z, g⟩ rfl = ⟨x, z, f ≫ g⟩ := by
  simp [comp_def]

/-- The composite of total arrows depends only on the arrows, not on the proof that they are
composable. -/
theorem comp_congr {a a' b b' : Quiver.Total C} (ha : a = a') (hb : b = b')
    (h : a.right = b.left) (h' : a'.right = b'.left) : a.comp b h = a'.comp b' h' := by
  subst ha hb
  rfl

/-- Composing two total arrows read as morphisms with matching endpoints gives their composite as
total arrows. -/
theorem mk_homOfEq_comp_homOfEq (a b : Quiver.Total C) {y z w : C} (hy : a.left = y)
    (hz : a.right = z) (hz' : b.left = z) (hw : b.right = w) :
    (⟨y, w, Quiver.homOfEq a.hom hy hz ≫ Quiver.homOfEq b.hom hz' hw⟩ : Quiver.Total C) =
      a.comp b (hz.trans hz'.symm) := by
  obtain ⟨a₁, a₂, f⟩ := a
  obtain ⟨b₁, b₂, g⟩ := b
  dsimp only at hy hz hz' hw
  subst hy hz hz' hw
  simp

end Quiver.Total
