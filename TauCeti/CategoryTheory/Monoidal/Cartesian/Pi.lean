/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Splitting off the first factor of a finite product

In a cartesian monoidal category `C`, the product `∏ᶜ f` of a family `f : Fin (n + 1) → C` is
the binary product `f 0 ⊗ ∏ᶜ (fun i : Fin n => f i.succ)` of its first factor and the product of
the others. The isomorphism `piFinSuccIso f` sends `(a₀, a₁, …, a_n)` to `(a₀, (a₁, …, a_n))`;
its inverse reassembles the tuple in order. It is the categorical form of `Fin.consEquiv`, and is
used to separate the head coordinate of a power `G ×_S ⋯ ×_S G` of a group scheme from its tail.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {n : ℕ} (f : Fin (n + 1) → C)
  [HasProduct f] [HasProduct fun i : Fin n => f i.succ]

/-- The product of a family `f : Fin (n + 1) → C` is the binary product of its first factor and
the product of the remaining factors: `(a₀, a₁, …, a_n) ↦ (a₀, (a₁, …, a_n))`. -/
noncomputable def piFinSuccIso : ∏ᶜ f ≅ f 0 ⊗ ∏ᶜ fun i : Fin n => f i.succ where
  hom := lift (Pi.π f 0) (Pi.lift fun i => Pi.π f i.succ)
  inv := Pi.lift (Fin.cons (fst _ _) fun i => snd _ _ ≫ Pi.π _ i)
  hom_inv_id := Pi.hom_ext _ _ fun i => by cases i using Fin.cases <;> simp
  inv_hom_id := by ext <;> simp

/-- The first component of `piFinSuccIso f` is the first projection of the product. -/
@[reassoc (attr := simp)]
theorem piFinSuccIso_hom_fst : (piFinSuccIso f).hom ≫ fst _ _ = Pi.π f 0 := by
  simp [piFinSuccIso]

/-- Coordinate `i` of the second component of `piFinSuccIso f` is coordinate `i + 1` of the
product. -/
@[reassoc (attr := simp)]
theorem piFinSuccIso_hom_snd_π (i : Fin n) :
    (piFinSuccIso f).hom ≫ snd _ _ ≫ Pi.π _ i = Pi.π f i.succ := by
  simp [piFinSuccIso]

/-- The inverse of `piFinSuccIso f` puts the first factor in coordinate `0`. -/
@[reassoc (attr := simp)]
theorem piFinSuccIso_inv_π_zero : (piFinSuccIso f).inv ≫ Pi.π f 0 = fst _ _ := by
  simp [piFinSuccIso]

/-- The inverse of `piFinSuccIso f` puts coordinate `i` of the second factor in coordinate
`i + 1`. -/
@[reassoc (attr := simp)]
theorem piFinSuccIso_inv_π_succ (i : Fin n) :
    (piFinSuccIso f).inv ≫ Pi.π f i.succ = snd _ _ ≫ Pi.π _ i := by
  simp [piFinSuccIso]

/-- On a point `(a₀, …, a_n)` with values in `T`, `piFinSuccIso f` gives `(a₀, (a₁, …, a_n))`. -/
@[reassoc (attr := simp)]
theorem lift_comp_piFinSuccIso_hom {T : C} (a : ∀ i, T ⟶ f i) :
    Pi.lift a ≫ (piFinSuccIso f).hom = lift (a 0) (Pi.lift fun i : Fin n => a i.succ) := by
  ext <;> simp

/-- On a point `(a₀, (a₁, …, a_n))` with values in `T`, the inverse of `piFinSuccIso f` gives
`(a₀, a₁, …, a_n)`. -/
@[reassoc (attr := simp)]
theorem lift_comp_piFinSuccIso_inv {T : C} (a₀ : T ⟶ f 0) (a : T ⟶ ∏ᶜ fun i : Fin n => f i.succ) :
    lift a₀ a ≫ (piFinSuccIso f).inv = Pi.lift (Fin.cons a₀ fun i => a ≫ Pi.π _ i) :=
  Pi.hom_ext _ _ fun i => by cases i using Fin.cases <;> simp

end CategoryTheory.CartesianMonoidalCategory
