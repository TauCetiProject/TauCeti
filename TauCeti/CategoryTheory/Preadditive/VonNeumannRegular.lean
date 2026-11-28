/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.VonNeumannRegular

import Mathlib.Algebra.BigOperators.Fin

/-!
# Von Neumann regular preadditive categories

A category is von Neumann regular if every morphism has an inner inverse.
In a regular preadditive category a finite family of arrows with common
source admits a common projection at that source, built from the arrows and
fixing each of them. The Jacobson radical of a regular category is zero.

See D. Simson, *On pure global dimension of locally finitely presented
Grothendieck categories*, §1, p. 93, for the inner-inverse condition.
-/

public section

open CategoryTheory Limits Opposite BigOperators

universe v u

namespace TauCeti

namespace IsVonNeumannRegularCategory

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [IsVonNeumannRegularCategory C]

/-- A finite row `β` in a von Neumann regular category admits an endomorphism of its
common source, of the form `∑ j, β j ≫ γ j`, that acts as the identity on the row. -/
theorem exists_sum_comp_comp_eq_self {X : C} {n : ℕ} {Y : Fin n → C}
    (β : ∀ j, X ⟶ Y j) : ∃ γ : ∀ j, Y j ⟶ X, ∀ k, (∑ j, β j ≫ γ j) ≫ β k = β k := by
  induction n with
  | zero => exact ⟨fun j ↦ j.elim0, fun k ↦ k.elim0⟩
  | succ n ih =>
    obtain ⟨γ, hγ⟩ := ih (fun j ↦ β j.succ)
    let e : X ⟶ X := ∑ j, β j.succ ≫ γ j
    have he (j : Fin n) : e ≫ β j.succ = β j.succ := hγ j
    -- Correct the projection for the tail by splitting off the residual head.
    let f := (𝟙 X - e) ≫ β 0
    obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f
    let a := g ≫ (𝟙 X - e)
    let γ' : ∀ j, Y j ⟶ X := Fin.cases a fun j ↦ γ j - γ j ≫ β 0 ≫ a
    have hsum : (∑ j, β j ≫ γ' j) = e + f ≫ a := by
      simp only [γ', Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, Preadditive.comp_sub,
        Finset.sum_sub_distrib, ← Category.assoc _ (γ _) _, ← Preadditive.sum_comp, f, e,
        Preadditive.sub_comp, Category.id_comp]
      simp only [Category.assoc]
      abel
    refine ⟨γ', Fin.cases ?_ fun j ↦ ?_⟩
    · have hfa : a ≫ β 0 = g ≫ f := Category.assoc _ _ _
      rw [hsum, Preadditive.add_comp, Category.assoc f a, hfa, hg]
      simp [f, Preadditive.sub_comp]
    · have hj : (𝟙 X - e) ≫ β j.succ = 0 := by simp [Preadditive.sub_comp, he]
      rw [hsum, Preadditive.add_comp, he]
      simp only [a, Category.assoc, hj, comp_zero, add_zero]

/-- Every radical morphism in a von Neumann regular preadditive category is zero. -/
@[simp] theorem jacobsonRadical_eq_bot (X Y : C) : jacobsonRadical X Y = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ AddSubgroup.mem_bot.mpr ?_
  obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f
  have := (mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp hf) g
  apply (cancel_epi (𝟙 X - f ≫ g)).mp
  rw [comp_zero, Preadditive.sub_comp, Category.id_comp, Category.assoc f g f, hg, sub_self]

/-- The Jacobson radical ideal vanishes in a von Neumann regular preadditive category. -/
@[simp] theorem jacobsonRadicalIdeal_eq_bot : jacobsonRadicalIdeal C = ⊥ := by
  ext X Y f
  simp

end IsVonNeumannRegularCategory

end TauCeti
