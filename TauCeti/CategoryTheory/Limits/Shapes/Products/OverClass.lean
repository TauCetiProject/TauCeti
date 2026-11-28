/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of objects over a base

A coproduct of objects over `S` has a structure morphism obtained by descending those of its
summands. Its coprojections and the descent of any family of morphisms over `S` are morphisms
over `S`. This allows coproduct constructions to use the `OverClass` API without repackaging
their commutative squares.
-/

public section

universe u v w

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {ι : Type w} (X : ι → C) [HasCoproduct X]
  (S : C) [∀ i, OverClass (X i) S]

/-- The coproduct structure map descends the specified structure maps of its summands. -/
noncomputable instance instOverSigma : OverClass (∐ X) S :=
  ⟨Sigma.desc fun i ↦ X i ↘ S⟩

/-- The structure map of a coproduct is the descent of the summands' structure maps. -/
theorem over_sigma : (∐ X) ↘ S = Sigma.desc fun i ↦ X i ↘ S := (rfl)

/-- Coprojections are morphisms over the common base. The simp lemmas `comp_over` and
`comp_over_assoc` compute their composites with the descended structure map. -/
instance instHomIsOverSigmaι (i : ι) : HomIsOver (Sigma.ι X i) S :=
  ⟨by rw [over_sigma, Sigma.ι_comp_desc]⟩

/-- Descending a family of morphisms over a common base gives a morphism over that base. -/
instance instHomIsOverSigmaDesc {Y : C} [OverClass Y S] (f : ∀ i, X i ⟶ Y)
    [∀ i, HomIsOver (f i) S] : HomIsOver (Sigma.desc f) S := by
  constructor
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_comp_desc_assoc, comp_over]

end CategoryTheory
