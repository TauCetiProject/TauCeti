/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of short complexes

A retract `e : Retract S T` of short complexes is a retract in each degree, and its two maps are
retracts in the arrow category.

* `CategoryTheory.Retract.retract_τ₁`, `retract_τ₂`, `retract_τ₃`: the componentwise identities
  `e.i.τₙ ≫ e.r.τₙ = 𝟙`.
* `CategoryTheory.Retract.retractArrowF : RetractArrow S.f T.f` and
  `CategoryTheory.Retract.retractArrowG : RetractArrow S.g T.g`.
-/

public section

namespace CategoryTheory.Retract

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] {S T : ShortComplex C}
  (e : Retract S T)

/-- The first component of a retract of short complexes is a retract. -/
@[reassoc (attr := simp)]
lemma retract_τ₁ : e.i.τ₁ ≫ e.r.τ₁ = 𝟙 S.X₁ := by
  rw [← ShortComplex.comp_τ₁, e.retract, ShortComplex.id_τ₁]

/-- The second component of a retract of short complexes is a retract. -/
@[reassoc (attr := simp)]
lemma retract_τ₂ : e.i.τ₂ ≫ e.r.τ₂ = 𝟙 S.X₂ := by
  rw [← ShortComplex.comp_τ₂, e.retract, ShortComplex.id_τ₂]

/-- The third component of a retract of short complexes is a retract. -/
@[reassoc (attr := simp)]
lemma retract_τ₃ : e.i.τ₃ ≫ e.r.τ₃ = 𝟙 S.X₃ := by
  rw [← ShortComplex.comp_τ₃, e.retract, ShortComplex.id_τ₃]

/-- The first map of a retract of short complexes is a retract of the first map. -/
@[expose, simps]
def retractArrowF : RetractArrow S.f T.f where
  i := Arrow.homMk e.i.τ₁ e.i.τ₂ e.i.comm₁₂
  r := Arrow.homMk e.r.τ₁ e.r.τ₂ e.r.comm₁₂
  retract := Arrow.hom_ext _ _ (by simp) (by simp)

/-- The second map of a retract of short complexes is a retract of the second map. -/
@[expose, simps]
def retractArrowG : RetractArrow S.g T.g where
  i := Arrow.homMk e.i.τ₂ e.i.τ₃ e.i.comm₂₃
  r := Arrow.homMk e.r.τ₂ e.r.τ₃ e.r.comm₂₃
  retract := Arrow.hom_ext _ _ (by simp) (by simp)

end CategoryTheory.Retract
