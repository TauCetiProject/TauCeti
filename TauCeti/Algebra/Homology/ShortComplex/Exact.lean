/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness under composition with epimorphisms and monomorphisms

A short complex `X ⟶ Y ⟶ Z` stays exact, and reflects exactness, when its first map is
precomposed with an epimorphism (`CategoryTheory.ShortComplex.exact_mk_epi_comp_iff`) or its second
map is postcomposed with a monomorphism (`CategoryTheory.ShortComplex.exact_mk_comp_mono_iff`).
Both are the case of `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono` in which the
middle component is the identity.

## Main results

* `CategoryTheory.ShortComplex.exact_mk_epi_comp_iff`: `X' ⟶ Y ⟶ Z` with first map `p ≫ f`, for an
  epimorphism `p`, is exact exactly when `X ⟶ Y ⟶ Z` with first map `f` is.
* `CategoryTheory.ShortComplex.exact_mk_comp_mono_iff`: `X ⟶ Y ⟶ Z'` with second map `g ≫ m`, for a
  monomorphism `m`, is exact exactly when `X ⟶ Y ⟶ Z` with second map `g` is.
-/

public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- Precomposing the first map of a short complex with an epimorphism does not change exactness. -/
theorem exact_mk_epi_comp_iff {X' X Y Z : C} (p : X' ⟶ X) [Epi p] (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (p ≫ f) ≫ g = 0) (w' : f ≫ g = 0) :
    (ShortComplex.mk (p ≫ f) g w).Exact ↔ (ShortComplex.mk f g w').Exact :=
  exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := p, τ₂ := 𝟙 Y, τ₃ := 𝟙 Z, comm₁₂ := by simp, comm₂₃ := by simp }

/-- Postcomposing the second map of a short complex with a monomorphism does not change
exactness. -/
theorem exact_mk_comp_mono_iff {X Y Z Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (m : Z ⟶ Z') [Mono m]
    (w : f ≫ g ≫ m = 0) (w' : f ≫ g = 0) :
    (ShortComplex.mk f (g ≫ m) w).Exact ↔ (ShortComplex.mk f g w').Exact :=
  (exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 X, τ₂ := 𝟙 Y, τ₃ := m, comm₁₂ := by simp, comm₂₃ := by simp }).symm

end CategoryTheory.ShortComplex
