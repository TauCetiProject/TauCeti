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

Conversely, in a balanced preadditive category with a zero object, if `X ⟶ Y ⟶ Z` is exact with
an epimorphism `g` as second map, and postcomposing `g` with `h` leaves it exact, then `h` is a
monomorphism (`CategoryTheory.ShortComplex.Exact.mono_of_exact_comp`). Even without balance, the
first map of an exact `X ⟶ Y ⟶ Z` lifts to an epimorphism onto any kernel of the second
(`CategoryTheory.ShortComplex.Exact.epi_lift_of_isLimit`).

## Main results

* `CategoryTheory.ShortComplex.exact_mk_epi_comp_iff`: `X' ⟶ Y ⟶ Z` with first map `p ≫ f`, for an
  epimorphism `p`, is exact exactly when `X ⟶ Y ⟶ Z` with first map `f` is.
* `CategoryTheory.ShortComplex.exact_mk_comp_mono_iff`: `X ⟶ Y ⟶ Z'` with second map `g ≫ m`, for a
  monomorphism `m`, is exact exactly when `X ⟶ Y ⟶ Z` with second map `g` is.
* `CategoryTheory.ShortComplex.Exact.mono_of_exact_comp`: if `X ⟶ Y ⟶ Z` is exact with second map
  an epimorphism `g`, and so is `X ⟶ Y ⟶ Z'` with second map `g ≫ h`, then `h` is a monomorphism.
* `CategoryTheory.ShortComplex.Exact.epi_lift_of_isLimit`: the lift of the first map of an exact
  short complex to a kernel of its second map is an epimorphism.
-/

public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

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

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] [HasZeroObject C] {S : ShortComplex C}

/-- If `X ⟶ Y ⟶ Z` is exact, then the lift of its first map to any kernel of its second map is an
epimorphism. -/
theorem Exact.epi_lift_of_isLimit (hS : S.Exact) {kf : KernelFork S.g} (hkf : IsLimit kf) :
    Epi (hkf.lift (KernelFork.ofι S.f S.zero)) := by
  -- the lift is the map `f'` of the left homology data of `S` with cycles `kf`
  have e : (hS.leftHomologyDataOfIsLimitKernelFork kf hkf).f' =
      hkf.lift (KernelFork.ofι S.f S.zero) :=
    Fork.IsLimit.hom_ext hkf (by
      simpa using (hS.leftHomologyDataOfIsLimitKernelFork kf hkf).f'_i)
  exact e ▸ hS.epi_f' _

/-- If `X ⟶ Y ⟶ Z` is exact with an epimorphism `g : Y ⟶ Z` as second map, and postcomposing `g`
with `h : Z ⟶ Z'` leaves it exact, then `h` is a monomorphism. -/
theorem Exact.mono_of_exact_comp [Balanced C] (hS : S.Exact) [Epi S.g] {Z' : C} (h : S.X₃ ⟶ Z')
    (w : S.f ≫ S.g ≫ h = 0) (hS' : (ShortComplex.mk S.f (S.g ≫ h) w).Exact) : Mono h := by
  -- `h` is the map `g'` of the right homology data of `X ⟶ Y ⟶ Z'` with opcycles `g`
  have e : (hS'.rightHomologyDataOfIsColimitCokernelCofork _ hS.gIsCokernel).g' = h :=
    (cancel_epi S.g).1 (by
      simpa using (hS'.rightHomologyDataOfIsColimitCokernelCofork _ hS.gIsCokernel).p_g')
  exact e ▸ hS'.mono_g' _

end Preadditive

end CategoryTheory.ShortComplex
