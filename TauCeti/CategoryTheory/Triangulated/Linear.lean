/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finiteness of Hom modules across distinguished triangles

In an `R`-linear pretriangulated category `C`, the representable Hom functors `Z ⟶ -` and `- ⟶ Z`
send a distinguished triangle `T` to a half-exact sequence of `R`-modules. Because the rightmost
map `(Z ⟶ T.obj₂) →ₗ[R] (Z ⟶ T.obj₃)` (or `(T.obj₂ ⟶ Z) →ₗ[R] (T.obj₁ ⟶ Z)`) need not be
surjective, finite generation of the middle Hom module requires finite generation of its image
inside the outer Hom module, which is guaranteed when that outer Hom module is Noetherian:

* `CategoryTheory.Pretriangulated.Triangle.moduleFinite_hom_of_distTriang_right`: if `T` is
  distinguished, `Z ⟶ T.obj₁` is a finite `R`-module, and `Z ⟶ T.obj₃` is a Noetherian
  `R`-module, then `Z ⟶ T.obj₂` is a finite `R`-module.
* `CategoryTheory.Pretriangulated.Triangle.moduleFinite_hom_of_distTriang_left`: dually in the
  contravariant variable, if `T.obj₃ ⟶ Z` is finite and `T.obj₁ ⟶ Z` is Noetherian, then
  `T.obj₂ ⟶ Z` is finite.

Together with the linear truncation equivalences in
`TauCeti.CategoryTheory.Triangulated.TStructure.Linear`, these lemmas supply the triangle-induction
step for Hom finiteness in derived categories
(`TauCeti.Algebra.Homology.DerivedCategory.FiniteHom`).
-/

public section

open CategoryTheory Limits

universe t' v u

namespace CategoryTheory.Pretriangulated

variable {R : Type t'} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  [Linear R C]

/-- If `T` is a distinguished triangle in an `R`-linear pretriangulated category, `Z ⟶ T.obj₁` is
a finite `R`-module and `Z ⟶ T.obj₃` is a Noetherian `R`-module, then `Z ⟶ T.obj₂` is a finite
`R`-module. -/
theorem Triangle.moduleFinite_hom_of_distTriang_right (T : Triangle C) (hT : T ∈ distTriang C)
    (Z : C) [Module.Finite R (Z ⟶ T.obj₁)] [IsNoetherian R (Z ⟶ T.obj₃)] :
    Module.Finite R (Z ⟶ T.obj₂) := by
  let f : (Z ⟶ T.obj₁) →ₗ[R] (Z ⟶ T.obj₂) := Linear.rightComp R Z T.mor₁
  let g : (Z ⟶ T.obj₂) →ₗ[R] (Z ⟶ T.obj₃) := Linear.rightComp R Z T.mor₂
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, f, g, Linear.rightComp_apply]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
    · obtain ⟨y, hy⟩ := T.coyoneda_exact₂ hT x hx
      exact ⟨y, hy.symm⟩
    · rw [← hy, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  exact ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g
    (by rw [Submodule.map_top]; exact IsNoetherian.noetherian _)
    (by
      rw [top_inf_eq, LinearMap.exact_iff.mp hfg, LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map f)⟩

/-- If `T` is a distinguished triangle in an `R`-linear pretriangulated category, `T.obj₃ ⟶ Z` is
a finite `R`-module and `T.obj₁ ⟶ Z` is a Noetherian `R`-module, then `T.obj₂ ⟶ Z` is a finite
`R`-module. -/
theorem Triangle.moduleFinite_hom_of_distTriang_left (T : Triangle C) (hT : T ∈ distTriang C)
    (Z : C) [Module.Finite R (T.obj₃ ⟶ Z)] [IsNoetherian R (T.obj₁ ⟶ Z)] :
    Module.Finite R (T.obj₂ ⟶ Z) := by
  let f : (T.obj₃ ⟶ Z) →ₗ[R] (T.obj₂ ⟶ Z) := Linear.leftComp R Z T.mor₂
  let g : (T.obj₂ ⟶ Z) →ₗ[R] (T.obj₁ ⟶ Z) := Linear.leftComp R Z T.mor₁
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, f, g, Linear.leftComp_apply]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
    · obtain ⟨y, hy⟩ := T.yoneda_exact₂ hT x hx
      exact ⟨y, hy.symm⟩
    · rw [← hy, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  exact ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g
    (by rw [Submodule.map_top]; exact IsNoetherian.noetherian _)
    (by
      rw [top_inf_eq, LinearMap.exact_iff.mp hfg, LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map f)⟩

end CategoryTheory.Pretriangulated
