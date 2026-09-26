/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Consequences of the long exact cohomology sequence of abelian sheaves

Mathlib's `CategoryTheory.Sheaf.H.longSequence` is the long exact cohomology sequence

`⋯ ⟶ Hⁿ⁰(F₁) ⟶ Hⁿ⁰(F₂) ⟶ Hⁿ⁰(F₃) ⟶ Hⁿ¹(F₁) ⟶ Hⁿ¹(F₂) ⟶ Hⁿ¹(F₃) ⟶ ⋯`

of a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves on a site `(C, J)`, as a
`ComposableArrows` in `AddCommGrpCat`. This file repackages the exactness of the three
consecutive pairs as `Function.Exact` statements about the underlying additive maps, which is the
form in which the sequence is used, and records the injectivity and vanishing consequences that
follow from it.

## Main declarations

* `CategoryTheory.Sheaf.H.map_injective`, the injectivity of `H⁰(F₁) →+ H⁰(F₂)`, which is where
  the sequence starts;
* `CategoryTheory.Sheaf.H.exact_map_map`, `H.exact_map_δ` and `H.exact_δ_map`, the exactness of
  the sequence at `Hⁿ(F₂)`, at `Hⁿ⁰(F₃)` and at `Hⁿ¹(F₁)`;
* `CategoryTheory.Sheaf.H.map_g_surjective`, `H.subsingleton_X₂`, `H.subsingleton_X₃` and
  `H.subsingleton_X₁`, the vanishing consequences that the sequence is normally used for.

The underlying exactness statements are Mathlib's `CategoryTheory.Sheaf.H.longSequence_exact₁'`,
`longSequence_exact₂'` and `longSequence_exact₃'`. Sheaf cohomology on the small Zariski site of a
scheme is the cohomology of a sheaf of modules; the module-level form of the sequence is in
`TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence`.
-/

public section

open CategoryTheory Abelian

universe w v u

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

namespace H

/-- A monomorphism of abelian sheaves is injective on cohomology in degree zero. -/
theorem map_injective {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f] :
    Function.Injective (map f 0) := by
  intro x y hxy
  apply (Ext.addEquiv₀ (C := Sheaf J AddCommGrpCat.{v})).injective
  rw [← cancel_mono f, ← addEquiv₀_map, ← addEquiv₀_map, hxy]

include hS

/-- The long exact cohomology sequence is exact at `Hⁿ(F₂)`. -/
theorem exact_map_map (n : ℕ) : Function.Exact (map S.f n) (map S.g n) := by
  have := longSequence_exact₂' hS n
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact cohomology sequence is exact at `Hⁿ⁰(F₃)`. -/
theorem exact_map_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (map S.g n₀) (δ hS n₀ n₁ h) := by
  have := longSequence_exact₃' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact cohomology sequence is exact at `Hⁿ¹(F₁)`. -/
theorem exact_δ_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) := by
  have := longSequence_exact₁' hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- If `Hⁿ¹(F₁)` vanishes, then `Hⁿ⁰(F₂) →+ Hⁿ⁰(F₃)` is surjective. -/
theorem map_g_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h₁ : Subsingleton (H S.X₁ n₁)) :
    Function.Surjective (map S.g n₀) := fun x ↦
  (exact_map_δ hS n₀ n₁ h x).1 (Subsingleton.elim _ _)

/-- If `Hⁿ(F₁)` and `Hⁿ(F₃)` vanish, then so does `Hⁿ(F₂)`. -/
theorem subsingleton_X₂ (n : ℕ) (h₁ : Subsingleton (H S.X₁ n))
    (h₃ : Subsingleton (H S.X₃ n)) : Subsingleton (H S.X₂ n) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₁, hx₁⟩ := (exact_map_map hS n x).1 (Subsingleton.elim _ _)
  obtain ⟨y₁, hy₁⟩ := (exact_map_map hS n y).1 (Subsingleton.elim _ _)
  rw [← hx₁, ← hy₁, Subsingleton.elim x₁ y₁]

/-- If `Hⁿ⁰(F₂)` and `Hⁿ¹(F₁)` vanish, then so does `Hⁿ⁰(F₃)`. -/
theorem subsingleton_X₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h₂ : Subsingleton (H S.X₂ n₀))
    (h₁ : Subsingleton (H S.X₁ n₁)) : Subsingleton (H S.X₃ n₀) :=
  (map_g_surjective hS n₀ n₁ h h₁).subsingleton

/-- If `Hⁿ⁰(F₃)` and `Hⁿ¹(F₂)` vanish, then so does `Hⁿ¹(F₁)`. -/
theorem subsingleton_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h₃ : Subsingleton (H S.X₃ n₀))
    (h₂ : Subsingleton (H S.X₂ n₁)) : Subsingleton (H S.X₁ n₁) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₃, hx₃⟩ := (exact_δ_map hS n₀ n₁ h x).1 (Subsingleton.elim _ _)
  obtain ⟨y₃, hy₃⟩ := (exact_δ_map hS n₀ n₁ h y).1 (Subsingleton.elim _ _)
  rw [← hx₃, ← hy₃, Subsingleton.elim x₃ y₃]

end H

end Sheaf

end CategoryTheory
