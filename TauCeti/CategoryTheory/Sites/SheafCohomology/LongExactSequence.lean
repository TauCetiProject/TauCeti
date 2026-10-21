/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

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
  `H.subsingleton_X₁`, the vanishing consequences that the sequence is normally used for;
* `CategoryTheory.Sheaf.H.δ_surjective` and `H.δ_bijective`, the connecting map is onto, or an
  isomorphism, when the middle sheaf has no cohomology in the relevant degrees;
* `CategoryTheory.Sheaf.H'.postcomp_g_surjective`, `H'.subsingleton_X₃` and
  `H'.g_hom_app_surjective`, the corresponding statements for the cohomology `Hⁿ(V, -)` over an
  object `V` of the site, read off from the long exact `Ext` sequence out of the free abelian sheaf
  on `V`; the last is the degree zero case of the first, and says that
  sections over `V` of `F₂` map onto those of `F₃` when `H¹(V, F₁) = 0`, so that the sequence
  `0 ⟶ F₁(V) ⟶ F₂(V) ⟶ F₃(V) ⟶ 0` of sections is then short exact
  (`H'.shortExact_map_sheafSections`).

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
theorem map_g_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₁ n₁)) :
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
theorem subsingleton_X₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₂ n₀))
    (h₁ : Subsingleton (H S.X₁ n₁)) : Subsingleton (H S.X₃ n₀) :=
  (map_g_surjective hS n₀ n₁ h h₁).subsingleton

/-- If `Hⁿ⁰(F₃)` and `Hⁿ¹(F₂)` vanish, then so does `Hⁿ¹(F₁)`. -/
theorem subsingleton_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h₃ : Subsingleton (H S.X₃ n₀))
    (h₂ : Subsingleton (H S.X₂ n₁)) : Subsingleton (H S.X₁ n₁) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₃, hx₃⟩ := (exact_δ_map hS n₀ n₁ h x).1 (Subsingleton.elim _ _)
  obtain ⟨y₃, hy₃⟩ := (exact_δ_map hS n₀ n₁ h y).1 (Subsingleton.elim _ _)
  rw [← hx₃, ← hy₃, Subsingleton.elim x₃ y₃]

/-- If `Hⁿ¹(F₂)` vanishes, then the connecting map `Hⁿ⁰(F₃) →+ Hⁿ¹(F₁)` is surjective. -/
theorem δ_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₂ n₁)) :
    Function.Surjective (δ hS n₀ n₁ h) := fun x ↦
  (exact_δ_map hS n₀ n₁ h x).1 (Subsingleton.elim _ _)

/-- If `Hⁿ⁰(F₂)` and `Hⁿ¹(F₂)` vanish, then the connecting map `Hⁿ⁰(F₃) →+ Hⁿ¹(F₁)` is
bijective. -/
theorem δ_bijective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (_ : Subsingleton (H S.X₂ n₀))
    (h₁ : Subsingleton (H S.X₂ n₁)) : Function.Bijective (δ hS n₀ n₁ h) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, δ_surjective hS n₀ n₁ h h₁⟩
  obtain ⟨y, rfl⟩ := (exact_map_δ hS n₀ n₁ h x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

end H

namespace H'

open Opposite TauCeti.CategoryTheory

include hS

/-- If `Hⁿ⁺¹(V, F₁)` vanishes, then `Hⁿ(V, F₂) ⟶ Hⁿ(V, F₃)` is surjective. Here `Hⁿ(V, -)` is
`Ext` out of the free abelian sheaf on `V` (`TauCeti.CategoryTheory.sheafH'_eq`), and the map is
postcomposition with `F₂ ⟶ F₃`. -/
theorem postcomp_g_surjective (V : C) (n : ℕ) (h : Subsingleton (S.X₁.H' (n + 1) V)) :
    Function.Surjective
      ((Ext.mk₀ S.g).postcomp ((freeYonedaSheafFunctor J).obj V) (add_zero n)) := by
  have : Subsingleton (Ext ((freeYonedaSheafFunctor J).obj V) S.X₁ (n + 1)) := by
    simpa only [sheafH'_eq] using h
  exact fun x₃ ↦ Ext.covariant_sequence_exact₃ _ hS x₃ rfl (Subsingleton.elim _ _)

/-- If `Hⁿ(V, F₂)` and `Hⁿ⁺¹(V, F₁)` vanish, then so does `Hⁿ(V, F₃)`. -/
theorem subsingleton_X₃ (V : C) (n : ℕ) (h₂ : Subsingleton (S.X₂.H' n V))
    (h₁ : Subsingleton (S.X₁.H' (n + 1) V)) : Subsingleton (S.X₃.H' n V) := by
  have : Subsingleton (Ext ((freeYonedaSheafFunctor J).obj V) S.X₂ n) := by
    simpa only [sheafH'_eq] using h₂
  simpa only [sheafH'_eq] using (postcomp_g_surjective hS V n h₁).subsingleton

/-- If `H¹(V, F₁)` vanishes, then every section of `F₃` over `V` lifts to a section of `F₂`. -/
theorem g_hom_app_surjective (V : C) (h : Subsingleton (S.X₁.H' 1 V)) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  obtain ⟨x, hx⟩ := postcomp_g_surjective hS V 0 h
    (Ext.mk₀ ((freeYonedaSheafSectionsEquiv J V S.X₃).symm s))
  refine ⟨freeYonedaSheafSectionsEquiv J V S.X₂ (Ext.addEquiv₀ x), ?_⟩
  rw [← freeYonedaSheafSectionsEquiv_naturality_right]
  have hx' : Ext.addEquiv₀ x ≫ S.g = (freeYonedaSheafSectionsEquiv J V S.X₃).symm s :=
    (TauCeti.ext_addEquiv₀_comp_mk₀ x S.g).symm.trans <| (congrArg Ext.addEquiv₀ hx).trans <|
      Ext.addEquiv₀.apply_symm_apply _
  rw [hx', AddEquiv.apply_symm_apply]

/-- If `H¹(V, F₁)` vanishes, then the sequence of sections `0 ⟶ F₁(V) ⟶ F₂(V) ⟶ F₃(V) ⟶ 0` is
short exact. -/
theorem shortExact_map_sheafSections (V : C) (h : Subsingleton (S.X₁.H' 1 V)) :
    (S.map (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V))).ShortExact := by
  have := hS.mono_f
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
  · exact Functor.map_mono (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)) S.f
  · exact (AddCommGrpCat.epi_iff_surjective _).2 (g_hom_app_surjective hS V h)

end H'

end Sheaf

end CategoryTheory
