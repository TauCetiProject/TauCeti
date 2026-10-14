/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Ideal
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ProjectiveBasis
import TauCeti.Algebra.Category.GradedModuleCat.Free
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.ObjectProperty.Retract
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Exhausting graded projectives with homogeneous idempotents

For a finite-dimensional graded algebra, a complete family of homogeneous degree-zero
idempotents whose associated graded ideals are indecomposable meets every finite graded
indecomposable projective up to shift. Consequently their classes span the actual Laurent
Grothendieck group of graded projectives.

A finite graded free cover splits over a projective. Resolving each of its regular summands
using the complete idempotents expresses the identity of the projective as a finite sum of
maps through shifted idempotent ideals. Its local endomorphism ring makes one summand
invertible, and indecomposability of that ideal turns the resulting retract into an isomorphism.
This argument needs no positivity assumption on the grading.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* H. Krause, "Krull–Schmidt categories and projective covers", *Expositiones Mathematicae*
  **33** (2015), 535–549.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped _root_.DirectSum

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {I : Type uI} [Fintype I] {e : I → A}
  (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)

private abbrev idempotentProjective (i : I) :
    (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
    gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩

section FreeCoordinates

variable {J : Type uA} [Fintype J] (d : J → ℤ)

private def freeIdempotentProjection (r : J) (i : I) :
    GradedModuleCat.free 𝒜 d ⟶ (idempotentProjective he hI i).obj.shiftObj (d r) := by
  let f := (LinearMap.mulRight A (e i)).comp (DirectSum.component A J (fun _ => A) r)
  refine GradedModuleCat.ofHom (f.codRestrict (Ideal.span {e i}) fun x => ?_)
    (LinearMap.isHomogeneous_def.2 fun p x hx => ?_)
  · exact (mem_span_singleton_iff_mul_eq_self (he.idem i)).2
      (by simp only [f, LinearMap.comp_apply, LinearMap.mulRight_apply, mul_assoc,
        (he.idem i).eq])
  · rw [add_zero, GradedModuleCat.mem_shiftObj_piece_iff,
      GradedModuleCat.mem_ofIdeal_piece_iff (hI i)]
    have hx' := (GradedModuleCat.mem_free_piece_iff 𝒜 d p x).1 hx r
    -- The codomain restriction changes the subtype but not the projected algebra element.
    change x r * e i ∈ 𝒜 (p - d r)
    simpa only [add_zero] using
      SetLike.GradedMul.mul_mem hx' (he₀ i)

private def freeIdempotentInclusion (r : J) (i : I) :
    (idempotentProjective he hI i).obj.shiftObj (d r) ⟶ GradedModuleCat.free 𝒜 d := by
  classical
  refine GradedModuleCat.ofHom
    ((DirectSum.lof A J (fun _ => A) r).comp (Ideal.span {e i} : Ideal A).subtype)
    (LinearMap.isHomogeneous_def.2 fun p x hx => ?_)
  rw [add_zero, GradedModuleCat.mem_free_piece_iff]
  have hx' := (GradedModuleCat.mem_ofIdeal_piece_iff (hI i)).1
    ((GradedModuleCat.mem_shiftObj_piece_iff
      (idempotentProjective he hI i).obj (d r) p x).1 hx)
  intro s
  by_cases h : r = s
  · subst s
    simpa using hx'
  · simp [LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.of_apply, h]

private theorem sum_freeIdempotentProjection_inclusion :
    ∑ r : J, ∑ i : I,
      freeIdempotentProjection he he₀ hI d r i ≫ freeIdempotentInclusion he hI d r i =
        𝟙 (GradedModuleCat.free 𝒜 d) := by
  classical
  apply GradedModuleCat.hom_ext
  let H : (GradedModuleCat.free 𝒜 d ⟶ GradedModuleCat.free 𝒜 d) →+
      (GradedModuleCat.free 𝒜 d →ₗ[A] GradedModuleCat.free 𝒜 d) :=
    ⟨⟨fun f => f.hom, rfl⟩, fun _ _ => rfl⟩
  -- Package the underlying-map projection additively to move it through the finite sums.
  change H (∑ r : J, ∑ i : I, _) = LinearMap.id
  simp only [map_sum]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.id_apply]
  apply DFinsupp.ext
  intro s
  -- The concrete free-module coordinates retain the same direct-sum carrier under shift.
  change (∑ r : J, ∑ i : I, DirectSum.lof A J (fun _ => A) r (x r * e i)) s = x s
  simp only [DirectSum.sum_apply]
  simp only [DirectSum.lof_eq_of, DirectSum.of_apply, Finset.sum_dite_irrel,
    Finset.sum_const_zero, Finset.sum_dite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, he.complete, mul_one]

end FreeCoordinates

variable [Module.Finite k A]

include he₀ in
/-- A complete family of homogeneous degree-zero idempotents whose graded ideals are
indecomposable exhausts all finite graded indecomposable projectives up to internal shift. -/
theorem isExhaustiveGradedIndecomposableProjectiveFamily_of_completeOrthogonalIdempotents
    (hind : ∀ i, Indecomposable
      (⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
        gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩ :
          (gradedFiniteProjectiveModules 𝒜).FullSubcategory)) :
    IsExhaustiveGradedIndecomposableProjectiveFamily (fun i =>
      ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
        gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩) := by
  classical
  rw [isExhaustiveGradedIndecomposableProjectiveFamily_iff]
  intro M hM
  -- Split a finite homogeneous free cover using projectivity of the underlying module.
  obtain ⟨J, hJ, d, π, hπ⟩ := GradedModuleCat.exists_finite_free_surjection M.obj
  have : Finite J := hJ
  let : Fintype J := Fintype.ofFinite J
  have : Epi π := (GradedModuleCat.epi_iff_surjective π).2 hπ
  let σ := Projective.factorThru (𝟙 M.obj) π
  have hσ : σ ≫ π = 𝟙 M.obj := Projective.factorThru_comp _ _
  let P (r : J) (i : I) : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
    ⟨(idempotentProjective he hI i).obj.shiftObj (d r),
      gradedFiniteProjectiveModules_shiftObj (idempotentProjective he hI i).property (d r)⟩
  let α (r : J) (i : I) : M ⟶ P r i :=
    ObjectProperty.homMk (σ ≫ freeIdempotentProjection he he₀ hI d r i)
  let β (r : J) (i : I) : P r i ⟶ M :=
    ObjectProperty.homMk (freeIdempotentInclusion he hI d r i ≫ π)
  -- Completeness resolves the identity through the finitely many shifted idempotent ideals.
  have hsum : ∑ r : J, ∑ i : I, α r i ≫ β r i = 𝟙 M := by
    apply ObjectProperty.hom_ext
    -- Full-subcategory morphisms have the same additive underlying graded maps.
    change InducedCategory.homLinearEquiv (R := k) (∑ r : J, ∑ i : I, _) = 𝟙 M.obj
    simp only [map_sum]
    -- Expand only the two lifted morphisms, retaining their categorical compositions.
    change ∑ r : J, ∑ i : I,
      (σ ≫ freeIdempotentProjection he he₀ hI d r i) ≫
        (freeIdempotentInclusion he hI d r i ≫ π) = 𝟙 M.obj
    calc
      _ = σ ≫ ((∑ r : J, ∑ i : I,
          freeIdempotentProjection he he₀ hI d r i ≫
            freeIdempotentInclusion he hI d r i) ≫ π) := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 M.obj := by
        rw [sum_freeIdempotentProjection_inclusion he he₀ hI d, Category.id_comp, hσ]
  have : IsLocalRing (End M) := isLocalRing_end_of_indecomposable (k := k) hM
  -- A sum equal to the identity in the local endomorphism ring has an invertible summand.
  have hunit : IsUnit (∑ r : J, ∑ i : I, α r i ≫ β r i : End M) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨r, -, hr⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum hr
  have hcomp : IsIso (α r i ≫ β r i) := (isUnit_iff_isIso _).1 hi
  have hP : Indecomposable (P r i) := indecomposable_shiftObj (hind i) (d r)
  -- The corresponding retract of an indecomposable ideal is the entire ideal.
  have hα : IsIso (α r i) := isIso_of_isIso_comp
    (fun h => hM.1 ((IsZero.iff_id_eq_zero M).2 h))
    (fun f hf => idempotent_eq_zero_or_id_of_indecomposable hP hf) (α r i) (β r i) hcomp
  exact ⟨i, d r, ⟨asIso (α r i)⟩⟩

end TauCeti
