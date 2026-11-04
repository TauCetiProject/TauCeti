/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Ideal
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ProjectiveBasis
import TauCeti.Algebra.Category.GradedModuleCat.Free
import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.ObjectProperty.Retract
import TauCeti.RingTheory.GradedAlgebra.Basic
import TauCeti.RingTheory.Idempotents.Hom
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

If the `eᵢ` are moreover primitive idempotents of `A` whose ungraded left ideals `A eᵢ` are
pairwise nonisomorphic, then the classes `[A eᵢ]` form a basis of `K₀^gr(proj A)` over
`ℤ[q,q⁻¹]`. A graded endomorphism or isomorphism is in particular an `A`-linear one, so
indecomposability of the ungraded module `A eᵢ` makes the graded module `A eᵢ` indecomposable,
and nonisomorphic ungraded modules `A eᵢ`, `A eⱼ` are not isomorphic up to any internal shift.
These hypotheses involve no grading positivity and no splitting: the degree-zero corners
`eᵢ A eᵢ ∩ 𝒜 0` need not be the lines `k eᵢ`, so the field need not split the simple modules.

If `A` is nonnegatively graded and its degree-zero piece is spanned by the nonzero
idempotents `eᵢ`, both hypotheses hold. The degree-zero part of the corner `eᵢ A eᵢ` is `k eᵢ`,
and an idempotent of `A` without degree-zero component vanishes
(`TauCeti.GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero`), so each `eᵢ` is
primitive. An isomorphism `A eᵢ ≃ A eⱼ` with `i ≠ j` would write `eᵢ = x y` with `x ∈ eᵢ A eⱼ`,
while off-diagonal corners live in positive degrees, so the degree-zero component of `x y`
vanishes. This is the projective counterpart of the basis of graded heads.

## Main definitions

* `TauCeti.gradedIdempotentProjectiveBasisOfPrimitive`: the basis `[A eᵢ]` of `K₀^gr(proj A)` for
  primitive idempotents with pairwise nonisomorphic left ideals.
* `TauCeti.gradedIdempotentProjectiveBasis`: the same basis when the degree-zero piece of a
  nonnegatively graded algebra is spanned by the `eᵢ`.

## Main results

* `TauCeti.isExhaustiveGradedIndecomposableProjectiveFamily_of_completeOrthogonalIdempotents`:
  indecomposable idempotent ideals `A eᵢ` exhaust the finite graded indecomposable projectives.
* `TauCeti.indecomposable_ofIdeal_span_singleton`: the graded projective `A f` of a primitive
  idempotent `f` is indecomposable.
* `TauCeti.cornerSubmodule_inf_zero_eq_span_singleton` and
  `TauCeti.pos_of_mem_cornerSubmodule_inf`: if the degree-zero piece of a nonnegatively graded
  algebra is spanned by orthogonal idempotents, its diagonal corners are `k eᵢ` in degree zero
  and its off-diagonal corners live in positive degrees.
* `TauCeti.coe_decompose_mem_cornerSubmodule`: the homogeneous components of an element of a
  corner `aAb` cut out by idempotents of degree zero lie in that corner.
* `TauCeti.isPrimitiveIdempotent_of_gradeZero_le_span`: each `eᵢ` is a primitive idempotent of
  `A`.
* `TauCeti.isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span`: the ungraded modules `A eᵢ`
  are pairwise nonisomorphic.

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

/-! ### Homogeneous components in corners -/

section CornerComponents

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- The homogeneous components of an element of the corner `aAb` cut out by two idempotents of
degree zero lie in the same corner. -/
theorem coe_decompose_mem_cornerSubmodule {a b x : A} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) (ha₀ : a ∈ 𝒜 0) (hb₀ : b ∈ 𝒜 0)
    (hx : x ∈ cornerSubmodule k a b) (p : ℤ) :
    (DirectSum.decompose 𝒜 x p : A) ∈ cornerSubmodule k a b := by
  rw [mem_cornerSubmodule_iff k ha hb] at hx ⊢
  rw [← DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 ha₀,
    ← DirectSum.coe_decompose_mul_of_right_mem_zero 𝒜 hb₀, hx]

end CornerComponents

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

/-! ### Degree-zero corners -/

section Corner

variable (ho : OrthogonalIdempotents e) (hneg : ∀ p < 0, 𝒜 p = ⊥)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))

omit [GradedAlgebra 𝒜] [Fintype I] in
include ho he₀ hspan in
/-- **The degree-zero part of a diagonal corner is the line through the idempotent**: if the
degree-zero piece of `A` is spanned by the orthogonal idempotents `eᵢ`, then
`eᵢ A eᵢ ∩ 𝒜 0 = k eᵢ`. -/
theorem cornerSubmodule_inf_zero_eq_span_singleton (i : I) :
    cornerSubmodule k (e i) (e i) ⊓ 𝒜 0 = Submodule.span k {e i} := by
  ext x
  rw [Submodule.mem_inf, mem_cornerSubmodule_iff k (ho.idem i) (ho.idem i),
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hc, hx⟩
    have hxi : x ∈ (Ideal.span {e i} : Ideal A) :=
      (mem_span_singleton_iff_mul_eq_self (ho.idem i)).2
        (by rw [← hc, mul_assoc, (ho.idem i).eq])
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_mem_zero ho hspan hx hxi
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨?_, Submodule.smul_mem _ c (he₀ i)⟩
    rw [mul_smul_comm, smul_mul_assoc, (ho.idem i).eq, (ho.idem i).eq]

omit [GradedAlgebra 𝒜] [Fintype I] in
include hneg ho hspan in
/-- **Off-diagonal corners live in positive degrees**: in a nonnegatively graded algebra whose
degree-zero piece is spanned by the orthogonal idempotents `eᵢ`, a nonzero homogeneous element
of `eᵢ A eⱼ` with `i ≠ j` has positive degree. -/
theorem pos_of_mem_cornerSubmodule_inf {i j : I} (hij : i ≠ j) {p : ℤ} {x : A}
    (hx : x ∈ cornerSubmodule k (e i) (e j) ⊓ 𝒜 p) (hx₀ : x ≠ 0) : 0 < p := by
  rw [Submodule.mem_inf, mem_cornerSubmodule_iff k (ho.idem i) (ho.idem j)] at hx
  obtain ⟨hc, hx⟩ := hx
  by_contra! hp
  rcases hp.lt_or_eq with hp | rfl
  · rw [hneg p hp, Submodule.mem_bot] at hx
    exact hx₀ hx
  · have hxj : x ∈ (Ideal.span {e j} : Ideal A) :=
      (mem_span_singleton_iff_mul_eq_self (ho.idem j)).2
        (by rw [← hc, mul_assoc, (ho.idem j).eq])
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_mem_zero ho hspan hx hxj
    apply hx₀
    rw [← hc, mul_smul_comm, ho.ortho hij, smul_zero, zero_mul]

omit [Fintype I] in
include ho he₀ hneg hspan in
open _root_.DirectSum in
/-- **Each `eᵢ` is a primitive idempotent of `A`** when `A` is nonnegatively graded and its
degree-zero piece is spanned by the orthogonal idempotents `eᵢ`. -/
theorem isPrimitiveIdempotent_of_gradeZero_le_span (i : I) (hne : e i ≠ 0) :
    IsPrimitiveIdempotent (e i) := by
  have hei := ho.idem i
  refine isPrimitiveIdempotent_of_eq_zero_or_eq hei hne fun f hf hef hfe => ?_
  -- The degree-zero component of `f` is an idempotent of `eᵢ A eᵢ ∩ 𝒜 0 = k eᵢ`, hence `0` or
  -- `eᵢ`; accordingly `f` or `eᵢ - f` is an idempotent without degree-zero component.
  have hmem : (decompose 𝒜 f 0 : A) ∈ cornerSubmodule k (e i) (e i) ⊓ 𝒜 0 :=
    ⟨coe_decompose_mem_cornerSubmodule hei hei (he₀ i) (he₀ i)
      ((mem_cornerSubmodule_iff k hei hei).2 (by rw [hef, hfe])) 0, (decompose 𝒜 f 0).2⟩
  rw [cornerSubmodule_inf_zero_eq_span_singleton he₀ ho hspan i,
    Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcc : c * c = c := by
    have h := GradedAlgebra.coe_decompose_mul_zero_of_nonneg hneg f f
    rw [hf.eq, ← hc, smul_mul_smul_comm, hei.eq] at h
    exact smul_left_injective k hne h.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hcc with rfl | rfl
  · exact .inl (GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero hneg hf
      (by rw [← hc, zero_smul]))
  · refine .inr (sub_eq_zero.1 ?_).symm
    refine GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero hneg
      (hf.sub hei hfe hef) ?_
    rw [decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, decompose_of_mem_same 𝒜 (he₀ i),
      ← hc, one_smul, sub_self]

omit [Fintype I] in
include ho he₀ hneg hspan in
open _root_.DirectSum in
/-- **The ungraded modules `A eᵢ` are pairwise nonisomorphic** when `A` is nonnegatively graded
and its degree-zero piece is spanned by the orthogonal idempotents `eᵢ`. -/
theorem isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span {i j : I} (hij : i ≠ j)
    (hi : e i ≠ 0) :
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)) := by
  -- `φ` and its inverse send the generators to `x ∈ eᵢ A eⱼ` and `y ∈ eⱼ A eᵢ` with `eᵢ = x y`;
  -- the degree-zero component of `x` lies in `eᵢ A eⱼ ∩ 𝒜 0 = 0`, so that of `x y` vanishes.
  refine ⟨fun φ => hi ?_⟩
  set x : A := (φ (spanSingletonGenerator (e i)) : A) with hxdef
  have hx : x ∈ cornerSubmodule k (e i) (e j) :=
    apply_generator_mem_cornerSubmodule (ho.idem i) φ.toLinearMap
  have hxy : e i = x * (φ.symm (spanSingletonGenerator (e j)) : A) := by
    have h := coe_apply_eq_mul_apply_generator (ho.idem j) φ.symm.toLinearMap
      (φ (spanSingletonGenerator (e i)))
    simpa using h
  have hx₀ : (decompose 𝒜 x 0 : A) = 0 := by
    by_contra h
    exact lt_irrefl 0 (pos_of_mem_cornerSubmodule_inf ho hneg hspan hij
      ⟨coe_decompose_mem_cornerSubmodule (ho.idem i) (ho.idem j) (he₀ i) (he₀ j) hx 0,
        (decompose 𝒜 x 0).2⟩ h)
  rw [← decompose_of_mem_same 𝒜 (he₀ i), hxy, GradedAlgebra.coe_decompose_mul_zero_of_nonneg hneg,
    hx₀, zero_mul]

end Corner

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
  have : IsLocalRing (End M) := isLocalRing_end_of_indecomposable (R := k) hM
  -- A sum equal to the identity in the local endomorphism ring has an invertible summand.
  have hunit : IsUnit (∑ r : J, ∑ i : I, End.of (α r i ≫ β r i)) := by
    convert isUnit_one (M := End M)
    apply End.ext
    simpa only [End.sum_asHom, End.one_asHom] using hsum
  obtain ⟨r, -, hr⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum hr
  have hcomp : IsIso (α r i ≫ β r i) := (isUnit_iff_isIso _).1 hi
  have hP : Indecomposable (P r i) := indecomposable_shiftObj (hind i) (d r)
  -- The corresponding retract of an indecomposable ideal is the entire ideal.
  have hα : IsIso (α r i) := isIso_of_isIso_comp
    (fun h => hM.1 ((IsZero.iff_id_eq_zero M).2 h))
    (fun f hf => idempotent_eq_zero_or_id_of_indecomposable hP hf) (α r i) (β r i) hcomp
  exact ⟨i, d r, ⟨asIso (α r i)⟩⟩

/-! ### The idempotent projective basis -/

section Basis

omit [Module.Finite k A] in
/-- **The graded projective `A f` of a primitive idempotent `f` is indecomposable.** A graded
endomorphism of `A f` is in particular an `A`-linear endomorphism, and `A f` is an indecomposable
module (`TauCeti.IsPrimitiveIdempotent.isIndecomposableModule`), so its only idempotent graded
endomorphisms are `0` and the identity. No hypothesis on the grading is needed. -/
theorem indecomposable_ofIdeal_span_singleton {f : A} (hf : IsPrimitiveIdempotent f)
    (hfI : (Ideal.span {f} : Ideal A).IsHomogeneous 𝒜) :
    Indecomposable (⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {f}) hfI,
      gradedFiniteProjectiveModules_ofIdeal_span_singleton hf.isIdempotentElem hfI⟩ :
        (gradedFiniteProjectiveModules 𝒜).FullSubcategory) := by
  have hind := hf.isIndecomposableModule
  refine indecomposable_of_idempotent_eq_zero_or_id (fun h => ?_) fun φ hφ => ?_
  · -- The underlying module of a zero object would be trivial.
    have := hind.nontrivial
    exact not_subsingleton (Ideal.span {f} : Ideal A) (ModuleCat.isZero_iff_subsingleton.1
      (((gradedFiniteProjectiveModules 𝒜).ι ⋙ GradedModuleCat.toModuleCat).map_isZero h))
  · -- Composition of graded maps is composition of the underlying linear maps.
    have hφ' : IsIdempotentElem φ.hom.hom := by
      rw [IsIdempotentElem, Module.End.mul_eq_comp]
      simpa only [ObjectProperty.FullSubcategory.comp_hom, GradedModuleCat.hom_comp] using
        congrArg (fun ψ => ψ.hom.hom) hφ
    rcases hind.eq_zero_or_eq_one_of_isIdempotentElem hφ' with h | h
    · exact .inl (ObjectProperty.hom_ext _ (GradedModuleCat.hom_ext h))
    · exact .inr (ObjectProperty.hom_ext _ (GradedModuleCat.hom_ext h))

variable (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

include he₀ hprim hnoniso in
/-- **The graded projectives `A eᵢ` of primitive idempotents form a basis of `K₀^gr(proj A)`**
over `ℤ[q,q⁻¹]`, for a finite-dimensional graded algebra with a complete family of orthogonal
primitive idempotents `eᵢ` of degree zero whose ungraded left ideals `A eᵢ` are pairwise
nonisomorphic. Its basis vector at `i` is the class `[A eᵢ]`. The degree-zero corners
`eᵢ A eᵢ ∩ 𝒜 0` need not be the lines `k eᵢ`, so the field need not split the simple modules. This
is the graded counterpart of `TauCeti.idempotentProjectiveBasis`. -/
def gradedIdempotentProjectiveBasisOfPrimitive :
    Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :=
  gradedIndecomposableProjectiveClassBasis _
    (fun i => indecomposable_ofIdeal_span_singleton (hprim i) (hI i))
    -- A graded isomorphism `A eᵢ ≅ (A eⱼ){d}` forgets to an `A`-linear isomorphism `A eᵢ ≃ A eⱼ`.
    (fun _ _ hij _ => ⟨fun φ => (hnoniso hij).false
      (((gradedFiniteProjectiveModules 𝒜).ι ⋙ GradedModuleCat.toModuleCat).mapIso
        φ).toLinearEquiv⟩)
    (isExhaustiveGradedIndecomposableProjectiveFamily_of_completeOrthogonalIdempotents he he₀ hI
      fun i => indecomposable_ofIdeal_span_singleton (hprim i) (hI i))

/-- The basis vector of `TauCeti.gradedIdempotentProjectiveBasisOfPrimitive` at `i` is the class
`[A eᵢ]`. -/
@[simp]
theorem gradedIdempotentProjectiveBasisOfPrimitive_apply (i : I) :
    gradedIdempotentProjectiveBasisOfPrimitive he he₀ hI hprim hnoniso i =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩ :=
  gradedIndecomposableProjectiveClassBasis_apply _ _ _ _ i

variable (hneg : ∀ p < 0, 𝒜 p = ⊥) (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e))
  (hne : ∀ i, e i ≠ 0)

include hneg hspan hne in
/-- **The graded projectives `A eᵢ` form a basis of `K₀^gr(proj A)`** over `ℤ[q,q⁻¹]`, for a
nonnegatively graded finite-dimensional algebra whose degree-zero piece is spanned by a complete
family of orthogonal nonzero idempotents `eᵢ`. Its basis vector at `i` is the class `[A eᵢ]`. This
is the projective counterpart of the head basis `TauCeti.gradedIdempotentHeadBasis`, and the case of
`TauCeti.gradedIdempotentProjectiveBasisOfPrimitive` where each `eᵢ` is primitive by
`TauCeti.isPrimitiveIdempotent_of_gradeZero_le_span` and the `A eᵢ` are pairwise nonisomorphic by
`TauCeti.isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span`. -/
def gradedIdempotentProjectiveBasis :
    Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :=
  gradedIdempotentProjectiveBasisOfPrimitive he he₀ hI
    (fun i => isPrimitiveIdempotent_of_gradeZero_le_span he₀ he.toOrthogonalIdempotents hneg hspan i
      (hne i))
    (fun i _ hij => isEmpty_linearEquiv_span_singleton_of_gradeZero_le_span he₀
      he.toOrthogonalIdempotents hneg hspan hij (hne i))

/-- The basis vector of `TauCeti.gradedIdempotentProjectiveBasis` at `i` is the class `[A eᵢ]`. -/
@[simp]
theorem gradedIdempotentProjectiveBasis_apply (i : I) :
    gradedIdempotentProjectiveBasis he he₀ hI hneg hspan hne i =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton (he.idem i) (hI i)⟩ :=
  gradedIdempotentProjectiveBasisOfPrimitive_apply _ _ _ _ _ i

end Basis

end TauCeti
