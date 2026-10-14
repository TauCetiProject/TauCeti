/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.DG.Basic
public import TauCeti.CategoryTheory.AInfinity.StrictFunctor.Basic
public import TauCeti.CategoryTheory.AInfinity.ToDGCategory
public import TauCeti.CategoryTheory.DG.Functor

/-!
# Differential graded categories are the `A∞` categories with vanishing higher operations

A differential graded category `C` is an `A∞` category `TauCeti.DGCategory.toAInfinityCategory`
whose operations of arity at least three vanish and whose identities are strict, and conversely an
`A∞` category `𝒞` with `m₃ = 0` and degree-zero identities `e` for `m₂` determines the differential
graded category `TauCeti.AInfinityCategory.AsDGCategory`.  This file proves that the two
conversions are mutually inverse, so that differential graded categories are exactly the `A∞`
categories with `mₙ = 0` for `n ≥ 3` and identities for `m₂`.

The hom modules change along the way: the hom module of `toAInfinityCategory` from `X` to `Y` is
the direct sum `⨁ n, Hom^n(X, Y)` of the morphisms of each degree, and the morphisms of degree `n`
of `AsDGCategory` are the degree-`n` morphisms of `𝒞`.  So the round trips are isomorphisms which
are the identity on objects and the canonical identifications of the morphisms of each degree, not
equalities.

* Starting from a differential graded category `C`, the differential graded category
  `TauCeti.DGCategory.AInfinityDG R C` of its `A∞` category is isomorphic to `C` through the
  mutually inverse DG functors `TauCeti.DGCategory.toAInfinityDGFunctor` and
  `TauCeti.DGCategory.ofAInfinityDGFunctor`.  A morphism `f` of degree `n` of `C` corresponds to
  `homLof f`.
* Starting from an `A∞` category `𝒞` with `mₙ = 0` for `n ≥ 3`, the `A∞` category of its
  differential graded category is isomorphic to `𝒞` through the mutually inverse strict functors
  `TauCeti.AInfinityCategory.toAsDGCategoryStrictFunctor` and
  `TauCeti.AInfinityCategory.ofAsDGCategoryStrictFunctor`, which split a morphism of `𝒞` into its
  homogeneous components.  The vanishing of every higher operation is necessary here, since the
  `A∞` category of a differential graded category has no higher operations.  No condition beyond
  being identities for `m₂` is imposed on `e`: with the higher operations vanishing, they are
  automatically strict.

## Main definitions

* `TauCeti.DGCategory.aInfinityDGHomEquiv`: the morphisms of degree `n` of `C` and of the
  differential graded category of its `A∞` category agree.
* `TauCeti.DGCategory.toAInfinityDGFunctor` and `TauCeti.DGCategory.ofAInfinityDGFunctor`: the
  DG functors between `C` and the differential graded category of its `A∞` category.
* `TauCeti.AInfinityCategory.asDGCategoryHomEquiv`: the hom modules of `𝒞` and of the `A∞`
  category of its differential graded category agree, compatibly with `m₁` and `m₂`.
* `TauCeti.AInfinityCategory.toAsDGCategoryStrictFunctor` and
  `TauCeti.AInfinityCategory.ofAsDGCategoryStrictFunctor`: the strict functors between `𝒞` and the
  `A∞` category of its differential graded category.

## Main results

* `TauCeti.DGCategory.toAInfinityDGFunctor_comp_ofAInfinityDGFunctor` and
  `TauCeti.DGCategory.ofAInfinityDGFunctor_comp_toAInfinityDGFunctor`: the DG functors are
  mutually inverse.
* `TauCeti.AInfinityCategory.toAsDGCategoryStrictFunctor_comp_ofAsDGCategoryStrictFunctor` and
  `TauCeti.AInfinityCategory.ofAsDGCategoryStrictFunctor_comp_toAsDGCategoryStrictFunctor`: the
  strict functors are mutually inverse.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
-/

public section

open CategoryTheory

namespace TauCeti

open GradedLinearQuiver

universe v u

/-! ### From a differential graded category and back -/

namespace DGCategory

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

/-- The objects of the differential graded category of the `A∞` category
`TauCeti.DGCategory.toAInfinityCategory R C` of a differential graded category `C`, built with the
identities of `C` as identities for `m₂`. -/
abbrev AInfinityDG : Type u :=
  (toAInfinityCategory R C).AsDGCategory (toAInfinityCategory_m_of_three_le le_rfl)
    strictUnit_toAInfinityCategory.degree_zero strictUnit_toAInfinityCategory.binary_left
    strictUnit_toAInfinityCategory.binary_right

variable {R C}

/-- The morphisms of degree `n` of a differential graded category `C` are those of the
differential graded category `AInfinityDG R C` of its `A∞` category: a morphism `f` of `C`
corresponds to the morphism `homLof f` of the graded linear quiver of `C`. -/
noncomputable def aInfinityDGHomEquiv (X Y : C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (C := AInfinityDG R C) ⟨X⟩ ⟨Y⟩ :=
  (grHomEquiv X Y n).trans (AInfinityCategory.dgHomEquiv _ _ _ _ ⟨X⟩ ⟨Y⟩ n).symm

@[simp]
theorem coe_dgHomEquiv_aInfinityDGHomEquiv {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (AInfinityCategory.dgHomEquiv _ _ _ _ ⟨X⟩ ⟨Y⟩ n (aInfinityDGHomEquiv X Y n f) :
      homModule (R := R) X Y) = homLof X Y n f := by
  rw [aInfinityDGHomEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, coe_grHomEquiv]

/-- `TauCeti.DGCategory.aInfinityDGHomEquiv` commutes with the differentials. -/
@[simp]
theorem aInfinityDGHomEquiv_dgDifferential {X Y : C} (n : ℤ) (f : DGHom R n X Y) :
    aInfinityDGHomEquiv X Y (n + 1) (dgDifferential R n f) =
      dgDifferential R n (aInfinityDGHomEquiv X Y n f) := by
  apply (AInfinityCategory.dgHomEquiv _ _ _ _ ⟨X⟩ ⟨Y⟩ (n + 1)).injective
  apply Subtype.ext
  rw [coe_dgHomEquiv_aInfinityDGHomEquiv, AInfinityCategory.dgHomEquiv_dgDifferential,
    coe_dgHomEquiv_aInfinityDGHomEquiv, homDifferential_toAInfinityCategory_homLof]

/-- `TauCeti.DGCategory.aInfinityDGHomEquiv` preserves identities. -/
@[simp]
theorem aInfinityDGHomEquiv_dgId (X : C) :
    aInfinityDGHomEquiv X X 0 (dgId R X) = dgId R (C := AInfinityDG R C) ⟨X⟩ := by
  apply (AInfinityCategory.dgHomEquiv _ _ _ _ ⟨X⟩ ⟨X⟩ 0).injective
  apply Subtype.ext
  rw [coe_dgHomEquiv_aInfinityDGHomEquiv, AInfinityCategory.dgHomEquiv_dgId]

/-- `TauCeti.DGCategory.aInfinityDGHomEquiv` preserves composition: the two Koszul signs between
the enriched and Keller orders of composition cancel. -/
@[simp]
theorem aInfinityDGHomEquiv_dgComp {X Y Z : C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    aInfinityDGHomEquiv X Z n (dgComp R f g h) =
      dgComp R (aInfinityDGHomEquiv X Y p f) (aInfinityDGHomEquiv Y Z q g) h := by
  subst h
  apply (AInfinityCategory.dgHomEquiv _ _ _ _ ⟨X⟩ ⟨Z⟩ (p + q)).injective
  apply Subtype.ext
  rw [coe_dgHomEquiv_aInfinityDGHomEquiv, AInfinityCategory.dgHomEquiv_dgComp,
    coe_dgHomEquiv_aInfinityDGHomEquiv, coe_dgHomEquiv_aInfinityDGHomEquiv,
    comp_toAInfinityCategory_homLof, negOnePow_smul_negOnePow_smul]

variable (R C)

/-- The DG functor from a differential graded category `C` to the differential graded category of
its `A∞` category: the identity on objects, sending a morphism `f` of degree `n` to `homLof f`. -/
-- The body is exposed so that the object map reduces in the types of the characteristic equations.
@[expose]
noncomputable def toAInfinityDGFunctor :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C (AInfinityDG R C) :=
  EnrichedFunctor.ofDGMap (fun X ↦ ⟨X⟩) (fun n ↦ (aInfinityDGHomEquiv _ _ n).toLinearMap)
    aInfinityDGHomEquiv_dgDifferential aInfinityDGHomEquiv_dgId aInfinityDGHomEquiv_dgComp

/-- The DG functor from the differential graded category of the `A∞` category of a differential
graded category `C` back to `C`: the identity on objects, sending `homLof f` to `f`. -/
-- The body is exposed for the same reason as that of `toAInfinityDGFunctor`.
@[expose]
noncomputable def ofAInfinityDGFunctor :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (AInfinityDG R C) C :=
  EnrichedFunctor.ofDGMap (fun X ↦ X.as) (fun n ↦ (aInfinityDGHomEquiv _ _ n).symm.toLinearMap)
    (fun {X Y} n g ↦ by
      obtain ⟨f, rfl⟩ := (aInfinityDGHomEquiv X.as Y.as n).surjective g
      simp only [LinearEquiv.coe_coe]
      rw [← aInfinityDGHomEquiv_dgDifferential, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply])
    (fun X ↦ by
      simp only [LinearEquiv.coe_coe]
      rw [← aInfinityDGHomEquiv_dgId, LinearEquiv.symm_apply_apply])
    (fun {X Y Z p q n} f g h ↦ by
      obtain ⟨f, rfl⟩ := (aInfinityDGHomEquiv X.as Y.as p).surjective f
      obtain ⟨g, rfl⟩ := (aInfinityDGHomEquiv Y.as Z.as q).surjective g
      simp only [LinearEquiv.coe_coe]
      rw [← aInfinityDGHomEquiv_dgComp, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply])

variable {R C}

@[simp]
theorem toAInfinityDGFunctor_obj (X : C) : (toAInfinityDGFunctor R C).obj X = ⟨X⟩ :=
  (rfl)

@[simp]
theorem dgMap_toAInfinityDGFunctor {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    (toAInfinityDGFunctor R C).dgMap n f = aInfinityDGHomEquiv X Y n f :=
  EnrichedFunctor.dgMap_ofDGMap _ _ _ _ _ n f

@[simp]
theorem ofAInfinityDGFunctor_obj (X : AInfinityDG R C) :
    (ofAInfinityDGFunctor R C).obj X = X.as :=
  (rfl)

@[simp]
theorem dgMap_ofAInfinityDGFunctor {X Y : AInfinityDG R C} {n : ℤ} (g : DGHom R n X Y) :
    (ofAInfinityDGFunctor R C).dgMap n g = (aInfinityDGHomEquiv X.as Y.as n).symm g :=
  EnrichedFunctor.dgMap_ofDGMap _ _ _ _ _ n g

variable (R C)

/-- **A differential graded category is recovered from its `A∞` category**: `ofAInfinityDGFunctor`
is a left inverse of `toAInfinityDGFunctor`. -/
theorem toAInfinityDGFunctor_comp_ofAInfinityDGFunctor :
    (toAInfinityDGFunctor R C).comp _ (ofAInfinityDGFunctor R C) =
      EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C := by
  refine EnrichedFunctor.ext _ (fun X ↦ rfl) fun X Y ↦ ?_
  ext n f
  -- The composite is the identity on objects, so its `eqToHom` is along a reflexive equation, and
  -- it acts on the morphisms of degree `n` by `aInfinityDGHomEquiv` followed by its inverse
  -- (`dgMap_toAInfinityDGFunctor` and `dgMap_ofAInfinityDGFunctor`).
  exact (aInfinityDGHomEquiv X Y n).symm_apply_apply f

/-- `ofAInfinityDGFunctor` is a right inverse of `toAInfinityDGFunctor`. -/
theorem ofAInfinityDGFunctor_comp_toAInfinityDGFunctor :
    (ofAInfinityDGFunctor R C).comp _ (toAInfinityDGFunctor R C) =
      EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) (AInfinityDG R C) := by
  refine EnrichedFunctor.ext _ (fun X ↦ rfl) fun X Y ↦ ?_
  ext n f
  -- As in `toAInfinityDGFunctor_comp_ofAInfinityDGFunctor`, with the two maps interchanged.
  exact (aInfinityDGHomEquiv X.as Y.as n).apply_symm_apply f

end DGCategory

/-! ### From an `A∞` category and back -/

namespace AInfinityCategory

variable {R : Type v} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, v} R C]
  {𝒞 : AInfinityCategory R C} {e : ∀ X : C, homModule (R := R) X X}

section HomEquiv

variable (h₃ : 𝒞.m 3 = 0) (he₀ : ∀ X, e X ∈ (grading (R := R) X X).piece 0)
  (hel : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X Y Y (e Y) f = f)
  (her : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X X Y f (e X) = f)

/-- The hom module of an `A∞` category `𝒞` with `m₃ = 0` is that of the `A∞` category of its
differential graded category, the direct sum of the morphisms of each degree of `𝒞`: a morphism
corresponds to the family of its homogeneous components. -/
noncomputable def asDGCategoryHomEquiv (X Y : C) :
    homModule (R := R) X Y ≃ₗ[R]
      homModule (R := R) (C := 𝒞.AsDGCategory h₃ he₀ hel her) ⟨X⟩ ⟨Y⟩ :=
  (DirectSum.decomposeLinearEquiv (grading (R := R) X Y).piece).trans
    ((DirectSum.congrLinearEquiv fun n ↦
      (dgHomEquiv h₃ he₀ hel her ⟨X⟩ ⟨Y⟩ n).symm.trans
        (DGCategory.grHomEquiv (⟨X⟩ : 𝒞.AsDGCategory h₃ he₀ hel her) ⟨Y⟩ n)).trans
      (DirectSum.decomposeLinearEquiv
        (grading (R := R) (C := 𝒞.AsDGCategory h₃ he₀ hel her) ⟨X⟩ ⟨Y⟩).piece).symm)

/-- `TauCeti.AInfinityCategory.asDGCategoryHomEquiv` sends a morphism `g` of degree `n` to the
morphism `g` of degree `n` of the differential graded category. -/
@[simp]
theorem asDGCategoryHomEquiv_coe {X Y : C} {n : ℤ} (g : grHom R X Y n) :
    asDGCategoryHomEquiv h₃ he₀ hel her X Y g =
      DGCategory.homLof (⟨X⟩ : 𝒞.AsDGCategory h₃ he₀ hel her) ⟨Y⟩ n
        ((dgHomEquiv h₃ he₀ hel her ⟨X⟩ ⟨Y⟩ n).symm g) := by
  rw [asDGCategoryHomEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    DirectSum.decomposeLinearEquiv_symm_lof, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    DGCategory.coe_grHomEquiv]

/-- The inverse of `TauCeti.AInfinityCategory.asDGCategoryHomEquiv` sends a morphism `f` of
degree `n` of the differential graded category to the morphism `f` of degree `n` of `𝒞`. -/
@[simp]
theorem asDGCategoryHomEquiv_symm_homLof {X Y : 𝒞.AsDGCategory h₃ he₀ hel her} {n : ℤ}
    (f : DGHom R n X Y) :
    (asDGCategoryHomEquiv h₃ he₀ hel her X.as Y.as).symm (DGCategory.homLof X Y n f) =
      dgHomEquiv h₃ he₀ hel her X Y n f := by
  rw [LinearEquiv.symm_apply_eq, asDGCategoryHomEquiv_coe, LinearEquiv.symm_apply_apply]

private theorem asDGCategoryHomEquiv_symm_homDifferential
    (X Y : 𝒞.AsDGCategory h₃ he₀ hel her) (f : homModule (R := R) X Y) :
    (asDGCategoryHomEquiv h₃ he₀ hel her X.as Y.as).symm
        ((DGCategory.toAInfinityCategory R _).homDifferential X Y f) =
      𝒞.homDifferential X.as Y.as ((asDGCategoryHomEquiv h₃ he₀ hel her X.as Y.as).symm f) := by
  induction f using DGCategory.homModule_induction with
  | zero => simp only [map_zero]
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | homLof n f =>
    rw [DGCategory.homDifferential_toAInfinityCategory_homLof, asDGCategoryHomEquiv_symm_homLof,
      asDGCategoryHomEquiv_symm_homLof, dgHomEquiv_dgDifferential]

private theorem asDGCategoryHomEquiv_symm_comp (X Y Z : 𝒞.AsDGCategory h₃ he₀ hel her)
    (g : homModule (R := R) Y Z) (f : homModule (R := R) X Y) :
    (asDGCategoryHomEquiv h₃ he₀ hel her X.as Z.as).symm
        ((DGCategory.toAInfinityCategory R _).comp X Y Z g f) =
      𝒞.comp X.as Y.as Z.as ((asDGCategoryHomEquiv h₃ he₀ hel her Y.as Z.as).symm g)
        ((asDGCategoryHomEquiv h₃ he₀ hel her X.as Y.as).symm f) := by
  induction g using DGCategory.homModule_induction with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
  | homLof q g =>
  induction f using DGCategory.homModule_induction with
  | zero => simp only [map_zero]
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | homLof p f =>
    rw [DGCategory.comp_toAInfinityCategory_homLof, map_zsmul_unit,
      asDGCategoryHomEquiv_symm_homLof, dgHomEquiv_dgComp, asDGCategoryHomEquiv_symm_homLof,
      asDGCategoryHomEquiv_symm_homLof, negOnePow_smul_negOnePow_smul]

/-- `TauCeti.AInfinityCategory.asDGCategoryHomEquiv` preserves degrees. -/
theorem asDGCategoryHomEquiv_mem_piece {X Y : C} {p : ℤ} {f : homModule (R := R) X Y}
    (hf : f ∈ (grading (R := R) X Y).piece p) :
    asDGCategoryHomEquiv h₃ he₀ hel her X Y f ∈
      (grading (R := R) (C := 𝒞.AsDGCategory h₃ he₀ hel her) ⟨X⟩ ⟨Y⟩).piece p := by
  lift f to grHom R X Y p using hf
  rw [asDGCategoryHomEquiv_coe]
  exact DGCategory.homLof_mem_piece _

/-- The inverse of `TauCeti.AInfinityCategory.asDGCategoryHomEquiv` preserves degrees. -/
theorem asDGCategoryHomEquiv_symm_mem_piece {X Y : 𝒞.AsDGCategory h₃ he₀ hel her} {p : ℤ}
    {f : homModule (R := R) X Y} (hf : f ∈ (grading (R := R) X Y).piece p) :
    (asDGCategoryHomEquiv h₃ he₀ hel her X.as Y.as).symm f ∈
      (grading (R := R) X.as Y.as).piece p := by
  rw [DGCategory.grading_piece] at hf
  obtain ⟨f, rfl⟩ := hf
  rw [asDGCategoryHomEquiv_symm_homLof]
  exact (dgHomEquiv h₃ he₀ hel her X Y p f).2

/-- `TauCeti.AInfinityCategory.asDGCategoryHomEquiv` commutes with the differentials `m₁`. -/
@[simp]
theorem asDGCategoryHomEquiv_homDifferential (X Y : C) (f : homModule (R := R) X Y) :
    asDGCategoryHomEquiv h₃ he₀ hel her X Y (𝒞.homDifferential X Y f) =
      (DGCategory.toAInfinityCategory R (𝒞.AsDGCategory h₃ he₀ hel her)).homDifferential ⟨X⟩ ⟨Y⟩
        (asDGCategoryHomEquiv h₃ he₀ hel her X Y f) := by
  apply (asDGCategoryHomEquiv h₃ he₀ hel her X Y).symm.injective
  rw [LinearEquiv.symm_apply_apply,
    asDGCategoryHomEquiv_symm_homDifferential (X := ⟨X⟩) (Y := ⟨Y⟩), LinearEquiv.symm_apply_apply]

/-- `TauCeti.AInfinityCategory.asDGCategoryHomEquiv` preserves the compositions `m₂`. -/
@[simp]
theorem asDGCategoryHomEquiv_comp (X Y Z : C) (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y) :
    asDGCategoryHomEquiv h₃ he₀ hel her X Z (𝒞.comp X Y Z g f) =
      (DGCategory.toAInfinityCategory R (𝒞.AsDGCategory h₃ he₀ hel her)).comp ⟨X⟩ ⟨Y⟩ ⟨Z⟩
        (asDGCategoryHomEquiv h₃ he₀ hel her Y Z g)
        (asDGCategoryHomEquiv h₃ he₀ hel her X Y f) := by
  apply (asDGCategoryHomEquiv h₃ he₀ hel her X Z).symm.injective
  rw [LinearEquiv.symm_apply_apply, asDGCategoryHomEquiv_symm_comp (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩),
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end HomEquiv

variable (hm : ∀ n, 3 ≤ n → 𝒞.m n = 0) (he₀ : ∀ X, e X ∈ (grading (R := R) X X).piece 0)
  (hel : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X Y Y (e Y) f = f)
  (her : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X X Y f (e X) = f)

/-- The strict functor from an `A∞` category `𝒞` whose operations of arity at least three vanish
to the `A∞` category of its differential graded category: the identity on objects, sending a
morphism of `𝒞` to the family of its homogeneous components. -/
-- The body is exposed so that the object map reduces in the types of the characteristic equations.
@[expose]
noncomputable def toAsDGCategoryStrictFunctor :
    AInfinityStrictFunctor 𝒞
      (DGCategory.toAInfinityCategory R (𝒞.AsDGCategory (hm 3 le_rfl) he₀ hel her)) :=
  AInfinityStrictFunctor.ofHomDifferentialComp hm
    (fun _ ↦ DGCategory.toAInfinityCategory_m_of_three_le) (fun X ↦ ⟨X⟩)
    (fun X Y ↦ (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X Y).toLinearMap)
    (fun _ _ _ _ hf ↦ asDGCategoryHomEquiv_mem_piece (hm 3 le_rfl) he₀ hel her hf)
    (asDGCategoryHomEquiv_homDifferential (hm 3 le_rfl) he₀ hel her)
    (asDGCategoryHomEquiv_comp (hm 3 le_rfl) he₀ hel her)

/-- The strict functor from the `A∞` category of the differential graded category of an `A∞`
category `𝒞` whose operations of arity at least three vanish back to `𝒞`: the identity on
objects, sending a family of homogeneous morphisms of `𝒞` to its sum. -/
-- The body is exposed for the same reason as that of `toAsDGCategoryStrictFunctor`.
@[expose]
noncomputable def ofAsDGCategoryStrictFunctor :
    AInfinityStrictFunctor
      (DGCategory.toAInfinityCategory R (𝒞.AsDGCategory (hm 3 le_rfl) he₀ hel her)) 𝒞 :=
  AInfinityStrictFunctor.ofHomDifferentialComp
    (fun _ ↦ DGCategory.toAInfinityCategory_m_of_three_le) hm AsDGCategory.as
    (fun X Y ↦ (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X.as Y.as).symm.toLinearMap)
    (fun _ _ _ _ hf ↦ asDGCategoryHomEquiv_symm_mem_piece (hm 3 le_rfl) he₀ hel her hf)
    (fun X Y f ↦ (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X.as Y.as).injective <| by
      simp only [LinearEquiv.coe_coe]
      rw [LinearEquiv.apply_symm_apply, asDGCategoryHomEquiv_homDifferential,
        LinearEquiv.apply_symm_apply])
    (fun X Y Z g f ↦ (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X.as Z.as).injective <| by
      simp only [LinearEquiv.coe_coe]
      rw [LinearEquiv.apply_symm_apply, asDGCategoryHomEquiv_comp, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])

@[simp]
theorem toAsDGCategoryStrictFunctor_obj (X : C) :
    (toAsDGCategoryStrictFunctor hm he₀ hel her).obj X = ⟨X⟩ :=
  (rfl)

@[simp]
theorem toAsDGCategoryStrictFunctor_map (X Y : C) (f : homModule (R := R) X Y) :
    (toAsDGCategoryStrictFunctor hm he₀ hel her).map X Y f =
      asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X Y f :=
  (rfl)

@[simp]
theorem ofAsDGCategoryStrictFunctor_obj (X : 𝒞.AsDGCategory (hm 3 le_rfl) he₀ hel her) :
    (ofAsDGCategoryStrictFunctor hm he₀ hel her).obj X = X.as :=
  (rfl)

@[simp]
theorem ofAsDGCategoryStrictFunctor_map (X Y : 𝒞.AsDGCategory (hm 3 le_rfl) he₀ hel her)
    (f : homModule (R := R) X Y) :
    (ofAsDGCategoryStrictFunctor hm he₀ hel her).map X Y f =
      (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X.as Y.as).symm f :=
  (rfl)

/-- **An `A∞` category with vanishing higher operations is recovered from its differential graded
category**: `ofAsDGCategoryStrictFunctor` is a left inverse of `toAsDGCategoryStrictFunctor`. -/
theorem ofAsDGCategoryStrictFunctor_comp_toAsDGCategoryStrictFunctor :
    (ofAsDGCategoryStrictFunctor hm he₀ hel her).comp (toAsDGCategoryStrictFunctor hm he₀ hel her) =
      AInfinityStrictFunctor.id 𝒞 :=
  AInfinityStrictFunctor.ext_of_obj_eq rfl fun X Y f ↦
    (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X Y).symm_apply_apply f

/-- `ofAsDGCategoryStrictFunctor` is a right inverse of `toAsDGCategoryStrictFunctor`. -/
theorem toAsDGCategoryStrictFunctor_comp_ofAsDGCategoryStrictFunctor :
    (toAsDGCategoryStrictFunctor hm he₀ hel her).comp (ofAsDGCategoryStrictFunctor hm he₀ hel her) =
      AInfinityStrictFunctor.id _ :=
  AInfinityStrictFunctor.ext_of_obj_eq rfl fun X Y f ↦
    (asDGCategoryHomEquiv (hm 3 le_rfl) he₀ hel her X.as Y.as).apply_symm_apply f

end AInfinityCategory

end TauCeti
