/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Subobjects of homological complexes

A subobject of a homological complex `K` in a category with finite limits is determined by its
terms: two subobjects `A` and `B` of `K` whose terms `A.X i` and `B.X i` are the same subobjects
of `K.X i` for every `i` are equal (`HomologicalComplex.subobjectMk_f_injective`). Consequently, the
subobjects of `K` are at most as numerous as the families of subobjects of its terms
(`HomologicalComplex.hasCardinalLT_subobject`). This bounds the size of complexes, for instance in
transfinite constructions with complexes over a Grothendieck abelian category.
-/

public section

universe w

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] [HasFiniteLimits C] {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- A subobject `A` of a homological complex `K` is determined by the subobjects of the terms
`K.X i` given by its terms `A.X i`. -/
lemma subobjectMk_f_injective :
    Function.Injective (fun (A : Subobject K) (i : ι) ↦ Subobject.mk (A.arrow.f i)) := by
  intro A B h
  let e (i : ι) := Subobject.isoOfMkEqMk _ _ (congrFun h i)
  have he (i : ι) : (e i).hom ≫ B.arrow.f i = A.arrow.f i :=
    Subobject.ofMkLEMk_comp (congrFun h i).le
  let φ : (A : HomologicalComplex C c) ≅ B := Hom.isoOfComponents e fun i j _ ↦ by
    rw [← cancel_mono (B.arrow.f j), Category.assoc, Category.assoc, ← B.arrow.comm,
      reassoc_of% (he i), he j, A.arrow.comm]
  rw [← Subobject.mk_arrow A, ← Subobject.mk_arrow B]
  exact Subobject.mk_eq_mk_of_comm _ _ φ (by ext i; exact he i)

/-- If the families of subobjects of the terms of `K` are fewer than `κ`, so are the subobjects
of `K`. -/
lemma hasCardinalLT_subobject {κ : Cardinal.{w}} (h : HasCardinalLT (∀ i, Subobject (K.X i)) κ) :
    HasCardinalLT (Subobject K) κ :=
  h.of_injective _ K.subobjectMk_f_injective

end HomologicalComplex
