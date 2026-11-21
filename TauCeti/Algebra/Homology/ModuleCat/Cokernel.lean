/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Cokernels of morphisms of complexes of modules, on elements

Let `φ : B ⟶ A` be a morphism of homological complexes of modules. Cokernels of complexes are
computed degreewise, so the projection `π : A ⟶ cokernel φ` is surjective in each degree
(`HomologicalComplex.cokernel_π_f_surjective`) and its kernel in degree `i` is the range of
`φ.f i` (`HomologicalComplex.cokernel_π_f_apply_eq_zero_iff`). This file records the resulting
description of the cycles and homology classes of `cokernel φ` through representatives in `A`.

* The image `π c` of `c ∈ A_i` is a cycle exactly when the boundary of `c` lies in the range of
  `φ` (`HomologicalComplex.cokernel_d_π_f_apply_eq_zero_iff`).
* Changing `c` by a boundary of `A` does not change the homology class of `π c`
  (`HomologicalComplex.moduleCatKerHomologyClass_cokernel_π_sub_d`), and conversely two
  representatives with the same class differ by a boundary up to an element of the range of `φ`
  (`HomologicalComplex.exists_sub_sub_d_mem_range_of_moduleCatKerHomologyClass_eq`).

For an inclusion of subcomplexes `φ`, these are the classical descriptions of relative cycles and
relative homology classes of the pair `(A, B)`.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

universe v

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {A B : HomologicalComplex (ModuleCat.{v} R) c} (φ : B ⟶ A)

/-- An element of `A_i` vanishes in the cokernel of `φ` exactly when it lies in the range of
`φ.f i`. -/
@[simp]
lemma cokernel_π_f_apply_eq_zero_iff (i : ι) (y : A.X i) :
    (cokernel.π φ).f i y = 0 ↔ y ∈ LinearMap.range (φ.f i).hom := by
  constructor
  · intro h
    have hS := (exact_iff_degreewise_exact _).1 (ShortComplex.exact_cokernel φ) i
    rw [ShortComplex.moduleCat_exact_iff] at hS
    exact hS y h
  · rintro ⟨u, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← comp_f, cokernel.condition, zero_f]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The projection onto the cokernel of `φ` is surjective in each degree. -/
lemma cokernel_π_f_surjective (i : ι) : Function.Surjective ((cokernel.π φ).f i) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The image of `c ∈ A_i` in the cokernel of `φ` is killed by the differential to degree `j`
exactly when the boundary of `c` lies in the range of `φ.f j`. -/
lemma cokernel_d_π_f_apply_eq_zero_iff (i j : ι) (x : A.X i) :
    (cokernel φ).d i j ((cokernel.π φ).f i x) = 0 ↔
      A.d i j x ∈ LinearMap.range (φ.f j).hom := by
  rw [Hom.comm_apply, cokernel_π_f_apply_eq_zero_iff]

variable {n m p : ι} (hm : c.next n = m) (hp : c.prev n = p)
include hp

/-- Changing a representative by a boundary of `A` does not change the homology class of its
image in the cokernel of `φ`. -/
lemma moduleCatKerHomologyClass_cokernel_π_sub_d (x : A.X n) (e : A.X p)
    (h₁ : (cokernel φ).d n m ((cokernel.π φ).f n (x - A.d p n e)) = 0)
    (h₂ : (cokernel φ).d n m ((cokernel.π φ).f n x) = 0) :
    (cokernel φ).moduleCatKerHomologyClass hm ⟨(cokernel.π φ).f n (x - A.d p n e), h₁⟩ =
      (cokernel φ).moduleCatKerHomologyClass hm ⟨(cokernel.π φ).f n x, h₂⟩ := by
  rw [← sub_eq_zero, ← map_sub]
  refine ((cokernel φ).exact_inclusion_moduleCatKerHomologyClass hm hp _).2
    ⟨⟨_, (cokernel.π φ).f p (-e), rfl⟩, Subtype.ext ?_⟩
  simp only [Submodule.coe_inclusion, Submodule.coe_sub, map_sub, sub_sub_cancel_left,
    map_neg, Hom.comm_apply]

/-- Two representatives in `A_n` of the same homology class of the cokernel of `φ` differ by a
boundary of `A`, up to an element of the range of `φ.f n`. -/
lemma exists_sub_sub_d_mem_range_of_moduleCatKerHomologyClass_eq (x x' : A.X n)
    (hx : (cokernel φ).d n m ((cokernel.π φ).f n x) = 0)
    (hx' : (cokernel φ).d n m ((cokernel.π φ).f n x') = 0)
    (h : (cokernel φ).moduleCatKerHomologyClass hm ⟨(cokernel.π φ).f n x, hx⟩ =
      (cokernel φ).moduleCatKerHomologyClass hm ⟨(cokernel.π φ).f n x', hx'⟩) :
    ∃ e : A.X p, x - x' - A.d p n e ∈ LinearMap.range (φ.f n).hom := by
  rw [← sub_eq_zero, ← map_sub] at h
  obtain ⟨⟨_, ⟨w, rfl⟩⟩, hw⟩ :=
    ((cokernel φ).exact_inclusion_moduleCatKerHomologyClass hm hp _).1 h
  obtain ⟨e, rfl⟩ := cokernel_π_f_surjective φ p w
  refine ⟨e, (cokernel_π_f_apply_eq_zero_iff _ _ _).1 ?_⟩
  have hw' := congrArg Subtype.val hw
  simp only [Submodule.coe_inclusion, Submodule.coe_sub] at hw'
  rw [map_sub, map_sub, ← Hom.comm_apply, hw', sub_self]

end HomologicalComplex
