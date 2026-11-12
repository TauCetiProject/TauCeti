/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.HomologicalComplex.Basic

import TauCeti.Algebra.Homology.HomologicalComplex.Subobject

/-!
# Factoring through subcomplexes of complexes of modules

A subcomplex `S` of a homological complex `L` of modules is recorded degreewise by the range of
the components of `S.arrow`. A morphism of complexes into `L` factors through `S` as soon as it
does degreewise, that is, as soon as each of its components lands in the range of the
corresponding component of `S.arrow` (`CategoryTheory.Subobject.factors_of_forall_mem_range`).

The degreewise ranges are monotone in the subcomplex
(`CategoryTheory.Subobject.range_arrow_f_hom_le`) and stable under the differentials of `L`
(`CategoryTheory.Subobject.d_mem_range_arrow_f_hom`). When `S ≤ T` and the quotient complex `T/S`
is exact in degree `j`, a cycle of `L` lying in `T` is a boundary of an element of `T` up to an
element of `S`
(`CategoryTheory.Subobject.exists_sub_d_mem_range_arrow_f_hom_of_isZero_homology_cokernel`).

## Main results

* `CategoryTheory.Subobject.factors_iff_forall_mem_range`: a morphism factors through a subcomplex
  exactly when it does degreewise.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Subobject

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat R) c} (S : Subobject L) (g : K ⟶ L)

/-- A morphism of complexes of modules whose components land in the ranges of the components of
the inclusion of a subcomplex factors through it. -/
theorem factors_of_forall_mem_range
    (h : ∀ n x, (g.f n).hom x ∈ LinearMap.range (S.arrow.f n).hom) : S.Factors g := by
  refine (factors_iff_forall_exists_comp_arrow_f_eq S g).2 fun n ↦ ?_
  have hinj : Function.Injective (S.arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  -- The degreewise lift, through the isomorphism of `S` with the range of its inclusion.
  exact ⟨ModuleCat.ofHom ((LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ
    (g.f n).hom.codRestrict _ (h n)), ModuleCat.hom_ext (LinearMap.ext fun x ↦ by simp)⟩

/-- A morphism of complexes of modules factors through a subcomplex exactly when each of its
components lands in the range of the corresponding component of the inclusion. -/
theorem factors_iff_forall_mem_range :
    S.Factors g ↔ ∀ n x, (g.f n).hom x ∈ LinearMap.range (S.arrow.f n).hom := by
  refine ⟨fun hS n x ↦ ⟨((S.factorThru g hS).f n).hom x, ?_⟩, factors_of_forall_mem_range S g⟩
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
    Subobject.factorThru_arrow]

variable {S} in
/-- The degreewise ranges of the inclusions of subcomplexes are monotone in the subcomplex. -/
theorem range_arrow_f_hom_le {T : Subobject L} (h : S ≤ T) (n : ι) :
    LinearMap.range (S.arrow.f n).hom ≤ LinearMap.range (T.arrow.f n).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨((Subobject.ofLE S T h).f n).hom x, by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
      Subobject.ofLE_arrow]⟩

/-- The differentials of `L` send the degreewise range of the inclusion of a subcomplex into the
range in the next degree. -/
theorem d_mem_range_arrow_f_hom (i j : ι) {x : L.X i}
    (hx : x ∈ LinearMap.range (S.arrow.f i).hom) :
    (L.d i j).hom x ∈ LinearMap.range (S.arrow.f j).hom := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨((S : HomologicalComplex (ModuleCat R) c).d i j).hom y, by
    rw [← HomologicalComplex.Hom.comm_apply]⟩

variable {S} in
/-- The elementwise form of the vanishing of `H^j(T/S)` for subcomplexes `S ≤ T`: a cycle of `L`
lying in `T` is, up to an element of `S`, the boundary of an element of `T`. -/
theorem exists_sub_d_mem_range_arrow_f_hom_of_isZero_homology_cokernel {T : Subobject L}
    (h : S ≤ T) {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (hH : IsZero ((cokernel (Subobject.ofLE S T h)).homology j))
    {z : L.X j} (hz : z ∈ LinearMap.range (T.arrow.f j).hom) (hdz : (L.d j k).hom z = 0) :
    ∃ y ∈ LinearMap.range (T.arrow.f i).hom,
      z - (L.d i j).hom y ∈ LinearMap.range (S.arrow.f j).hom := by
  obtain ⟨z, rfl⟩ := hz
  set φ := Subobject.ofLE S T h
  have hdz' : ((T : HomologicalComplex (ModuleCat R) c).d j k).hom z = 0 := by
    apply (ModuleCat.mono_iff_injective (T.arrow.f k)).1 inferInstance
    rw [map_zero, ← HomologicalComplex.Hom.comm_apply]
    exact hdz
  have hc : ((cokernel φ).d j k).hom ((cokernel.π φ).f j z) = 0 := by
    rw [HomologicalComplex.Hom.comm_apply, hdz', map_zero]
  have hQ := ((cokernel φ).exactAt_iff' i j k hi hk).1
    (((cokernel φ).exactAt_iff_isZero_homology j).2 hH)
  rw [ShortComplex.moduleCat_exact_iff] at hQ
  obtain ⟨w, hw⟩ := hQ ((cokernel.π φ).f j z) hc
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective ((cokernel.π φ).f i)).1 inferInstance w
  have hS :=
    (HomologicalComplex.exact_iff_degreewise_exact _).1 (ShortComplex.exact_cokernel φ) j
  rw [ShortComplex.moduleCat_exact_iff] at hS
  obtain ⟨u, hu⟩ := hS (z - ((T : HomologicalComplex (ModuleCat R) c).d i j).hom w) (by
    dsimp at hw ⊢
    rw [map_sub, ← HomologicalComplex.Hom.comm_apply (cokernel.π φ), hw, sub_self])
  refine ⟨(T.arrow.f i).hom w, ⟨w, rfl⟩, u, ?_⟩
  dsimp at hu
  rw [← Subobject.ofLE_arrow h, HomologicalComplex.comp_f, ModuleCat.comp_apply, hu, map_sub,
    ← HomologicalComplex.Hom.comm_apply T.arrow]

end CategoryTheory.Subobject
