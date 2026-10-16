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

/-!
# Factoring through subcomplexes of complexes of modules

A subcomplex `S` of a homological complex `L` of modules is recorded degreewise by the range of
the components of `S.arrow`. A morphism of complexes into `L` factors through `S` as soon as it
does degreewise, that is, as soon as each of its components lands in the range of the
corresponding component of `S.arrow` (`HomologicalComplex.factors_of_forall_mem_range`).

## Main results

* `HomologicalComplex.factors_iff_forall_mem_range`: a morphism factors through a subcomplex
  exactly when it does degreewise.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}

section Factors

variable {K L : HomologicalComplex (ModuleCat R) c} (S : Subobject L) (g : K ⟶ L)

/-- A morphism of complexes of modules whose components land in the ranges of the components of
the inclusion of a subcomplex factors through it: the lift is the inverse of the corestricted
inclusion, degree by degree. -/
theorem factors_of_forall_mem_range (h : ∀ n x, (g.f n).hom x ∈ LinearMap.range (S.arrow.f n).hom) :
    S.Factors g := by
  have hinj (n : ι) : Function.Injective (S.arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  -- The degreewise lift, through the isomorphism of `S` with the range of its inclusion.
  let l (n : ι) : K.X n ⟶ (S : HomologicalComplex (ModuleCat R) c).X n := ModuleCat.ofHom
    ((LinearEquiv.ofInjective _ (hinj n)).symm.toLinearMap ∘ₗ
      (g.f n).hom.codRestrict _ (h n))
  have hl (n : ι) (x : K.X n) : (S.arrow.f n).hom ((l n).hom x) = (g.f n).hom x :=
    by simp [l]
  let lift : K ⟶ (S : HomologicalComplex (ModuleCat R) c) :=
    { f := l, comm' := fun i j _ ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ hinj j (by
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hl]
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.Hom.comm,
          ModuleCat.hom_comp, LinearMap.comp_apply, hl, ← LinearMap.comp_apply,
          ← ModuleCat.hom_comp, HomologicalComplex.Hom.comm, ModuleCat.hom_comp,
          LinearMap.comp_apply])) }
  have e : lift ≫ S.arrow = g :=
    HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ hl n x)
  exact e ▸ Subobject.factors_comp_arrow lift

/-- A morphism of complexes of modules factors through a subcomplex exactly when each of its
components lands in the range of the corresponding component of the inclusion. -/
theorem factors_iff_forall_mem_range :
    S.Factors g ↔ ∀ n x, (g.f n).hom x ∈ LinearMap.range (S.arrow.f n).hom := by
  refine ⟨fun hS n x ↦ ⟨((S.factorThru g hS).f n).hom x, ?_⟩, factors_of_forall_mem_range S g⟩
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f,
    Subobject.factorThru_arrow]

end Factors

end HomologicalComplex
