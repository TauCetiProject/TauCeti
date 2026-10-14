/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.RepresentationTheory.Continuous.TopRep.KernelCokernel

import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Monomorphisms and epimorphisms of smooth discrete representations

In the full subcategory `TauCeti.SmoothDiscreteTopRep R G` of `TopRep R G`, the monomorphisms are
the injective morphisms and the epimorphisms are the surjective ones. The kernel of a morphism of
smooth discrete representations, with the subspace topology, is again smooth discrete, and so is
its cokernel with the quotient topology, the latter because stabilizers in the quotient contain
open stabilizers upstairs. A monomorphism therefore has zero kernel and an epimorphism has zero
cokernel.

This is what lets an exactness statement about underlying maps, such as
`TauCeti.coindFunctor_map_shortExact`, be read as a statement about monomorphisms and
epimorphisms of the category.

## Main results

* `TauCeti.SmoothDiscreteTopRep.mono_iff_injective`: a morphism is a monomorphism exactly when it
  is injective.
* `TauCeti.SmoothDiscreteTopRep.epi_iff_surjective`: over a group with separately continuous
  multiplication, a morphism is an epimorphism exactly when it is surjective.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

namespace SmoothDiscreteTopRep

variable {R : Type u} [Ring R] [TopologicalSpace R]

/-- A morphism of smooth discrete representations is a monomorphism exactly when it is
injective. -/
theorem mono_iff_injective {G : Type v} [Monoid G] [TopologicalSpace G]
    {A B : SmoothDiscreteTopRep.{u, v, w} R G} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f.hom.hom := by
  refine ⟨fun hf x y hxy ↦ ?_, fun hf ↦
    (smoothDiscreteι R G).mono_of_mono_map (ConcreteCategory.mono_of_injective _ hf)⟩
  -- the kernel of `f` is smooth discrete, and `f` kills its inclusion, which is therefore zero
  let K : SmoothDiscreteTopRep.{u, v, w} R G :=
    ⟨TopRep.ker f.hom, .of_injective _ (TopRep.kerι_injective f.hom) A.property⟩
  let i : K ⟶ A := ObjectProperty.homMk (TopRep.kerι f.hom)
  have hi : i = 0 := (cancel_mono f).1 <| ObjectProperty.hom_ext _ (by simp [i])
  have hxy' : x - y ∈ f.hom.hom.ker := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hxy
  have h := congr(($hi).hom.hom ⟨x - y, hxy'⟩)
  simp only [i, ObjectProperty.homMk_hom, ObjectProperty.zero_hom, TopRep.hom_zero,
    ContIntertwiningMap.zero_apply] at h
  rw [TopRep.kerι_apply] at h
  exact sub_eq_zero.1 h

/-- Over a group with separately continuous multiplication, a morphism of smooth discrete
representations is an epimorphism exactly when it is surjective. -/
theorem epi_iff_surjective {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {A B : SmoothDiscreteTopRep.{u, v, w} R G} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f.hom.hom := by
  refine ⟨fun hf b ↦ ?_, fun hf ↦
    (smoothDiscreteι R G).epi_of_epi_map (ConcreteCategory.epi_of_surjective _ hf)⟩
  -- the cokernel of `f` is smooth discrete, and its projection kills `f`, so it is zero
  have : DiscreteTopology (TopRep.coker f.hom).V :=
    QuotientAddGroup.discreteTopology (N := f.hom.hom.range.toAddSubgroup) (isOpen_discrete _)
  let Q : SmoothDiscreteTopRep.{u, v, w} R G :=
    ⟨TopRep.coker f.hom, .of_surjective _ (TopRep.cokerπ_surjective f.hom) B.property⟩
  let p : B ⟶ Q := ObjectProperty.homMk (TopRep.cokerπ f.hom)
  have hp : p = 0 := (cancel_epi f).1 <| ObjectProperty.hom_ext _ (by simp [p])
  have h := congr(($hp).hom.hom b)
  rw [ObjectProperty.homMk_hom, TopRep.cokerπ_apply, ObjectProperty.zero_hom, TopRep.hom_zero,
    ContIntertwiningMap.zero_apply, Submodule.Quotient.mk_eq_zero] at h
  exact h

end SmoothDiscreteTopRep

end TauCeti
