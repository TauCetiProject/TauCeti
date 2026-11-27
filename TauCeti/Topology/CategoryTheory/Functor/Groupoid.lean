/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic

/-!
# Transport of topological groupoids

A functor transports a topological groupoid structure to its domain when the object and
total-arrow topologies are induced along the functor.
-/

public section

open Topology TauCeti

namespace CategoryTheory.Functor

/-- A functor whose object and total-arrow maps are inducing transports the topological
groupoid structure of its codomain to its domain. -/
theorem isTopologicalGroupoid_of_isInducing {C D : Type*}
    [Category C] [IsGroupoid C] [Category D] [IsGroupoid D]
    [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
    [TopologicalSpace D] [TopologicalSpace (Quiver.Total D)] [IsTopologicalGroupoid D]
    (F : C ⥤ D) (h₀ : IsInducing F.obj) (h₁ : IsInducing F.toPrefunctor.mapTotal) :
    IsTopologicalGroupoid C := by
  refine ⟨h₀.continuous_iff.mpr ?_, h₀.continuous_iff.mpr ?_,
    h₁.continuous_iff.mpr ?_, h₁.continuous_iff.mpr ?_, h₁.continuous_iff.mpr ?_⟩
  · exact IsTopologicalGroupoid.continuous_source.comp h₁.continuous
  · exact IsTopologicalGroupoid.continuous_target.comp h₁.continuous
  · exact (IsTopologicalGroupoid.continuous_unit.comp h₀.continuous).congr fun x ↦ by
      simp
  · refine (IsTopologicalGroupoid.continuous_inverse.comp h₁.continuous).congr ?_
    rintro ⟨x, y, f⟩
    rw [Function.comp_apply, Prefunctor.mapTotal_mk]
    simp
  · let g (p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}) :
        {p : Quiver.Total D × Quiver.Total D // p.1.right = p.2.left} :=
      ⟨(F.toPrefunctor.mapTotal p.val.1, F.toPrefunctor.mapTotal p.val.2),
        congrArg F.obj p.property⟩
    have hg : Continuous g :=
      ((h₁.continuous.comp (continuous_fst.comp continuous_subtypeVal)).prodMk
        (h₁.continuous.comp (continuous_snd.comp continuous_subtypeVal))).subtype_mk _
    refine (IsTopologicalGroupoid.continuous_comp.comp hg).congr ?_
    rintro ⟨⟨⟨x, y, f⟩, ⟨y', z, k⟩⟩, h⟩
    dsimp only at h
    subst y'
    simp [g]

end CategoryTheory.Functor
