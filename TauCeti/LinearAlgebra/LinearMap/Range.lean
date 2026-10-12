/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Ranges of composite linear maps

Range identities for factoring a composite through a linear map's image.
-/

public section

namespace LinearMap

/-- Composing through the range restriction does not change a composite linear map's range. -/
theorem range_comp_rangeRestrict
    {R V W N : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid N] [Module R N]
    (f : V →ₗ[R] W) (g : W →ₗ[R] N) :
    Set.range (g.comp f) = Set.range (g.comp f.range.subtype) := by
  have h : (g.comp f).range = (g.comp f.range.subtype).range := by
    simpa only [LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict] using
      (LinearMap.range_comp_of_range_eq_top (g.comp f.range.subtype)
        (LinearMap.range_rangeRestrict f))
  simpa only [LinearMap.coe_range] using
    congrArg (fun p : Submodule R N => (p : Set N)) h

/-- Mapping a submodule into a linear map's range does not change the composite range. -/
theorem range_comp_map_subtype
    {R V W N : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid N] [Module R N]
    (f : V →ₗ[R] W) (I : Submodule R V) (g : W →ₗ[R] N) :
    Set.range (g.comp (f.comp I.subtype)) =
      Set.range ((g.comp f.range.subtype).comp (I.map f.rangeRestrict).subtype) := by
  have h : (g.comp (f.comp I.subtype)).range =
      ((g.comp f.range.subtype).comp (I.map f.rangeRestrict).subtype).range := by
    simp only [LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp,
      LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict]
  simpa only [LinearMap.coe_range] using
    congrArg (fun p : Submodule R N => (p : Set N)) h

end LinearMap
