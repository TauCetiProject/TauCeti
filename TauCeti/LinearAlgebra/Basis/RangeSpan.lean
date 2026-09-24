/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spans of the images of a basis

A linear map has the same scalar-extended image span when evaluated on a basis as when evaluated
on its entire domain.
-/

public section

namespace Module.Basis

/-- Over a scalar extension, the image of a linear map is spanned by its values on any basis. -/
theorem span_range_eq_span_range_basis
    {R S M N ι : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (b : Module.Basis ι R M) (f : M →ₗ[R] N) :
    Submodule.span S (Set.range f) = Submodule.span S (Set.range (f ∘ b)) := by
  rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← b.span_eq,
    LinearMap.map_span, Submodule.span_span_of_tower]
  congr 1
  rw [Set.range_comp]

/-- A coordinate outside a set of basis indices vanishes on the span of those basis vectors. -/
theorem repr_eq_zero_of_mem_span_range
    {R V ι κ : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis ι R V) (e : κ → ι) {x : V} {i : ι}
    (hx : x ∈ Submodule.span R (Set.range fun k => b (e k)))
    (hi : i ∉ Set.range e) : b.repr x i = 0 := by
  have hset : Set.range (fun k => b (e k)) = b '' Set.range e := by
    simpa only [Function.comp_def] using (Set.range_comp (b : ι → V) e)
  have hx' : x ∈ Submodule.span R (b '' Set.range e) := by
    rw [← hset]
    exact hx
  have hsupp := b.mem_span_image.mp hx'
  exact Finsupp.notMem_support_iff.mp fun himem => hi (hsupp himem)

end Module.Basis

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
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    let y : I.map f.rangeRestrict := ⟨f.rangeRestrict x, Submodule.mem_map_of_mem x.2⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, by
      simp only [LinearMap.comp_apply]
      exact congrArg g (congrArg Subtype.val hxy)⟩

end LinearMap
