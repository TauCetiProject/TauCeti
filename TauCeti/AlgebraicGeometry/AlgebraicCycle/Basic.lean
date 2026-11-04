/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Pushforward of algebraic cycles

This file records basic support and coefficient lemmas for Mathlib's pushforward
`AlgebraicGeometry.AlgebraicCycle.map` of algebraic cycles along a quasi-compact morphism.

* `AlgebraicCycle.support_map_subset_range` and `AlgebraicCycle.map_apply_eq_zero_of_notMem_range`:
  a pushforward is supported on the image of the morphism.
* `AlgebraicCycle.map_height_apply_of_isClosedImmersion`: along a closed immersion, the pushforward
  with height weights transports coefficients, since closed immersions preserve heights and have
  residue degree one. Consequently it is additive, injective, supported on the image of the support
  and compatible with composition (`AlgebraicCycle.map_height_add_of_isClosedImmersion`,
  `AlgebraicCycle.map_height_injective_of_isClosedImmersion`,
  `AlgebraicCycle.support_map_height_of_isClosedImmersion`,
  `AlgebraicCycle.map_height_comp_of_isClosedImmersion`).
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {R : Type*} [Semiring R]

section map

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] {N : Type*} [DecidableEq N]
  (wx : X → N) (wy : Y → N)

/-- The pushforward of a cycle is supported on the image of the morphism. -/
lemma support_map_subset_range (c : AlgebraicCycle X R) :
    (map f wx wy c).support ⊆ Set.range f :=
  Function.locallyFinsupp.support_map_subset_of_forall_mem _ _ c Set.univ _
    (Set.subset_univ _) fun x _ _ ↦ Set.mem_range_self x

/-- The pushforward of a cycle vanishes off the image of the morphism. -/
lemma map_apply_eq_zero_of_notMem_range (c : AlgebraicCycle X R) {y : Y}
    (hy : y ∉ Set.range f) : map f wx wy c y = 0 :=
  Function.notMem_support.mp fun h ↦ hy (support_map_subset_range f wx wy c h)

end map

section ClosedImmersion

variable {X W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]

/-- Along a closed immersion, Mathlib's pushforward of cycles with height weights transports
coefficients: closed immersions preserve heights and have residue degree one. -/
lemma map_height_apply_of_isClosedImmersion (c : AlgebraicCycle W R) (y : W) :
    map i height height c (i y) = c y := by
  rw [map, Function.locallyFinsupp.map_apply, ← Set.image_singleton,
    i.isClosedEmbedding.injective.preimage_image, finsum_mem_singleton]
  simp [mapCoeff]

/-- Along a closed immersion, the pushforward with height weights is supported on the image of the
support. -/
lemma support_map_height_of_isClosedImmersion (c : AlgebraicCycle W R) :
    (map i height height c).support = i '' c.support := by
  ext x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    simp [map_height_apply_of_isClosedImmersion, i.isClosedEmbedding.injective.eq_iff]
  · simp only [Function.mem_support, map_apply_eq_zero_of_notMem_range i _ _ c hx, ne_eq,
      not_true_eq_false, Set.mem_image, false_iff, not_exists, not_and]
    exact fun y _ hy ↦ hx ⟨y, hy⟩

/-- Along a closed immersion, the pushforward with height weights is additive. -/
lemma map_height_add_of_isClosedImmersion (c d : AlgebraicCycle W R) :
    map i height height (c + d) = map i height height c + map i height height d := by
  ext x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    simp [map_height_apply_of_isClosedImmersion]
  · simp [map_apply_eq_zero_of_notMem_range i _ _ _ hx]

/-- Along a closed immersion, the pushforward with height weights is injective. -/
lemma map_height_injective_of_isClosedImmersion :
    Function.Injective (map (R := R) i height height) := fun c d h ↦ by
  ext y
  rw [← map_height_apply_of_isClosedImmersion i c y, h, map_height_apply_of_isClosedImmersion]

/-- The pushforward with height weights along a composite of closed immersions is the composite of
the pushforwards. -/
lemma map_height_comp_of_isClosedImmersion {V : Scheme.{u}} (i' : V ⟶ W) [IsClosedImmersion i']
    (c : AlgebraicCycle V R) :
    map (i' ≫ i) height height c = map i height height (map i' height height c) := by
  ext x
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    rw [map_height_apply_of_isClosedImmersion]
    by_cases hy : y ∈ Set.range i'
    · obtain ⟨z, rfl⟩ := hy
      rw [← Scheme.Hom.comp_apply, map_height_apply_of_isClosedImmersion,
        map_height_apply_of_isClosedImmersion]
    · rw [map_apply_eq_zero_of_notMem_range i' _ _ _ hy, map_apply_eq_zero_of_notMem_range]
      rintro ⟨z, hz⟩
      rw [Scheme.Hom.comp_apply, i.isClosedEmbedding.injective.eq_iff] at hz
      exact hy ⟨z, hz⟩
  · rw [map_apply_eq_zero_of_notMem_range i _ _ _ hx, map_apply_eq_zero_of_notMem_range]
    rintro ⟨z, rfl⟩
    exact hx ⟨i' z, (Scheme.Hom.comp_apply i' i z).symm⟩

end ClosedImmersion

end AlgebraicGeometry.AlgebraicCycle
