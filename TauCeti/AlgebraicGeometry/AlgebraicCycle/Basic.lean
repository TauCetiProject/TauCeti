/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.Topology.LocallyFinsupp.LocallyFiniteSum
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Pushforward of algebraic cycles

This file records basic support and coefficient lemmas for Mathlib's pushforward
`AlgebraicGeometry.AlgebraicCycle.map` of algebraic cycles along a quasi-compact morphism.

* `AlgebraicCycle.support_map_subset_range` and `AlgebraicCycle.map_apply_eq_zero_of_notMem_range`:
  a pushforward is supported on the image of the morphism.
* `AlgebraicCycle.finite_preimage_singleton_inter_support` and `AlgebraicCycle.map_add`: a cycle
  has finitely many points of nonzero coefficient in each fibre, and the pushforward is additive.
* `AlgebraicCycle.map_comp`: the pushforward is functorial when the multiplicities are
  multiplicative along composites.
* `AlgebraicCycle.locallyFinite_support_map` and `AlgebraicCycle.map_locallyFiniteSum`: the
  pushforward preserves local finiteness of families of supports and commutes with locally finite
  sums.
* `AlgebraicCycle.map_height_apply_of_isClosedImmersion`: along a closed immersion, the pushforward
  with height weights transports coefficients, since closed immersions preserve heights and have
  residue degree one. Consequently it is injective, supported on the image of the support and
  compatible with composition (`AlgebraicCycle.map_height_injective_of_isClosedImmersion`,
  `AlgebraicCycle.support_map_height_of_isClosedImmersion`,
  `AlgebraicCycle.map_height_comp_of_isClosedImmersion`, the last for a closed immersion followed
  by any quasi-compact morphism).
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

/-- A cycle has only finitely many points with nonzero coefficient in each fibre of a
quasi-compact morphism: a fibre lies in the preimage of an affine open, which is quasi-compact. -/
lemma finite_preimage_singleton_inter_support (c : AlgebraicCycle X R) (y : Y) :
    (f ⁻¹' {y} ∩ c.support).Finite := by
  obtain ⟨U, -, hyU, hK⟩ := f.exists_isOpen_mem_isCompact_preimage y
  exact (c.locallyFiniteSupport.finite_inter_support_of_isCompact hK).subset
    (Set.inter_subset_inter_left _ (Set.preimage_mono (Set.singleton_subset_iff.mpr hyU)))

/-- A cycle with pointwise weighted coefficients has only finitely many points with nonzero
coefficient in each fibre of a quasi-compact morphism. -/
private lemma finite_preimage_singleton_inter_support_mul (c : AlgebraicCycle X R) (w : X → R)
    (y : Y) : (f ⁻¹' {y} ∩ Function.support fun x ↦ c x * w x).Finite :=
  (finite_preimage_singleton_inter_support f c y).subset
    (Set.inter_subset_inter_right _ (Function.support_mul_subset_left _ _))

/-- The pushforward along a quasi-compact morphism of a family of cycles with locally finite
supports again has locally finite supports: the preimage of an affine open is quasi-compact, so it
meets only finitely many of the original supports. -/
lemma locallyFinite_support_map {ι : Type*} (c : ι → AlgebraicCycle X R)
    (hc : LocallyFinite fun i ↦ (c i).support) :
    LocallyFinite fun i ↦ (map f wx wy (c i)).support := by
  intro y
  obtain ⟨U, hU, hyU, hK⟩ := f.exists_isOpen_mem_isCompact_preimage y
  refine ⟨U, hU.mem_nhds hyU, (hc.finite_nonempty_inter_compact hK).subset ?_⟩
  rintro i ⟨z, hz, hzU⟩
  obtain ⟨x, rfl, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hz
  exact ⟨x, left_ne_zero_of_mul hx, hzU⟩

/-- The pushforward of cycles is additive. -/
lemma map_add (c d : AlgebraicCycle X R) :
    map f wx wy (c + d) = map f wx wy c + map f wx wy d := by
  ext y
  simp only [map, Function.locallyFinsupp.map_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, add_mul]
  exact finsum_mem_add_distrib' (finite_preimage_singleton_inter_support_mul f c _ y)
    (finite_preimage_singleton_inter_support_mul f d _ y)

/-- The pushforward along a quasi-compact morphism of a locally finite sum of cycles is the
locally finite sum of the pushforwards. -/
lemma map_locallyFiniteSum {ι : Type*} (c : ι → AlgebraicCycle X R)
    (hc : LocallyFinite fun i ↦ (c i).support) :
    map f wx wy (Function.locallyFinsupp.locallyFiniteSum c hc) =
      Function.locallyFinsupp.locallyFiniteSum (fun i ↦ map f wx wy (c i))
        (locallyFinite_support_map f wx wy c hc) := by
  classical
  ext y
  simp only [map, Function.locallyFinsupp.map_apply,
    Function.locallyFinsupp.locallyFiniteSum_apply]
  -- Only finitely many members `c i` meet the quasi-compact preimage `K` of an affine open
  -- neighbourhood of `y`, and each meets the fibre over `y` in finitely many points.
  obtain ⟨U, -, hyU, hK⟩ := f.exists_isOpen_mem_isCompact_preimage y
  have hI := hc.finite_nonempty_inter_compact hK
  have hS : (⋃ i ∈ {i | ((c i).support ∩ f ⁻¹' U).Nonempty},
      f ⁻¹' {y} ∩ (c i).support).Finite :=
    hI.biUnion fun i _ ↦ finite_preimage_singleton_inter_support f (c i) y
  have hfib {x : X} (hx : f x = y) {i : ι} (hi : c i x ≠ 0) : i ∈ hI.toFinset :=
    hI.mem_toFinset.mpr ⟨x, hi, by rw [Set.mem_preimage, hx]; exact hyU⟩
  have hsum {x : X} (hx : f x = y) : ∑ᶠ i, c i x = ∑ i ∈ hI.toFinset, c i x :=
    finsum_eq_sum_of_support_subset _ fun i hi ↦ hfib hx hi
  have hmem {x : X} (hx : f x = y) {i : ι} (hi : c i x ≠ 0) : x ∈ hS.toFinset :=
    hS.mem_toFinset.mpr (Set.mem_biUnion (hI.mem_toFinset.mp (hfib hx hi)) ⟨hx, hi⟩)
  have hsub : (hS.toFinset : Set X) ⊆ f ⁻¹' {y} := fun x hx ↦ by
    obtain ⟨i, -, hx, -⟩ := Set.mem_iUnion₂.mp (hS.mem_toFinset.mp hx)
    exact hx
  rw [finsum_mem_eq_sum_of_subset _ (t := hS.toFinset) ?_ hsub,
    finsum_eq_sum_of_support_subset (s := hI.toFinset), Finset.sum_congr rfl fun x hx ↦ by
      rw [hsum (hsub hx), Finset.sum_mul], Finset.sum_comm]
  · refine Finset.sum_congr rfl fun i _ ↦ (finsum_mem_eq_sum_of_subset _ ?_ hsub).symm
    rintro x ⟨hx, hix⟩
    exact hmem hx (left_ne_zero_of_mul hix)
  · intro i hi
    obtain ⟨x, hx, hix⟩ := exists_ne_zero_of_finsum_mem_ne_zero hi
    exact hfib hx (left_ne_zero_of_mul hix)
  · rintro x ⟨hx, hsx⟩
    obtain ⟨i, hi⟩ : ∃ i, c i x ≠ 0 := by
      by_contra! h
      exact hsx (by simp [h])
    exact hmem hx hi

/-- The pushforward of cycles is functorial for weights whose multiplicities are multiplicative
along the composite, such as height weights over a field. -/
lemma map_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [QuasiCompact g] (wz : Z → N)
    (c : AlgebraicCycle X R)
    (h : ∀ x, mapCoeff (f ≫ g) wx wz x = mapCoeff g wy wz (f x) * mapCoeff f wx wy x) :
    map (f ≫ g) wx wz c = map g wy wz (map f wx wy c) := by
  ext z
  simp only [map, Function.locallyFinsupp.map_apply]
  have hpre : (f ≫ g) ⁻¹' {z} = f ⁻¹' (g ⁻¹' {z}) := by
    ext
    simp
  have hfin : (f ⁻¹' (g ⁻¹' {z}) ∩
      Function.support fun x ↦ c x * (mapCoeff (f ≫ g) wx wz x : R)).Finite :=
    hpre ▸ finite_preimage_singleton_inter_support_mul (f ≫ g) c _ z
  rw [hpre, ← TauCeti.finsum_mem_fiberwise f (g ⁻¹' {z}) _ hfin]
  refine finsum_mem_congr rfl fun y _ ↦ ?_
  rw [← AddMonoidHom.mulRight_apply,
    AddMonoidHom.map_finsum_mem' _ (finite_preimage_singleton_inter_support_mul f c _ y)]
  simp only [AddMonoidHom.mulRight_apply]
  refine finsum_mem_congr rfl fun x hx ↦ ?_
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [h, ← hx, mul_assoc, ← Nat.cast_mul, Nat.mul_comm (mapCoeff g wy wz (f x))]

end map

section ClosedImmersion

variable {X W : Scheme.{u}}

section

variable (i : W ⟶ X) [IsClosedImmersion i]

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

/-- Along a closed immersion, the pushforward with height weights is injective. -/
lemma map_height_injective_of_isClosedImmersion :
    Function.Injective (map (R := R) i height height) := fun c d h ↦ by
  ext y
  rw [← map_height_apply_of_isClosedImmersion i c y, h, map_height_apply_of_isClosedImmersion]

end

/-- The pushforward with height weights along a closed immersion followed by a quasi-compact
morphism is the composite of the pushforwards: the closed immersion preserves heights and has
residue degree one. -/
lemma map_height_comp_of_isClosedImmersion {V Y : Scheme.{u}} (i' : V ⟶ W) [IsClosedImmersion i']
    (f : W ⟶ Y) [QuasiCompact f] (c : AlgebraicCycle V R) :
    map (i' ≫ f) height height c = map f height height (map i' height height c) :=
  map_comp i' height height f height c fun x ↦ by
    simp [mapCoeff, Scheme.Hom.height_apply_eq_height]

end ClosedImmersion

end AlgebraicGeometry.AlgebraicCycle
