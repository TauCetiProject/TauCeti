/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Continuity of maps into a restricted product

The topology of a restricted product `Πʳ i, [R i, A i]` is the final topology over its principal
stages `Πʳ i, [R i, A i]_[𝓟 T]`, `T` cofinite, and is in general strictly finer than the topology
induced from the full product `Π i, R i`. Continuity of a map *into* a restricted product therefore
does not follow from continuity of its coordinates. This file records two criteria that do apply:
the first when the map is controlled by a single stage, the second by applying the first stagewise
through the universal property of the restricted product.

* `continuous_restrictedProduct_iff_of_forall_mem`: a map whose values all lie in one principal
  stage of the filter is continuous exactly when it is continuous into the full product.
* `continuous_restrictedProduct_of_apply_eq_of_isOpen`: for a finite set `S` of indices, a map
  recombining an arbitrary family of coordinates on `S` with a restricted-product element away
  from `S` is continuous, provided the reference sets away from `S` are open. Its domain is a
  product with a restricted-product factor, so the openness hypothesis is that of Mathlib's
  universal property with parameters, `RestrictedProduct.continuous_dom_prod_left`, and it is
  asked only at the indices carrying a reference set. This is the topological input for the
  inverse of the decomposition of a restricted product into the plain product over a finite set
  of indices times the restricted product away from it. The openness hypothesis cannot be
  dropped: see `not_continuous_restrictedProduct_of_apply_eq_rat_bot`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- A map into a restricted product whose values all lie in a principal stage `T` of the filter
is continuous exactly when it is continuous as a map into the full product `Π i, R i`. -/
theorem continuous_restrictedProduct_iff_of_forall_mem {X : Type*} [TopologicalSpace X]
    {𝓕 : Filter ι} {f : X → Πʳ i, [R i, A i]_[𝓕]} {T : Set ι} (hT : 𝓕 ≤ 𝓟 T)
    (hf : ∀ x, ∀ i ∈ T, f x i ∈ A i) :
    Continuous f ↔ Continuous fun x ↦ (f x : ∀ i, R i) := by
  refine ⟨fun h ↦ RestrictedProduct.continuous_coe.comp h, fun h ↦ ?_⟩
  let g : X → Πʳ i, [R i, A i]_[𝓟 T] :=
    fun x ↦ ⟨f x, eventually_principal.mpr (hf x)⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.mpr h
  exact (RestrictedProduct.continuous_inclusion hT).comp hg

/-- For a finite set `S` of indices, a map that recombines a family of coordinates on `S` with a
restricted-product element away from `S` into an element of the full restricted product is
continuous when the reference sets away from `S` are open. The map is pinned by its two coordinate
formulas: on `S` it returns the given coordinate, and away from `S` it returns the coordinate of
the given restricted-product element. -/
theorem continuous_restrictedProduct_of_apply_eq_of_isOpen {S : Set ι} (hS : S.Finite)
    (hA : ∀ i ∉ S, IsOpen (A i))
    {f : (∀ i : S, R i) × (Πʳ j : {j // j ∉ S}, [R j, A j]) → Πʳ i, [R i, A i]}
    (hmem : ∀ p (i : S), f p i = p.1 i)
    (hnotMem : ∀ p (j : {j // j ∉ S}), f p j = p.2 j) :
    Continuous f := by
  rw [RestrictedProduct.continuous_dom_prod_left fun j : {j // j ∉ S} ↦ hA j.1 j.2]
  intro T hT
  have hT' : cofinite ≤ 𝓟 (Subtype.val '' T) := by
    rw [le_principal_iff, mem_cofinite]
    refine (hS.union ((mem_cofinite.mp (le_principal_iff.mp hT)).image Subtype.val)).subset ?_
    intro i hi
    by_cases hiS : i ∈ S
    · exact Or.inl hiS
    · exact Or.inr ⟨⟨i, hiS⟩, fun h ↦ hi ⟨⟨i, hiS⟩, h, rfl⟩, rfl⟩
  have hmem' : ∀ p (i : S), (f ∘ Prod.map id (RestrictedProduct.inclusion _ _ hT)) p i = p.1 i :=
    fun p i ↦ hmem _ i
  have hnotMem' : ∀ p (j : {j // j ∉ S}),
      (f ∘ Prod.map id (RestrictedProduct.inclusion _ _ hT)) p j = p.2 j :=
    fun p j ↦ (hnotMem _ j).trans (RestrictedProduct.inclusion_apply _ _ hT j)
  rw [continuous_restrictedProduct_iff_of_forall_mem hT']
  · refine continuous_pi fun i ↦ ?_
    by_cases hi : i ∈ S
    · exact ((continuous_apply (⟨i, hi⟩ : S)).comp continuous_fst).congr
        fun p ↦ (hmem' p ⟨i, hi⟩).symm
    · exact ((RestrictedProduct.continuous_eval (⟨i, hi⟩ : {j // j ∉ S})).comp
        continuous_snd).congr fun p ↦ (hnotMem' p ⟨i, hi⟩).symm
  · rintro p i ⟨j, hj, rfl⟩
    rw [hnotMem' p j]
    exact eventually_principal.mp p.2.2 j hj

end TauCeti
