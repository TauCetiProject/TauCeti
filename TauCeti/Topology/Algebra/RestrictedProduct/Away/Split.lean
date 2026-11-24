/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Box

/-!
# Splitting a restricted product of groups at a finite set of indices

For a family of groups `G i` with subgroup-like reference sets `B i` and a finite set `T` of
indices, `TauCeti.restrictedProductSplit B T` is the isomorphism of `Πʳ i, [G i, B i]` with the
product of the finite product `Π i : T, G i` and the restricted product over the complement of
`T`. The reference sets may be any `SubgroupClass` family, and `T` is a `Finset`. For a family of
`Subgroup`s and a finite `Set` of indices, `TauCeti.awayDecomposition` in
`TauCeti/Topology/Algebra/RestrictedProduct/Away/Decomposition.lean` is the same splitting,
stated with `RestrictedProductGroup`.

## Main definitions and results

* `TauCeti.restrictedProductSplit`: the splitting at a finite set `T`, with its coordinate lemmas.
* `TauCeti.preimage_restrictedProductSplit_symm_box`: a box pulls back to the product of the box
  over `T` with the box over the complement.
-/

public section

open Filter RestrictedProduct Set
open scoped RestrictedProduct

namespace TauCeti

/-- For a finite set `T` of indices and `y` in a restricted product over the complement of `T`, a
set of indices is finite when each of its elements outside `T` is an index at which `y` leaves its
reference set. -/
theorem finite_of_forall_mem_imp_apply_notMem {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
    (T : Finset ι) (y : Πʳ i : {i // i ∉ T}, [R i.val, A i.val]) {s : Set ι}
    (hs : ∀ i (hi : i ∉ T), i ∈ s → y ⟨i, hi⟩ ∉ A i) : s.Finite :=
  (T.finite_toSet.union ((eventually_cofinite.mp y.property).image Subtype.val)).subset
    fun i hi ↦ by
      by_cases h : i ∈ T
      · exact Or.inl h
      · exact Or.inr ⟨⟨i, h⟩, hs i h hi, rfl⟩

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} {K : ι → Type*} [∀ i, Group (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- The splitting of `Πʳ i, [G i, B i]` at a finite set `T` of indices, as the product of the
finite product `Π i : T, G i` with the restricted product over the complement of `T`. -/
@[to_additive addRestrictedProductSplit /-- The splitting of `Πʳ i, [G i, B i]` at a
finite set `T` of indices, as the product of the finite product `Π i : T, G i` with the restricted
product over the complement of `T`. -/]
def restrictedProductSplit (B : ∀ i, K i) (T : Finset ι) :
    (Πʳ i, [G i, B i]) ≃* (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val] where
  toFun x := (fun i ↦ x i.val,
    ⟨fun i ↦ x i.val, Subtype.val_injective.tendsto_cofinite.eventually x.property⟩)
  invFun y := ⟨fun i ↦ if h : i ∈ T then y.1 ⟨i, h⟩ else y.2 ⟨i, h⟩,
    eventually_cofinite.mpr <| finite_of_forall_mem_imp_apply_notMem
      (A := fun i ↦ (B i : Set (G i))) T y.2 fun i h hi ↦ by simpa [h] using hi⟩
  left_inv x := by
    ext i
    simp
  right_inv y := by
    ext i
    · simp [i.property]
    · simp [i.property]
  map_mul' _ _ := rfl

variable (B : ∀ i, K i) (T : Finset ι)

/-- The finite component of `restrictedProductSplit B T` reads off the coordinates in `T`. -/
@[to_additive (attr := simp) addRestrictedProductSplit_apply_fst /-- The finite component of
`addRestrictedProductSplit B T` reads off the coordinates in `T`. -/]
theorem restrictedProductSplit_apply_fst (x : Πʳ i, [G i, B i]) (i : T) :
    (restrictedProductSplit B T x).1 i = x i := by
  rfl

/-- The restricted component of `restrictedProductSplit B T` reads off the coordinates outside
`T`. -/
@[to_additive (attr := simp) addRestrictedProductSplit_apply_snd /-- The restricted component of
`addRestrictedProductSplit B T` reads off the coordinates outside `T`. -/]
theorem restrictedProductSplit_apply_snd (x : Πʳ i, [G i, B i]) (i : {i // i ∉ T}) :
    (restrictedProductSplit B T x).2 i = x i := by
  rfl

/-- The inverse of `restrictedProductSplit B T` takes its coordinates in `T` from the finite
component and its other coordinates from the restricted component. -/
@[to_additive (attr := simp) addRestrictedProductSplit_symm_apply /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates in `T` from the finite component and its
other coordinates from the restricted component. -/]
theorem restrictedProductSplit_symm_apply
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) (i : ι) :
    (restrictedProductSplit B T).symm y i = if h : i ∈ T then y.1 ⟨i, h⟩ else y.2 ⟨i, h⟩ := by
  -- the inverse of the equivalence is its `invFun` field, by definition
  rfl

/-- The inverse of `restrictedProductSplit B T` takes its coordinates in `T` from the finite
component. -/
@[to_additive addRestrictedProductSplit_symm_apply_of_mem /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates in `T` from the finite component. -/]
theorem restrictedProductSplit_symm_apply_of_mem
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) {i : ι} (hi : i ∈ T) :
    (restrictedProductSplit B T).symm y i = y.1 ⟨i, hi⟩ := by
  simp [hi]

/-- The inverse of `restrictedProductSplit B T` takes its coordinates outside `T` from the
restricted component. -/
@[to_additive addRestrictedProductSplit_symm_apply_of_notMem /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates outside `T` from the restricted
component. -/]
theorem restrictedProductSplit_symm_apply_of_notMem
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) {i : ι} (hi : i ∉ T) :
    (restrictedProductSplit B T).symm y i = y.2 ⟨i, hi⟩ := by
  simp [hi]

/-- The inverse image of a box under the inverse of `restrictedProductSplit B T` is the product
of the box over `T` with the box over the complement. -/
@[to_additive preimage_addRestrictedProductSplit_symm_box /-- The inverse image of a box under the
inverse of `addRestrictedProductSplit B T` is the product of the box over `T` with the box over
the complement. -/]
theorem preimage_restrictedProductSplit_symm_box (C : ∀ i, Set (G i)) :
    (restrictedProductSplit B T).symm ⁻¹' box C =
      (univ.pi fun i : T ↦ C i) ×ˢ box fun i : {i // i ∉ T} ↦ C i := by
  ext y
  simp only [mem_preimage, mem_box, mem_prod, mem_univ_pi]
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩, fun ⟨h₁, h₂⟩ i ↦ ?_⟩
  · simpa [restrictedProductSplit_symm_apply_of_mem B T y i.property] using h i
  · simpa [restrictedProductSplit_symm_apply_of_notMem B T y i.property] using h i
  · by_cases hi : i ∈ T
    · simpa [restrictedProductSplit_symm_apply_of_mem B T y hi] using h₁ ⟨i, hi⟩
    · simpa [restrictedProductSplit_symm_apply_of_notMem B T y hi] using h₂ ⟨i, hi⟩

end TauCeti
