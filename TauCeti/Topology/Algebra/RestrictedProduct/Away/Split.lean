/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Decomposition
public import TauCeti.Topology.Algebra.RestrictedProduct.Box

/-!
# Splitting a restricted product of groups at a finite set of indices

For a family of groups `G i` with subgroup-like reference sets `B i` and a finite set `T` of
indices, `TauCeti.restrictedProductSplit B T` is the isomorphism of `Πʳ i, [G i, B i]` with the
product of the finite product `Π i : T, G i` and the restricted product over the complement of
`T`. The reference sets may be any `SubgroupClass` family, and `T` is a `Finset`. It is
`TauCeti.awayDecomposition`, from
`TauCeti/Topology/Algebra/RestrictedProduct/Away/Decomposition.lean`, for the `Subgroup` family
`Subgroup.ofClass (B i)` and the set `(T : Set ι)`, restated with the reference sets `B i`
themselves, so that it applies directly to restricted products such as the domain of
`TauCeti.restrictedHaar`; its coordinate and continuity lemmas are those of
`TauCeti.awayDecomposition`.

## Main definitions and results

* `TauCeti.restrictedProductSplit`: the splitting at a finite set `T`, with its coordinate lemmas.
* `TauCeti.continuous_restrictedProductSplit`, `TauCeti.continuous_restrictedProductSplit_symm`:
  the splitting is continuous, and so is its inverse when the reference sets outside `T` are open.
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

variable {ι : Type*} {G : ι → Type*} {K : ι → Type*} [∀ i, Group (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- The splitting of `Πʳ i, [G i, B i]` at a finite set `T` of indices, as the product of the
finite product `Π i : T, G i` with the restricted product over the complement of `T`.

This is `awayDecomposition` for the `Subgroup` family `Subgroup.ofClass (B i)` and the finite set
`(T : Set ι)`. Its type is stated with the reference sets `B i` and the subtype of `T` themselves,
which agree with those of `awayDecomposition` only up to unfolding `Subgroup.ofClass` and the
coercion of `T` to a set; the coordinate and continuity lemmas below are transported once here, so
that users never see that unfolding. -/
@[to_additive addRestrictedProductSplit /-- The splitting of `Πʳ i, [G i, B i]` at a
finite set `T` of indices, as the product of the finite product `Π i : T, G i` with the restricted
product over the complement of `T`.

This is `addAwayDecomposition` for the `AddSubgroup` family `AddSubgroup.ofClass (B i)` and the
finite set `(T : Set ι)`. Its type is stated with the reference sets `B i` and the subtype of `T`
themselves, which agree with those of `addAwayDecomposition` only up to unfolding
`AddSubgroup.ofClass` and the coercion of `T` to a set; the coordinate and continuity lemmas below
are transported once here, so that users never see that unfolding. -/]
noncomputable def restrictedProductSplit (B : ∀ i, K i) (T : Finset ι) :
    (Πʳ i, [G i, B i]) ≃* (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val] :=
  awayDecomposition (T : Set ι) T.finite_toSet fun i ↦ Subgroup.ofClass (B i)

variable (B : ∀ i, K i) (T : Finset ι)

/-- The finite component of `restrictedProductSplit B T` reads off the coordinates in `T`. -/
@[to_additive (attr := simp) addRestrictedProductSplit_apply_fst /-- The finite component of
`addRestrictedProductSplit B T` reads off the coordinates in `T`. -/]
theorem restrictedProductSplit_apply_fst (x : Πʳ i, [G i, B i]) (i : T) :
    (restrictedProductSplit B T x).1 i = x i :=
  awayDecomposition_fst (T : Set ι) T.finite_toSet (fun i ↦ Subgroup.ofClass (B i)) x i

/-- The restricted component of `restrictedProductSplit B T` reads off the coordinates outside
`T`. -/
@[to_additive (attr := simp) addRestrictedProductSplit_apply_snd /-- The restricted component of
`addRestrictedProductSplit B T` reads off the coordinates outside `T`. -/]
theorem restrictedProductSplit_apply_snd (x : Πʳ i, [G i, B i]) (i : {i // i ∉ T}) :
    (restrictedProductSplit B T x).2 i = x i :=
  awayDecomposition_snd (T : Set ι) T.finite_toSet (fun i ↦ Subgroup.ofClass (B i)) x i

/-- The inverse of `restrictedProductSplit B T` takes its coordinates in `T` from the finite
component. -/
@[to_additive addRestrictedProductSplit_symm_apply_of_mem /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates in `T` from the finite component. -/]
theorem restrictedProductSplit_symm_apply_of_mem
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) {i : ι} (hi : i ∈ T) :
    (restrictedProductSplit B T).symm y i = y.1 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_mem (T : Set ι) T.finite_toSet
    (fun i ↦ Subgroup.ofClass (B i)) y i hi

/-- The inverse of `restrictedProductSplit B T` takes its coordinates outside `T` from the
restricted component. -/
@[to_additive addRestrictedProductSplit_symm_apply_of_notMem /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates outside `T` from the restricted
component. -/]
theorem restrictedProductSplit_symm_apply_of_notMem
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) {i : ι} (hi : i ∉ T) :
    (restrictedProductSplit B T).symm y i = y.2 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_notMem (T : Set ι) T.finite_toSet
    (fun i ↦ Subgroup.ofClass (B i)) y i hi

/-- The inverse of `restrictedProductSplit B T` takes its coordinates in `T` from the finite
component and its other coordinates from the restricted component. -/
@[to_additive (attr := simp) addRestrictedProductSplit_symm_apply /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates in `T` from the finite component and its
other coordinates from the restricted component. -/]
theorem restrictedProductSplit_symm_apply [DecidableEq ι]
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) (i : ι) :
    (restrictedProductSplit B T).symm y i = if h : i ∈ T then y.1 ⟨i, h⟩ else y.2 ⟨i, h⟩ := by
  split_ifs with h
  · exact restrictedProductSplit_symm_apply_of_mem B T y h
  · exact restrictedProductSplit_symm_apply_of_notMem B T y h

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

section Topology

variable [∀ i, TopologicalSpace (G i)]

/-- The splitting `restrictedProductSplit B T` is continuous for every reference family, by
`continuous_awayDecomposition`. -/
@[to_additive continuous_addRestrictedProductSplit /-- The splitting
`addRestrictedProductSplit B T` is continuous for every reference family, by
`continuous_addAwayDecomposition`. -/]
theorem continuous_restrictedProductSplit : Continuous (restrictedProductSplit B T) :=
  continuous_awayDecomposition (T : Set ι) T.finite_toSet fun i ↦ Subgroup.ofClass (B i)

/-- The inverse of `restrictedProductSplit B T` is continuous when the reference sets outside `T`
are open; the reference sets in `T` play no role (`continuous_awayDecomposition_symm`). -/
@[to_additive continuous_addRestrictedProductSplit_symm /-- The inverse of
`addRestrictedProductSplit B T` is continuous when the reference sets outside `T` are open; the
reference sets in `T` play no role (`continuous_addAwayDecomposition_symm`). -/]
theorem continuous_restrictedProductSplit_symm (hB : ∀ i ∉ T, IsOpen (B i : Set (G i))) :
    Continuous (restrictedProductSplit B T).symm :=
  continuous_awayDecomposition_symm (T : Set ι) T.finite_toSet (fun i ↦ Subgroup.ofClass (B i)) hB

end Topology

end TauCeti
