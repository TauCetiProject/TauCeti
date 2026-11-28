/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Finite products of restricted products

For a finite type `n`, a family `(j : n) → Πʳ i, [G j i, U j i]_[𝓕]` of elements of restricted
products is the same as one element of
`Πʳ i, [(j : n) → G j i, Set.univ.pi fun j ↦ U j i]_[𝓕]`, by swapping the two arguments. A family
is restricted coordinatewise exactly
when it is restricted jointly, because the filter is closed under finite intersections. This file
records that identification `TauCeti.piRestrictedProduct` as a multiplicative equivalence for every
filter, and shows that it is a homeomorphism for the cofinite filter when the reference sets are
open (`TauCeti.piRestrictedProductContinuousMulEquiv`).

Its use is to identify column vectors `n → 𝔸` over a restricted product ring `𝔸`, such as the
finite adeles of a Dedekind domain, with the restricted product of the column vectors over the
factors; a matrix over `𝔸` then acts factorwise.

Everything here is also stated for additive groups (`addPiRestrictedProduct`, …).

## References

* A. Weil, *Basic Number Theory*, Chapter IV, §1.
-/

public section

namespace TauCeti

open Filter Set
open scoped RestrictedProduct

variable {ι n : Type*} {G : n → ι → Type*} {S : n → ι → Type*}
variable [∀ j i, Group (G j i)] [∀ j i, SetLike (S j i) (G j i)]
  [∀ j i, SubgroupClass (S j i) (G j i)]
variable {𝓕 : Filter ι}

/-- A finite family of restricted products is equivalent to the restricted product of the finite
products, by swapping the two arguments. -/
@[to_additive addPiRestrictedProduct /-- A finite family of additive restricted products is
equivalent to the additive restricted product of the finite products, by swapping the two
arguments. -/]
def piRestrictedProduct [Finite n] (U : ∀ j i, S j i) :
    ((j : n) → Πʳ i, [G j i, (U j i : Set (G j i))]_[𝓕]) ≃*
      Πʳ i, [(j : n) → G j i,
        (Subgroup.pi univ fun j : n ↦ Subgroup.ofClass (U j i) : Set ((j : n) → G j i))]_[𝓕] where
  toFun x := ⟨fun i j ↦ x j i,
    (eventually_all.mpr fun j ↦ (x j).property).mono fun _ hi j _ ↦ hi j⟩
  invFun y j := ⟨fun i ↦ y i j, y.property.mono fun _ hi ↦ hi j (mem_univ j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (U : ∀ j i, S j i)

/-- The coordinates of the swapped family. -/
@[to_additive (attr := simp) addPiRestrictedProduct_apply /-- The coordinates of the swapped
additive family. -/]
theorem piRestrictedProduct_apply [Finite n]
    (x : (j : n) → Πʳ i, [G j i, (U j i : Set (G j i))]_[𝓕]) (i : ι)
    (j : n) :
    piRestrictedProduct U x i j = x j i := by
  rfl

/-- The coordinates of the inverse swap. -/
@[to_additive (attr := simp) addPiRestrictedProduct_symm_apply /-- The coordinates of the inverse
additive swap. -/]
theorem piRestrictedProduct_symm_apply [Finite n]
    (y : Πʳ i, [(j : n) → G j i,
        (Subgroup.pi univ fun j : n ↦ Subgroup.ofClass (U j i) : Set ((j : n) → G j i))]_[𝓕])
    (j : n) (i : ι) :
    (piRestrictedProduct U).symm y j i = y i j := by
  rfl

variable [∀ j i, TopologicalSpace (G j i)]

/-- The inverse swap is continuous for every filter and every reference family: each of its
components is a coordinatewise continuous map of restricted products. -/
@[to_additive continuous_addPiRestrictedProduct_symm /-- The inverse additive swap is continuous
for every filter and every reference family: each of its components is a coordinatewise continuous
map of restricted products. -/]
theorem continuous_piRestrictedProduct_symm [Finite n] :
    Continuous (piRestrictedProduct (G := G) (n := n) (𝓕 := 𝓕) U).symm :=
  continuous_pi fun j ↦ (RestrictedProduct.mapAlong_continuous
    (A₁ := fun i ↦ (Subgroup.pi univ fun j : n ↦ Subgroup.ofClass (U j i) : Set ((j : n) → G j i)))
    (A₂ := fun i ↦ (U j i : Set (G j i))) _ (G j) id tendsto_id (fun i (y : (j : n) → G j i) ↦ y j)
    (.of_forall fun _ _ hy ↦ hy j (mem_univ j)) fun _ ↦ continuous_apply j).congr fun y ↦ by
      ext i
      simp only [RestrictedProduct.mapAlong_apply, piRestrictedProduct_symm_apply, id_eq]

/-- For the cofinite filter and open reference sets, the swap is continuous. -/
@[to_additive continuous_addPiRestrictedProduct /-- For the cofinite filter and open reference
sets, the additive swap is continuous. -/]
theorem continuous_piRestrictedProduct [Finite n] (hU : ∀ j i, IsOpen (U j i : Set (G j i))) :
    Continuous (piRestrictedProduct (G := G) (n := n) (𝓕 := cofinite) U) := by
  -- The universal property reduces continuity to the principal stages, whose topology is
  -- induced from the full product.
  refine (RestrictedProduct.continuous_dom_pi hU).mpr fun T hT ↦ ?_
  -- On the stage `T`, the swap factors through the swap of the principal restricted products.
  let swapT : ((j : n) → Πʳ i, [G j i, (U j i : Set (G j i))]_[𝓟 T]) →
      Πʳ i, [(j : n) → G j i,
        (Subgroup.pi univ fun j : n ↦ Subgroup.ofClass (U j i) : Set ((j : n) → G j i))]_[𝓟 T] :=
    piRestrictedProduct U
  have hswapT : Continuous swapT :=
    RestrictedProduct.continuous_rng_of_principal.mpr <| continuous_pi fun i ↦ continuous_pi
      fun j ↦ ((RestrictedProduct.continuous_eval i).comp (continuous_apply j)).congr fun x ↦
        (piRestrictedProduct_apply U x i j).symm
  refine ((RestrictedProduct.continuous_inclusion hT).comp hswapT).congr fun x ↦ ?_
  ext i j
  simp only [Function.comp_apply, swapT, RestrictedProduct.inclusion_apply,
    piRestrictedProduct_apply, Pi.map_apply]

/-- For the cofinite filter and open reference sets, the swap of a finite family of elements of
restricted products of groups is a group isomorphism that is also a homeomorphism. -/
@[to_additive addPiRestrictedProductContinuousAddEquiv /-- For the cofinite filter and open
reference sets, the swap of a finite family of elements of additive restricted products of
additive groups is an additive group isomorphism that is also a homeomorphism. -/]
def piRestrictedProductContinuousMulEquiv [Finite n] (hU : ∀ j i, IsOpen (U j i : Set (G j i))) :
    ((j : n) → Πʳ i, [G j i, (U j i : Set (G j i))]) ≃ₜ*
      Πʳ i, [(j : n) → G j i,
        (Subgroup.pi univ fun j : n ↦ Subgroup.ofClass (U j i) : Set ((j : n) → G j i))] where
  toMulEquiv := piRestrictedProduct U
  continuous_toFun := continuous_piRestrictedProduct U hU
  continuous_invFun := continuous_piRestrictedProduct_symm U

/-- The topological swap is the swap. -/
@[to_additive (attr := simp) coe_addPiRestrictedProductContinuousAddEquiv /-- The topological
additive swap is the additive swap. -/]
theorem coe_piRestrictedProductContinuousMulEquiv [Finite n]
    (hU : ∀ j i, IsOpen (U j i : Set (G j i))) :
    ⇑(piRestrictedProductContinuousMulEquiv (n := n) U hU) = piRestrictedProduct U := by
  rfl

/-- The inverse of the topological swap is the inverse swap. -/
@[to_additive (attr := simp) coe_addPiRestrictedProductContinuousAddEquiv_symm /-- The inverse of
the topological additive swap is the inverse additive swap. -/]
theorem coe_piRestrictedProductContinuousMulEquiv_symm [Finite n]
    (hU : ∀ j i, IsOpen (U j i : Set (G j i))) :
    ⇑(piRestrictedProductContinuousMulEquiv (n := n) U hU).symm = (piRestrictedProduct U).symm := by
  rfl

end TauCeti
