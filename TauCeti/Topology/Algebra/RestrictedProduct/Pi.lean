/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Finite products of restricted products

For a finite type `n`, a family `n → Πʳ i, [G i, U i]_[𝓕]` of elements of one restricted product
is the same as one element of the restricted product `Πʳ i, [n → G i, Set.univ.pi fun _ ↦ U i]_[𝓕]`
of the finite powers, by swapping the two arguments: a family is restricted coordinatewise exactly
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

variable {ι n : Type*} {G : ι → Type*} {S : ι → Type*}
variable [∀ i, Group (G i)] [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
variable {𝓕 : Filter ι}

/-- A finite family of elements of a restricted product is an element of the restricted product
of the finite powers, by swapping the two arguments. -/
@[to_additive addPiRestrictedProduct /-- A finite family of elements of an additive restricted
product is an element of the additive restricted product of the finite powers, by swapping the two
arguments. -/]
def piRestrictedProduct [Finite n] (U : ∀ i, S i) :
    (n → Πʳ i, [G i, (U i : Set (G i))]_[𝓕]) ≃*
      Πʳ i, [n → G i,
        (Subgroup.pi univ fun _ : n ↦ Subgroup.ofClass (U i) : Set (n → G i))]_[𝓕] where
  toFun x := ⟨fun i j ↦ x j i,
    (eventually_all.mpr fun j ↦ (x j).property).mono fun _ hi j _ ↦ hi j⟩
  invFun y j := ⟨fun i ↦ y i j, y.property.mono fun _ hi ↦ hi j (mem_univ j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (U : ∀ i, S i)

/-- The coordinates of the swapped family. -/
@[to_additive (attr := simp) addPiRestrictedProduct_apply /-- The coordinates of the swapped
additive family. -/]
theorem piRestrictedProduct_apply [Finite n] (x : n → Πʳ i, [G i, (U i : Set (G i))]_[𝓕]) (i : ι)
    (j : n) :
    piRestrictedProduct U x i j = x j i := by
  rfl

/-- The coordinates of the inverse swap. -/
@[to_additive (attr := simp) addPiRestrictedProduct_symm_apply /-- The coordinates of the inverse
additive swap. -/]
theorem piRestrictedProduct_symm_apply [Finite n]
    (y : Πʳ i, [n → G i,
        (Subgroup.pi univ fun _ : n ↦ Subgroup.ofClass (U i) : Set (n → G i))]_[𝓕])
    (j : n) (i : ι) :
    (piRestrictedProduct U).symm y j i = y i j := by
  rfl

variable [∀ i, TopologicalSpace (G i)]

/-- The inverse swap is continuous for every filter and every reference family: each of its
components is a coordinatewise continuous map of restricted products. -/
@[to_additive continuous_addPiRestrictedProduct_symm /-- The inverse additive swap is continuous
for every filter and every reference family: each of its components is a coordinatewise continuous
map of restricted products. -/]
theorem continuous_piRestrictedProduct_symm [Finite n] :
    Continuous (piRestrictedProduct (G := G) (n := n) (𝓕 := 𝓕) U).symm :=
  continuous_pi fun j ↦ RestrictedProduct.mapAlong_continuous
    (A₁ := fun i ↦ (Subgroup.pi univ fun _ : n ↦ Subgroup.ofClass (U i) : Set (n → G i)))
    (A₂ := fun i ↦ (U i : Set (G i))) _ G id tendsto_id (fun i (y : n → G i) ↦ y j)
    (.of_forall fun _ _ hy ↦ hy j (mem_univ j)) fun _ ↦ continuous_apply j

/-- For the cofinite filter and open reference sets, the swap is continuous: by Mathlib's
universal property of a finite product of restricted products, it suffices to check this on the
principal stages, where the topology is induced from the full product. -/
@[to_additive continuous_addPiRestrictedProduct /-- For the cofinite filter and open reference
sets, the additive swap is continuous: by Mathlib's universal property of a finite product of
restricted products, it suffices to check this on the principal stages, where the topology is
induced from the full product. -/]
theorem continuous_piRestrictedProduct [Finite n] (hU : ∀ i, IsOpen (U i : Set (G i))) :
    Continuous (piRestrictedProduct (G := G) (n := n) (𝓕 := cofinite) U) := by
  refine (RestrictedProduct.continuous_dom_pi fun _ ↦ hU).mpr fun T hT ↦ ?_
  -- On the stage `T`, the swap factors through the swap of the principal restricted products.
  let swapT : (n → Πʳ i, [G i, (U i : Set (G i))]_[𝓟 T]) →
      Πʳ i, [n → G i,
        (Subgroup.pi univ fun _ : n ↦ Subgroup.ofClass (U i) : Set (n → G i))]_[𝓟 T] :=
    piRestrictedProduct U
  have hswapT : Continuous swapT :=
    RestrictedProduct.continuous_rng_of_principal.mpr <| continuous_pi fun i ↦ continuous_pi
      fun j ↦ (RestrictedProduct.continuous_eval i).comp (continuous_apply j)
  exact (RestrictedProduct.continuous_inclusion hT).comp hswapT

/-- For the cofinite filter and open reference sets, the swap of a finite family of elements of
a restricted product of topological groups is an isomorphism of topological groups. -/
@[to_additive addPiRestrictedProductContinuousAddEquiv /-- For the cofinite filter and open
reference sets, the swap of a finite family of elements of an additive restricted product of
topological groups is an isomorphism of topological additive groups. -/]
def piRestrictedProductContinuousMulEquiv [Finite n] (hU : ∀ i, IsOpen (U i : Set (G i))) :
    (n → Πʳ i, [G i, (U i : Set (G i))]) ≃ₜ*
      Πʳ i, [n → G i,
        (Subgroup.pi univ fun _ : n ↦ Subgroup.ofClass (U i) : Set (n → G i))] where
  toMulEquiv := piRestrictedProduct U
  continuous_toFun := continuous_piRestrictedProduct U hU
  continuous_invFun := continuous_piRestrictedProduct_symm U

/-- The topological swap is the swap. -/
@[to_additive (attr := simp) coe_addPiRestrictedProductContinuousAddEquiv /-- The topological
additive swap is the additive swap. -/]
theorem coe_piRestrictedProductContinuousMulEquiv [Finite n] (hU : ∀ i, IsOpen (U i : Set (G i))) :
    ⇑(piRestrictedProductContinuousMulEquiv (n := n) U hU) = piRestrictedProduct U := by
  rfl

/-- The inverse of the topological swap is the inverse swap. -/
@[to_additive (attr := simp) coe_addPiRestrictedProductContinuousAddEquiv_symm /-- The inverse of
the topological additive swap is the inverse additive swap. -/]
theorem coe_piRestrictedProductContinuousMulEquiv_symm [Finite n]
    (hU : ∀ i, IsOpen (U i : Set (G i))) :
    ⇑(piRestrictedProductContinuousMulEquiv (n := n) U hU).symm = (piRestrictedProduct U).symm := by
  rfl

end TauCeti
