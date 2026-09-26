/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Restricted products of groups away from a set of indices

This file names the restricted product of a family of groups relative to a family of reference
subgroups over the indices outside a set `S`. This is the shape in which restricted products
appear when the local groups at a finite set of places are set apart from the rest of an adelic
group: the finite adelic points away from a finite set of places.

It then constructs the restriction homomorphism from the restricted product to the restricted
product away from `S`, which forgets the coordinates indexed by `S`. This is Mathlib's
`RestrictedProduct.mapAlongMonoidHom` along the inclusion `{i // i ∉ S} → ι`, which carries the
cofinite filter to the cofinite filter because it is injective. Its coordinate formula, its
continuity for every reference family, and its compatibility with nested index sets are the
facts the decomposition `awayDecomposition` of a restricted product along a finite set of indices
needs.

No finiteness of `S` is assumed anywhere: the away-`S` restricted product and the restriction to
it make sense for every set of indices.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The restricted product of `G` relative to `U` over the indices **outside** `S`. This is
`RestrictedProductGroup` at the index type `{i // i ∉ S}`; no finiteness of `S` is needed to form
it. -/
abbrev RestrictedProductGroupAway (S : Set ι) (U : ∀ i, Subgroup (G i)) :=
  RestrictedProductGroup fun i : {i // i ∉ S} ↦ U i.1

/-- Restriction of a restricted product to the indices outside `S`, forgetting the coordinates
indexed by `S`. -/
def restrictAway (S : Set ι) (U : ∀ i, Subgroup (G i)) :
    RestrictedProductGroup U →* RestrictedProductGroupAway S U :=
  RestrictedProduct.mapAlongMonoidHom G (fun i : {i // i ∉ S} ↦ G i.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun i ↦ MonoidHom.id (G i.1))
    (.of_forall fun _ _ hx ↦ hx)

/-- The restriction away from `S` keeps the coordinates outside `S` unchanged. -/
@[simp]
theorem restrictAway_apply (S : Set ι) (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroup U) (i : {i // i ∉ S}) :
    restrictAway S U x i = x i.1 :=
  RestrictedProduct.mapAlongMonoidHom_apply G (fun i : {i // i ∉ S} ↦ G i.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun i ↦ MonoidHom.id (G i.1))
    (.of_forall fun _ _ hx ↦ hx) x i

/-- Restricting away from a larger set factors through restricting away from a smaller one:
the coordinate of `restrictAway T U x` at `i ∉ T` is the coordinate of `restrictAway S U x` at
the same index, viewed outside `S ⊆ T`. -/
theorem restrictAway_restrictAway {S T : Set ι} (hST : S ⊆ T) (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroup U) (i : {i // i ∉ T}) :
    restrictAway T U x i = restrictAway S U x ⟨i.1, fun hi ↦ i.2 (hST hi)⟩ := by
  simp

/-- The restriction away from `S` is continuous for every reference family: it is a map out of a
single restricted product whose coordinate maps are identities. -/
theorem continuous_restrictAway [∀ i, TopologicalSpace (G i)] (S : Set ι)
    (U : ∀ i, Subgroup (G i)) :
    Continuous (restrictAway S U) :=
  RestrictedProduct.mapAlong_continuous G (fun i : {i // i ∉ S} ↦ G i.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite
    (fun i ↦ (MonoidHom.id (G i.1) : G i.1 → G i.1)) (.of_forall fun _ _ hx ↦ hx)
    fun _ ↦ continuous_id

end TauCeti
