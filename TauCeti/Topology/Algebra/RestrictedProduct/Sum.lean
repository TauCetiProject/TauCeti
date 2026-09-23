/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Splitting a restricted product over a sum of index types

A restricted product of groups indexed by `ι₁ ⊕ ι₂` is the product of the restricted products
over the two summands.  The algebraic content is that a subset of `ι₁ ⊕ ι₂` is finite exactly
when its preimages under `Sum.inl` and `Sum.inr` are, so the restrictedness conditions match up
in both directions; the equivalence `restrictedProductSum` is the restriction of
`Equiv.sumPiEquivProdPi` to the restricted subtypes.

The forward map is continuous for every reference family (`continuous_restrictedProductSum`).
The inverse is continuous when every reference subgroup is open
(`continuous_restrictedProductSum_symm`); this is the same openness hypothesis under which
Mathlib's `RestrictedProduct.isTopologicalGroup` holds, so under it `restrictedProductSum` is a
homeomorphism. The hypothesis cannot be dropped: `not_continuous_restrictedProductSum_symm`
exhibits a family with trivial reference subgroups for which the inverse is discontinuous.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u₁ u₂ v

variable {ι₁ : Type u₁} {ι₂ : Type u₂} {G : ι₁ ⊕ ι₂ → Type v}
variable [∀ k, Group (G k)]

/-- A restricted product over `ι₁ ⊕ ι₂` is the product of the restricted products over the two
summands, coordinatewise the identity in both directions. -/
def restrictedProductSum (U : ∀ k, Subgroup (G k)) :
    (Πʳ k, [G k, (U k : Set (G k))]) ≃*
      (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]) ×
        (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))]) where
  toFun x :=
    (x.mapAlongMonoidHom G (fun i ↦ G (Sum.inl i)) Sum.inl Sum.inl_injective.tendsto_cofinite
        (fun _ ↦ MonoidHom.id _) (.of_forall fun _ ↦ Set.mapsTo_id _),
      x.mapAlongMonoidHom G (fun j ↦ G (Sum.inr j)) Sum.inr Sum.inr_injective.tendsto_cofinite
        (fun _ ↦ MonoidHom.id _) (.of_forall fun _ ↦ Set.mapsTo_id _))
  invFun y := ⟨(Equiv.sumPiEquivProdPi G).symm (⇑y.1, ⇑y.2), by
    rw [eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨eventually_cofinite.mp y.1.2, eventually_cofinite.mp y.2.2⟩⟩
  left_inv x := by
    ext (i | j) <;> rfl
  right_inv y := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

variable (U : ∀ k, Subgroup (G k))

/-- The left component of the splitting is the restriction of coordinates to `ι₁`. -/
@[simp]
theorem restrictedProductSum_apply_inl (x : Πʳ k, [G k, (U k : Set (G k))]) (i : ι₁) :
    (restrictedProductSum U x).1 i = x (Sum.inl i) := by
  rfl

/-- The right component of the splitting is the restriction of coordinates to `ι₂`. -/
@[simp]
theorem restrictedProductSum_apply_inr (x : Πʳ k, [G k, (U k : Set (G k))]) (j : ι₂) :
    (restrictedProductSum U x).2 j = x (Sum.inr j) := by
  rfl

/-- The inverse of the splitting reads its `Sum.inl` coordinates off the left factor. -/
@[simp]
theorem restrictedProductSum_symm_apply_inl
    (y : (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]) ×
      (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))])) (i : ι₁) :
    (restrictedProductSum U).symm y (Sum.inl i) = y.1 i := by
  rfl

/-- The inverse of the splitting reads its `Sum.inr` coordinates off the right factor. -/
@[simp]
theorem restrictedProductSum_symm_apply_inr
    (y : (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]) ×
      (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))])) (j : ι₂) :
    (restrictedProductSum U).symm y (Sum.inr j) = y.2 j := by
  rfl

variable [∀ k, TopologicalSpace (G k)]

/-- The splitting over a sum is continuous for every reference family; unlike its inverse, it
needs no openness hypothesis on the reference subgroups. -/
theorem continuous_restrictedProductSum : Continuous (restrictedProductSum U) := by
  refine continuous_prodMk.mpr ⟨?_, ?_⟩
  · exact RestrictedProduct.mapAlong_continuous G (fun i ↦ G (Sum.inl i)) Sum.inl
      Sum.inl_injective.tendsto_cofinite (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _)
      fun _ ↦ continuous_id
  · exact RestrictedProduct.mapAlong_continuous G (fun j ↦ G (Sum.inr j)) Sum.inr
      Sum.inr_injective.tendsto_cofinite (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _)
      fun _ ↦ continuous_id

/-- The inverse of the splitting over a sum is continuous when every reference subgroup is open.
This is the same openness hypothesis under which Mathlib's `RestrictedProduct.isTopologicalGroup`
holds; the forward direction `continuous_restrictedProductSum` needs no such hypothesis. -/
theorem continuous_restrictedProductSum_symm (hU : ∀ k, IsOpen (U k : Set (G k))) :
    Continuous (restrictedProductSum U).symm := by
  rw [RestrictedProduct.continuous_dom_prod_right fun i ↦ hU (Sum.inl i)]
  intro S₁ hS₁
  rw [RestrictedProduct.continuous_dom_prod_left fun j ↦ hU (Sum.inr j)]
  intro S₂ hS₂
  let T : Set (ι₁ ⊕ ι₂) := {k | Sum.elim (· ∈ S₁) (· ∈ S₂) k}
  have hT : cofinite ≤ 𝓟 T := by
    rw [le_principal_iff, mem_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨mem_cofinite.mp (le_principal_iff.mp hS₁), mem_cofinite.mp (le_principal_iff.mp hS₂)⟩
  -- The coordinatewise map into the stage `𝓟 T`, through which the composite factors.
  let g : (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]_[𝓟 S₁]) ×
      (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))]_[𝓟 S₂]) →
        Πʳ k, [G k, (U k : Set (G k))]_[𝓟 T] :=
    fun y ↦ ⟨(Equiv.sumPiEquivProdPi G).symm (⇑y.1, ⇑y.2), by
      rw [eventually_principal]
      rintro (i | j) hk
      · exact y.1.2 hk
      · exact y.2.2 hk⟩
  have key : ((restrictedProductSum U).symm ∘ Prod.map (RestrictedProduct.inclusion _ _ hS₁) id) ∘
      Prod.map id (RestrictedProduct.inclusion _ _ hS₂) =
        RestrictedProduct.inclusion _ _ hT ∘ g := by
    ext y (i | j) <;>
      rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
        RestrictedProduct.inclusion_apply, RestrictedProduct.mk_apply,
        Equiv.sumPiEquivProdPi_symm_apply] <;>
      simp only [Prod.map_fst, Prod.map_snd, id_eq, restrictedProductSum_symm_apply_inl,
        restrictedProductSum_symm_apply_inr, RestrictedProduct.inclusion_apply]
  rw [key]
  refine (RestrictedProduct.continuous_inclusion hT).comp ?_
  refine RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi ?_)
  rintro (i | j)
  · exact (RestrictedProduct.continuous_eval i).comp continuous_fst
  · exact (RestrictedProduct.continuous_eval j).comp continuous_snd

end TauCeti
