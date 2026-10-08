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
over the two summands.  For a filter `𝓕` on `ι₁ ⊕ ι₂` the summand filters are the comaps
`𝓕.comap Sum.inl` and `𝓕.comap Sum.inr`, and the algebraic content is that `𝓕` is recovered from
them (`Filter.map_comap_inl_sup_map_comap_inr`), so the restrictedness conditions match up in
both directions; the equivalence `restrictedProductSum` is the restriction of
`Equiv.sumPiEquivProdPi` to the restricted subtypes.  It takes the two summand filters as
arguments together with the equations identifying them with the comaps, so that each can be given
in its preferred form: for the cofinite filter both comaps are cofinite again, because `Sum.inl`
and `Sum.inr` are injective (`Function.Injective.comap_cofinite_eq`).  The summand filters need not
be cofinite in general: for `𝓕 = 𝓟 (Set.range Sum.inl)` the second comap is `⊥`, and the right
factor is the unrestricted product `Π j, G (Sum.inr j)`.

The forward map is continuous for every filter and every reference family
(`continuous_restrictedProductSum`).  The inverse is a map out of a product of two restricted
products, and its continuity depends on the filter and on the reference family.  For a principal
filter it is continuous for every family (`continuous_restrictedProductSum_symm_of_principal`),
and hence so is its composite with the inclusions of principal stages
(`continuous_restrictedProductSum_symm_comp_prodMap_inclusion`).  For the cofinite filter,
Mathlib's universal property with parameters passes from the stages to the restricted products
when the reference subgroups are open: over both summands (`continuous_restrictedProductSum_symm`,
the openness hypothesis under which `RestrictedProduct.isTopologicalGroup` holds), or over the
right summand alone when the left summand is finite
(`continuous_restrictedProductSum_symm_of_finite_left`).  Under either hypothesis
`restrictedProductSum` is a homeomorphism.  Openness cannot be dropped altogether:
`not_continuous_restrictedProductSum_symm` exhibits a family with trivial reference subgroups for
which the inverse is discontinuous.

Everything here except that counterexample is also stated for additive groups
(`addRestrictedProductSum`, …).

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
variable {𝓕 : Filter (ι₁ ⊕ ι₂)} {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}

/-- A restricted product over `ι₁ ⊕ ι₂` with respect to a filter `𝓕` is the product of the
restricted products over the two summands with respect to the comaps of `𝓕` along `Sum.inl` and
`Sum.inr`, coordinatewise the identity in both directions. -/
@[to_additive addRestrictedProductSum /-- A restricted product of additive groups over `ι₁ ⊕ ι₂`
with respect to a filter `𝓕` is the product of the restricted products over the two summands with
respect to the comaps of `𝓕` along `Sum.inl` and `Sum.inr`, coordinatewise the identity in both
directions. -/]
def restrictedProductSum (U : ∀ k, Subgroup (G k)) (h₁ : 𝓕.comap Sum.inl = 𝓕₁)
    (h₂ : 𝓕.comap Sum.inr = 𝓕₂) :
    (Πʳ k, [G k, (U k : Set (G k))]_[𝓕]) ≃*
      (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]_[𝓕₁]) ×
        (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))]_[𝓕₂]) where
  toFun x :=
    (x.mapAlongMonoidHom G (fun i ↦ G (Sum.inl i)) Sum.inl (tendsto_iff_comap.mpr h₁.ge)
        (fun _ ↦ MonoidHom.id _) (.of_forall fun _ ↦ Set.mapsTo_id _),
      x.mapAlongMonoidHom G (fun j ↦ G (Sum.inr j)) Sum.inr (tendsto_iff_comap.mpr h₂.ge)
        (fun _ ↦ MonoidHom.id _) (.of_forall fun _ ↦ Set.mapsTo_id _))
  invFun y := ⟨(Equiv.sumPiEquivProdPi G).symm (⇑y.1, ⇑y.2), by
    rw [← map_comap_inl_sup_map_comap_inr 𝓕, eventually_sup, eventually_map, eventually_map, h₁,
      h₂]
    exact ⟨y.1.2, y.2.2⟩⟩
  left_inv x := by
    ext (i | j) <;> rfl
  right_inv y := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

variable (U : ∀ k, Subgroup (G k)) (h₁ : 𝓕.comap Sum.inl = 𝓕₁) (h₂ : 𝓕.comap Sum.inr = 𝓕₂)

/-- The left component of the splitting is the restriction of coordinates to `ι₁`. -/
@[to_additive (attr := simp) addRestrictedProductSum_apply_inl /-- The left component of the
additive splitting is the restriction of coordinates to `ι₁`. -/]
theorem restrictedProductSum_apply_inl (x : Πʳ k, [G k, (U k : Set (G k))]_[𝓕]) (i : ι₁) :
    (restrictedProductSum U h₁ h₂ x).1 i = x (Sum.inl i) := by
  rfl

/-- The right component of the splitting is the restriction of coordinates to `ι₂`. -/
@[to_additive (attr := simp) addRestrictedProductSum_apply_inr /-- The right component of the
additive splitting is the restriction of coordinates to `ι₂`. -/]
theorem restrictedProductSum_apply_inr (x : Πʳ k, [G k, (U k : Set (G k))]_[𝓕]) (j : ι₂) :
    (restrictedProductSum U h₁ h₂ x).2 j = x (Sum.inr j) := by
  rfl

/-- The inverse of the splitting reads its `Sum.inl` coordinates off the left factor. -/
@[to_additive (attr := simp) addRestrictedProductSum_symm_apply_inl /-- The inverse of the additive
splitting reads its `Sum.inl` coordinates off the left factor. -/]
theorem restrictedProductSum_symm_apply_inl
    (y : (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]_[𝓕₁]) ×
      (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))]_[𝓕₂])) (i : ι₁) :
    (restrictedProductSum U h₁ h₂).symm y (Sum.inl i) = y.1 i := by
  rfl

/-- The inverse of the splitting reads its `Sum.inr` coordinates off the right factor. -/
@[to_additive (attr := simp) addRestrictedProductSum_symm_apply_inr /-- The inverse of the additive
splitting reads its `Sum.inr` coordinates off the right factor. -/]
theorem restrictedProductSum_symm_apply_inr
    (y : (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]_[𝓕₁]) ×
      (Πʳ j, [G (Sum.inr j), (U (Sum.inr j) : Set (G (Sum.inr j)))]_[𝓕₂])) (j : ι₂) :
    (restrictedProductSum U h₁ h₂).symm y (Sum.inr j) = y.2 j := by
  rfl

variable [∀ k, TopologicalSpace (G k)]

/-- The splitting over a sum is continuous for every filter and every reference family; unlike
its inverse, it needs no hypothesis on either. -/
@[to_additive continuous_addRestrictedProductSum /-- The additive splitting over a sum is continuous
for every filter and every reference family; unlike its inverse, it needs no hypothesis on
either. -/]
theorem continuous_restrictedProductSum : Continuous (restrictedProductSum U h₁ h₂) := by
  refine continuous_prodMk.mpr ⟨?_, ?_⟩
  · exact RestrictedProduct.mapAlong_continuous G (fun i ↦ G (Sum.inl i)) Sum.inl
      (tendsto_iff_comap.mpr h₁.ge) (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _)
      fun _ ↦ continuous_id
  · exact RestrictedProduct.mapAlong_continuous G (fun j ↦ G (Sum.inr j)) Sum.inr
      (tendsto_iff_comap.mpr h₂.ge) (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _)
      fun _ ↦ continuous_id

/-- For a principal filter on `ι₁ ⊕ ι₂` the inverse of the splitting is continuous for every
reference family, so that the splitting is a homeomorphism: the target is a principal stage,
whose topology is induced from the product. -/
@[to_additive continuous_addRestrictedProductSum_symm_of_principal /-- For a principal filter on
`ι₁ ⊕ ι₂` the inverse of the additive splitting is continuous for every reference family, so that
the splitting is a homeomorphism: the target is a principal stage, whose topology is induced from
the product. -/]
theorem continuous_restrictedProductSum_symm_of_principal {T : Set (ι₁ ⊕ ι₂)}
    (hT₁ : (𝓟 T).comap Sum.inl = 𝓕₁) (hT₂ : (𝓟 T).comap Sum.inr = 𝓕₂) :
    Continuous (restrictedProductSum U hT₁ hT₂).symm := by
  refine RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi ?_)
  rintro (i | j)
  · simp only [Function.comp_apply, restrictedProductSum_symm_apply_inl]
    exact (RestrictedProduct.continuous_eval i).comp continuous_fst
  · simp only [Function.comp_apply, restrictedProductSum_symm_apply_inr]
    exact (RestrictedProduct.continuous_eval j).comp continuous_snd

/-- On principal stages the inverse of the splitting over a sum is continuous for every filter
and every reference family: for the cofinite filter, openness of the reference subgroups is needed
only to pass from the stages to the restricted products themselves. -/
@[to_additive continuous_addRestrictedProductSum_symm_comp_prodMap_inclusion /-- On principal stages
the inverse of the additive splitting over a sum is continuous for every filter and every reference
family: for the cofinite filter, openness of the reference subgroups is needed only to pass from the
stages to the restricted products themselves. -/]
theorem continuous_restrictedProductSum_symm_comp_prodMap_inclusion {S₁ : Set ι₁} {S₂ : Set ι₂}
    (hS₁ : 𝓕₁ ≤ 𝓟 S₁) (hS₂ : 𝓕₂ ≤ 𝓟 S₂) :
    Continuous ((restrictedProductSum U h₁ h₂).symm ∘
      Prod.map (RestrictedProduct.inclusion _ _ hS₁) (RestrictedProduct.inclusion _ _ hS₂)) := by
  -- The composite factors through the splitting at the principal stage `𝓟 T` of `ι₁ ⊕ ι₂`, where
  -- `T` is `S₁` on `ι₁` and `S₂` on `ι₂`, whose summand filters are `𝓟 S₁` and `𝓟 S₂`.
  obtain ⟨T, hT₁, hT₂⟩ : ∃ T : Set (ι₁ ⊕ ι₂),
      (𝓟 T).comap Sum.inl = 𝓟 S₁ ∧ (𝓟 T).comap Sum.inr = 𝓟 S₂ :=
    ⟨{k | Sum.elim (· ∈ S₁) (· ∈ S₂) k}, comap_principal, comap_principal⟩
  have hT : 𝓕 ≤ 𝓟 T := by
    rw [← map_comap_inl_sup_map_comap_inr 𝓕, ← map_comap_inl_sup_map_comap_inr (𝓟 T), h₁, h₂,
      hT₁, hT₂]
    exact sup_le_sup (map_mono hS₁) (map_mono hS₂)
  have key : (restrictedProductSum U h₁ h₂).symm ∘
      Prod.map (RestrictedProduct.inclusion _ _ hS₁) (RestrictedProduct.inclusion _ _ hS₂) =
        RestrictedProduct.inclusion _ _ hT ∘ (restrictedProductSum U hT₁ hT₂).symm := by
    ext y (i | j) <;>
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd,
        restrictedProductSum_symm_apply_inl, restrictedProductSum_symm_apply_inr,
        RestrictedProduct.inclusion_apply]
  rw [key]
  exact (RestrictedProduct.continuous_inclusion hT).comp
    (continuous_restrictedProductSum_symm_of_principal U hT₁ hT₂)

/-- The inverse of the splitting over a sum, for the cofinite filter, is continuous when every
reference subgroup is open. This is the same openness hypothesis under which Mathlib's
`RestrictedProduct.isTopologicalGroup` holds; the forward direction
`continuous_restrictedProductSum` needs no such hypothesis. -/
@[to_additive continuous_addRestrictedProductSum_symm /-- The inverse of the additive splitting over
a sum, for the cofinite filter, is continuous when every reference subgroup is open. This is the
same openness hypothesis under which Mathlib's `RestrictedProduct.isTopologicalAddGroup` holds; the
forward direction `continuous_addRestrictedProductSum` needs no such hypothesis. -/]
theorem continuous_restrictedProductSum_symm (hU : ∀ k, IsOpen (U k : Set (G k))) :
    Continuous (restrictedProductSum U Sum.inl_injective.comap_cofinite_eq
      Sum.inr_injective.comap_cofinite_eq).symm := by
  rw [RestrictedProduct.continuous_dom_prod_right fun i ↦ hU (Sum.inl i)]
  intro S₁ hS₁
  rw [RestrictedProduct.continuous_dom_prod_left fun j ↦ hU (Sum.inr j)]
  intro S₂ hS₂
  rw [Function.comp_assoc, Prod.map_comp_map, Function.comp_id, Function.id_comp]
  exact continuous_restrictedProductSum_symm_comp_prodMap_inclusion U _ _ hS₁ hS₂

/-- The inverse of the splitting over a sum, for the cofinite filter, is continuous when the left
summand is finite and every reference subgroup over the right summand is open; the reference
subgroups over the finite summand need not be open. -/
@[to_additive continuous_addRestrictedProductSum_symm_of_finite_left /-- The inverse of the additive
splitting over a sum, for the cofinite filter, is continuous when the left summand is finite and
every reference subgroup over the right summand is open; the reference subgroups over the finite
summand need not be open. -/]
theorem continuous_restrictedProductSum_symm_of_finite_left [Finite ι₁]
    (hU : ∀ j, IsOpen (U (Sum.inr j) : Set (G (Sum.inr j)))) :
    Continuous (restrictedProductSum U Sum.inl_injective.comap_cofinite_eq
      Sum.inr_injective.comap_cofinite_eq).symm := by
  rw [RestrictedProduct.continuous_dom_prod_left hU]
  intro S₂ hS₂
  -- Over the finite summand the cofinite filter is `⊥ = 𝓟 ∅`, so the whole restricted product
  -- is the empty stage.
  have hempty : (cofinite : Filter ι₁) ≤ 𝓟 (∅ : Set ι₁) := by
    rw [principal_empty]
    exact cofinite_eq_bot.le
  let p : (Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]) →
      Πʳ i, [G (Sum.inl i), (U (Sum.inl i) : Set (G (Sum.inl i)))]_[𝓟 ∅] :=
    fun x ↦ RestrictedProduct.mk x (eventually_principal.mpr fun _ h ↦ h.elim)
  have key : (restrictedProductSum U Sum.inl_injective.comap_cofinite_eq
      Sum.inr_injective.comap_cofinite_eq).symm ∘
        Prod.map id (RestrictedProduct.inclusion _ _ hS₂) =
      ((restrictedProductSum U Sum.inl_injective.comap_cofinite_eq
        Sum.inr_injective.comap_cofinite_eq).symm ∘
        Prod.map (RestrictedProduct.inclusion _ _ hempty) (RestrictedProduct.inclusion _ _ hS₂)) ∘
          Prod.map p id := by
    ext y (i | j) <;>
      simp only [p, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        restrictedProductSum_symm_apply_inl, restrictedProductSum_symm_apply_inr,
        RestrictedProduct.inclusion_apply, RestrictedProduct.mk_apply]
  rw [key]
  refine (continuous_restrictedProductSum_symm_comp_prodMap_inclusion U _ _ hempty hS₂).comp
    (Continuous.prodMap ?_ continuous_id)
  refine RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun i ↦ ?_)
  simpa only [p, Function.comp_apply, RestrictedProduct.mk_apply] using
    RestrictedProduct.continuous_eval i

end TauCeti
