/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic

/-!
# Restriction to `G_{K,S}`

Let `K` be a number field, `Ω` a normal extension of `K` (such as an algebraic closure) and `S` a
set of finite places of `K`. Restriction of automorphisms to the maximal extension `K_S` of `K`
unramified outside `S` is a continuous surjection `Gal(Ω / K) → G_{K,S}`
(`TauCeti.RestrictedRamification.restrictionS`) whose kernel is the closed normal subgroup
`H_S = Gal(Ω / K_S)` fixing `K_S`. It is an open quotient map; the induced isomorphism of
topological groups `Gal(Ω / K) ⧸ H_S ≃ₜ* G_{K,S}` is `TauCeti.quotientFixingSubgroupEquiv`
applied to `K_S`.

## Main definitions

* `TauCeti.RestrictedRamification.restrictionS`: the restriction `Gal(Ω / K) →ₜ* G_{K,S}`.

## Main results

* `TauCeti.RestrictedRamification.restrictionS_surjective`: restriction is surjective.
* `TauCeti.RestrictedRamification.ker_restrictionS`: its kernel is the fixing subgroup of `K_S`.
* `TauCeti.RestrictedRamification.isQuotientMap_restrictionS`: it is a quotient map.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

noncomputable section

open IntermediateField IsDedekindDomain

open scoped NumberField

namespace TauCeti.RestrictedRamification

variable (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Normal K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **Restriction to `G_{K,S}`.** For `Ω / K` normal, restricting an automorphism of `Ω` to the
maximal extension `K_S` unramified outside `S` is a continuous homomorphism
`Gal(Ω / K) → G_{K,S}`. -/
def restrictionS : Gal(Ω/K) →ₜ* galoisGroupS K Ω S where
  toMonoidHom := AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _

variable {K Ω S}

/-- The restriction of `σ` to `K_S` agrees with `σ` on `K_S`. -/
@[simp]
theorem coe_restrictionS_apply (σ : Gal(Ω/K)) (x : maxUnramifiedOutside K Ω S) :
    ((restrictionS K Ω S σ x : maxUnramifiedOutside K Ω S) : Ω) = σ x :=
  AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K Ω S) x

/-- `restrictionS` is `AlgEquiv.restrictNormalHom` on `K_S`. -/
theorem restrictionS_apply (σ : Gal(Ω/K)) :
    restrictionS K Ω S σ = AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) σ :=
  (rfl)

variable (K Ω S)

/-- **Restriction to `G_{K,S}` is surjective.** -/
theorem restrictionS_surjective : Function.Surjective (restrictionS K Ω S) :=
  AlgEquiv.restrictNormalHom_surjective Ω

/-- **The kernel of restriction** is the closed normal subgroup `H_S = Gal(Ω / K_S)` fixing
`K_S`. -/
theorem ker_restrictionS :
    (restrictionS K Ω S).toMonoidHom.ker = (maxUnramifiedOutside K Ω S).fixingSubgroup :=
  (maxUnramifiedOutside K Ω S).restrictNormalHom_ker

/-- An automorphism of `Ω` restricts to the identity of `K_S` exactly when it fixes `K_S`. -/
theorem restrictionS_eq_one_iff {σ : Gal(Ω/K)} :
    restrictionS K Ω S σ = 1 ↔ σ ∈ (maxUnramifiedOutside K Ω S).fixingSubgroup := by
  rw [← ker_restrictionS]
  rfl

/-- **Restriction to `G_{K,S}` is an open map.** -/
theorem isOpenMap_restrictionS : IsOpenMap (restrictionS K Ω S) := by
  have h : ⇑(restrictionS K Ω S) =
      quotientFixingSubgroupEquiv K Ω (maxUnramifiedOutside K Ω S) ∘
        ((↑) : Gal(Ω/K) → Gal(Ω/K) ⧸ (maxUnramifiedOutside K Ω S).fixingSubgroup) :=
    funext fun σ ↦ (quotientFixingSubgroupEquiv_mk σ).symm
  rw [h]
  exact (quotientFixingSubgroupEquiv K Ω _).toHomeomorph.isOpenMap.comp
    (QuotientGroup.isOpenMap_coe)

/-- **Restriction to `G_{K,S}` is a quotient map**: `G_{K,S}` carries the quotient topology of
`Gal(Ω / K)`. -/
theorem isQuotientMap_restrictionS : Topology.IsQuotientMap (restrictionS K Ω S) :=
  (isOpenMap_restrictionS K Ω S).isQuotientMap (restrictionS K Ω S).continuous
    (restrictionS_surjective K Ω S)

end TauCeti.RestrictedRamification
