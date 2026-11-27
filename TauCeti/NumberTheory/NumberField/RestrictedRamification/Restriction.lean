/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import TauCeti.FieldTheory.Galois.Restriction

/-!
# Restriction to `G_{K,S}`

Let `K` be a number field, `Ω` a normal extension of `K` (such as an algebraic closure) and `S` a
set of finite places of `K`. Restriction of automorphisms to the maximal extension `K_S` of `K`
unramified outside `S` is a continuous surjection `Gal(Ω / K) → G_{K,S}`
(`TauCeti.RestrictedRamification.restrictionS`) whose kernel is the closed normal subgroup
`H_S = Gal(Ω / K_S)` fixing `K_S`. It is an open quotient map; the induced isomorphism of
topological groups `Gal(Ω / K) ⧸ H_S ≃ₜ* G_{K,S}` is `TauCeti.quotientFixingSubgroupEquiv`
applied to `K_S`. For `S ⊆ T`, restricting from `K_T` to `K_S` gives the
surjective transition homomorphism `G_{K,T} →ₜ* G_{K,S}`.

## Main definitions

* `TauCeti.RestrictedRamification.restrictionS`: the restriction `Gal(Ω / K) →ₜ* G_{K,S}`.

* `TauCeti.RestrictedRamification.galoisGroupSMap`: the transition map `G_{K,T} →ₜ* G_{K,S}`.

## Main results

* `TauCeti.RestrictedRamification.restrictionS_surjective`: restriction is surjective.
* `TauCeti.RestrictedRamification.ker_restrictionS`: its kernel is the fixing subgroup of `K_S`.
* `TauCeti.RestrictedRamification.isQuotientMap_restrictionS`: it is a quotient map.

* `TauCeti.RestrictedRamification.ext_restrictionS`: maps out of `G_{K,S}` are determined by
  composition with `restrictionS`.

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
  exact MonoidHom.mem_ker.symm

/-- **Restriction to `G_{K,S}` is an open map.** -/
theorem isOpenMap_restrictionS : IsOpenMap (restrictionS K Ω S) :=
  isOpenMap_restrictNormalHom (maxUnramifiedOutside K Ω S)

/-- **Restriction to `G_{K,S}` is a quotient map**: `G_{K,S}` carries the quotient topology of
`Gal(Ω / K)`. -/
theorem isQuotientMap_restrictionS : Topology.IsQuotientMap (restrictionS K Ω S) :=
  isQuotientMap_restrictNormalHom (maxUnramifiedOutside K Ω S)

variable {S}

/-- Two continuous homomorphisms out of `G_{K,S}` agree if they agree after composing with
`restrictionS`. -/
@[ext]
theorem ext_restrictionS {S : Set (HeightOneSpectrum (𝓞 K))}
    {H : Type*} [Monoid H] [TopologicalSpace H] {ψ₁ ψ₂ : galoisGroupS K Ω S →ₜ* H}
    (h : ψ₁.comp (restrictionS K Ω S) = ψ₂.comp (restrictionS K Ω S)) :
    ψ₁ = ψ₂ := by
  ext y
  obtain ⟨σ, rfl⟩ := restrictionS_surjective K Ω S y
  exact DFunLike.congr_fun h σ

private theorem restrictNormalHom_inclusion_comp_restrictionS
    {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    (IntermediateField.inclusion (maxUnramifiedOutside_mono (Ω := Ω) h)).restrictNormalHom.comp
      (restrictionS K Ω T).toMonoidHom = (restrictionS K Ω S).toMonoidHom := by
  apply MonoidHom.ext
  intro σ
  have hST := maxUnramifiedOutside_mono (Ω := Ω) h
  exact AlgEquiv.restrictNormalHom_of_compatible
    (inclusion hST).restrictNormalHom (inclusion hST)
    (inclusion hST).restrictNormalHom_commutes (coe_inclusion hST) σ

/-- **Functoriality of `G_{K,S}` in `S`.** For `S ⊆ T`, restricting from `K_T` to `K_S` gives a
continuous group homomorphism `G_{K,T} →ₜ* G_{K,S}`. -/
def galoisGroupSMap {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    galoisGroupS K Ω T →ₜ* galoisGroupS K Ω S where
  toMonoidHom := (IntermediateField.inclusion (maxUnramifiedOutside_mono h)).restrictNormalHom
  continuous_toFun := by
    refine (isQuotientMap_restrictionS K Ω T).continuous_iff.2 ?_
    convert (restrictionS K Ω S).continuous using 1
    exact funext (DFunLike.congr_fun (restrictNormalHom_inclusion_comp_restrictionS K Ω h))

/-- The transition map `G_{K,T} → G_{K,S}` acts on `K_S` by applying the element of `G_{K,T}`. -/
@[simp]
theorem galoisGroupSMap_apply {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T)
    (σ : galoisGroupS K Ω T) (x : maxUnramifiedOutside K Ω S) :
    (galoisGroupSMap K Ω h σ x : Ω) =
      (σ (IntermediateField.inclusion (maxUnramifiedOutside_mono h) x) : Ω) :=
  congrArg Subtype.val
    ((IntermediateField.inclusion (maxUnramifiedOutside_mono h)).restrictNormalHom_commutes σ x)

/-- The transition map `G_{K,T} → G_{K,S}` is surjective. -/
theorem galoisGroupSMap_surjective {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    Function.Surjective (galoisGroupSMap K Ω h) :=
  AlgHom.restrictNormalHom_surjective _

/-- Restricting from `Gal(Ω / K)` to `G_{K,T}` and then to `G_{K,S}` equals restricting directly
to `G_{K,S}`. -/
@[simp]
theorem galoisGroupSMap_comp_restrictionS {S T : Set (HeightOneSpectrum (𝓞 K))}
    (h : S ⊆ T) :
    (galoisGroupSMap K Ω h).comp (restrictionS K Ω T) = restrictionS K Ω S :=
  ContinuousMonoidHom.ext fun σ ↦
    DFunLike.congr_fun (restrictNormalHom_inclusion_comp_restrictionS K Ω h) σ

/-- The transition map for `S ⊆ S` is the identity homomorphism. -/
@[simp]
theorem galoisGroupSMap_refl (S : Set (HeightOneSpectrum (𝓞 K))) :
    galoisGroupSMap K Ω (Set.Subset.refl S) = ContinuousMonoidHom.id (galoisGroupS K Ω S) := by
  ext σ x
  simp

/-- Transition maps compose along chains `S ⊆ T ⊆ U`. -/
@[simp]
theorem galoisGroupSMap_comp {S T U : Set (HeightOneSpectrum (𝓞 K))} (h₁ : S ⊆ T) (h₂ : T ⊆ U) :
    (galoisGroupSMap K Ω h₁).comp (galoisGroupSMap K Ω h₂) = galoisGroupSMap K Ω (h₁.trans h₂) := by
  ext σ x
  simp

end TauCeti.RestrictedRamification
