/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.FieldTheory.Galois.Restriction

/-!
# Restriction and transition maps for Galois groups with restricted ramification

Let `K` be a number field, `Ω / K` a normal extension, and `S` a set of finite places of `K`.
This file constructs the continuous quotient homomorphism
`restrictGaloisGroupS : Gal(Ω / K) →ₜ* G_{K,S}` and, for `S ⊆ T`, the functorial transition map
`galoisGroupSMap : G_{K,T} →ₜ* G_{K,S}`, together with their surjectivity, kernel, topological
quotient property, and functoriality laws.

## Main definitions and results

* `TauCeti.RestrictedRamification.restrictGaloisGroupS`: the continuous restriction map
  `Gal(Ω / K) →ₜ* G_{K,S}`.
* `TauCeti.RestrictedRamification.ker_restrictGaloisGroupS`: its kernel is the fixing subgroup of
  `maxUnramifiedOutside K Ω S`.
* `TauCeti.RestrictedRamification.isQuotientMap_restrictGaloisGroupS`: restriction to `G_{K,S}` is
  a topological quotient map.
* `TauCeti.RestrictedRamification.galoisGroupSMap`: for `S ⊆ T`, the surjective continuous
  transition map `G_{K,T} →ₜ* G_{K,S}`, with `galoisGroupSMap_refl`, `galoisGroupSMap_comp`, and
  `galoisGroupSMap_comp_restrictGaloisGroupS`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

noncomputable section

open IntermediateField IsDedekindDomain NumberField TauCeti
open scoped NumberField

namespace TauCeti.RestrictedRamification

variable (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- **Restriction to `G_{K,S}`.** For a normal extension `Ω / K`, restriction of automorphisms to
the maximal subextension `K_S` unramified outside `S` is a continuous group homomorphism
`Gal(Ω / K) →ₜ* G_{K,S}`. -/
def restrictGaloisGroupS (S : Set (HeightOneSpectrum (𝓞 K))) :
    (Ω ≃ₐ[K] Ω) →ₜ* galoisGroupS K Ω S where
  toMonoidHom := AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S)
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous (maxUnramifiedOutside K Ω S)

/-- Restriction to `G_{K,S}` agrees on `K_S` with the original automorphism. -/
@[simp]
theorem restrictGaloisGroupS_apply (S : Set (HeightOneSpectrum (𝓞 K))) (σ : Ω ≃ₐ[K] Ω)
    (x : maxUnramifiedOutside K Ω S) :
    (restrictGaloisGroupS K Ω S σ x : Ω) = σ x :=
  AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K Ω S) x

/-- The underlying map of `restrictGaloisGroupS` is `AlgEquiv.restrictNormalHom`. -/
theorem restrictGaloisGroupS_eq_restrictNormalHom (S : Set (HeightOneSpectrum (𝓞 K)))
    (σ : Ω ≃ₐ[K] Ω) :
    restrictGaloisGroupS K Ω S σ =
      AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) σ :=
  (rfl)

/-- Restriction `Gal(Ω / K) → G_{K,S}` is surjective. -/
theorem restrictGaloisGroupS_surjective (S : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (restrictGaloisGroupS K Ω S) :=
  AlgEquiv.restrictNormalHom_surjective Ω

/-- The kernel of `Gal(Ω / K) → G_{K,S}` is the fixing subgroup of `K_S`. -/
theorem ker_restrictGaloisGroupS (S : Set (HeightOneSpectrum (𝓞 K))) :
    (restrictGaloisGroupS K Ω S).toMonoidHom.ker =
      (maxUnramifiedOutside K Ω S).fixingSubgroup :=
  (maxUnramifiedOutside K Ω S).restrictNormalHom_ker

/-- For a normal extension `Ω / K`, the restriction map `Gal(Ω / K) → G_{K,S}` is a topological
quotient map. -/
theorem isQuotientMap_restrictGaloisGroupS (S : Set (HeightOneSpectrum (𝓞 K))) :
    Topology.IsQuotientMap (restrictGaloisGroupS K Ω S) :=
  (restrictGaloisGroupS K Ω S).continuous.isClosedMap.isQuotientMap
    (restrictGaloisGroupS K Ω S).continuous (restrictGaloisGroupS_surjective K Ω S)

private theorem restrictNormalHom_inclusion_comp_restrictGaloisGroupS
    {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    (IntermediateField.inclusion (maxUnramifiedOutside_mono (Ω := Ω) h)).restrictNormalHom.comp
      (restrictGaloisGroupS K Ω T).toMonoidHom = (restrictGaloisGroupS K Ω S).toMonoidHom := by
  ext σ x
  have h1 := congrArg Subtype.val
    ((IntermediateField.inclusion (maxUnramifiedOutside_mono h)).restrictNormalHom_commutes
      (restrictGaloisGroupS K Ω T σ) x)
  exact h1.trans ((restrictGaloisGroupS_apply K Ω T σ _).trans
    (restrictGaloisGroupS_apply K Ω S σ x).symm)

/-- **Functoriality of `G_{K,S}` in `S`.** For `S ⊆ T`, restricting from `K_T` to `K_S` gives a
continuous group homomorphism `G_{K,T} →ₜ* G_{K,S}`. -/
def galoisGroupSMap {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    galoisGroupS K Ω T →ₜ* galoisGroupS K Ω S where
  toMonoidHom := (IntermediateField.inclusion (maxUnramifiedOutside_mono h)).restrictNormalHom
  continuous_toFun := by
    refine (isQuotientMap_restrictGaloisGroupS K Ω T).continuous_iff.2 ?_
    convert (restrictGaloisGroupS K Ω S).continuous using 1
    exact funext (DFunLike.congr_fun (restrictNormalHom_inclusion_comp_restrictGaloisGroupS K Ω h))

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
theorem galoisGroupSMap_comp_restrictGaloisGroupS {S T : Set (HeightOneSpectrum (𝓞 K))}
    (h : S ⊆ T) :
    (galoisGroupSMap K Ω h).comp (restrictGaloisGroupS K Ω T) = restrictGaloisGroupS K Ω S :=
  ContinuousMonoidHom.ext fun σ ↦
    DFunLike.congr_fun (restrictNormalHom_inclusion_comp_restrictGaloisGroupS K Ω h) σ

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
