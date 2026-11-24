/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import TauCeti.RingTheory.LocalRing.Basic
public import TauCeti.RingTheory.LocalRing.Localization
import TauCeti.RingTheory.Spectrum.Prime.Point

/-!
# Functoriality and local-ring identifications for prime residue fields

For ring maps `f : R → S` and `g : S → T` and primes `P`, `Q`, `Q'` of `R`, `S`, `T` lying over
one another, the maps `κ(P) → κ(Q) → κ(Q')` of Mathlib's `Ideal.ResidueField.map` compose to the
map `κ(P) → κ(Q')` induced by `g ∘ f`. Thus residue fields are preserved along a composite when
they are preserved along each step, as for a tower of étale neighbourhoods that do not extend the
residue field at a point.

For a local ring `R`, localizing at `maximalIdeal R` inverts only units, identifying the prime
residue field `(maximalIdeal R).ResidueField` with `IsLocalRing.ResidueField R` as an `R`-algebra
(`TauCeti.IsLocalRing.maximalIdealResidueFieldAlgEquiv`). Transporting field-valued points along
this equivalence relates `R`-algebra maps `S →ₐ[R] IsLocalRing.ResidueField R` to primes `𝔮` of
`S` lying over `maximalIdeal R` whose residue-field map `κ(𝔪_R) → κ(𝔮)` is surjective or bijective.

## Main definitions and results

* `Ideal.ResidueField.map_comp_map`: the residue field maps of `f` and `g` compose to that of
  `g ∘ f`.
* `Ideal.ResidueField.map_bijective_of_comap`: if an `R`-algebra retraction `τ : S →ₐ[R] R` pulls a
  prime `P` of `R` back to `𝔮`, then `κ(P) → κ(𝔮)` is bijective.
* `TauCeti.IsLocalRing.maximalIdealResidueFieldAlgEquiv`: canonical `R`-algebra equivalence
  `(maximalIdeal R).ResidueField ≃ₐ[R] IsLocalRing.ResidueField R`.
* `AlgHom.residueFieldMap_bijective_of_ker_eq`: a prime cut out by an `R`-algebra map to
  `ResidueField R` has bijective residue-field map over `𝔪_R`.
* `TauCeti.IsLocalRing.exists_algHom_residueField_ker_eq`: every prime `𝔮` over `𝔪_R` with
  `κ(𝔪_R) → κ(𝔮)` surjective is the kernel of an `R`-algebra map `S →ₐ[R] ResidueField R`.
-/

public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The residue field maps `κ(P) → κ(Q)` along `f` and `κ(Q) → κ(Q')` along `g` compose to the
residue field map `κ(P) → κ(Q')` along `g ∘ f`. -/
theorem Ideal.ResidueField.map_comp_map (P : Ideal R) (Q : Ideal S) (Q' : Ideal T) [P.IsPrime]
    [Q.IsPrime] [Q'.IsPrime] (f : R →+* S) (g : S →+* T) (hf : P = Q.comap f)
    (hg : Q = Q'.comap g) :
    (Ideal.ResidueField.map Q Q' g hg).comp (Ideal.ResidueField.map P Q f hf) =
      Ideal.ResidueField.map P Q' (g.comp f) (by rw [hf, hg, Ideal.comap_comap]) :=
  Ideal.ResidueField.ringHom_ext <| RingHom.ext fun r ↦ by
    simp [Ideal.ResidueField.map_algebraMap]

/-- If an `R`-algebra retraction `τ : S →ₐ[R] R` pulls a prime `P` of `R` back to a prime `𝔮` of
`S`, then `𝔮` lies over `P` and the induced map `κ(P) → κ(𝔮)` on residue fields is bijective. -/
theorem Ideal.ResidueField.map_bijective_of_comap {P : Ideal R} [P.IsPrime] [Algebra R S]
    {τ : S →ₐ[R] R} {𝔮 : Ideal S} [𝔮.IsPrime] (hτ : P.comap τ = 𝔮)
    (h𝔮 : 𝔮.comap (algebraMap R S) = P := by
      rw [← hτ, Ideal.comap_comap]
      simpa [RingHom.ext_iff] using congrArg P.comap τ.comp_algebraMap) :
    Function.Bijective (Ideal.ResidueField.map P 𝔮 (algebraMap R S) h𝔮.symm) := by
  have hker : RingHom.ker ((Algebra.ofId R P.ResidueField).comp τ) = 𝔮 := by
    ext s
    simp [← hτ, RingHom.mem_ker]
  subst hker
  exact ((Algebra.ofId R P.ResidueField).comp τ).residueFieldMap_bijective

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

section Equiv

variable (R) [_root_.IsLocalRing R]

/-- For a local ring `R`, the prime residue field `(maximalIdeal R).ResidueField` at the maximal
ideal is canonically `R`-isomorphic to `IsLocalRing.ResidueField R`, because localizing `R` at
`maximalIdeal R` inverts only units. -/
noncomputable def maximalIdealResidueFieldAlgEquiv :
    (maximalIdeal R).ResidueField ≃ₐ[R] ResidueField R :=
  (ResidueField.mapAlgEquiv (algEquivLocalizationAtMaximalIdeal R R)).symm

/-- `maximalIdealResidueFieldAlgEquiv` sends the residue of `x` in the localization at
`maximalIdeal R` to the residue of its preimage in `R`. -/
@[simp]
theorem maximalIdealResidueFieldAlgEquiv_residue (x : Localization.AtPrime (maximalIdeal R)) :
    maximalIdealResidueFieldAlgEquiv R (residue _ x) =
      residue R ((algEquivLocalizationAtMaximalIdeal R R).symm x) := by
  rfl

/-- `maximalIdealResidueFieldAlgEquiv` sends the image of `r : R` in
`(maximalIdeal R).ResidueField` to `residue R r`. -/
theorem maximalIdealResidueFieldAlgEquiv_algebraMap (r : R) :
    maximalIdealResidueFieldAlgEquiv R (algebraMap R (maximalIdeal R).ResidueField r) =
      residue R r := by
  simp

/-- The inverse of `maximalIdealResidueFieldAlgEquiv` sends `residue R r` to the image of `r` in
`(maximalIdeal R).ResidueField`. -/
@[simp]
theorem maximalIdealResidueFieldAlgEquiv_symm_residue (r : R) :
    (maximalIdealResidueFieldAlgEquiv R).symm (residue R r) =
      algebraMap R (maximalIdeal R).ResidueField r := by
  simp [maximalIdealResidueFieldAlgEquiv,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime (maximalIdeal R))
      (maximalIdeal R).ResidueField]

end Equiv

/-- A prime `𝔮` of `S` over `𝔪_R` with `κ(𝔪_R) → κ(𝔮)` surjective is the kernel of an
`R`-algebra map `S →ₐ[R] ResidueField R`. -/
theorem exists_algHom_residueField_ker_eq [_root_.IsLocalRing R] [Algebra R S] {𝔮 : Ideal S}
    [𝔮.IsPrime] (h𝔮 : 𝔮.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Surjective
      (Ideal.ResidueField.map (maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm)) :
    ∃ ψ : S →ₐ[R] ResidueField R, RingHom.ker ψ = 𝔮 := by
  let f := Ideal.ResidueField.mapₐ (maximalIdeal R) 𝔮 (Algebra.ofId R S) h𝔮.symm
  let e : (maximalIdeal R).ResidueField ≃ₐ[R] 𝔮.ResidueField :=
    AlgEquiv.ofBijective f ⟨f.toRingHom.injective, hκ⟩
  let embedding : 𝔮.ResidueField →ₐ[R] ResidueField R :=
    (maximalIdealResidueFieldAlgEquiv R).toAlgHom.comp e.symm.toAlgHom
  exact ⟨embedding.comp (IsScalarTower.toAlgHom R S 𝔮.ResidueField),
    Ideal.ker_residueEmbedding_comp 𝔮 embedding⟩

end TauCeti.IsLocalRing

/-- If `𝔮` is the kernel of an `R`-algebra map `ψ : S →ₐ[R] ResidueField R`, then the induced map
`κ(𝔪_R) → κ(𝔮)` on residue fields is bijective. -/
theorem AlgHom.residueFieldMap_bijective_of_ker_eq [IsLocalRing R] [Algebra R S]
    (ψ : S →ₐ[R] IsLocalRing.ResidueField R) {𝔮 : Ideal S} [𝔮.IsPrime]
    (hker : RingHom.ker ψ = 𝔮)
    (h𝔮 : 𝔮.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
      hker ▸ ψ.comap_ker_residueField) :
    Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal R) 𝔮 (algebraMap R S) h𝔮.symm) := by
  let ψ' : S →ₐ[R] (IsLocalRing.maximalIdeal R).ResidueField :=
    (TauCeti.IsLocalRing.maximalIdealResidueFieldAlgEquiv R).symm.toAlgHom.comp ψ
  have hker' : RingHom.ker ψ' = 𝔮 := by
    rw [← hker]
    ext s
    simp [ψ', RingHom.mem_ker]
  subst hker'
  exact ψ'.residueFieldMap_bijective
