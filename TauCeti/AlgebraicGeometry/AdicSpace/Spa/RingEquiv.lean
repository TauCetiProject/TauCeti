/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import Mathlib.RingTheory.Ideal.Maps

/-!
# Isomorphisms of topological rings induce homeomorphisms of adic spectra

An isomorphism of topological commutative rings `e : A ≃+* B` carrying a subring `A⁺ ⊆ A` onto a
subring `B⁺ ⊆ B` induces a contravariant homeomorphism of sub-unit valuation loci

```text
Spa (B, B⁺) ≃ₜ Spa (A, A⁺)
```

by pullback along `e`, with inverse given by pullback along `e.symm`. Because a homeomorphic ring
isomorphism carries open ideals onto open ideals, this homeomorphism also matches the families of
rational subsets `spaRationalFamily` of the two spaces.

No Huber, completeness, or separation hypothesis is needed: both the topological identification
and the preservation of open numerator ideals use only continuity of `e` and `e.symm`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv`: the homeomorphism
  `spa Bplus ≃ₜ spa Aplus` induced by a topological ring isomorphism `e : A ≃+* B` preserving the
  chosen subrings in both directions.

## Main results

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_apply`,
  `TauCeti.ValuationSpectrum.coe_spaHomeomorphOfRingEquiv`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_symm_apply`,
  `TauCeti.ValuationSpectrum.coe_spaHomeomorphOfRingEquiv_symm`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_val`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_symm_val`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_symm`: pointwise, functional, underlying
  valuation, and symmetry characterizations of `spaHomeomorphOfRingEquiv`.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_refl`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_trans`: contravariant functoriality with
  respect to `RingEquiv.refl` and `RingEquiv.trans`.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff`,
  `TauCeti.ValuationSpectrum.bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily`:
  preimage under `spaHomeomorphOfRingEquiv` bijects `spaRationalFamily Aplus` onto
  `spaRationalFamily Bplus`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23 and Remark 7.30.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- A topological ring isomorphism `e : A ≃+* B` carrying `A⁺` into `B⁺` and `B⁺` back into `A⁺`
induces a homeomorphism `Spa (B, B⁺) ≃ₜ Spa (A, A⁺)` by pullback of valuations along `e`. -/
def spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    spa Bplus ≃ₜ spa Aplus where
  toFun := spaComap (e : A →+* B) he Aplus Bplus hplus
  invFun := spaComap (e.symm : B →+* A) he' Bplus Aplus hplus'
  left_inv := spaComap_spaComap (e.symm : B →+* A) he' hplus' (e : A →+* B) he
    e.apply_symm_apply hplus
  right_inv := spaComap_spaComap (e : A →+* B) he hplus (e.symm : B →+* A) he'
    e.symm_apply_apply hplus'
  continuous_toFun := continuous_spaComap (e : A →+* B) he Aplus Bplus hplus
  continuous_invFun := continuous_spaComap (e.symm : B →+* A) he' Bplus Aplus hplus'

/-- `spaHomeomorphOfRingEquiv` acts on points as `spaComap` along `e`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_apply (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    (v : spa Bplus) :
    spaHomeomorphOfRingEquiv e he he' hplus hplus' v =
      spaComap (e : A →+* B) he Aplus Bplus hplus v := (rfl)

/-- As a function, `spaHomeomorphOfRingEquiv` is `spaComap` along `e`. -/
@[simp]
theorem coe_spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    ⇑(spaHomeomorphOfRingEquiv e he he' hplus hplus') =
      spaComap (e : A →+* B) he Aplus Bplus hplus :=
  funext (spaHomeomorphOfRingEquiv_apply e he he' hplus hplus')

/-- The inverse of `spaHomeomorphOfRingEquiv` acts on points as `spaComap` along `e.symm`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_symm_apply (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    (v : spa Aplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus hplus').symm v =
      spaComap (e.symm : B →+* A) he' Bplus Aplus hplus' v := (rfl)

/-- As a function, `(spaHomeomorphOfRingEquiv e ...).symm` is `spaComap` along `e.symm`. -/
@[simp]
theorem coe_spaHomeomorphOfRingEquiv_symm (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    ⇑(spaHomeomorphOfRingEquiv e he he' hplus hplus').symm =
      spaComap (e.symm : B →+* A) he' Bplus Aplus hplus' :=
  funext (spaHomeomorphOfRingEquiv_symm_apply e he he' hplus hplus')

/-- On underlying points of `Spv`, `spaHomeomorphOfRingEquiv` acts as `ValuationSpectrum.comap`
along `e`. -/
theorem spaHomeomorphOfRingEquiv_val (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    (v : spa Bplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus hplus' v).1 = comap (e : A →+* B) v.1 :=
  spaComap_val (e : A →+* B) he Aplus Bplus hplus v

/-- On underlying points of `Spv`, `(spaHomeomorphOfRingEquiv e ...).symm` acts as
`ValuationSpectrum.comap` along `e.symm`. -/
theorem spaHomeomorphOfRingEquiv_symm_val (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    (v : spa Aplus) :
    ((spaHomeomorphOfRingEquiv e he he' hplus hplus').symm v).1 =
      comap (e.symm : B →+* A) v.1 :=
  spaComap_val (e.symm : B →+* A) he' Bplus Aplus hplus' v

/-- The inverse of `spaHomeomorphOfRingEquiv` is `spaHomeomorphOfRingEquiv` for `e.symm`. -/
theorem spaHomeomorphOfRingEquiv_symm (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus hplus').symm =
      spaHomeomorphOfRingEquiv e.symm he' he hplus' hplus :=
  Homeomorph.ext fun _ ↦ rfl

/-- `spaHomeomorphOfRingEquiv` of the identity ring equivalence is the identity homeomorphism. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_refl (Aplus : Subring A) :
    spaHomeomorphOfRingEquiv (RingEquiv.refl A) continuous_id continuous_id
      (Aplus := Aplus) (Bplus := Aplus) (fun _ ha ↦ ha) (fun _ ha ↦ ha) =
      Homeomorph.refl (spa Aplus) :=
  Homeomorph.ext fun v ↦ congr_fun (spaComap_id Aplus) v

/-- `spaHomeomorphOfRingEquiv` is contravariantly functorial for `RingEquiv.trans`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_trans (e₁ : A ≃+* B) (he₁ : Continuous e₁)
    (he₁' : Continuous e₁.symm) (e₂ : B ≃+* C) (he₂ : Continuous e₂) (he₂' : Continuous e₂.symm)
    {Aplus : Subring A} {Bplus : Subring B} {Cplus : Subring C}
    (hplus₁ : ∀ a ∈ Aplus, e₁ a ∈ Bplus) (hplus₁' : ∀ b ∈ Bplus, e₁.symm b ∈ Aplus)
    (hplus₂ : ∀ b ∈ Bplus, e₂ b ∈ Cplus) (hplus₂' : ∀ c ∈ Cplus, e₂.symm c ∈ Bplus) :
    spaHomeomorphOfRingEquiv (e₁.trans e₂) (he₂.comp he₁) (he₁'.comp he₂')
        (fun a ha ↦ hplus₂ (e₁ a) (hplus₁ a ha))
        (fun c hc ↦ hplus₁' (e₂.symm c) (hplus₂' c hc)) =
      (spaHomeomorphOfRingEquiv e₂ he₂ he₂' hplus₂ hplus₂').trans
        (spaHomeomorphOfRingEquiv e₁ he₁ he₁' hplus₁ hplus₁') :=
  Homeomorph.ext fun v ↦ congr_fun
    (spaComap_comp (φ := (e₁ : A →+* B)) he₁ (ψ := (e₂ : B →+* C)) he₂
      Aplus Bplus Cplus hplus₁ hplus₂) v

/-- Preimage under `spaHomeomorphOfRingEquiv` carries rational subsets of `Spa (A, A⁺)` to rational
subsets of `Spa (B, B⁺)`. -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) :
    spaHomeomorphOfRingEquiv e he he' hplus hplus' ⁻¹' U ∈ spaRationalFamily Bplus := by
  rw [coe_spaHomeomorphOfRingEquiv]
  refine spaComap_preimage_mem_spaRationalFamily (e : A →+* B) he Aplus Bplus hplus
    (fun J hJ ↦ ?_) hU
  have hmap : Ideal.map (e : A →+* B) J = J.comap e.symm := (Ideal.comap_symm e).symm
  rw [hmap, Ideal.coe_comap]
  exact hJ.preimage he'

/-- Image under `spaHomeomorphOfRingEquiv` carries rational subsets of `Spa (B, B⁺)` to rational
subsets of `Spa (A, A⁺)`. -/
theorem spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    {V : Set (spa Bplus)} (hV : V ∈ spaRationalFamily Bplus) :
    spaHomeomorphOfRingEquiv e he he' hplus hplus' '' V ∈ spaRationalFamily Aplus := by
  rw [Homeomorph.image_eq_preimage_symm, spaHomeomorphOfRingEquiv_symm]
  exact spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e.symm he' he hplus' hplus hV

/-- A subset of `Spa (A, A⁺)` is rational if and only if its preimage under
`spaHomeomorphOfRingEquiv` is a rational subset of `Spa (B, B⁺)`. -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    {U : Set (spa Aplus)} :
    spaHomeomorphOfRingEquiv e he he' hplus hplus' ⁻¹' U ∈ spaRationalFamily Bplus ↔
      U ∈ spaRationalFamily Aplus := by
  refine ⟨fun h ↦ ?_, spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus hplus'⟩
  have himage := spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus hplus' h
  rwa [Set.image_preimage_eq _ (spaHomeomorphOfRingEquiv e he he' hplus hplus').surjective]
    at himage

/-- Preimage under `spaHomeomorphOfRingEquiv` bijects the rational subsets of `Spa (A, A⁺)` onto
the rational subsets of `Spa (B, B⁺)`. -/
theorem bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    Set.BijOn (fun U : Set (spa Aplus) ↦ spaHomeomorphOfRingEquiv e he he' hplus hplus' ⁻¹' U)
      (spaRationalFamily Aplus) (spaRationalFamily Bplus) :=
  ⟨fun _ hU ↦ spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus hplus' hU,
    (spaHomeomorphOfRingEquiv e he he' hplus hplus').surjective.preimage_injective.injOn,
    fun V hV ↦ ⟨spaHomeomorphOfRingEquiv e he he' hplus hplus' '' V,
      spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus hplus' hV,
      (spaHomeomorphOfRingEquiv e he he' hplus hplus').preimage_image V⟩⟩

end TauCeti.ValuationSpectrum

end
