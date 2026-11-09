/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Site
public import TauCeti.Topology.GTopology.ContinuousMap

/-!
# Morphisms of classical affinoid sites

An algebra homomorphism `φ : A →ₐ[K] B` induces a continuous map from the weak affinoid
G-site of `Sp B` to that of `Sp A`. Inverse images are the actual inverse images of classical
points, and preserve finite affinoid covers. The universal property of subdomains supplies
pullback of functions, natural under restriction and compatible with identities and composition.
The restriction compatibility is the naturality square for the coordinate presheaves.

Only algebraic affinoidness is assumed: no norms on `A` or `B` are selected. The coordinate
algebras retain nilpotents. This constructs morphisms of sites and their coordinate presheaves,
not a sheaf condition or a local-ringed-space structure.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§7.2.2 and 9.1.4.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.AffinoidSubdomain

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]
  [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]
  [hC : Fact (IsAffinoidAlgebra K C)]

/-- The inverse image of an affinoid subdomain under the classical point map of an algebra
homomorphism. Its representing algebra exists by affinoid base change. -/
noncomputable def comap (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) : AffinoidSubdomain K B :=
  ⟨hB.out.maximalSpectrumComap φ ⁻¹' (U : Set (MaximalSpectrum A)), by
    obtain ⟨D, _, _, θ, hθ⟩ := U.isAffinoidSubdomainMap.exists_preimage hA.out hB.out φ
    exact ⟨CommAlgCat.of K D, θ, hθ⟩⟩

@[simp]
theorem coe_comap (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) :
    (U.comap φ : Set (MaximalSpectrum B)) =
      hB.out.maximalSpectrumComap φ ⁻¹' (U : Set (MaximalSpectrum A)) := (rfl)

@[simp]
theorem mem_comap (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) (x : MaximalSpectrum B) :
    x ∈ U.comap φ ↔ hB.out.maximalSpectrumComap φ x ∈ U := Iff.rfl

/-- Inverse image preserves inclusions of affinoid subdomains. -/
theorem comap_mono {U V : AffinoidSubdomain K A} (h : U ≤ V) (φ : A →ₐ[K] B) :
    U.comap φ ≤ V.comap φ := Set.preimage_mono h

@[simp]
theorem comap_id (U : AffinoidSubdomain K A) : U.comap (AlgHom.id K A) = U := by
  ext x
  simp

/-- Inverse image of subdomains is contravariantly functorial in the algebra. -/
@[simp]
theorem comap_comp (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    U.comap (ψ.comp φ) = (U.comap φ).comap ψ := by
  ext x
  simp [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]

@[simp]
theorem comap_top {φ : A →ₐ[K] B} : (⊤ : AffinoidSubdomain K A).comap φ = ⊤ := by
  apply SetLike.coe_injective
  simp

@[simp]
theorem comap_bot {φ : A →ₐ[K] B} : (⊥ : AffinoidSubdomain K A).comap φ = ⊥ := by
  apply SetLike.coe_injective
  simp

@[simp]
theorem comap_inf (U V : AffinoidSubdomain K A) (φ : A →ₐ[K] B) :
    (U ⊓ V).comap φ = U.comap φ ⊓ V.comap φ := by
  ext x
  simp

/-- Inverse image preserves weak admissible covers, including covers with only a finite
subcover and the empty cover of the empty subdomain. -/
theorem covers_comap {U : AffinoidSubdomain K A} {S : Set (AffinoidSubdomain K A)}
    (h : weakGTopology.Covers U S) (φ : A →ₐ[K] B) :
    weakGTopology.Covers (U.comap φ) ((fun V ↦ V.comap φ) '' S) := by
  rw [weakGTopology_covers_iff] at h ⊢
  obtain ⟨hSU, R, hRS, hfin, hR⟩ := h
  refine ⟨?_, (fun V ↦ V.comap φ) '' R, Set.image_mono hRS, hfin.image _, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact comap_mono (hSU V hV) φ
  · simpa only [Set.image_image, coe_comap, Set.sUnion_image, Set.biUnion_image,
      Set.preimage_iUnion] using congrArg (hB.out.maximalSpectrumComap φ ⁻¹' ·) hR

/-- The classical point map of the composite of the structure map on a pulled-back subdomain
with the original algebra map has image in the original subdomain. -/
private theorem range_comap_toSections_comp (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) :
    Set.range ((U.comap φ).isAffinoidAlgebra.maximalSpectrumComap
      ((U.comap φ).toSections.comp φ)) ⊆ (U : Set (MaximalSpectrum A)) := by
  rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out (U.comap φ).isAffinoidAlgebra,
    Set.range_comp, Set.image_subset_iff]
  exact (U.comap φ).isAffinoidSubdomainMap.range_maximalSpectrumComap_subset

/-- Pullback of functions to the inverse-image affinoid subdomain. -/
noncomputable def comapSections (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) :
    U.sections →ₐ[K] (U.comap φ).sections :=
  U.isAffinoidSubdomainMap.lift (U.comap φ).isAffinoidAlgebra
    ((U.comap φ).toSections.comp φ) (range_comap_toSections_comp U φ)

@[simp]
theorem comapSections_toSections (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) (a : A) :
    U.comapSections φ (U.toSections a) = (U.comap φ).toSections (φ a) :=
  U.isAffinoidSubdomainMap.lift_apply _ _ _ a

/-- Pullback of functions commutes with restriction to a smaller subdomain. -/
theorem comapSections_restrict {U V : AffinoidSubdomain K A} (h : U ≤ V)
    (φ : A →ₐ[K] B) :
    (U.comapSections φ).comp (restrict h) =
      (restrict (comap_mono h φ)).comp (V.comapSections φ) := by
  apply V.isAffinoidSubdomainMap.algHom_ext (U.comap φ).isAffinoidAlgebra
  ext a
  simp

/-- Pullback along the identity is the identity, after the canonical identification of its
inverse-image subdomain. -/
@[simp]
theorem restrict_comapSections_id (U : AffinoidSubdomain K A) :
    (restrict (le_of_eq U.comap_id.symm)).comp (U.comapSections (AlgHom.id K A)) =
      AlgHom.id K U.sections := by
  apply U.isAffinoidSubdomainMap.algHom_ext U.isAffinoidAlgebra
  ext a
  simp

/-- Pullback of functions respects composition, with the canonical identification between
successive inverse images and the inverse image under the composite. -/
theorem comapSections_comp (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    (restrict (le_of_eq (U.comap_comp φ ψ).symm)).comp (U.comapSections (ψ.comp φ)) =
      ((U.comap φ).comapSections ψ).comp (U.comapSections φ) := by
  apply U.isAffinoidSubdomainMap.algHom_ext ((U.comap φ).comap ψ).isAffinoidAlgebra
  ext a
  simp

end TauCeti.AffinoidSubdomain

namespace AlgHom

open TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]
  [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]
  [hC : Fact (IsAffinoidAlgebra K C)]

/-- An affinoid algebra homomorphism induces a continuous map of weak classical affinoid sites.
Its inverse-image functor therefore induces the native direct image on sheaves. -/
noncomputable def weakAffinoidMap (φ : A →ₐ[K] B) :
    (AffinoidSubdomain.weakGTopology (K := K) (A := B)).ContinuousMap
      (AffinoidSubdomain.weakGTopology (K := K) (A := A)) where
  toFun := hB.out.maximalSpectrumComap φ
  comap U := U.comap φ
  coe_comap' U := by simp
  covers_comap h := AffinoidSubdomain.covers_comap h φ

@[simp]
theorem weakAffinoidMap_apply (φ : A →ₐ[K] B) (x : MaximalSpectrum B) :
    φ.weakAffinoidMap x = hB.out.maximalSpectrumComap φ x := (rfl)

@[simp]
theorem weakAffinoidMap_comap (φ : A →ₐ[K] B) (U : AffinoidSubdomain K A) :
    φ.weakAffinoidMap.comap U = U.comap φ := (rfl)

@[simp]
theorem weakAffinoidMap_id : (AlgHom.id K A).weakAffinoidMap =
    GTopology.ContinuousMap.id (AffinoidSubdomain.weakGTopology (K := K) (A := A)) := by
  ext x
  simp

/-- The induced weak-site maps compose in the opposite order to the algebra maps. -/
@[simp]
theorem weakAffinoidMap_comp (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    (ψ.comp φ).weakAffinoidMap = φ.weakAffinoidMap.comp ψ.weakAffinoidMap := by
  ext x
  simp [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]

end AlgHom
