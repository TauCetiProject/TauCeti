/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.ContractiveRenorming
public import TauCeti.RingTheory.Affinoid.Pushout.Basic
public import TauCeti.RingTheory.Affinoid.Subdomain.Basic

import TauCeti.RingTheory.Affinoid.QuotientNorm

/-!
# Inverse images and intersections of affinoid subdomains

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, and let `φ : A → B`
represent a set `U ⊆ Sp A` of classical points as an affinoid subdomain
(`TauCeti.IsAffinoidSubdomainMap`). This file shows that affinoid subdomains are stable under
inverse images along morphisms of affinoid spectra and under finite intersections.

* **Inverse images.** For a `K`-algebra map `ψ : A → C` into an affinoid algebra, the inverse image
  of `U` under `Sp C → Sp A` is an affinoid subdomain of `Sp C`. It is represented by the
  map from `C` into the affinoid pushout of `B` and `C` over `A`.
* **Intersections.** If `φ' : A → C` represents `V`, then `U ∩ V` is an affinoid subdomain of
  `Sp A`, represented by the composite of `φ'` with that map.

The inverse-image statement only uses the universal property of the pushout among affinoid
algebras: for any commutative square `χ ∘ φ = θ ∘ ψ` whose corner `D` is a pushout of `B` and
`C` over `A` for maps into affinoid algebras, `θ : C → D` represents the inverse image of `U`
(`TauCeti.IsAffinoidSubdomainMap.preimage`). A map `γ : C → E` whose classical points lie over
`U` gives a map `B → E` by the universal property of `U`, and the pushout combines the two. The
pushout itself is the algebra `A⟨X, Y⟩ ⧸ (I, J)` of `TauCeti.AffinoidPushout`, for presentations
`B = A⟨X⟩ ⧸ I` and `C = A⟨Y⟩ ⧸ J` extending `φ` and `ψ`, and its universal property is
`TauCeti.AffinoidPushout.existsUnique_algHom`. It is built from a complete ultrametric algebra norm
on `A`; since every affinoid algebra carries one, the residue norm of a Tate presentation
(`TauCeti.IsAffinoidAlgebra.residueNormedCommRing`), the two results below hold for every affinoid
algebra `A` with no chosen norm.

## Main results

* `TauCeti.IsAffinoidSubdomainMap.preimage`: the corner of a pushout square represents the
  inverse image of an affinoid subdomain.
* `TauCeti.IsAffinoidSubdomainMap.exists_preimage`: the inverse image of an affinoid subdomain
  under a morphism of affinoid spectra is an affinoid subdomain.
* `TauCeti.IsAffinoidSubdomainMap.exists_inter`: the intersection of two affinoid subdomains is
  an affinoid subdomain.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §7.2.2.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries

universe u

namespace IsAffinoidSubdomainMap

section Pushout

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]

/-- **Inverse images of affinoid subdomains along a pushout square.** Let `φ : A → B` represent
`U ⊆ Sp A`, and let `χ ∘ φ = θ ∘ ψ` be a commutative square of `K`-algebra maps with `D` affinoid,
which is a pushout for maps into affinoid algebras: two maps `β : B → E` and `γ : C → E` into an
affinoid algebra with `β ∘ φ = γ ∘ ψ` factor through exactly one map `D → E`. Then `θ : C → D`
represents the inverse image of `U` under `Sp C → Sp A`. -/
theorem preimage {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U)
    (hC : IsAffinoidAlgebra K C) (hD : IsAffinoidAlgebra K D) {ψ : A →ₐ[K] C} {χ : B →ₐ[K] D}
    {θ : C →ₐ[K] D} (hsq : χ.comp φ = θ.comp ψ)
    (hpush : ∀ {E : Type u} [CommRing E] [Algebra K E], IsAffinoidAlgebra K E →
      ∀ (β : B →ₐ[K] E) (γ : C →ₐ[K] E), β.comp φ = γ.comp ψ →
        ∃! δ : D →ₐ[K] E, δ.comp χ = β ∧ δ.comp θ = γ) :
    IsAffinoidSubdomainMap θ (hC.maximalSpectrumComap ψ ⁻¹' U) where
  isAffinoidAlgebra := hD
  range_maximalSpectrumComap_subset := by
    rintro _ ⟨z, rfl⟩
    have hz := h.range_maximalSpectrumComap_comp_subset hD χ ⟨z, rfl⟩
    rwa [hsq, IsAffinoidAlgebra.maximalSpectrumComap_comp hC hD] at hz
  existsUnique_algHom {E} _ _ hE γ hγ := by
    -- The classical points of `E` lie over `U`, so `γ ∘ ψ` factors through `φ`.
    have hγU : Set.range (hE.maximalSpectrumComap (γ.comp ψ)) ⊆ U := by
      rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hC hE, Set.range_comp]
      exact Set.image_subset_iff.mpr hγ
    obtain ⟨δ, ⟨-, hδθ⟩, huniq⟩ :=
      hpush hE (h.lift hE (γ.comp ψ) hγU) γ (h.lift_comp hE (γ.comp ψ) hγU)
    -- A map `δ' : D → E` with `δ' ∘ θ = γ` restricts along `χ` to the factorisation of `γ ∘ ψ`.
    refine ⟨δ, hδθ, fun δ' hδ' ↦ huniq δ' ⟨h.eq_lift hE (γ.comp ψ) hγU ?_, hδ'⟩⟩
    rw [AlgHom.comp_assoc, hsq, ← AlgHom.comp_assoc, hδ']

end Pushout

section Normed

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]

omit [IsUltrametricDist K] [CompleteSpace K] [CompleteSpace A] in
/-- A presentation `β : A⟨X⟩ → B` extending `φ : A → B` identifies the image of `a : A` in
`A⟨X⟩ ⧸ ker β` with `φ a`. -/
private theorem quotientKerAlgEquivOfSurjective_algebraMap {φ : A →ₐ[K] B} {m : ℕ}
    {β : IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) →ₐ[K] B} (hβ : Function.Surjective β)
    (hβφ : ∀ a, β (algebraMap A _ a) = φ a) (a : A) :
    Ideal.quotientKerAlgEquivOfSurjective hβ (algebraMap A _ a) = φ a := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotientKerAlgEquivOfSurjective_mk, hβφ]

/-- The affinoid pushout `A⟨X, Y⟩ ⧸ (I, J)` of the presentations `B ≃ A⟨X⟩ ⧸ I` and
`C ≃ A⟨Y⟩ ⧸ J` is a pushout of `B` and `C` over `A` for maps into every affinoid algebra. -/
private theorem existsUnique_affinoidPushout (hA : IsAffinoidAlgebra K A) {φ : A →ₐ[K] B}
    {ψ : A →ₐ[K] C} {m n : ℕ}
    {β : IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) →ₐ[K] B} (hβ : Function.Surjective β)
    (hβφ : ∀ a, β (algebraMap A _ a) = φ a)
    {γ : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) →ₐ[K] C} (hγ : Function.Surjective γ)
    (hγψ : ∀ a, γ (algebraMap A _ a) = ψ a)
    {E : Type u} [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E) (b : B →ₐ[K] E)
    (c : C →ₐ[K] E) (hbc : b.comp φ = c.comp ψ) :
    ∃! δ : AffinoidPushout (RingHom.ker β) (RingHom.ker γ) →ₐ[K] E,
      δ.comp (((AffinoidPushout.inl (RingHom.ker β) (RingHom.ker γ)).restrictScalars K).comp
          (Ideal.quotientKerAlgEquivOfSurjective hβ).symm.toAlgHom) = b ∧
      δ.comp (((AffinoidPushout.inr (RingHom.ker β) (RingHom.ker γ)).restrictScalars K).comp
          (Ideal.quotientKerAlgEquivOfSurjective hγ).symm.toAlgHom) = c := by
  let eB := Ideal.quotientKerAlgEquivOfSurjective hβ
  let eC := Ideal.quotientKerAlgEquivOfSurjective hγ
  obtain ⟨δ, ⟨hl, hr⟩, huniq⟩ := AffinoidPushout.existsUnique_algHom hA hE
    (b.comp eB.toAlgHom) (c.comp eC.toAlgHom) fun a ↦ by
      simpa [eB, eC, quotientKerAlgEquivOfSurjective_algebraMap hβ hβφ,
        quotientKerAlgEquivOfSurjective_algebraMap hγ hγψ] using AlgHom.congr_fun hbc a
  refine ⟨δ, ⟨AlgHom.ext fun y ↦ ?_, AlgHom.ext fun z ↦ ?_⟩,
    fun δ' ⟨hl', hr'⟩ ↦ huniq δ' ⟨fun x ↦ ?_, fun y ↦ ?_⟩⟩
  · simp [hl, eB]
  · simp [hr, eC]
  · simp [← hl', eB]
  · simp [← hr', eC]

/-- The inverse image of an affinoid subdomain, for an affinoid algebra `A` carrying a complete
ultrametric algebra norm. -/
private theorem exists_preimage_of_normed (hA : IsAffinoidAlgebra K A) {φ : A →ₐ[K] B}
    {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U) (hC : IsAffinoidAlgebra K C)
    (ψ : A →ₐ[K] C) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra K D) (θ : C →ₐ[K] D),
      IsAffinoidSubdomainMap θ (hC.maximalSpectrumComap ψ ⁻¹' U) := by
  obtain ⟨m, β, hβ, hβφ⟩ := hA.exists_surjective_algHom_isRestricted_subring h.isAffinoidAlgebra φ
  obtain ⟨n, γ, hγ, hγψ⟩ := hA.exists_surjective_algHom_isRestricted_subring hC ψ
  refine ⟨_, _, _, _, h.preimage hC (AffinoidPushout.isAffinoidAlgebra _ _ hA) ?_
    (fun hE b c hbc ↦ existsUnique_affinoidPushout hA hβ hβφ hγ hγψ hE b c hbc)⟩
  -- The square commutes: both composites are the structure map of the pushout as an `A`-algebra.
  refine AlgHom.ext fun a ↦ ?_
  simp [(AlgEquiv.symm_apply_eq _).mpr (quotientKerAlgEquivOfSurjective_algebraMap hβ hβφ a).symm,
    (AlgEquiv.symm_apply_eq _).mpr (quotientKerAlgEquivOfSurjective_algebraMap hγ hγψ a).symm]

end Normed

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}

/-- **Inverse images of affinoid subdomains.** If `φ : A → B` represents `U ⊆ Sp A` as an affinoid
subdomain and `ψ : A → C` is a `K`-algebra map into an affinoid algebra, then the inverse image of
`U` under `Sp C → Sp A` is an affinoid subdomain of `Sp C`: some `K`-algebra map `θ : C → D`
represents it. -/
theorem exists_preimage (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A)
    (hC : IsAffinoidAlgebra K C) (ψ : A →ₐ[K] C) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra K D) (θ : C →ₐ[K] D),
      IsAffinoidSubdomainMap θ (hC.maximalSpectrumComap ψ ⁻¹' U) := by
  -- Give `A` the residue norm of a Tate presentation.
  let _ := hA.residueNormedCommRing
  let _ := hA.residueNormedAlgebra
  have := hA.isUltrametricDist_residueNormedCommRing
  have := hA.completeSpace_residueNormedCommRing
  exact exists_preimage_of_normed hA h hC ψ

/-- **Intersections of affinoid subdomains.** If `φ : A → B` represents `U ⊆ Sp A` and
`φ' : A → C` represents `V ⊆ Sp A` as affinoid subdomains, then `U ∩ V` is an affinoid subdomain
of `Sp A`: some `K`-algebra map `θ : A → D` represents it. -/
theorem exists_inter (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A)
    {φ' : A →ₐ[K] C} {V : Set (MaximalSpectrum A)} (h' : IsAffinoidSubdomainMap φ' V) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra K D) (θ : A →ₐ[K] D),
      IsAffinoidSubdomainMap θ (U ∩ V) := by
  obtain ⟨D, _, _, θ, hθ⟩ := h.exists_preimage hA h'.isAffinoidAlgebra φ'
  -- The image in `Sp A` of the inverse image of `U` in `Sp C ≃ V` is `U ∩ V`.
  have := h'.comp hA hθ
  rw [Set.image_preimage_eq_inter_range, h'.range_maximalSpectrumComap hA] at this
  exact ⟨D, _, _, _, this⟩

end IsAffinoidSubdomainMap

end TauCeti
