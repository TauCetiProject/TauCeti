/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.MaximalSpectrum

/-!
# Affinoid subdomains

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, with classical spectrum
`Sp A = MaximalSpectrum A`. A `K`-algebra map `φ : A → B` *represents* a set `U ⊆ Sp A` as an
affinoid subdomain (`TauCeti.IsAffinoidSubdomainMap φ U`) if `B` is affinoid, the induced map
`Sp B → Sp A` takes values in `U`, and every `K`-algebra map `ψ : A → C` into an affinoid algebra
for which `Sp C → Sp A` takes values in `U` factors uniquely through `φ`. The predicate is
algebraic: no norm on `A`, `B` or the test algebras `C` is chosen. The test algebras range over the
universe of `A` and `B`.

The universal property alone determines the points and the infinitesimal neighbourhoods of `U`.

* If every maximal ideal containing an ideal `I` of `A` lies in `U`, then `A ⧸ I → B ⧸ I B` is an
  isomorphism. In particular `A ⧸ 𝔪ₓⁿ ≃ B ⧸ 𝔪ₓⁿ B` for every `x ∈ U` and every `n`.
* The maximal ideals of `B` are exactly the extensions `𝔪ₓ B` for `x ∈ U`, so `Sp B → Sp A` is a
  bijection onto `U`. In particular the represented set is determined by `φ`.

The representing map is unique up to unique isomorphism, the identity represents `Sp A`, the zero
quotient represents the empty set, and representing maps compose: if `φ` represents `U` and
`φ' : B → C` represents `V ⊆ Sp B`, then `φ' ∘ φ` represents the image of `V` in `Sp A`.

## Main definitions

* `TauCeti.IsAffinoidSubdomainMap φ U`: `φ : A → B` represents `U` as an affinoid subdomain.
* `TauCeti.IsAffinoidSubdomainMap.lift`: the factorisation through `φ` of a map whose classical
  points lie over `U`.
* `TauCeti.IsAffinoidSubdomainMap.quotientAlgEquiv`: the isomorphism `A ⧸ I ≃ B ⧸ I B`.
* `TauCeti.IsAffinoidSubdomainMap.maximalSpectrumEquiv`: the bijection `Sp B ≃ U`.
* `TauCeti.IsAffinoidSubdomainMap.algEquiv`: the isomorphism between two representing algebras.

## Main results

* `TauCeti.IsAffinoidSubdomainMap.algHom_ext`: maps out of `B` are determined on `A`.
* `TauCeti.IsAffinoidSubdomainMap.isMaximal_map`: `𝔪ₓ B` is maximal for `x ∈ U`.
* `TauCeti.IsAffinoidSubdomainMap.map_maximalSpectrumComap_asIdeal`: every maximal ideal of `B` is
  the extension of the point of `U` below it.
* `TauCeti.IsAffinoidSubdomainMap.range_maximalSpectrumComap`: the image of `Sp B → Sp A` is `U`.
* `TauCeti.IsAffinoidSubdomainMap.maximalSpectrumComap_injective`: `Sp B → Sp A` is injective.
* `TauCeti.IsAffinoidSubdomainMap.comp`: transitivity of affinoid subdomains.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §7.2.2.
-/

public section

namespace TauCeti

universe u

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- **Affinoid subdomains.** The `K`-algebra map `φ : A → B` represents the set `U` of classical
points of `A` as an affinoid subdomain: `B` is affinoid, every classical point of `B` lies over a
point of `U`, and every `K`-algebra map `ψ : A → C` into an affinoid algebra whose classical points
all lie over `U` factors uniquely through `φ`. The test algebras `C` carry no chosen norm and range
over the universe of `A` and `B`. -/
structure IsAffinoidSubdomainMap (φ : A →ₐ[K] B) (U : Set (MaximalSpectrum A)) : Prop where
  /-- The representing algebra is affinoid. -/
  isAffinoidAlgebra : IsAffinoidAlgebra K B
  /-- Every classical point of the representing algebra lies over a point of `U`. -/
  range_maximalSpectrumComap_subset : Set.range (isAffinoidAlgebra.maximalSpectrumComap φ) ⊆ U
  /-- The universal property: maps whose classical points lie over `U` factor uniquely. -/
  existsUnique_algHom {C : Type u} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    (ψ : A →ₐ[K] C) (hψ : Set.range (hC.maximalSpectrumComap ψ) ⊆ U) :
    ∃! χ : B →ₐ[K] C, χ.comp φ = ψ

namespace IsAffinoidSubdomainMap

variable {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)} (h : IsAffinoidSubdomainMap φ U)
  {C : Type u} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)

section UniversalProperty

include h in
/-- The classical points of an affinoid algebra receiving a map from `B` lie over `U`. -/
theorem range_maximalSpectrumComap_comp_subset (χ : B →ₐ[K] C) :
    Set.range (hC.maximalSpectrumComap (χ.comp φ)) ⊆ U := by
  rw [IsAffinoidAlgebra.maximalSpectrumComap_comp h.isAffinoidAlgebra hC, Set.range_comp]
  exact (Set.image_subset_range _ _).trans h.range_maximalSpectrumComap_subset

include h hC in
/-- `K`-algebra maps from the representing algebra into an affinoid algebra are determined by their
restrictions to `A`. -/
theorem algHom_ext {χ₁ χ₂ : B →ₐ[K] C} (hχ : χ₁.comp φ = χ₂.comp φ) : χ₁ = χ₂ :=
  (h.existsUnique_algHom hC _ (h.range_maximalSpectrumComap_comp_subset hC χ₂)).unique hχ rfl

variable (ψ : A →ₐ[K] C) (hψ : Set.range (hC.maximalSpectrumComap ψ) ⊆ U)

/-- The factorisation through the representing algebra of a `K`-algebra map `ψ : A → C` into an
affinoid algebra whose classical points lie over `U`. -/
noncomputable def lift : B →ₐ[K] C :=
  (h.existsUnique_algHom hC ψ hψ).exists.choose

@[simp]
theorem lift_comp : (h.lift hC ψ hψ).comp φ = ψ :=
  (h.existsUnique_algHom hC ψ hψ).exists.choose_spec

@[simp]
theorem lift_apply (a : A) : h.lift hC ψ hψ (φ a) = ψ a :=
  DFunLike.congr_fun (h.lift_comp hC ψ hψ) a

/-- Every factorisation of `ψ` through `φ` is `IsAffinoidSubdomainMap.lift`. -/
theorem eq_lift {χ : B →ₐ[K] C} (hχ : χ.comp φ = ψ) : χ = h.lift hC ψ hψ :=
  h.algHom_ext hC (hχ.trans (h.lift_comp hC ψ hψ).symm)

end UniversalProperty

section Points

variable (hA : IsAffinoidAlgebra K A)

/-- **Infinitesimal neighbourhoods of an affinoid subdomain.** If every maximal ideal of `A`
containing the ideal `I` is a point of `U`, then `φ` induces an isomorphism `A ⧸ I ≃ B ⧸ I B`. -/
noncomputable def quotientAlgEquiv {I : Ideal A}
    (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U) : (A ⧸ I) ≃ₐ[K] B ⧸ I.map φ :=
  have hB := h.isAffinoidAlgebra
  -- The classical points of `A ⧸ I` lie over `U`, so the residue map factors through `B`.
  have hq : Set.range ((hA.quotient I).maximalSpectrumComap (Ideal.Quotient.mkₐ K I)) ⊆ U := by
    rintro _ ⟨y, rfl⟩
    refine hI _ fun a ha ↦ ?_
    simp [IsAffinoidAlgebra.maximalSpectrumComap_asIdeal, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  let χ := h.lift (hA.quotient I) _ hq
  have hχ (b : B) (hb : b ∈ I.map φ) : χ b = 0 := by
    refine (Ideal.map_le_iff_le_comap.mpr (fun a ha ↦ ?_) hb : b ∈ RingHom.ker χ)
    simp [χ, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  AlgEquiv.ofAlgHom (Ideal.quotientMapₐ _ φ Ideal.le_comap_map) (Ideal.Quotient.liftₐ _ χ hχ)
    (by
      -- Both composites `B → B ⧸ I B` restrict along `φ` to the residue map of `φ`.
      refine Ideal.Quotient.algHom_ext K (h.algHom_ext (hB.quotient (I.map φ)) ?_)
      simp only [AlgHom.comp_assoc, AlgHom.id_comp]
      rw [← AlgHom.comp_assoc (Ideal.Quotient.liftₐ _ χ hχ), Ideal.Quotient.liftₐ_comp, h.lift_comp,
        Ideal.quotient_map_comp_mkₐ])
    (Ideal.Quotient.algHom_ext K <| by
      rw [AlgHom.comp_assoc, Ideal.quotient_map_comp_mkₐ, ← AlgHom.comp_assoc,
        Ideal.Quotient.liftₐ_comp, h.lift_comp, AlgHom.id_comp])

@[simp]
theorem quotientAlgEquiv_mk {I : Ideal A} (hI : ∀ x : MaximalSpectrum A, I ≤ x.asIdeal → x ∈ U)
    (a : A) :
    h.quotientAlgEquiv hA hI (Ideal.Quotient.mk I a) = Ideal.Quotient.mk (I.map φ) (φ a) :=
  (rfl)

/-- **Infinitesimal neighbourhoods of a point of an affinoid subdomain.** For `x ∈ U` and every
`n`, the representing map induces an isomorphism `A ⧸ 𝔪ₓⁿ ≃ B ⧸ 𝔪ₓⁿ B`. -/
noncomputable def quotientPowAlgEquiv {x : MaximalSpectrum A} (hx : x ∈ U) (n : ℕ) :
    (A ⧸ x.asIdeal ^ n) ≃ₐ[K] B ⧸ (x.asIdeal ^ n).map φ :=
  -- The only maximal ideal containing a power of `𝔪ₓ` is `𝔪ₓ`; no maximal ideal contains `𝔪ₓ⁰`.
  h.quotientAlgEquiv hA fun y hy ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (by simpa using hy) y.isMaximal.ne_top
    · rwa [← MaximalSpectrum.ext (x.isMaximal.eq_of_le y.isMaximal.ne_top
        (Ideal.IsPrime.le_of_pow_le hy))]

@[simp]
theorem quotientPowAlgEquiv_mk {x : MaximalSpectrum A} (hx : x ∈ U) (n : ℕ) (a : A) :
    h.quotientPowAlgEquiv hA hx n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) :=
  (rfl)

include h hA in
/-- The extension `𝔪ₓ B` of the maximal ideal of a point `x ∈ U` is a maximal ideal of `B`. -/
theorem isMaximal_map {x : MaximalSpectrum A} (hx : x ∈ U) : (x.asIdeal.map φ).IsMaximal := by
  have e := (h.quotientAlgEquiv hA (I := x.asIdeal) fun y hy ↦ by
    rwa [← MaximalSpectrum.ext (x.isMaximal.eq_of_le y.isMaximal.ne_top hy)]).symm
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp x.isMaximal) e.toMulEquiv

include h hA in
/-- The extension `𝔪ₓ B` of the maximal ideal of a point `x ∈ U` contracts to `𝔪ₓ`. -/
theorem comap_map_of_mem {x : MaximalSpectrum A} (hx : x ∈ U) :
    (x.asIdeal.map φ).comap φ = x.asIdeal :=
  (x.isMaximal.eq_of_le (Ideal.comap_ne_top _ (h.isMaximal_map hA hx).ne_top)
    Ideal.le_comap_map).symm

include h hA in
/-- **Classical points of an affinoid subdomain.** Every maximal ideal of the representing algebra
`B` is the extension `𝔪ₓ B` of the point `x ∈ U` below it. -/
theorem map_maximalSpectrumComap_asIdeal (y : MaximalSpectrum B) :
    (h.isAffinoidAlgebra.maximalSpectrumComap φ y).asIdeal.map φ = y.asIdeal :=
  (h.isMaximal_map hA (h.range_maximalSpectrumComap_subset ⟨y, rfl⟩)).eq_of_le y.isMaximal.ne_top
    (by simpa only [IsAffinoidAlgebra.maximalSpectrumComap_asIdeal] using Ideal.map_comap_le)

include h hA in
/-- The map `Sp B → Sp A` induced by a representing map is injective. -/
theorem maximalSpectrumComap_injective :
    Function.Injective (h.isAffinoidAlgebra.maximalSpectrumComap φ) := fun y₁ y₂ hy ↦
  MaximalSpectrum.ext <| by
    rw [← h.map_maximalSpectrumComap_asIdeal hA y₁, hy, h.map_maximalSpectrumComap_asIdeal hA y₂]

include h hA in
/-- The image of the map `Sp B → Sp A` induced by a representing map is the represented set. In
particular a representing map represents only one set. -/
theorem range_maximalSpectrumComap : Set.range (h.isAffinoidAlgebra.maximalSpectrumComap φ) = U :=
  subset_antisymm h.range_maximalSpectrumComap_subset fun x hx ↦
    ⟨⟨x.asIdeal.map φ, h.isMaximal_map hA hx⟩, MaximalSpectrum.ext <|
      (IsAffinoidAlgebra.maximalSpectrumComap_asIdeal _ _ _).trans (h.comap_map_of_mem hA hx)⟩

/-- **The classical points of an affinoid subdomain**: the contraction of maximal ideals along a
representing map `φ : A → B` is a bijection `Sp B ≃ U`. -/
noncomputable def maximalSpectrumEquiv : MaximalSpectrum B ≃ U :=
  (Equiv.ofInjective _ (h.maximalSpectrumComap_injective hA)).trans
    (Set.equivOfEq (h.range_maximalSpectrumComap hA))

@[simp]
theorem coe_maximalSpectrumEquiv (y : MaximalSpectrum B) :
    (h.maximalSpectrumEquiv hA y : MaximalSpectrum A) =
      h.isAffinoidAlgebra.maximalSpectrumComap φ y :=
  (rfl)

@[simp]
theorem maximalSpectrumEquiv_symm_apply_asIdeal (x : U) :
    ((h.maximalSpectrumEquiv hA).symm x).asIdeal = (x : MaximalSpectrum A).asIdeal.map φ := by
  obtain ⟨y, rfl⟩ := (h.maximalSpectrumEquiv hA).surjective x
  rw [Equiv.symm_apply_apply, coe_maximalSpectrumEquiv, h.map_maximalSpectrumComap_asIdeal hA]

end Points

section Uniqueness

variable {B' : Type u} [CommRing B'] [Algebra K B'] {φ' : A →ₐ[K] B'}
  (h' : IsAffinoidSubdomainMap φ' U)

/-- **Uniqueness of representing algebras.** Two representing algebras of the same set are
isomorphic, compatibly with the maps from `A`; by `IsAffinoidSubdomainMap.algHom_ext`, the
isomorphism is unique. -/
noncomputable def algEquiv : B ≃ₐ[K] B' :=
  AlgEquiv.ofAlgHom (h.lift h'.isAffinoidAlgebra φ' h'.range_maximalSpectrumComap_subset)
    (h'.lift h.isAffinoidAlgebra φ h.range_maximalSpectrumComap_subset)
    (h'.algHom_ext h'.isAffinoidAlgebra <| by
      rw [AlgHom.comp_assoc, lift_comp, lift_comp, AlgHom.id_comp])
    (h.algHom_ext h.isAffinoidAlgebra <| by
      rw [AlgHom.comp_assoc, lift_comp, lift_comp, AlgHom.id_comp])

@[simp]
theorem algEquiv_apply (a : A) : h.algEquiv h' (φ a) = φ' a :=
  h.lift_apply h'.isAffinoidAlgebra φ' h'.range_maximalSpectrumComap_subset a

end Uniqueness

/-- The identity represents the whole classical spectrum of an affinoid algebra. -/
protected theorem id (hA : IsAffinoidAlgebra K A) :
    IsAffinoidSubdomainMap (AlgHom.id K A) Set.univ where
  isAffinoidAlgebra := hA
  range_maximalSpectrumComap_subset := Set.subset_univ _
  existsUnique_algHom _ ψ _ := ⟨ψ, AlgHom.comp_id ψ, fun χ hχ ↦ (AlgHom.comp_id χ).symm.trans hχ⟩

/-- The quotient by the unit ideal, the zero algebra, represents the empty set of classical points
of an affinoid algebra. -/
theorem empty (hA : IsAffinoidAlgebra K A) :
    IsAffinoidSubdomainMap (Ideal.Quotient.mkₐ K (⊤ : Ideal A)) ∅ where
  isAffinoidAlgebra := hA.quotient ⊤
  range_maximalSpectrumComap_subset := by
    rintro _ ⟨y, -⟩
    refine y.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    rw [Subsingleton.elim (1 : A ⧸ (⊤ : Ideal A)) 0]
    exact y.asIdeal.zero_mem
  existsUnique_algHom {C} _ _ hC ψ hψ := by
    -- An affinoid algebra without classical points is the zero algebra.
    have : Subsingleton C := not_nontrivial_iff_subsingleton.mp fun _ ↦ by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal C
      exact hψ ⟨⟨M, hM⟩, rfl⟩
    exact ⟨Ideal.Quotient.liftₐ _ ψ fun _ _ ↦ Subsingleton.elim _ _,
      AlgHom.ext fun _ ↦ Subsingleton.elim _ _,
      fun _ _ ↦ AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩

/-- **Transitivity of affinoid subdomains.** If `φ : A → B` represents `U ⊆ Sp A` and
`φ' : B → C` represents `V ⊆ Sp B`, then `φ' ∘ φ` represents the image of `V` in `Sp A`. -/
theorem comp (hA : IsAffinoidAlgebra K A) {φ' : B →ₐ[K] C} {V : Set (MaximalSpectrum B)}
    (h' : IsAffinoidSubdomainMap φ' V) :
    IsAffinoidSubdomainMap (φ'.comp φ) (h.isAffinoidAlgebra.maximalSpectrumComap φ '' V) where
  isAffinoidAlgebra := h'.isAffinoidAlgebra
  range_maximalSpectrumComap_subset := by
    rw [IsAffinoidAlgebra.maximalSpectrumComap_comp h.isAffinoidAlgebra, Set.range_comp]
    exact Set.image_mono h'.range_maximalSpectrumComap_subset
  existsUnique_algHom {D} _ _ hD ψ hψ := by
    have hψU : Set.range (hD.maximalSpectrumComap ψ) ⊆ U :=
      hψ.trans ((Set.image_subset_range _ _).trans h.range_maximalSpectrumComap_subset)
    -- The factorisation of `ψ` through `B` has its classical points over `V`, by injectivity of
    -- `Sp B → Sp A`.
    have hχ : Set.range (hD.maximalSpectrumComap (h.lift hD ψ hψU)) ⊆ V := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨v, hv, hvz⟩ := hψ ⟨z, rfl⟩
      have hz := congr_fun (IsAffinoidAlgebra.maximalSpectrumComap_comp h.isAffinoidAlgebra hD φ
        (h.lift hD ψ hψU)) z
      rw [h.lift_comp] at hz
      rwa [← h.maximalSpectrumComap_injective hA (hvz.trans hz)]
    refine ⟨h'.lift hD _ hχ, by beta_reduce; rw [← AlgHom.comp_assoc, h'.lift_comp, h.lift_comp],
      fun θ hθ ↦ h'.eq_lift hD _ hχ (h.eq_lift hD ψ hψU ?_)⟩
    rwa [AlgHom.comp_assoc]

/-- If both a map and its composite represent affinoid subdomains, the second map represents
an affinoid subdomain of the first coordinate algebra, with the expected underlying set. -/
theorem of_comp {χ : B →ₐ[K] C} {V : Set (MaximalSpectrum A)}
    (hχ : IsAffinoidSubdomainMap (χ.comp φ) V) :
    IsAffinoidSubdomainMap χ (h.isAffinoidAlgebra.maximalSpectrumComap φ ⁻¹' V) where
  isAffinoidAlgebra := hχ.isAffinoidAlgebra
  range_maximalSpectrumComap_subset := by
    rintro _ ⟨z, rfl⟩
    have hz := hχ.range_maximalSpectrumComap_subset ⟨z, rfl⟩
    rwa [IsAffinoidAlgebra.maximalSpectrumComap_comp h.isAffinoidAlgebra
      hχ.isAffinoidAlgebra] at hz
  existsUnique_algHom {D} _ _ hD ψ hψ := by
    have hψV : Set.range (hD.maximalSpectrumComap (ψ.comp φ)) ⊆ V := by
      rw [IsAffinoidAlgebra.maximalSpectrumComap_comp h.isAffinoidAlgebra hD, Set.range_comp]
      exact Set.image_subset_iff.mpr hψ
    obtain ⟨δ, hδ, huniq⟩ := hχ.existsUnique_algHom hD (ψ.comp φ) hψV
    refine ⟨δ, h.algHom_ext hD ?_, fun δ' hδ' ↦ huniq δ' ?_⟩
    · simpa only [AlgHom.comp_assoc] using hδ
    · simpa only [AlgHom.comp_assoc] using
        congrArg (fun f : B →ₐ[K] D ↦ f.comp φ) hδ'

end IsAffinoidSubdomainMap

end TauCeti
