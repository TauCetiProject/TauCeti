/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Comap
public import TauCeti.Topology.GTopology.SlightlyFiner

/-!
# The strong classical affinoid G-topology

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, with classical spectrum
`Sp A = MaximalSpectrum A`. Following [BGR, §9.1.4], the *strong G-topology* tests admissible opens
and admissible covers against all affinoid morphisms into `Sp A`: a subset `U ⊆ Sp A` is
*strong-admissible open* (`TauCeti.StrongAdmissibleOpen`) if it is covered by affinoid subdomains
whose pullbacks along every `φ : A →ₐ[K] B` landing in `U` admit a finite affinoid refinement, and
a family `S` of strong-admissible opens in `U` is a *strong-admissible cover*
(`TauCeti.StrongAdmissibleOpen.strongGTopology`) under the same test condition.

We prove completeness (G0)–(G2) (`saturated_strongGTopology`), slight fineness over `weakGTopology`
(`slightlyFiner_strongGTopology`) and unique sheaf extension (`sheafEquivWeakStrong`), functoriality
(`AlgHom.strongAffinoidMap`), and the universal property (`exists_continuousMap_of_slightlyFiner`).

## Main definitions

* `TauCeti.IsAffinoidTestRefined`, `TauCeti.StrongAdmissibleOpen`,
  `TauCeti.AffinoidSubdomain.toStrongAdmissibleOpen`.
* `TauCeti.StrongAdmissibleOpen.strongGTopology`, `TauCeti.StrongAdmissibleOpen.strongToWeak`,
  `TauCeti.StrongAdmissibleOpen.sheafEquivWeakStrong`, `AlgHom.strongAffinoidMap`.

## Main results

* `TauCeti.StrongAdmissibleOpen.slightlyFiner_strongGTopology`: slight fineness over the weak site.
* `TauCeti.StrongAdmissibleOpen.saturated_strongGTopology`: completeness axioms (G0)–(G2).
* `TauCeti.StrongAdmissibleOpen.exists_continuousMap_of_slightlyFiner`: universal property.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§9.1.2, 9.1.4,
  and 9.2.3.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

universe u w w'

section TestRefined

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- A family `ℱ` of subsets of `Sp A` is *affinoid-test refined* on `U ⊆ Sp A` if for every
affinoid `K`-algebra `B` in the universe of `A` and every `φ : A →ₐ[K] B` whose classical points
land in `U`, there is a finite cover of `Sp B` by affinoid subdomains each mapping into some
member of `ℱ` [BGR, §9.1.4]. -/
def IsAffinoidTestRefined (U : Set (MaximalSpectrum A))
    (ℱ : Set (Set (MaximalSpectrum A))) : Prop :=
  ∀ ⦃B : Type u⦄ [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B),
    Set.range (hB.maximalSpectrumComap φ) ⊆ U →
      ∃ R : Set (AffinoidSubdomain K B), R.Finite ∧
        ⋃₀ ((fun W : AffinoidSubdomain K B ↦ (W : Set (MaximalSpectrum B))) '' R) = Set.univ ∧
        ∀ W ∈ R, ∃ V ∈ ℱ, (W : Set (MaximalSpectrum B)) ⊆ hB.maximalSpectrumComap φ ⁻¹' V

variable {K}

theorem isAffinoidTestRefined_iff {U : Set (MaximalSpectrum A)}
    {ℱ : Set (Set (MaximalSpectrum A))} :
    IsAffinoidTestRefined K U ℱ ↔
      ∀ ⦃B : Type u⦄ [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B),
        Set.range (hB.maximalSpectrumComap φ) ⊆ U →
          ∃ R : Set (AffinoidSubdomain K B), R.Finite ∧
            ⋃₀ ((fun W : AffinoidSubdomain K B ↦ (W : Set (MaximalSpectrum B))) '' R) =
              Set.univ ∧
            ∀ W ∈ R, ∃ V ∈ ℱ, (W : Set (MaximalSpectrum B)) ⊆ hB.maximalSpectrumComap φ ⁻¹' V :=
  Iff.rfl

namespace IsAffinoidTestRefined

theorem singleton (U : Set (MaximalSpectrum A)) : IsAffinoidTestRefined K U {U} :=
  fun _ _ _ hB _ hφ ↦ ⟨{AffinoidSubdomain.univ hB}, Set.finite_singleton _, by simp,
    fun _ _ ↦ ⟨U, Set.mem_singleton U, fun y _ ↦ hφ ⟨y, rfl⟩⟩⟩

/-- Any affinoid-test refined family on `U` covers `U` set-theoretically. -/
theorem subset_sUnion (hA : IsAffinoidAlgebra K A) {U : Set (MaximalSpectrum A)}
    {ℱ : Set (Set (MaximalSpectrum A))} (h : IsAffinoidTestRefined K U ℱ) : U ⊆ ⋃₀ ℱ := by
  intro x hx
  let φ : A →ₐ[K] A ⧸ x.asIdeal := Ideal.Quotient.mkₐ K x.asIdeal
  have hQ : IsAffinoidAlgebra K (A ⧸ x.asIdeal) := hA.quotient x.asIdeal
  have : Nontrivial (A ⧸ x.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr x.isMaximal.ne_top
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⧸ x.asIdeal)
  let y₀ : MaximalSpectrum (A ⧸ x.asIdeal) := ⟨m, hm⟩
  have hyx (y : MaximalSpectrum (A ⧸ x.asIdeal)) : hQ.maximalSpectrumComap φ y = x := by
    have hle : x.asIdeal ≤ Ideal.comap φ.toRingHom y.asIdeal := by
      simpa only [φ, Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using
        (Ideal.ker_le_comap (Ideal.Quotient.mk x.asIdeal) : _ ≤ Ideal.comap _ y.asIdeal)
    exact MaximalSpectrum.ext (hQ.maximalSpectrumComap_asIdeal φ y ▸
      (x.isMaximal.eq_of_le (hQ.comap_isMaximal φ y.asIdeal).ne_top hle).symm)
  obtain ⟨R, -, hRuniv, hRℱ⟩ := h hQ φ (by rintro _ ⟨y, rfl⟩; exact (hyx y).symm ▸ hx)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW⟩ := hRuniv ▸ Set.mem_univ y₀
  obtain ⟨V, hV, hWV⟩ := hRℱ W hW
  exact ⟨V, hV, hyx y₀ ▸ hWV hyW⟩

theorem of_refinement {U : Set (MaximalSpectrum A)} {ℱ 𝒢 : Set (Set (MaximalSpectrum A))}
    (h : IsAffinoidTestRefined K U ℱ) (hℱ𝒢 : ∀ V ∈ ℱ, ∃ V' ∈ 𝒢, V ⊆ V') :
    IsAffinoidTestRefined K U 𝒢 := by
  intro B _ _ hB φ hφ
  obtain ⟨R, hfin, hRuniv, hRℱ⟩ := h hB φ hφ
  refine ⟨R, hfin, hRuniv, fun W hW ↦ ?_⟩
  obtain ⟨V, hV, hWV⟩ := hRℱ W hW
  obtain ⟨V', hV', hVV'⟩ := hℱ𝒢 V hV
  exact ⟨V', hV', hWV.trans (Set.preimage_mono hVV')⟩

theorem anti {U V : Set (MaximalSpectrum A)} {ℱ : Set (Set (MaximalSpectrum A))}
    (hVU : V ⊆ U) (h : IsAffinoidTestRefined K U ℱ) : IsAffinoidTestRefined K V ℱ :=
  fun _ _ _ hB φ hφ ↦ h hB φ (hφ.trans hVU)

theorem inter {U : Set (MaximalSpectrum A)} {ℱ : Set (Set (MaximalSpectrum A))}
    (h : IsAffinoidTestRefined K U ℱ) (V : Set (MaximalSpectrum A)) :
    IsAffinoidTestRefined K (U ∩ V) ((fun W ↦ W ∩ V) '' ℱ) := by
  intro B _ _ hB φ hφ
  obtain ⟨R, hfin, hRuniv, hRℱ⟩ := h hB φ (hφ.trans Set.inter_subset_left)
  refine ⟨R, hfin, hRuniv, fun W hW ↦ ?_⟩
  obtain ⟨Z, hZ, hWZ⟩ := hRℱ W hW
  exact ⟨Z ∩ V, ⟨Z, hZ, rfl⟩, fun y hy ↦ ⟨hWZ hy, (hφ ⟨y, rfl⟩).2⟩⟩

/-- Transitivity of affinoid-test refinement along a refinement of each member. -/
theorem biUnion {U : Set (MaximalSpectrum A)} {ℱ : Set (Set (MaximalSpectrum A))}
    {𝒯 : Set (MaximalSpectrum A) → Set (Set (MaximalSpectrum A))}
    (h : IsAffinoidTestRefined K U ℱ)
    (h𝒯 : ∀ V ∈ ℱ, IsAffinoidTestRefined K (U ∩ V) (𝒯 V)) :
    IsAffinoidTestRefined K U (⋃ V ∈ ℱ, 𝒯 V) := by
  classical
  intro B _ _ hB φ hφ
  obtain ⟨R, hRfin, hRuniv, hRℱ⟩ := h hB φ hφ
  choose! V hVℱ hWV using hRℱ
  have hW_test (W : AffinoidSubdomain K B) (hW : W ∈ R) :=
    h𝒯 (V W) (hVℱ W hW) W.isAffinoidAlgebra (W.toSections.comp φ) <| by
      rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hB W.isAffinoidAlgebra, Set.range_comp]
      exact Set.subset_inter ((Set.image_subset_range _ _).trans hφ)
        ((Set.image_mono W.isAffinoidSubdomainMap.range_maximalSpectrumComap_subset).trans
          (Set.image_subset_iff.mpr (hWV W hW)))
  choose! Q hQfin hQuniv hQ𝒯 using hW_test
  refine ⟨⋃ W ∈ R, W.mapSubdomain hB '' Q W,
    hRfin.biUnion fun W hW ↦ (hQfin W hW).image _, ?_, ?_⟩
  · simp only [Set.image_iUnion, Set.sUnion_iUnion]
    rw [Set.iUnion₂_congr fun W hW ↦ W.sUnion_image_mapSubdomain hB (hQuniv W hW)]
    simpa only [Set.sUnion_image] using hRuniv
  · rintro P hp
    obtain ⟨W, hW, Z, hZ, rfl⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨T, hT, hZT⟩ := hQ𝒯 W hW Z hZ
    refine ⟨T, Set.mem_biUnion (hVℱ W hW) hT, ?_⟩
    rwa [AffinoidSubdomain.coe_mapSubdomain, Set.image_subset_iff, ← Set.preimage_comp,
      ← IsAffinoidAlgebra.maximalSpectrumComap_comp hB W.isAffinoidAlgebra]

theorem preimage {B : Type u} [CommRing B] [Algebra K B] (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) {U : Set (MaximalSpectrum A)} {ℱ : Set (Set (MaximalSpectrum A))}
    (h : IsAffinoidTestRefined K U ℱ) :
    IsAffinoidTestRefined K (hB.maximalSpectrumComap φ ⁻¹' U)
      ((fun V ↦ hB.maximalSpectrumComap φ ⁻¹' V) '' ℱ) := by
  intro C _ _ hC ψ hψ
  obtain ⟨R, hfin, hRuniv, hRℱ⟩ := h hC (ψ.comp φ) <| by
    rw [IsAffinoidAlgebra.maximalSpectrumComap_comp hB hC, Set.range_comp]
    exact Set.image_subset_iff.mpr hψ
  refine ⟨R, hfin, hRuniv, fun W hW ↦ ?_⟩
  obtain ⟨V, hV, hWV⟩ := hRℱ W hW
  refine ⟨_, ⟨V, hV, rfl⟩, ?_⟩
  rwa [← Set.preimage_comp, ← IsAffinoidAlgebra.maximalSpectrumComap_comp hB hC]

/-- Intersecting two affinoid-test refined families gives an affinoid-test refined family on the
intersection. -/
theorem image2_inter {U₁ U₂ : Set (MaximalSpectrum A)}
    {ℱ₁ ℱ₂ : Set (Set (MaximalSpectrum A))}
    (h₁ : IsAffinoidTestRefined K U₁ ℱ₁) (h₂ : IsAffinoidTestRefined K U₂ ℱ₂) :
    IsAffinoidTestRefined K (U₁ ∩ U₂) (Set.image2 (· ∩ ·) ℱ₁ ℱ₂) := by
  have hbi : IsAffinoidTestRefined K (U₁ ∩ U₂) (⋃ V ∈ ℱ₁, (fun W ↦ W ∩ V) '' ℱ₂) :=
    (h₁.anti Set.inter_subset_left).biUnion fun V _ ↦
      (h₂.inter V).anti (Set.inter_subset_inter Set.inter_subset_right Set.Subset.rfl)
  have himg : (⋃ V ∈ ℱ₁, (fun W ↦ W ∩ V) '' ℱ₂) = Set.image2 (· ∩ ·) ℱ₁ ℱ₂ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_image2, exists_prop]
    exact ⟨fun ⟨V, hV, W, hW, h⟩ ↦ ⟨V, hV, W, hW, (Set.inter_comm V W).trans h⟩,
      fun ⟨V, hV, W, hW, h⟩ ↦ ⟨V, hV, W, hW, (Set.inter_comm W V).trans h⟩⟩
  exact himg ▸ hbi

end IsAffinoidTestRefined

end TestRefined

/-- A subset of `Sp A = MaximalSpectrum A` is *strong-admissible open* [BGR, §9.1.4, Definition 1]
if it is covered by a family of affinoid subdomains that is refined by a finite affinoid cover
after every affinoid test map into it. -/
structure StrongAdmissibleOpen (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type u) [CommRing A] [Algebra K A] where
  /-- The underlying set of classical points. -/
  carrier : Set (MaximalSpectrum A)
  /-- Existence of an affinoid-test refined covering by affinoid subdomains. -/
  exists_affinoid_cover : ∃ S : Set (AffinoidSubdomain K A),
    ⋃₀ ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' S) = carrier ∧
      IsAffinoidTestRefined K carrier
        ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' S)

section BasicOpen

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

namespace StrongAdmissibleOpen

instance : SetLike (StrongAdmissibleOpen K A) (MaximalSpectrum A) where
  coe := carrier
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ rfl; rfl

@[ext]
theorem ext {U V : StrongAdmissibleOpen K A} (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h

instance : PartialOrder (StrongAdmissibleOpen K A) := .ofSetLike _

@[simp]
theorem carrier_eq_coe (U : StrongAdmissibleOpen K A) :
    U.carrier = (U : Set (MaximalSpectrum A)) := (rfl)

@[simp]
theorem coe_mk (U : Set (MaximalSpectrum A)) (hU) :
    (⟨U, hU⟩ : StrongAdmissibleOpen K A) = U := (rfl)

@[simp]
theorem mem_mk (U : Set (MaximalSpectrum A)) (hU) (x : MaximalSpectrum A) :
    x ∈ (⟨U, hU⟩ : StrongAdmissibleOpen K A) ↔ x ∈ U := Iff.rfl

/-- Every strong-admissible open admits an affinoid-test refined cover by affinoid subdomains,
stated in terms of its coerced set of classical points. -/
theorem exists_affinoidSubdomain_cover (U : StrongAdmissibleOpen K A) :
    ∃ S : Set (AffinoidSubdomain K A),
      ⋃₀ ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' S) =
        (U : Set (MaximalSpectrum A)) ∧
      IsAffinoidTestRefined K (U : Set (MaximalSpectrum A))
        ((fun V : AffinoidSubdomain K A ↦ (V : Set (MaximalSpectrum A))) '' S) := by
  rw [← carrier_eq_coe]
  exact U.exists_affinoid_cover

/-- The order embedding of strong-admissible opens into subsets of `MaximalSpectrum A`. -/
def setEmbedding : StrongAdmissibleOpen K A ↪o Set (MaximalSpectrum A) :=
  ⟨⟨(↑), SetLike.coe_injective⟩, Iff.rfl⟩

@[simp]
theorem setEmbedding_apply (U : StrongAdmissibleOpen K A) :
    setEmbedding U = (U : Set (MaximalSpectrum A)) := (rfl)

/-- A subset of `Sp A` covered by strong-admissible opens whose union is `V` and which are
affinoid-test refined on `V` is itself strong-admissible open. -/
theorem mem_range_of_testRefined {V : Set (MaximalSpectrum A)}
    {S : Set (StrongAdmissibleOpen K A)}
    (hSu : ⋃₀ ((fun W : StrongAdmissibleOpen K A ↦ (W : Set (MaximalSpectrum A))) '' S) = V)
    (hS : IsAffinoidTestRefined K V
      ((fun W : StrongAdmissibleOpen K A ↦ (W : Set (MaximalSpectrum A))) '' S)) :
    V ∈ Set.range (setEmbedding (K := K) (A := A)) := by
  classical
  choose T hTu hT using fun W : StrongAdmissibleOpen K A ↦ W.exists_affinoidSubdomain_cover
  let 𝒯 (s : Set (MaximalSpectrum A)) : Set (Set (MaximalSpectrum A)) :=
    if hs : ∃ W ∈ S, (W : Set (MaximalSpectrum A)) = s then (↑) '' T hs.choose else ∅
  have h𝒯 : ∀ s ∈ ((↑) : StrongAdmissibleOpen K A → Set (MaximalSpectrum A)) '' S,
      IsAffinoidTestRefined K (V ∩ s) (𝒯 s) := by
    rintro _ ⟨W, hW, rfl⟩
    have hex : ∃ W' ∈ S, (W' : Set (MaximalSpectrum A)) = W := ⟨W, hW, rfl⟩
    have hWV : (W : Set (MaximalSpectrum A)) ⊆ V := hSu ▸ Set.subset_sUnion_of_mem ⟨W, hW, rfl⟩
    simp only [𝒯, hex, ↓reduceDIte, SetLike.coe_injective hex.choose_spec.2,
      Set.inter_eq_right.mpr hWV]
    exact hT W
  refine ⟨⟨V, ⋃ W ∈ S, T W, ?_, (hS.biUnion h𝒯).of_refinement fun s hs ↦ ?_⟩, by simp⟩
  · simp only [Set.image_iUnion, Set.sUnion_iUnion]
    exact (Set.iUnion₂_congr fun W _ ↦ hTu W).trans ((Set.sUnion_image _ _).symm.trans hSu)
  · obtain ⟨_, ⟨W, hW, rfl⟩, hs'⟩ := Set.mem_iUnion₂.mp hs
    have hex : ∃ W' ∈ S, (W' : Set (MaximalSpectrum A)) = W := ⟨W, hW, rfl⟩
    simp only [𝒯, hex, ↓reduceDIte, SetLike.coe_injective hex.choose_spec.2] at hs'
    obtain ⟨P, hPT, rfl⟩ := hs'
    exact ⟨P, ⟨P, Set.mem_biUnion hW hPT, rfl⟩, Set.Subset.rfl⟩

private theorem strongCovers_trans {U : StrongAdmissibleOpen K A}
    {S : Set (StrongAdmissibleOpen K A)}
    {T : StrongAdmissibleOpen K A → Set (StrongAdmissibleOpen K A)}
    (hS : (∀ V ∈ S, V ≤ U) ∧ IsAffinoidTestRefined K (U : Set (MaximalSpectrum A)) ((↑) '' S))
    (hT : ∀ V ∈ S, (∀ W ∈ T V, W ≤ V) ∧
      IsAffinoidTestRefined K (V : Set (MaximalSpectrum A)) ((↑) '' T V)) :
    (∀ W ∈ ⋃ V ∈ S, T V, W ≤ U) ∧
      IsAffinoidTestRefined K (U : Set (MaximalSpectrum A)) ((↑) '' ⋃ V ∈ S, T V) := by
  classical
  refine ⟨fun W hW ↦ let ⟨V, hV, hWV⟩ := Set.mem_iUnion₂.mp hW
    ((hT V hV).1 W hWV).trans (hS.1 V hV), ?_⟩
  let 𝒯 (s : Set (MaximalSpectrum A)) : Set (Set (MaximalSpectrum A)) :=
    if hs : ∃ V ∈ S, (V : Set (MaximalSpectrum A)) = s then (↑) '' T hs.choose else ∅
  have h𝒯 : ∀ s ∈ ((↑) : StrongAdmissibleOpen K A → Set (MaximalSpectrum A)) '' S,
      IsAffinoidTestRefined K ((U : Set (MaximalSpectrum A)) ∩ s) (𝒯 s) := by
    rintro _ ⟨V, hV, rfl⟩
    have hex : ∃ V' ∈ S, (V' : Set (MaximalSpectrum A)) = V := ⟨V, hV, rfl⟩
    simpa only [𝒯, hex, ↓reduceDIte, SetLike.coe_injective hex.choose_spec.2,
      Set.inter_eq_right.mpr (hS.1 V hV)] using (hT V hV).2
  refine (hS.2.biUnion h𝒯).of_refinement fun s hs ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hs𝒯⟩ := Set.mem_iUnion₂.mp hs
  have hex : ∃ V' ∈ S, (V' : Set (MaximalSpectrum A)) = V := ⟨V, hV, rfl⟩
  simp only [𝒯, hex, ↓reduceDIte, SetLike.coe_injective hex.choose_spec.2] at hs𝒯
  obtain ⟨W, hWT, rfl⟩ := hs𝒯
  exact ⟨W, ⟨W, Set.mem_biUnion hV hWT, rfl⟩, Set.Subset.rfl⟩

end StrongAdmissibleOpen

namespace AffinoidSubdomain

/-- Every affinoid subdomain is admissible open in the strong G-topology. -/
def toStrongAdmissibleOpen (U : AffinoidSubdomain K A) : StrongAdmissibleOpen K A where
  carrier := U
  exists_affinoid_cover := ⟨{U}, by simp, by
    simpa only [Set.image_singleton] using
      IsAffinoidTestRefined.singleton (U : Set (MaximalSpectrum A))⟩

@[simp]
theorem coe_toStrongAdmissibleOpen (U : AffinoidSubdomain K A) :
    (U.toStrongAdmissibleOpen : Set (MaximalSpectrum A)) = U := (rfl)

@[simp]
theorem mem_toStrongAdmissibleOpen (U : AffinoidSubdomain K A) (x : MaximalSpectrum A) :
    x ∈ U.toStrongAdmissibleOpen ↔ x ∈ U := Iff.rfl

theorem toStrongAdmissibleOpen_injective :
    Function.Injective (@toStrongAdmissibleOpen K _ _ _ A _ _) := fun _ _ h ↦
  SetLike.coe_injective <| by
    simpa only [coe_toStrongAdmissibleOpen] using
      congrArg ((↑) : StrongAdmissibleOpen K A → Set (MaximalSpectrum A)) h

@[simp]
theorem toStrongAdmissibleOpen_le_iff {U V : AffinoidSubdomain K A} :
    U.toStrongAdmissibleOpen ≤ V.toStrongAdmissibleOpen ↔ U ≤ V := Iff.rfl

end AffinoidSubdomain

namespace StrongAdmissibleOpen

/-- The whole classical spectrum as a strong-admissible open. -/
def univ (hA : IsAffinoidAlgebra K A) : StrongAdmissibleOpen K A :=
  (AffinoidSubdomain.univ hA).toStrongAdmissibleOpen

@[simp]
theorem coe_univ (hA : IsAffinoidAlgebra K A) :
    (univ hA : Set (MaximalSpectrum A)) = Set.univ :=
  AffinoidSubdomain.coe_univ hA

/-- The empty set as a strong-admissible open. -/
def empty (hA : IsAffinoidAlgebra K A) : StrongAdmissibleOpen K A :=
  (AffinoidSubdomain.empty hA).toStrongAdmissibleOpen

@[simp]
theorem coe_empty (hA : IsAffinoidAlgebra K A) :
    (empty hA : Set (MaximalSpectrum A)) = ∅ :=
  AffinoidSubdomain.coe_empty hA

section BoundedOrder

variable [hA : Fact (IsAffinoidAlgebra K A)]

instance : BoundedOrder (StrongAdmissibleOpen K A) where
  top := univ hA.out
  le_top U := by rw [← SetLike.coe_subset_coe, coe_univ]; exact Set.subset_univ _
  bot := empty hA.out
  bot_le U := by rw [← SetLike.coe_subset_coe, coe_empty]; exact Set.empty_subset _

@[simp]
theorem coe_top : (↑(⊤ : StrongAdmissibleOpen K A) : Set (MaximalSpectrum A)) = Set.univ :=
  coe_univ hA.out

@[simp]
theorem coe_bot : (↑(⊥ : StrongAdmissibleOpen K A) : Set (MaximalSpectrum A)) = ∅ :=
  coe_empty hA.out

@[simp]
theorem toStrongAdmissibleOpen_top :
    (⊤ : AffinoidSubdomain K A).toStrongAdmissibleOpen = ⊤ :=
  SetLike.coe_injective (by simp)

@[simp]
theorem toStrongAdmissibleOpen_bot :
    (⊥ : AffinoidSubdomain K A).toStrongAdmissibleOpen = ⊥ :=
  SetLike.coe_injective (by simp)

end BoundedOrder

end StrongAdmissibleOpen

end BasicOpen

section StrongSite

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]

namespace StrongAdmissibleOpen

section Site

variable [hA : Fact (IsAffinoidAlgebra K A)]

/-- Strong-admissible opens are closed under finite intersections. -/
noncomputable instance : SemilatticeInf (StrongAdmissibleOpen K A) where
  inf U₁ U₂ := ⟨(U₁ : Set (MaximalSpectrum A)) ∩ U₂, by
    obtain ⟨S₁, hS₁u, hS₁⟩ := U₁.exists_affinoidSubdomain_cover
    obtain ⟨S₂, hS₂u, hS₂⟩ := U₂.exists_affinoidSubdomain_cover
    have himg : ((↑) : AffinoidSubdomain K A → Set (MaximalSpectrum A)) ''
        Set.image2 (· ⊓ ·) S₁ S₂ = Set.image2 (· ∩ ·) ((↑) '' S₁) ((↑) '' S₂) := Set.ext fun _ ↦
      ⟨by rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
          exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, (AffinoidSubdomain.coe_inf a b).symm⟩,
       by rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
          exact ⟨a ⊓ b, Set.mem_image2_of_mem ha hb, AffinoidSubdomain.coe_inf a b⟩⟩
    refine ⟨Set.image2 (· ⊓ ·) S₁ S₂, ?_, himg ▸ hS₁.image2_inter hS₂⟩
    rw [himg, ← hS₁u, ← hS₂u]
    ext x; simp only [Set.mem_sUnion, Set.mem_image2, Set.mem_inter_iff]
    exact ⟨fun ⟨_, ⟨a, ha, b, hb, rfl⟩, hxa, hxb⟩ ↦ ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩,
      fun ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ ↦ ⟨a ∩ b, ⟨a, ha, b, hb, rfl⟩, hxa, hxb⟩⟩⟩
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ h₁ h₂ := Set.subset_inter h₁ h₂

@[simp]
theorem coe_inf (U V : StrongAdmissibleOpen K A) :
    (↑(U ⊓ V) : Set (MaximalSpectrum A)) = (U : Set _) ∩ V := (rfl)

@[simp]
theorem mem_inf (U V : StrongAdmissibleOpen K A) (x : MaximalSpectrum A) :
    x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V := Iff.rfl

@[simp]
theorem toStrongAdmissibleOpen_inf (U V : AffinoidSubdomain K A) :
    (U ⊓ V).toStrongAdmissibleOpen = U.toStrongAdmissibleOpen ⊓ V.toStrongAdmissibleOpen :=
  SetLike.coe_injective (AffinoidSubdomain.coe_inf U V)

/-- **The strong classical affinoid G-topology** [BGR, §9.1.4, Definition 1]. A family `S` of
strong-admissible opens contained in `U` covers `U` admissibly when its pullback along every
affinoid test map into `U` admits a finite affinoid refinement. -/
noncomputable def strongGTopology : GTopology (setEmbedding (K := K) (A := A)) where
  map_top := coe_top
  map_inf := coe_inf
  Covers U S := (∀ V ∈ S, V ≤ U) ∧
    IsAffinoidTestRefined K (U : Set (MaximalSpectrum A))
      ((fun V : StrongAdmissibleOpen K A ↦ (V : Set (MaximalSpectrum A))) '' S)
  subset h := h.1
  union_eq {U S} h := Set.Subset.antisymm
    (by rintro x ⟨_, ⟨V, hV, rfl⟩, hx⟩; exact h.1 V hV hx)
    (by simpa only [setEmbedding_apply] using h.2.subset_sUnion hA.out)
  identity U := ⟨by simp, by
    simpa only [Set.image_singleton] using
      IsAffinoidTestRefined.singleton (U : Set (MaximalSpectrum A))⟩
  restriction {U S} h V hVU := ⟨by rintro _ ⟨_, -, rfl⟩; exact inf_le_right, by
    simpa only [Set.image_image, coe_inf, Set.inter_eq_right.mpr hVU] using
      h.2.inter (V : Set (MaximalSpectrum A))⟩
  transitive hS hT := strongCovers_trans hS hT

@[simp]
theorem strongGTopology_covers_iff {U : StrongAdmissibleOpen K A}
    {S : Set (StrongAdmissibleOpen K A)} :
    strongGTopology.Covers U S ↔ (∀ V ∈ S, V ≤ U) ∧
      IsAffinoidTestRefined K (U : Set (MaximalSpectrum A))
        ((fun V : StrongAdmissibleOpen K A ↦ (V : Set (MaximalSpectrum A))) '' S) :=
  Iff.rfl

/-- An empty family is a strong-admissible cover only of the empty open. -/
theorem strongGTopology_covers_empty_iff {U : StrongAdmissibleOpen K A} :
    strongGTopology.Covers U ∅ ↔ U = ⊥ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hu := strongGTopology.union_eq h
    simp only [Set.image_empty, Set.sUnion_empty, setEmbedding_apply] at hu
    exact SetLike.coe_injective (hu.symm.trans coe_bot.symm)
  · rintro rfl
    refine ⟨by simp, fun B _ _ hB φ hφ ↦ ⟨∅, Set.finite_empty, ?_, by simp⟩⟩
    rw [Set.image_empty, Set.sUnion_empty, Set.eq_univ_iff_forall]
    intro y
    exact Set.notMem_empty _ (coe_bot (K := K) (A := A) ▸ SetLike.mem_coe.mpr (hφ ⟨y, rfl⟩))

/-- The identity of `MaximalSpectrum A`, as a continuous map from the strong G-topology to the
weak G-topology. -/
noncomputable def strongToWeak :
    (strongGTopology (K := K) (A := A)).ContinuousMap
      (AffinoidSubdomain.weakGTopology (K := K) (A := A)) where
  toFun := id
  comap := AffinoidSubdomain.toStrongAdmissibleOpen
  coe_comap' _ := by simp
  covers_comap {U S} hS := by
    obtain ⟨hSU, R₀, hR₀S, hfin, hR₀⟩ := AffinoidSubdomain.weakGTopology_covers_iff.mp hS
    refine ⟨by rintro _ ⟨V, hV, rfl⟩; exact hSU V hV, fun B _ _ hB φ hφ ↦ ?_⟩
    have : Fact (IsAffinoidAlgebra K B) := ⟨hB⟩
    refine ⟨(fun V : AffinoidSubdomain K A ↦ V.comap φ) '' R₀, hfin.image _, ?_, ?_⟩
    · simp only [Set.image_image, AffinoidSubdomain.coe_comap, Set.sUnion_image,
        ← Set.preimage_iUnion₂]
      rw [← Set.sUnion_image, hR₀]
      exact Set.eq_univ_iff_forall.mpr fun y ↦ hφ ⟨y, rfl⟩
    · rintro _ ⟨V, hVR₀, rfl⟩
      exact ⟨V, ⟨V.toStrongAdmissibleOpen, ⟨V, hR₀S hVR₀, rfl⟩, rfl⟩,
        (AffinoidSubdomain.coe_comap V φ).le⟩

@[simp]
theorem coe_strongToWeak : ⇑(strongToWeak (K := K) (A := A)) = id := (rfl)

@[simp]
theorem strongToWeak_comap :
    (strongToWeak (K := K) (A := A)).comap = AffinoidSubdomain.toStrongAdmissibleOpen := (rfl)

/-- Every strong-admissible open is strongly covered by the affinoid subdomains witnessing its
admissibility. -/
theorem exists_covers_toStrongAdmissibleOpen (V : StrongAdmissibleOpen K A) :
    ∃ S : Set (AffinoidSubdomain K A),
      strongGTopology.Covers V (AffinoidSubdomain.toStrongAdmissibleOpen '' S) ∧
        ⋃₀ ((fun U : AffinoidSubdomain K A ↦ (U : Set (MaximalSpectrum A))) '' S) = V := by
  obtain ⟨S, hSu, hS⟩ := V.exists_affinoidSubdomain_cover
  refine ⟨S, ⟨?_, ?_⟩, hSu⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact SetLike.coe_subset_coe.mp (hSu ▸ Set.subset_sUnion_of_mem ⟨U, hU, rfl⟩)
  · simpa only [Set.image_image, AffinoidSubdomain.coe_toStrongAdmissibleOpen] using hS

/-- **Enhancement of the weak affinoid G-topology** [BGR, §9.1.4, Proposition 2]: the strong
affinoid G-topology is slightly finer than the weak affinoid G-topology. -/
theorem slightlyFiner_strongGTopology :
    (strongGTopology (K := K) (A := A)).SlightlyFiner
      (AffinoidSubdomain.weakGTopology (K := K) (A := A)) where
  exists_continuousMap := ⟨strongToWeak, fun _ ↦ rfl⟩
  exists_covers V := by
    obtain ⟨S, hS, -⟩ := exists_covers_toStrongAdmissibleOpen V
    exact ⟨AffinoidSubdomain.toStrongAdmissibleOpen '' S, hS,
      by rintro _ ⟨U, -, rfl⟩; exact ⟨U, AffinoidSubdomain.setEmbedding_apply U⟩⟩
  exists_refinement {U V S} hVU hS := by
    simp only [setEmbedding_apply, AffinoidSubdomain.setEmbedding_apply] at hVU
    obtain ⟨Q, hQfin, hQuniv, hQS⟩ := hS.2 U.isAffinoidAlgebra U.toSections
      (hVU.symm ▸ U.isAffinoidSubdomainMap.range_maximalSpectrumComap_subset)
    refine ⟨U.mapSubdomain hA.out '' Q,
      (AffinoidSubdomain.weakGTopology_covers_iff_of_finite (hQfin.image _)).mpr
        (U.sUnion_image_mapSubdomain hA.out hQuniv), ?_⟩
    rintro _ ⟨W, hW, rfl⟩
    obtain ⟨_, ⟨V', hV', rfl⟩, hWV'⟩ := hQS W hW
    rw [AffinoidSubdomain.setEmbedding_apply, AffinoidSubdomain.coe_mapSubdomain]
    exact ⟨V', hV', Set.image_subset_iff.mpr hWV'⟩

/-- The weak affinoid site is a dense subsite of the strong affinoid site along `strongToWeak`. -/
theorem isDenseSubsite_strongToWeak :
    (strongToWeak (K := K) (A := A)).comapFunctor.IsDenseSubsite
      AffinoidSubdomain.weakGTopology.grothendieckTopology
      strongGTopology.grothendieckTopology :=
  slightlyFiner_strongGTopology.isDenseSubsite fun _ ↦ rfl

section SheafEquiv

variable (𝒟 : Type w) [Category.{w'} 𝒟]
  [∀ V, Limits.HasLimitsOfShape
    (StructuredArrow V (strongToWeak (K := K) (A := A)).comapFunctor.op) 𝒟]

/-- **Unique extension of sheaves from the weak to the strong affinoid site**
[BGR, §9.2.3, Theorem 1]. -/
noncomputable def sheafEquivWeakStrong :
    Sheaf (AffinoidSubdomain.weakGTopology (K := K) (A := A)).grothendieckTopology 𝒟 ≌
      Sheaf (strongGTopology (K := K) (A := A)).grothendieckTopology 𝒟 :=
  slightlyFiner_strongGTopology.sheafEquiv (f := strongToWeak) (fun _ ↦ rfl) 𝒟

@[simp]
theorem sheafEquivWeakStrong_inverse :
    (sheafEquivWeakStrong (K := K) (A := A) 𝒟).inverse =
      (strongToWeak (K := K) (A := A)).comapFunctor.sheafPushforwardContinuous 𝒟
        AffinoidSubdomain.weakGTopology.grothendieckTopology
        strongGTopology.grothendieckTopology :=
  GTopology.SlightlyFiner.sheafEquiv_inverse _ _ 𝒟

end SheafEquiv

/-- **(G0)–(G2) completeness of the strong affinoid G-topology** [BGR, §9.1.4, Proposition 2]. -/
theorem saturated_strongGTopology :
    (strongGTopology (K := K) (A := A)).Saturated where
  empty_mem_range := ⟨⊥, coe_bot⟩
  mem_range_of_covers {U S} hS V hVU hloc := by
    classical
    simp only [setEmbedding_apply] at hVU hloc
    let Z (W : StrongAdmissibleOpen K A) : StrongAdmissibleOpen K A :=
      if hW : W ∈ S then (hloc W hW).choose else ⊥
    have himg : ((↑) : StrongAdmissibleOpen K A → Set (MaximalSpectrum A)) '' (Z '' S) =
        (fun s ↦ s ∩ V) '' ((↑) '' S) := by
      simp only [Set.image_image]
      refine Set.image_congr fun W hW ↦ ?_
      rw [Set.inter_comm]
      simpa only [Z, hW, ↓reduceDIte, setEmbedding_apply] using (hloc W hW).choose_spec
    refine mem_range_of_testRefined (S := Z '' S) ?_
      (by simpa only [himg, Set.inter_eq_right.mpr hVU] using hS.2.inter V)
    have hu := strongGTopology.union_eq hS
    simp only [setEmbedding_apply] at hu
    rw [himg, Set.image_image, Set.sUnion_image, ← Set.iUnion₂_inter, ← Set.sUnion_image, hu,
      Set.inter_eq_right.mpr hVU]
  covers_of_refinement {U S R} hS hR hRS := ⟨fun W hW ↦ by
      rw [← setEmbedding.le_iff_le, ← hS]; exact Set.subset_sUnion_of_mem ⟨W, hW, rfl⟩,
    hR.2.of_refinement <| by
      rintro _ ⟨W, hW, rfl⟩; obtain ⟨W', hW', hWW'⟩ := hRS W hW; exact ⟨W', ⟨W', hW', rfl⟩, hWW'⟩⟩

end Site

section Comap

variable [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]

/-- The inverse image of a strong-admissible open along an affinoid algebra homomorphism
[BGR, §9.1.4, Proposition 3]. -/
noncomputable def comap (U : StrongAdmissibleOpen K A) (φ : A →ₐ[K] B) :
    StrongAdmissibleOpen K B where
  carrier := hB.out.maximalSpectrumComap φ ⁻¹' U
  exists_affinoid_cover := by
    obtain ⟨S, hSu, hS⟩ := U.exists_affinoidSubdomain_cover
    have himg : ((↑) : AffinoidSubdomain K B → Set (MaximalSpectrum B)) ''
        ((fun V : AffinoidSubdomain K A ↦ V.comap φ) '' S) =
        (fun s ↦ hB.out.maximalSpectrumComap φ ⁻¹' s) '' ((↑) '' S) := by
      simp only [Set.image_image, AffinoidSubdomain.coe_comap]
    refine ⟨(fun V : AffinoidSubdomain K A ↦ V.comap φ) '' S, ?_, himg ▸ hS.preimage hB.out φ⟩
    rw [himg, ← hSu]; ext x; simp

@[simp]
theorem coe_comap (U : StrongAdmissibleOpen K A) (φ : A →ₐ[K] B) :
    (U.comap φ : Set (MaximalSpectrum B)) =
      hB.out.maximalSpectrumComap φ ⁻¹' (U : Set (MaximalSpectrum A)) := (rfl)

@[simp]
theorem mem_comap (U : StrongAdmissibleOpen K A) (φ : A →ₐ[K] B) (x : MaximalSpectrum B) :
    x ∈ U.comap φ ↔ hB.out.maximalSpectrumComap φ x ∈ U := Iff.rfl

theorem comap_mono {U V : StrongAdmissibleOpen K A} (h : U ≤ V) (φ : A →ₐ[K] B) :
    U.comap φ ≤ V.comap φ := Set.preimage_mono h

@[simp]
theorem comap_id (U : StrongAdmissibleOpen K A) : U.comap (AlgHom.id K A) = U :=
  ext fun x ↦ by simp

@[simp]
theorem comap_comp [hC : Fact (IsAffinoidAlgebra K C)] (U : StrongAdmissibleOpen K A)
    (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    U.comap (ψ.comp φ) = (U.comap φ).comap ψ :=
  ext fun x ↦ by simp [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]

@[simp]
theorem comap_top {φ : A →ₐ[K] B} : (⊤ : StrongAdmissibleOpen K A).comap φ = ⊤ :=
  SetLike.coe_injective (by simp)

@[simp]
theorem comap_bot {φ : A →ₐ[K] B} : (⊥ : StrongAdmissibleOpen K A).comap φ = ⊥ :=
  SetLike.coe_injective (by simp)

@[simp]
theorem comap_inf (U V : StrongAdmissibleOpen K A) (φ : A →ₐ[K] B) :
    (U ⊓ V).comap φ = U.comap φ ⊓ V.comap φ :=
  ext fun _ ↦ Iff.rfl

@[simp]
theorem comap_toStrongAdmissibleOpen (U : AffinoidSubdomain K A) (φ : A →ₐ[K] B) :
    U.toStrongAdmissibleOpen.comap φ = (U.comap φ).toStrongAdmissibleOpen :=
  SetLike.coe_injective (AffinoidSubdomain.coe_comap U φ).symm

/-- Inverse image along an affinoid algebra homomorphism preserves strong-admissible covers
[BGR, §9.1.4, Proposition 3]. -/
theorem covers_comap {U : StrongAdmissibleOpen K A} {S : Set (StrongAdmissibleOpen K A)}
    (h : strongGTopology.Covers U S) (φ : A →ₐ[K] B) :
    strongGTopology.Covers (U.comap φ) ((fun V ↦ V.comap φ) '' S) :=
  ⟨by rintro _ ⟨V, hV, rfl⟩; exact comap_mono (h.1 V hV) φ,
    by simpa only [Set.image_image, coe_comap] using h.2.preimage hB.out φ⟩

end Comap

section UniversalProperty

private theorem isAffinoidTestRefined_of_slightlyFiner
    {Ω : ∀ (D : Type u) [CommRing D] [Algebra K D], IsAffinoidAlgebra K D → Type*}
    [∀ D [CommRing D] [Algebra K D] hD, SemilatticeInf (Ω D hD)]
    [∀ D [CommRing D] [Algebra K D] hD, OrderTop (Ω D hD)]
    {ι : ∀ D [CommRing D] [Algebra K D] hD, Ω D hD ↪o Set (MaximalSpectrum D)}
    (G : ∀ D [CommRing D] [Algebra K D] hD, GTopology (ι D hD))
    (hfiner : ∀ {D : Type u} [CommRing D] [Algebra K D] [hD : Fact (IsAffinoidAlgebra K D)],
      (G D hD.out).SlightlyFiner (AffinoidSubdomain.weakGTopology (K := K) (A := D)))
    (hmap : ∀ {D E : Type u} [CommRing D] [Algebra K D] [CommRing E] [Algebra K E]
      (hD : IsAffinoidAlgebra K D) (hE : IsAffinoidAlgebra K E) (φ : D →ₐ[K] E),
      ∃ f : (G E hE).ContinuousMap (G D hD), ∀ y, f y = hE.maximalSpectrumComap φ y)
    {E : Type u} [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    {V : Ω E hE} {S₀ : Set (Ω E hE)} (hS₀ : (G E hE).Covers V S₀) :
    IsAffinoidTestRefined K (ι E hE V) (ι E hE '' S₀) := by
  intro B _ _ hB φ hφ
  have : Fact (IsAffinoidAlgebra K B) := ⟨hB⟩
  obtain ⟨f, hf⟩ := hmap hE hB φ
  have hfV : ι B hB (f.comap V) =
      AffinoidSubdomain.setEmbedding (⊤ : AffinoidSubdomain K B) := by
    rw [f.coe_comap, AffinoidSubdomain.setEmbedding_apply, AffinoidSubdomain.coe_top]
    exact Set.eq_univ_iff_forall.mpr fun y ↦ by rw [Set.mem_preimage, hf y]; exact hφ ⟨y, rfl⟩
  obtain ⟨R₀, hR₀, hR₀S⟩ := hfiner.exists_refinement hfV (f.covers_comap hS₀)
  obtain ⟨-, R, hRR₀, hfin, hRuniv⟩ :=
    (AffinoidSubdomain.weakGTopology_covers_iff (K := K) (A := B)).mp hR₀
  rw [AffinoidSubdomain.coe_top] at hRuniv
  refine ⟨R, hfin, hRuniv, fun W hW ↦ ?_⟩
  obtain ⟨_, ⟨Z, hZ, rfl⟩, hWZ⟩ := hR₀S W (hRR₀ hW)
  rw [AffinoidSubdomain.setEmbedding_apply, f.coe_comap] at hWZ
  exact ⟨ι E hE Z, ⟨Z, hZ, rfl⟩, fun y hy ↦ by simpa only [Set.mem_preimage, hf y] using hWZ hy⟩

/-- **Universal property of the strong affinoid G-topology** [BGR, §9.1.4, Proposition 2].
Suppose every affinoid `K`-algebra `D` in `Type u` carries a G-topology `G D hD` slightly finer
than `AffinoidSubdomain.weakGTopology` such that every `K`-algebra homomorphism between affinoid
algebras induces a continuous map of G-topologies on maximal spectra. Then for every affinoid
algebra `E`, `strongGTopology` is finer than `G E hE.out`: the identity of `MaximalSpectrum E` is
a continuous map from `strongGTopology` to `G E hE.out`. -/
theorem exists_continuousMap_of_slightlyFiner
    {Ω : ∀ (D : Type u) [CommRing D] [Algebra K D], IsAffinoidAlgebra K D → Type*}
    [∀ D [CommRing D] [Algebra K D] hD, SemilatticeInf (Ω D hD)]
    [∀ D [CommRing D] [Algebra K D] hD, OrderTop (Ω D hD)]
    {ι : ∀ D [CommRing D] [Algebra K D] hD, Ω D hD ↪o Set (MaximalSpectrum D)}
    (G : ∀ D [CommRing D] [Algebra K D] hD, GTopology (ι D hD))
    (hfiner : ∀ {D : Type u} [CommRing D] [Algebra K D] [hD : Fact (IsAffinoidAlgebra K D)],
      (G D hD.out).SlightlyFiner (AffinoidSubdomain.weakGTopology (K := K) (A := D)))
    (hmap : ∀ {D E : Type u} [CommRing D] [Algebra K D] [CommRing E] [Algebra K E]
      (hD : IsAffinoidAlgebra K D) (hE : IsAffinoidAlgebra K E) (φ : D →ₐ[K] E),
      ∃ f : (G E hE).ContinuousMap (G D hD), ∀ y, f y = hE.maximalSpectrumComap φ y)
    (E : Type u) [CommRing E] [Algebra K E] [hE : Fact (IsAffinoidAlgebra K E)] :
    ∃ g : (strongGTopology (K := K) (A := E)).ContinuousMap (G E hE.out), ∀ x, g x = x := by
  have hadm (V : Ω E hE.out) :
      ∃ U : StrongAdmissibleOpen K E, (U : Set (MaximalSpectrum E)) = ι E hE.out V := by
    obtain ⟨S₀, hS₀, hS₀weak⟩ := hfiner.exists_covers V
    let S : Set (AffinoidSubdomain K E) :=
      {U | ∃ W ∈ S₀, (U : Set (MaximalSpectrum E)) = ι E hE.out W}
    have himg : ((↑) : AffinoidSubdomain K E → Set (MaximalSpectrum E)) '' S =
        ι E hE.out '' S₀ := Set.ext fun _ ↦
      ⟨by rintro ⟨_, ⟨W, hW, hUW⟩, rfl⟩; exact ⟨W, hW, hUW.symm⟩,
       by rintro ⟨W, hW, rfl⟩; obtain ⟨U, hUW⟩ := hS₀weak W hW
          rw [AffinoidSubdomain.setEmbedding_apply] at hUW; exact ⟨U, ⟨W, hW, hUW⟩, hUW⟩⟩
    exact ⟨⟨ι E hE.out V, S, (congrArg Set.sUnion himg).trans ((G E hE.out).union_eq hS₀),
      himg ▸ isAffinoidTestRefined_of_slightlyFiner G hfiner hmap hE.out hS₀⟩, coe_mk _ _⟩
  classical
  choose ψ hψ using hadm
  refine ⟨⟨id, ψ, fun V ↦ by rw [setEmbedding_apply, hψ V, Set.preimage_id],
    fun {V S₀} hS₀ ↦ ⟨?_, ?_⟩⟩, fun _ ↦ rfl⟩
  · rintro _ ⟨W, hW, rfl⟩
    rw [← SetLike.coe_subset_coe, hψ W, hψ V]
    exact (ι E hE.out).monotone ((G E hE.out).subset hS₀ W hW)
  · have himg : ((↑) : StrongAdmissibleOpen K E → Set (MaximalSpectrum E)) '' (ψ '' S₀) =
        ι E hE.out '' S₀ := by
      simp only [Set.image_image, hψ]
    rw [hψ V, himg]
    exact isAffinoidTestRefined_of_slightlyFiner G hfiner hmap hE.out hS₀

end UniversalProperty

end StrongAdmissibleOpen

end StrongSite

end TauCeti

namespace AlgHom

open TauCeti

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]
  [hA : Fact (IsAffinoidAlgebra K A)] [hB : Fact (IsAffinoidAlgebra K B)]

/-- An affinoid algebra homomorphism induces a continuous map of strong classical affinoid sites
[BGR, §9.1.4, Proposition 3]. -/
noncomputable def strongAffinoidMap (φ : A →ₐ[K] B) :
    (StrongAdmissibleOpen.strongGTopology (K := K) (A := B)).ContinuousMap
      (StrongAdmissibleOpen.strongGTopology (K := K) (A := A)) where
  toFun := hB.out.maximalSpectrumComap φ
  comap U := U.comap φ
  coe_comap' U := by simp
  covers_comap h := StrongAdmissibleOpen.covers_comap h φ

@[simp]
theorem strongAffinoidMap_apply (φ : A →ₐ[K] B) (x : MaximalSpectrum B) :
    φ.strongAffinoidMap x = hB.out.maximalSpectrumComap φ x := (rfl)

@[simp]
theorem strongAffinoidMap_comap (φ : A →ₐ[K] B) (U : StrongAdmissibleOpen K A) :
    φ.strongAffinoidMap.comap U = U.comap φ := (rfl)

@[simp]
theorem strongAffinoidMap_id : (AlgHom.id K A).strongAffinoidMap =
    GTopology.ContinuousMap.id (StrongAdmissibleOpen.strongGTopology (K := K) (A := A)) := by
  ext x; simp

/-- The induced strong-site maps compose contravariantly with algebra homomorphisms. -/
@[simp]
theorem strongAffinoidMap_comp [hC : Fact (IsAffinoidAlgebra K C)]
    (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    (ψ.comp φ).strongAffinoidMap = φ.strongAffinoidMap.comp ψ.strongAffinoidMap := by
  ext x; simp [IsAffinoidAlgebra.maximalSpectrumComap_comp hB.out hC.out]

/-- The enhancement maps `strongToWeak` form a natural transformation from strong affinoid maps to
weak affinoid maps. -/
theorem strongToWeak_comp_strongAffinoidMap (φ : A →ₐ[K] B) :
    (StrongAdmissibleOpen.strongToWeak (K := K) (A := A)).comp φ.strongAffinoidMap =
      φ.weakAffinoidMap.comp (StrongAdmissibleOpen.strongToWeak (K := K) (A := B)) := by
  ext x; simp

end AlgHom
