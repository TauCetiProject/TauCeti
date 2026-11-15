/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.BaseChange

import TauCeti.RingTheory.Huber.AdicHom.Localization
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Functoriality of completed rational localisations along maps of rational subsets

Let `φ : A →+* B` be a continuous ring homomorphism between topological rings equipped with pairs
of definition `P_A` and `P_B`, and let `R_A(T/s) ⊆ Spa(A, A⁺)` and `R_B(T'/s') ⊆ Spa(B, B⁺)` be
rational subsets such that pullback along `φ` sends `R_B(T'/s')` into `R_A(T/s)`. By the geometric
universal property of `A⟨T/s⟩` (Wedhorn, Lemma 8.1), `φ` extends uniquely across the structure maps
`ρ_A : A → A⟨T/s⟩` and `ρ_B : B → B⟨T'/s'⟩` to a continuous ring homomorphism

```text
ringHomOfMapsToRationalSubset … : A⟨T/s⟩ →+* B⟨T'/s'⟩
```

satisfying `σ ∘ ρ_A = ρ_B ∘ φ`. Neither completeness of `A` or `B`, nor syntactic compatibility
between `(T, s)` and `(T', s')`, nor even `φ(A⁺) ⊆ B⁺` on all of `A⁺` is required: `R_A(T/s)` is
already contained in `Spa(A, A⁺)`, so every point of `R_B(T'/s')` pulls back to a valuation
bounded by `1` on `A⁺`.

When `B⁺` contains the ideal of definition of `P_B`, `σ` carries `A_U⁺` into `B_V⁺`, upgrading `σ`
to a morphism of completed rational localisation Huber pairs (`pairHomOfMapsToRationalSubset`).
When `φ` is adic, `σ` is adic as well (`isAdicHom_ringHomOfMapsToRationalSubset`), because the
composite `σ ∘ ρ_A = ρ_B ∘ φ` is adic and both `ρ_A` and `σ` are continuous.

Specialising `φ` to `RingHom.id A` recovers the containment comparison map
`ringHomOfRationalSubsetSubset` of Wedhorn's Proposition 8.2(1), while specialising `(T', s')` to a
presentation with `φ(s) = s'` and `φ(T) ⊆ T'` recovers `PairOfDefinition.completionLocMap`.

## Main definitions

* `TauCeti.ValuationSpectrum.ringHomOfMapsToRationalSubset`: the unique continuous ring
  homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` extending `φ : A →+* B` when `comap φ` maps `R_B(T'/s')` into
  `R_A(T/s)`.
* `TauCeti.ValuationSpectrum.pairHomOfMapsToRationalSubset`: the corresponding morphism of
  rational localisation Huber pairs `(A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_V⁺)`.

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_mapsTo_rationalSubset`: existence
  and uniqueness of the continuous extension `A⟨T/s⟩ →+* B⟨T'/s'⟩`.
* `TauCeti.ValuationSpectrum.continuous_ringHomOfMapsToRationalSubset`,
  `TauCeti.ValuationSpectrum.ringHomOfMapsToRationalSubset_comp_toCompletionLoc`,
  `TauCeti.ValuationSpectrum.eq_ringHomOfMapsToRationalSubset`: defining properties and uniqueness,
  together with identity (`ringHomOfMapsToRationalSubset_self`), containment
  (`ringHomOfMapsToRationalSubset_id_eq_ringHomOfRationalSubsetSubset`), syntactic base-change
  (`ringHomOfMapsToRationalSubset_eq_completionLocMap`), and composition
  (`ringHomOfMapsToRationalSubset_comp`) laws.
* `TauCeti.ValuationSpectrum.isAdicHom_ringHomOfMapsToRationalSubset`: `σ` is adic whenever `φ` is
  adic.
* `TauCeti.ValuationSpectrum.ringHomOfMapsToRationalSubset_mem_completedPlusSubring` and
  `TauCeti.ValuationSpectrum.spaRationalLocalizationPairHomeomorph_spaComap`:
  preservation of completed plus rings and identification of the induced map on adic spectra with
  the restriction of `Spa(φ)` to `R_B(T'/s') → R_A(T/s)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46, Lemma 8.1 and
  Proposition 8.2.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

universe u v w

/-! ### Pullback criteria for rational subsets -/

section MapsTo

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B]

/-- `spaComap φ` maps the subtype preimage of `R_B(T'/s')` into that of `R_A(T/s)` if and only if
`comap φ` maps `R_B(T'/s')` into `R_A(T/s)`. -/
theorem mapsTo_spaComap_preimage_rationalSubset_iff (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (T : Finset A) (s : A) (T' : Finset B) (s' : B) :
    Set.MapsTo (spaComap φ hφ Aplus Bplus hplus)
        (Subtype.val ⁻¹' rationalSubset Bplus T' s')
        (Subtype.val ⁻¹' rationalSubset Aplus T s) ↔
      Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s) :=
  ⟨fun h v hv ↦ by
      simpa only [Set.mem_preimage, spaComap_val] using
        h (x := ⟨v, rationalSubset_subset_spa Bplus T' s' hv⟩) hv,
    fun h v hv ↦ by simpa only [Set.mem_preimage, spaComap_val] using h hv⟩

/-- If `φ` is continuous, carries `A⁺` into `B⁺`, sends `s` to `s'`, and sends `T` into `T'`, then
`comap φ` maps `R_B(T'/s')` into `R_A(T/s)`. -/
theorem mapsTo_comap_rationalSubset {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {T : Finset A} {s : A}
    {T' : Finset B} {s' : B} (hs : φ s = s') (hT : ∀ t ∈ T, φ t ∈ T') :
    Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s) := by
  intro v hv
  obtain ⟨hv_spa, hvT, hvs⟩ := (mem_rationalSubset_iff Bplus T' s' v).mp hv
  exact (mem_rationalSubset_iff Aplus T s _).mpr ⟨comap_mem_spa hφ hplus hv_spa,
    fun t ht ↦ by simpa only [comap_vle, hs] using hvT (φ t) (hT t ht),
    by simpa only [comap_vle, map_zero, hs] using hvs⟩

end MapsTo

/-! ### Continuous ring homomorphisms between completed rational localisations -/

section RingHom

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]

/-- **Geometric functoriality of completed rational localisations.** Let `φ : A →+* B` be a
continuous ring homomorphism such that `comap φ` maps `R_B(T'/s')` into `R_A(T/s)`. When `B⁺`
consists of power-bounded elements, there is a unique continuous ring homomorphism
`σ : A⟨T/s⟩ →+* B⟨T'/s'⟩` satisfying `σ ∘ ρ_A = ρ_B ∘ φ`. -/
theorem existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    {φ : A →+* B} (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    ∃! σ : Completion S →+* Completion S',
      Continuous σ ∧
        σ.comp (toCompletionLoc PA T s S hden) = (toCompletionLoc PB T' s' S' hden').comp φ := by
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  refine existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    PA Aplus T s S hden (powerBoundedSubring (Completion S'))
    ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
    ((continuous_toCompletionLoc PB T' s' S' hden').comp hφ).continuousAt fun w hw ↦ ?_
  have hle := completedPlusSubring_le_powerBoundedSubring PB Bplus hBplus T' s' S' hden'
  have hw' : comap (toCompletionLoc PB T' s' S' hden') w ∈ rationalSubset Bplus T' s' := by
    simpa only [spaComapLoc_val] using
      spaComapLoc_mem_rationalSubset PB Bplus T' s' S' hden' ⟨w, spa_antitone hle hw⟩
  rw [comap_comp]
  exact hmaps hw'

/-- **The continuous ring homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` induced by a map sending `R_B(T'/s')`
into `R_A(T/s)`.** It is uniquely determined among continuous ring homomorphisms by
`ringHomOfMapsToRationalSubset_comp_toCompletionLoc` (`eq_ringHomOfMapsToRationalSubset`). -/
noncomputable def ringHomOfMapsToRationalSubset
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    Completion S →+* Completion S' :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset PA Aplus T s S hden PB Bplus hBplus
    T' s' S' hden' hφ hmaps).choose

/-- `ringHomOfMapsToRationalSubset` is continuous. -/
theorem continuous_ringHomOfMapsToRationalSubset
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    Continuous (ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
      φ hφ hmaps) :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset PA Aplus T s S hden PB Bplus hBplus
    T' s' S' hden' hφ hmaps).choose_spec.1.1

/-- `ringHomOfMapsToRationalSubset` commutes with the structure maps from `A` and `B`. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_comp_toCompletionLoc
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    (ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
        φ hφ hmaps).comp (toCompletionLoc PA T s S hden) =
      (toCompletionLoc PB T' s' S' hden').comp φ :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset PA Aplus T s S hden PB Bplus hBplus
    T' s' S' hden' hφ hmaps).choose_spec.1.2

-- Not tagged `@[simp]`: `toCompletionLoc_apply` is `@[simp]` and simplifies `toCompletionLoc … a`.
/-- Pointwise compatibility of `ringHomOfMapsToRationalSubset` with `toCompletionLoc`. -/
theorem ringHomOfMapsToRationalSubset_toCompletionLoc
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))
    (a : A) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden' φ hφ hmaps
        (toCompletionLoc PA T s S hden a) =
      toCompletionLoc PB T' s' S' hden' (φ a) :=
  RingHom.congr_fun (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PA Aplus T s S hden
    PB Bplus hBplus T' s' S' hden' φ hφ hmaps) a

/-- **Uniqueness of `ringHomOfMapsToRationalSubset`**: any continuous ring homomorphism
`A⟨T/s⟩ →+* B⟨T'/s'⟩` compatible with the structure maps along `φ` equals
`ringHomOfMapsToRationalSubset`. -/
theorem eq_ringHomOfMapsToRationalSubset
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    ∀ g : Completion S →+* Completion S', Continuous g →
      g.comp (toCompletionLoc PA T s S hden) = (toCompletionLoc PB T' s' S' hden').comp φ →
      g = ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
        φ hφ hmaps :=
  fun g hgc hge ↦
    (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset PA Aplus T s S hden PB Bplus hBplus
      T' s' S' hden' hφ hmaps).choose_spec.2 g ⟨hgc, hge⟩

/-- Along `RingHom.id A` with a single pair of definition, `ringHomOfMapsToRationalSubset` agrees
with `ringHomOfRationalSubsetSubset`. -/
theorem ringHomOfMapsToRationalSubset_id_eq_ringHomOfRationalSubsetSubset
    (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hId : Continuous (RingHom.id A))
    (hmaps : Set.MapsTo (comap (RingHom.id A)) (rationalSubset Aplus T' s')
      (rationalSubset Aplus T s))
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ringHomOfMapsToRationalSubset P Aplus T s S hden P Aplus hAplus T' s' S' hden'
        (RingHom.id A) hId hmaps =
      ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  refine (eq_ringHomOfMapsToRationalSubset P Aplus T s S hden P Aplus hAplus T' s' S' hden'
    (RingHom.id A) hId hmaps _
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub)
    ?_).symm
  rw [ringHomOfRationalSubsetSubset_comp_toCompletionLoc, RingHom.comp_id]

/-- `ringHomOfMapsToRationalSubset` for `RingHom.id A` and the same presentation is the identity. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_self
    (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (hId : Continuous (RingHom.id A))
    (hmaps : Set.MapsTo (comap (RingHom.id A)) (rationalSubset Aplus T s)
      (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ringHomOfMapsToRationalSubset P Aplus T s S hden P Aplus hAplus T s S hden
      (RingHom.id A) hId hmaps = RingHom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  refine (eq_ringHomOfMapsToRationalSubset P Aplus T s S hden P Aplus hAplus T s S hden
    (RingHom.id A) hId hmaps (RingHom.id _) continuous_id ?_).symm
  rw [RingHom.id_comp, RingHom.comp_id]

/-- `ringHomOfMapsToRationalSubset` composes covariantly along composable maps of rings. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_comp
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (PC : PairOfDefinition C) (Cplus : Subring C) (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c)
    (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower PC T'' s'' S'')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps₁ : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))
    (ψ : B →+* C) (hψ : Continuous ψ)
    (hmaps₂ : Set.MapsTo (comap ψ) (rationalSubset Cplus T'' s'') (rationalSubset Bplus T' s'))
    (hψφ : Continuous (ψ.comp φ))
    (hmaps₁₂ : Set.MapsTo (comap (ψ.comp φ)) (rationalSubset Cplus T'' s'')
      (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := locUniformSpace PC T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace PC T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace PC T'' s'' S'' hden''
    (ringHomOfMapsToRationalSubset PB Bplus T' s' S' hden' PC Cplus hCplus T'' s'' S'' hden''
        ψ hψ hmaps₂).comp
      (ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
        φ hφ hmaps₁) =
      ringHomOfMapsToRationalSubset PA Aplus T s S hden PC Cplus hCplus T'' s'' S'' hden''
        (ψ.comp φ) hψφ hmaps₁₂ := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  let _ := locUniformSpace PC T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace PC T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace PC T'' s'' S'' hden''
  refine eq_ringHomOfMapsToRationalSubset PA Aplus T s S hden PC Cplus hCplus T'' s'' S'' hden''
    (ψ.comp φ) hψφ hmaps₁₂ _
    ((continuous_ringHomOfMapsToRationalSubset PB Bplus T' s' S' hden' PC Cplus hCplus T'' s'' S''
      hden'' ψ hψ hmaps₂).comp
      (continuous_ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
        φ hφ hmaps₁)) ?_
  rw [RingHom.comp_assoc, ringHomOfMapsToRationalSubset_comp_toCompletionLoc,
    ← RingHom.comp_assoc, ringHomOfMapsToRationalSubset_comp_toCompletionLoc, RingHom.comp_assoc]

/-- When `φ(s) = s'` and `φ(T) ⊆ T'`, `ringHomOfMapsToRationalSubset` agrees with the syntactic
base-change map `PairOfDefinition.completionLocMap`. -/
theorem ringHomOfMapsToRationalSubset_eq_completionLocMap
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))
    (hs : φ s = s') (hT : ∀ t ∈ T, φ t ∈ T') :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden' φ hφ hmaps =
      completionLocMap PA T s S hden PB φ hφ.continuousAt T' s' S' hden' hs hT := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  exact (eq_ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
    φ hφ hmaps _ (continuous_completionLocMap PA T s S hden PB φ hφ.continuousAt T' s' S' hden'
      hs hT)
    (completionLocMap_comp_toCompletionLoc PA T s S hden PB φ hφ.continuousAt T' s' S' hden'
      hs hT)).symm

/-- **Adicness of induced morphisms between completed rational localisations.** If `φ : A →+* B` is
adic and `comap φ` maps `R_B(T'/s')` into `R_A(T/s)`, then the induced homomorphism
`ringHomOfMapsToRationalSubset … : A⟨T/s⟩ →+* B⟨T'/s'⟩` is adic. -/
theorem isAdicHom_ringHomOfMapsToRationalSubset
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ) (hadic : IsAdicHom φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    IsAdicHom (ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
      φ hφ hmaps) := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  refine IsAdicHom.of_comp ?_ (continuous_toCompletionLoc PA T s S hden)
    (continuous_ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
      φ hφ hmaps)
  rw [ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
  exact (isAdicHom_toCompletionLoc PB T' s' S' hden').comp hadic

/-! ### Preservation of completed plus rings and morphisms of Huber pairs -/

/-- Pullback along `ringHomOfMapsToRationalSubset` sends `Spa(B⟨T'/s'⟩, B_V⁺)` into
`Spa(A⟨T/s⟩, A_U⁺)`. -/
theorem comap_ringHomOfMapsToRationalSubset_mem_spa
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    ∀ w ∈ spa (completedPlusSubring PB Bplus T' s' S' hden'),
      comap (ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
          φ hφ hmaps) w ∈
        spa (completedPlusSubring PA Aplus T s S hden) := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  intro w hw
  refine comap_mem_spa_completedPlusSubring PA Aplus T s S hden _
    (continuous_ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden'
      φ hφ hmaps) ((mem_spa_iff _ _).mp hw).1 ?_
  rw [ringHomOfMapsToRationalSubset_comp_toCompletionLoc, comap_comp]
  exact hmaps (by simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset PB Bplus T' s' S' hden' ⟨w, hw⟩)

/-- **Plus-ring preservation for `ringHomOfMapsToRationalSubset`.** When `B⁺` contains the ideal of
definition of `P_B`, `ringHomOfMapsToRationalSubset` carries `A_U⁺` into `B_V⁺`. -/
theorem ringHomOfMapsToRationalSubset_mem_completedPlusSubring
    (PA : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (Bplus : Subring B)
    (hIBplus : ∀ j : PB.ringOfDefinition, j ∈ PB.idealOfDefinition → (j : B) ∈ Bplus)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    ∀ f ∈ completedPlusSubring PA Aplus T s S hden,
      ringHomOfMapsToRationalSubset PA Aplus T s S hden PB Bplus hBplus T' s' S' hden' φ hφ hmaps
          f ∈
        completedPlusSubring PB Bplus T' s' S' hden' := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  have hB := isRingOfIntegralElements_completedPlusSubring PB Bplus hIBplus hBplus T' s' S' hden'
  refine fun f hf ↦ hB.mem_of_forall_vle_one fun w hw ↦ ?_
  simpa only [comap_vle, map_one] using
    ((mem_spa_iff _ _).mp (comap_ringHomOfMapsToRationalSubset_mem_spa PA Aplus T s S hden
      PB Bplus hBplus T' s' S' hden' φ hφ hmaps w hw)).2 f hf

end RingHom

section HuberPair

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- **The morphism of rational localisation Huber pairs `(A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_V⁺)` induced
by a continuous ring homomorphism `φ : A →+* B` whose valuation pullback sends `R_B(T'/s')` into
`R_A(T/s)`.** Note that `φ` itself need not be a morphism of Huber pairs `(A, A⁺) → (B, B⁺)`. -/
noncomputable def pairHomOfMapsToRationalSubset
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset UB.plus T' s') (rationalSubset UA.plus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    Pair.Hom (rationalLocalizationPair PA UA hPA T s S hden)
      (rationalLocalizationPair PB UB hPB T' s' S' hden') :=
  letI := locUniformSpace PA T s S hden
  letI := isUniformAddGroup_locUniformSpace PA T s S hden
  letI := isTopologicalRing_locUniformSpace PA T s S hden
  letI := isHuberRing_completion_locTopology PA T s S hden
  letI := locUniformSpace PB T' s' S' hden'
  letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  letI := isHuberRing_completion_locTopology PB T' s' S' hden'
  { toRingHom := ringHomOfMapsToRationalSubset PA UA.plus T s S hden PB UB.plus
      UB.isRingOfIntegralElements.isPowerBounded_of_mem T' s' S' hden' φ hφ hmaps
    continuous_toRingHom := continuous_ringHomOfMapsToRationalSubset PA UA.plus T s S hden
      PB UB.plus UB.isRingOfIntegralElements.isPowerBounded_of_mem T' s' S' hden' φ hφ hmaps
    map_mem_plus := by
      rw [rationalLocalizationPair_plus, rationalLocalizationPair_plus]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring PA UA.plus T s S hden PB UB.plus
        (fun j _ ↦ hPB j.2) UB.isRingOfIntegralElements.isPowerBounded_of_mem T' s' S' hden'
        φ hφ hmaps }

/-- The underlying ring homomorphism of `pairHomOfMapsToRationalSubset` is
`ringHomOfMapsToRationalSubset`. -/
@[simp]
theorem toRingHom_pairHomOfMapsToRationalSubset
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps : Set.MapsTo (comap φ) (rationalSubset UB.plus T' s') (rationalSubset UA.plus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    (pairHomOfMapsToRationalSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden'
      φ hφ hmaps).toRingHom =
      ringHomOfMapsToRationalSubset PA UA.plus T s S hden PB UB.plus
        UB.isRingOfIntegralElements.isPowerBounded_of_mem T' s' S' hden' φ hφ hmaps :=
  (rfl)

/-- When `f : Pair.Hom UA UB` is a morphism of Huber pairs, `pairHomOfMapsToRationalSubset`
commutes with `toCompletionLocHom`. -/
@[simp]
theorem pairHomOfMapsToRationalSubset_comp_toCompletionLocHom
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB) (hφ : Continuous f.toRingHom)
    (hmaps : Set.MapsTo (comap f.toRingHom) (rationalSubset UB.plus T' s')
      (rationalSubset UA.plus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    (pairHomOfMapsToRationalSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden'
        f.toRingHom hφ hmaps).comp (toCompletionLocHom PA UA hPA T s S hden) =
      (toCompletionLocHom PB UB hPB T' s' S' hden').comp f := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp, toRingHom_pairHomOfMapsToRationalSubset,
    toRingHom_toCompletionLocHom, toRingHom_toCompletionLocHom,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc]

/-- `pairHomOfMapsToRationalSubset` at `RingHom.id A` and the same presentation is the identity
morphism of Huber pairs. -/
@[simp]
theorem pairHomOfMapsToRationalSubset_self
    (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (hId : Continuous (RingHom.id A))
    (hmaps : Set.MapsTo (comap (RingHom.id A)) (rationalSubset U.plus T s)
      (rationalSubset U.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    pairHomOfMapsToRationalSubset P U hP T s S hden P U hP T s S hden (RingHom.id A) hId hmaps =
      Pair.Hom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  apply Pair.Hom.ext
  rw [toRingHom_pairHomOfMapsToRationalSubset, Pair.Hom.toRingHom_id,
    ringHomOfMapsToRationalSubset_self]

/-- `pairHomOfMapsToRationalSubset` composes covariantly along composable maps of rings. -/
@[simp]
theorem pairHomOfMapsToRationalSubset_comp
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (PC : PairOfDefinition C) (UC : Pair C) (hPC : PC.ringOfDefinition ≤ UC.plus)
    (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower PC T'' s'' S'')
    (φ : A →+* B) (hφ : Continuous φ)
    (hmaps₁ : Set.MapsTo (comap φ) (rationalSubset UB.plus T' s') (rationalSubset UA.plus T s))
    (ψ : B →+* C) (hψ : Continuous ψ)
    (hmaps₂ : Set.MapsTo (comap ψ) (rationalSubset UC.plus T'' s'') (rationalSubset UB.plus T' s'))
    (hψφ : Continuous (ψ.comp φ))
    (hmaps₁₂ : Set.MapsTo (comap (ψ.comp φ)) (rationalSubset UC.plus T'' s'')
      (rationalSubset UA.plus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    letI := locUniformSpace PC T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace PC T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace PC T'' s'' S'' hden''
    letI := isHuberRing_completion_locTopology PC T'' s'' S'' hden''
    (pairHomOfMapsToRationalSubset PB UB hPB T' s' S' hden' PC UC hPC T'' s'' S'' hden''
        ψ hψ hmaps₂).comp
      (pairHomOfMapsToRationalSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden'
        φ hφ hmaps₁) =
      pairHomOfMapsToRationalSubset PA UA hPA T s S hden PC UC hPC T'' s'' S'' hden''
        (ψ.comp φ) hψφ hmaps₁₂ := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  let _ := locUniformSpace PC T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace PC T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace PC T'' s'' S'' hden''
  have _ := isHuberRing_completion_locTopology PC T'' s'' S'' hden''
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, toRingHom_pairHomOfMapsToRationalSubset,
    toRingHom_pairHomOfMapsToRationalSubset, toRingHom_pairHomOfMapsToRationalSubset,
    ringHomOfMapsToRationalSubset_comp]

/-- The homeomorphism `Spa(A⟨T/s⟩, A_U⁺) ≃ₜ R_A(T/s)` phrased directly for the bundled Huber pair
`rationalLocalizationPair P U hP T s S hden`. -/
noncomputable def spaRationalLocalizationPairHomeomorph
    (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    spa (rationalLocalizationPair P U hP T s S hden).plus ≃ₜ
      (Subtype.val ⁻¹' rationalSubset U.plus T s : Set (spa U.plus)) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  (Homeomorph.setCongr (by rw [rationalLocalizationPair_plus])).trans
    (spaCompletedLocalizationHomeomorph P U.plus hP T s S hden)

/-- The underlying valuation of `spaRationalLocalizationPairHomeomorph P U hP T s S hden w` is
`comap (toCompletionLoc P T s S hden) w`. -/
@[simp]
theorem spaRationalLocalizationPairHomeomorph_coe_val
    (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ w : spa (rationalLocalizationPair P U hP T s S hden).plus,
      ((spaRationalLocalizationPairHomeomorph P U hP T s S hden w : spa U.plus)).1 =
        comap (toCompletionLoc P T s S hden) w.1 := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro w
  simp [spaRationalLocalizationPairHomeomorph]

/-- Pullback along `spaRationalLocalizationPairHomeomorph` bijects rational subsets of `Spa(A, A⁺)`
contained in `R_A(T/s)` onto
`spaRationalFamily (rationalLocalizationPair P U hP T s S hden).plus`. -/
theorem bijOn_preimage_spaRationalLocalizationPairHomeomorph_spaRationalFamily
    (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
    (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Set.BijOn (fun W : Set (spa U.plus) ↦
        spaRationalLocalizationPairHomeomorph P U hP T s S hden ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily U.plus | W ⊆ Subtype.val ⁻¹' rationalSubset U.plus T s}
      (spaRationalFamily (rationalLocalizationPair P U hP T s S hden).plus) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have hsetCongr :
      ∀ {L R : Subring (Completion S)} (h : L = R),
        Set.BijOn (fun V : Set (spa R) ↦ Homeomorph.setCongr (congrArg spa h) ⁻¹' V)
          (spaRationalFamily R) (spaRationalFamily L) := by
    rintro L _ rfl
    have hid : ∀ V : Set (spa L), Homeomorph.setCongr (rfl : spa L = spa L) ⁻¹' V = V :=
      fun V ↦ by ext ⟨v, hv⟩; simp
    exact ⟨fun V hV ↦ (hid V).symm ▸ hV, fun _ _ _ _ h ↦ by simpa only [hid] using h,
      fun V hV ↦ ⟨V, hV, hid V⟩⟩
  exact (hsetCongr (rationalLocalizationPair_plus P U hP T s S hden)).comp
    (bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily P U.plus hP T s hT S hden)

/-- **Across the homeomorphisms `Spa(A⟨T/s⟩, A_U⁺) ≃ₜ R_A(T/s)` and
`Spa(B⟨T'/s'⟩, B_V⁺) ≃ₜ R_B(T'/s')`, the map of adic spectra induced by
`pairHomOfMapsToRationalSubset` is the restriction of `f.spaComap` from `R_B(T'/s')` to
`R_A(T/s)`.** -/
theorem spaRationalLocalizationPairHomeomorph_spaComap
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB)
    (hmaps : Set.MapsTo f.spaComap (Subtype.val ⁻¹' rationalSubset UB.plus T' s')
      (Subtype.val ⁻¹' rationalSubset UA.plus T s)) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    ∀ w : spa (rationalLocalizationPair PB UB hPB T' s' S' hden').plus,
      spaRationalLocalizationPairHomeomorph PA UA hPA T s S hden
          ((pairHomOfMapsToRationalSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden'
            f.toRingHom f.continuous_toRingHom
            ((mapsTo_spaComap_preimage_rationalSubset_iff f.toRingHom f.continuous_toRingHom
              f.map_mem_plus T s T' s').mp (f.spaComap_def ▸ hmaps))).spaComap w) =
        hmaps.restrict f.spaComap _ _
          (spaRationalLocalizationPairHomeomorph PB UB hPB T' s' S' hden' w) := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  intro w
  apply Subtype.ext
  apply Subtype.ext
  change ((spaRationalLocalizationPairHomeomorph PA UA hPA T s S hden _ : spa UA.plus)).1 =
    (f.spaComap (spaRationalLocalizationPairHomeomorph PB UB hPB T' s' S' hden' w).1).1
  rw [spaRationalLocalizationPairHomeomorph_coe_val, Pair.Hom.spaComap_val,
    toRingHom_pairHomOfMapsToRationalSubset, Pair.Hom.spaComap_val,
    spaRationalLocalizationPairHomeomorph_coe_val,
    ← Function.comp_apply (f := comap (toCompletionLoc PA T s S hden)), ← comap_comp,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc, comap_comp, Function.comp_apply]

end HuberPair

end TauCeti.ValuationSpectrum

end
