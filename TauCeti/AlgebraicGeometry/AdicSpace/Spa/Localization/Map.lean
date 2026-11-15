/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
import TauCeti.RingTheory.Huber.AdicHom.Localization

/-!
# Functoriality and adicness of completed rational localisation along morphisms

Let `φ : A →+* B` be a ring homomorphism continuous at `0`, and let `R(T/s) ⊆ Spa (A, A⁺)` and
`R(T'/s') ⊆ Spa (B, B⁺)` be rational subsets such that pullback along `φ` maps `R(T'/s')` into
`R(T/s)`. Instantiating Wedhorn's Lemma 8.1 at the completed localisation `(B⟨T'/s'⟩, B_U'⁺)`
produces a unique continuous ring homomorphism

```text
σ : A⟨T/s⟩ →+* B⟨T'/s'⟩
```

commuting with the structure maps from `A` and `B`. Moreover:

* `σ` carries `A_U⁺` into `B_U'⁺`, giving a morphism of Huber pairs
  `pairHomOfMapsToRationalSubset : (A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_U'⁺)` compatible with
  `toCompletionLocHom`;
* when `φ` is adic, `σ` is adic (`isAdicHom_ringHomOfMapsToRationalSubset`), and in particular
  every restriction homomorphism `ringHomOfRationalSubsetSubset` between rational subsets of the
  same Huber pair is adic (`isAdicHom_ringHomOfRationalSubsetSubset`).

Global preservation `φ(A⁺) ⊆ B⁺` is not assumed: `MapsTo (comap φ) R(T'/s') R(T/s)` asks only
that `φ(A⁺)` be bounded by `1` at the points of `R(T'/s')`. Specialising `φ` to `RingHom.id A`
recovers `ringHomOfRationalSubsetSubset`.

## Main definitions

* `TauCeti.ValuationSpectrum.ringHomOfMapsToRationalSubset`: the unique continuous ring
  homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` extending `ρ' ∘ φ` across `ρ`.
* `TauCeti.ValuationSpectrum.pairHomOfMapsToRationalSubset`: the same map bundled as a morphism
  of completed rational localisation Huber pairs.

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_mapsTo_rationalSubset`: existence
  and uniqueness of the continuous extension.
* `TauCeti.ValuationSpectrum.ringHomOfMapsToRationalSubset_id`,
  `TauCeti.ValuationSpectrum.ringHomOfMapsToRationalSubset_comp`: identity and composition laws,
  with Huber-pair counterparts `pairHomOfMapsToRationalSubset_self` and
  `pairHomOfMapsToRationalSubset_comp`.
* `TauCeti.ValuationSpectrum.isAdicHom_ringHomOfMapsToRationalSubset`,
  `TauCeti.ValuationSpectrum.isAdicHom_ringHomOfRationalSubsetSubset`: adicness of induced maps
  between completed rational localisations.
* `TauCeti.ValuationSpectrum.spaComap_toCompletionLocHom_spaComap_pairHomOfMapsToRationalSubset`:
  compatibility of the induced map on `Spa` with `toCompletionLocHom`.
* `TauCeti.Huber.Pair.Hom.mapsTo_spaComap_rationalSubset_iff`: equivalence between `Set.MapsTo`
  for `f.spaComap` on subtype preimages and `Set.MapsTo` for `comap f.toRingHom` on ambient
  rational subsets.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46, Lemma 8.1, and
  Proposition 8.2.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

section RingHom

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]

/-- If `φ : A →+* B` is continuous at `0` and pullback along `φ` carries `R(T'/s')` into `R(T/s)`,
then `(toCompletionLoc P' T' s' S' hden').comp φ` extends uniquely along
`toCompletionLoc P T s S hden` to a continuous ring homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩`. -/
theorem existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∃! σ : Completion S →+* Completion S',
      Continuous σ ∧
        σ.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' s' S' hden').comp φ := by
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  refine existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    P Aplus T s S hden (powerBoundedSubring (Completion S'))
    ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
    ((continuous_toCompletionLoc P' T' s' S' hden').continuousAt.comp_of_eq hφ (map_zero φ))
    fun w hw ↦ ?_
  have hle := completedPlusSubring_le_powerBoundedSubring P' Bplus hBplus T' s' S' hden'
  rw [comap_comp, Function.comp_apply]
  exact hsub (by simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P' Bplus T' s' S' hden' ⟨w, spa_antitone hle hw⟩)

/-- The continuous ring homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` induced by a homomorphism `φ : A →+* B`
continuous at `0` whose valuation pullback maps `R(T'/s')` into `R(T/s)`. -/
noncomputable def ringHomOfMapsToRationalSubset
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    Completion S →+* Completion S' :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub).choose

/-- `ringHomOfMapsToRationalSubset` is continuous. -/
@[fun_prop]
theorem continuous_ringHomOfMapsToRationalSubset
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    Continuous (ringHomOfMapsToRationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub) :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub).choose_spec.1.1

/-- `ringHomOfMapsToRationalSubset` commutes with the structure maps from `A` and `B`. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_comp_toCompletionLoc
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    (ringHomOfMapsToRationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub).comp
        (toCompletionLoc P T s S hden) =
      (toCompletionLoc P' T' s' S' hden').comp φ :=
  (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
    P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub).choose_spec.1.2

/-- Pointwise action of `ringHomOfMapsToRationalSubset` on elements coming from `A`. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_algebraMap_coe
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))
    (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub
        (algebraMap A S a : Completion S) =
      (algebraMap B S' (φ a) : Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  rw [← toCompletionLoc_apply P T s S hden, ← toCompletionLoc_apply P' T' s' S' hden']
  exact RingHom.congr_fun
    (ringHomOfMapsToRationalSubset_comp_toCompletionLoc
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub) a

/-- Uniqueness characterization of `ringHomOfMapsToRationalSubset`: any continuous ring homomorphism
`A⟨T/s⟩ →+* B⟨T'/s'⟩` extending `ρ' ∘ φ` across `ρ` equals `ringHomOfMapsToRationalSubset`. -/
theorem eq_ringHomOfMapsToRationalSubset
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∀ (τ : Completion S →+* Completion S'),
      Continuous τ →
      τ.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' s' S' hden').comp φ →
      τ = ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub :=
  fun _ hτ hcomp ↦
    (existsUnique_continuous_ringHom_of_mapsTo_rationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub).choose_spec.2 _ ⟨hτ, hcomp⟩

/-- Along `RingHom.id A`, `ringHomOfMapsToRationalSubset` agrees with the containment comparison map
`ringHomOfRationalSubsetSubset`. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_id
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hId : ContinuousAt (RingHom.id A) 0)
    (hsub : Set.MapsTo (comap (RingHom.id A))
      (rationalSubset Aplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ringHomOfMapsToRationalSubset
        P Aplus T s S hden P Aplus hAplus T' s' S' hden' hId hsub =
      ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden'
        (fun v hv ↦ by simpa only [comap_id, id_eq] using hsub hv) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have hsub' : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s :=
    fun v hv ↦ by simpa only [comap_id, id_eq] using hsub hv
  refine (eq_ringHomOfMapsToRationalSubset
    P Aplus T s S hden P Aplus hAplus T' s' S' hden' hId hsub
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub')
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub')
    ?_).symm
  rw [ringHomOfRationalSubsetSubset_comp_toCompletionLoc, RingHom.comp_id]

/-- Functoriality of `ringHomOfMapsToRationalSubset` with respect to composition of ring
homomorphisms. -/
@[simp]
theorem ringHomOfMapsToRationalSubset_comp
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    (P'' : PairOfDefinition C) (Cplus : Subring C)
    (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c)
    (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P'' T'' s'' S'')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {ψ : B →+* C} (hψ : ContinuousAt ψ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s))
    (hsub' : Set.MapsTo (comap ψ) (rationalSubset Cplus T'' s'') (rationalSubset Bplus T' s')) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace P'' T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
    (ringHomOfMapsToRationalSubset
        P' Bplus T' s' S' hden' P'' Cplus hCplus T'' s'' S'' hden'' hψ hsub').comp
      (ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub) =
    ringHomOfMapsToRationalSubset
      P Aplus T s S hden P'' Cplus hCplus T'' s'' S'' hden'' (φ := ψ.comp φ)
      (hψ.comp_of_eq hφ (map_zero φ))
      (by rw [comap_comp]; exact hsub.comp hsub') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ := locUniformSpace P'' T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
  refine eq_ringHomOfMapsToRationalSubset
    P Aplus T s S hden P'' Cplus hCplus T'' s'' S'' hden'' (φ := ψ.comp φ)
    (hψ.comp_of_eq hφ (map_zero φ)) _ _
    ((continuous_ringHomOfMapsToRationalSubset
      P' Bplus T' s' S' hden' P'' Cplus hCplus T'' s'' S'' hden'' hψ hsub').comp
      (continuous_ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub))
    ?_
  rw [RingHom.comp_assoc, ringHomOfMapsToRationalSubset_comp_toCompletionLoc, ← RingHom.comp_assoc,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc, RingHom.comp_assoc]

/-- If `φ : A →+* B` is adic, then the induced map `A⟨T/s⟩ →+* B⟨T'/s'⟩` between completed rational
localisations is adic. -/
theorem isAdicHom_ringHomOfMapsToRationalSubset
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : IsAdicHom φ)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    IsAdicHom (ringHomOfMapsToRationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ.continuous.continuousAt hsub) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  refine IsAdicHom.of_comp (f := toCompletionLoc P T s S hden) ?_
    (continuous_toCompletionLoc P T s S hden)
    (continuous_ringHomOfMapsToRationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ.continuous.continuousAt hsub)
  rw [ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
  exact (isAdicHom_toCompletionLoc P' T' s' S' hden').comp hφ

/-- The restriction map `A⟨T/s⟩ →+* A⟨T'/s'⟩` of a containment `R(T'/s') ⊆ R(T/s)` of rational
subsets is adic. -/
theorem isAdicHom_ringHomOfRationalSubsetSubset
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    IsAdicHom (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have : IsHuberRing A := ⟨⟨P⟩⟩
  have hsub_id : Set.MapsTo (comap (RingHom.id A))
      (rationalSubset Aplus T' s') (rationalSubset Aplus T s) := by
    intro v hv
    simpa only [comap_id, id_eq] using hsub hv
  simpa only [ringHomOfMapsToRationalSubset_id] using
    isAdicHom_ringHomOfMapsToRationalSubset
      P Aplus T s S hden P Aplus hAplus T' s' S' hden' IsAdicHom.id hsub_id

/-- Pullback along `ringHomOfMapsToRationalSubset` sends `Spa (B⟨T'/s'⟩, B_U'⁺)` into
`Spa (A⟨T/s⟩, A_U⁺)`. -/
theorem comap_ringHomOfMapsToRationalSubset_mem_spa
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∀ w ∈ spa (completedPlusSubring P' Bplus T' s' S' hden'),
      comap (ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub) w ∈
        spa (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  intro w hw
  refine comap_mem_spa_completedPlusSubring P Aplus T s S hden _
    (continuous_ringHomOfMapsToRationalSubset
      P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub)
    ((mem_spa_iff _ _).mp hw).1 ?_
  rw [ringHomOfMapsToRationalSubset_comp_toCompletionLoc, comap_comp, Function.comp_apply]
  exact hsub (by simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P' Bplus T' s' S' hden' ⟨w, hw⟩)

/-- `ringHomOfMapsToRationalSubset` carries `A_U⁺` into `B_U'⁺`. -/
theorem ringHomOfMapsToRationalSubset_mem_completedPlusSubring
    (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (Bplus : Subring B)
    (hIplus' : ∀ j : P'.ringOfDefinition, j ∈ P'.idealOfDefinition → (j : B) ∈ Bplus)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset Bplus T' s') (rationalSubset Aplus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∀ f ∈ completedPlusSubring P Aplus T s S hden,
      ringHomOfMapsToRationalSubset
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub f ∈
        completedPlusSubring P' Bplus T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  have hint := isRingOfIntegralElements_completedPlusSubring P' Bplus hIplus' hBplus T' s' S' hden'
  refine fun f hf ↦ hint.mem_of_forall_vle_one fun w hw ↦ ?_
  simpa only [comap_vle, map_one] using
    ((mem_spa_iff _ _).mp
      (comap_ringHomOfMapsToRationalSubset_mem_spa
        P Aplus T s S hden P' Bplus hBplus T' s' S' hden' hφ hsub w hw)).2 f hf

end RingHom

section PairHom

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- `ringHomOfMapsToRationalSubset` bundled as a morphism of completed rational localisation Huber
pairs `(A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_U'⁺)`. -/
noncomputable def pairHomOfMapsToRationalSubset
    (P : PairOfDefinition A) (SA : Pair A) (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (SB : Pair B) (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    Pair.Hom
      (P.rationalLocalizationPair SA hP T s S hden)
      (P'.rationalLocalizationPair SB hP' T' s' S' hden') :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  letI := locUniformSpace P' T' s' S' hden'
  letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  letI := isHuberRing_completion_locTopology P' T' s' S' hden'
  { toRingHom := ringHomOfMapsToRationalSubset
      P SA.plus T s S hden P' SB.plus SB.isRingOfIntegralElements.isPowerBounded_of_mem
      T' s' S' hden' hφ hsub
    continuous_toRingHom := continuous_ringHomOfMapsToRationalSubset
      P SA.plus T s S hden P' SB.plus SB.isRingOfIntegralElements.isPowerBounded_of_mem
      T' s' S' hden' hφ hsub
    map_mem_plus := fun f hf ↦ by
      rw [rationalLocalizationPair_plus] at hf ⊢
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring
        P SA.plus T s S hden P' SB.plus (fun j _ ↦ hP' j.2)
        SB.isRingOfIntegralElements.isPowerBounded_of_mem T' s' S' hden' hφ hsub f hf }

/-- The underlying ring homomorphism of `pairHomOfMapsToRationalSubset` is
`ringHomOfMapsToRationalSubset`. -/
@[simp]
theorem pairHomOfMapsToRationalSubset_toRingHom
    (P : PairOfDefinition A) (SA : Pair A) (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (SB : Pair B) (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (pairHomOfMapsToRationalSubset
      P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub).toRingHom =
      ringHomOfMapsToRationalSubset
        P SA.plus T s S hden P' SB.plus SB.isRingOfIntegralElements.isPowerBounded_of_mem
        T' s' S' hden' hφ hsub := (rfl)

/-- When `φ` is the underlying ring homomorphism of a morphism of Huber pairs `f : SA → SB`,
`pairHomOfMapsToRationalSubset` forms a commuting square with `toCompletionLocHom` and `f`. -/
theorem pairHomOfMapsToRationalSubset_comp_toCompletionLocHom
    (P : PairOfDefinition A) {SA : Pair A} (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) {SB : Pair B} (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    (f : Pair.Hom SA SB) {φ : A →+* B} (hfφ : f.toRingHom = φ) (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (pairHomOfMapsToRationalSubset
        P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub).comp
      (P.toCompletionLocHom SA hP T s S hden) =
      (P'.toCompletionLocHom SB hP' T' s' S' hden').comp f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  apply Pair.Hom.ext
  simp [hfφ]

/-- On the same presentation along `RingHom.id A`, `pairHomOfMapsToRationalSubset` is the identity
morphism of Huber pairs. -/
@[simp]
theorem pairHomOfMapsToRationalSubset_self
    (P : PairOfDefinition A) (SA : Pair A) (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (hId : ContinuousAt (RingHom.id A) 0)
    (hsub : Set.MapsTo (comap (RingHom.id A))
      (rationalSubset SA.plus T s) (rationalSubset SA.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    pairHomOfMapsToRationalSubset
      P SA hP T s S hden P SA hP T s S hden hId hsub =
      Pair.Hom.id (P.rationalLocalizationPair SA hP T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  apply Pair.Hom.ext
  simp only [pairHomOfMapsToRationalSubset_toRingHom, Pair.Hom.toRingHom_id]
  exact (eq_ringHomOfMapsToRationalSubset P SA.plus T s S hden P SA.plus
    SA.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden hId hsub
    (RingHom.id _) continuous_id (by rw [RingHom.id_comp, RingHom.comp_id])).symm

/-- Functoriality of `pairHomOfMapsToRationalSubset` with respect to composition of ring
homomorphisms. -/
@[simp]
theorem pairHomOfMapsToRationalSubset_comp
    (P : PairOfDefinition A) (SA : Pair A) (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (SB : Pair B) (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    (P'' : PairOfDefinition C) (SC : Pair C) (hP'' : P''.ringOfDefinition ≤ SC.plus)
    (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P'' T'' s'' S'')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {ψ : B →+* C} (hψ : ContinuousAt ψ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s))
    (hsub' : Set.MapsTo (comap ψ) (rationalSubset SC.plus T'' s'') (rationalSubset SB.plus T' s')) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    letI := locUniformSpace P'' T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
    letI := isHuberRing_completion_locTopology P'' T'' s'' S'' hden''
    (pairHomOfMapsToRationalSubset
        P' SB hP' T' s' S' hden' P'' SC hP'' T'' s'' S'' hden'' hψ hsub').comp
      (pairHomOfMapsToRationalSubset
        P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub) =
    pairHomOfMapsToRationalSubset
      P SA hP T s S hden P'' SC hP'' T'' s'' S'' hden'' (φ := ψ.comp φ)
      (hψ.comp_of_eq hφ (map_zero φ))
      (by rw [comap_comp]; exact hsub.comp hsub') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  let _ := locUniformSpace P'' T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
  have _ := isHuberRing_completion_locTopology P'' T'' s'' S'' hden''
  apply Pair.Hom.ext
  simp

/-- Pulling a point of `Spa (B⟨T'/s'⟩, B_U'⁺)` back along `pairHomOfMapsToRationalSubset` and then
along `toCompletionLocHom` gives the valuation pullback along `φ` of its image in `Spa (B, B⁺)`. -/
theorem spaComap_toCompletionLocHom_spaComap_pairHomOfMapsToRationalSubset
    (P : PairOfDefinition A) (SA : Pair A) (hP : P.ringOfDefinition ≤ SA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition B) (SB : Pair B) (hP' : P'.ringOfDefinition ≤ SB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P' T' s' S')
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hsub : Set.MapsTo (comap φ) (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    ∀ w : spa (P'.rationalLocalizationPair SB hP' T' s' S' hden').plus,
      (((P.toCompletionLocHom SA hP T s S hden).spaComap
        ((pairHomOfMapsToRationalSubset
          P SA hP T s S hden P' SB hP' T' s' S' hden' hφ hsub).spaComap w)).1 : Spv A) =
        comap φ (((P'.toCompletionLocHom SB hP' T' s' S' hden').spaComap w).1 : Spv B) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  intro w
  simp only [Pair.Hom.spaComap_val, toRingHom_toCompletionLocHom,
    pairHomOfMapsToRationalSubset_toRingHom]
  rw [← Function.comp_apply (f := comap (toCompletionLoc P T s S hden)), ← comap_comp,
    ringHomOfMapsToRationalSubset_comp_toCompletionLoc, comap_comp, Function.comp_apply]

end PairHom

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open TauCeti.ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {SA : Pair A} {SB : Pair B}

/-- For a morphism of Huber pairs `f : SA → SB`, `f.spaComap` maps the subtype preimage of
`R(T'/s')` into the subtype preimage of `R(T/s)` if and only if `comap f.toRingHom` maps
`R(T'/s')` into `R(T/s)`. -/
theorem mapsTo_spaComap_rationalSubset_iff (f : Hom SA SB)
    (T : Finset A) (s : A) (T' : Finset B) (s' : B) :
    Set.MapsTo f.spaComap
      (Subtype.val ⁻¹' rationalSubset SB.plus T' s')
      (Subtype.val ⁻¹' rationalSubset SA.plus T s) ↔
    Set.MapsTo (comap f.toRingHom)
      (rationalSubset SB.plus T' s') (rationalSubset SA.plus T s) :=
  ⟨fun h v hv ↦ by
    simpa only [Set.mem_preimage, spaComap_val] using
      @h ⟨v, rationalSubset_subset_spa SB.plus T' s' hv⟩ hv,
   fun h v hv ↦ by
    simpa only [Set.mem_preimage, spaComap_val] using h hv⟩

end TauCeti.Huber.Pair.Hom

end
