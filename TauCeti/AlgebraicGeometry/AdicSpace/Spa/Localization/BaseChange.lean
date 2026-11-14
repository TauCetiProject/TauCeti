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
# Geometric universal property and base change of rational localisation pairs

`TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset`
establishes Wedhorn's Lemma 8.1 for the underlying coordinate ring `A⟨T/s⟩`: a continuous ring
homomorphism `φ : A →+* B` into a complete Hausdorff Huber pair `(B, B⁺)` whose induced map on
`Spa` lands in `R(T/s)` extends uniquely to a continuous ring homomorphism `A⟨T/s⟩ →+* B`.

This file upgrades Lemma 8.1 to **morphisms of Huber pairs** and deduces the **geometric base
change** of rational localisation pairs:

1. **Plus-ring preservation** (`completedPlusSubring_le_comap_of_forall_comap_mem_rationalSubset`):
   any continuous ring homomorphism `g : A⟨T/s⟩ →+* B` into a Huber ring `B` with ring of integral
   elements `B⁺` whose composite with `A → A⟨T/s⟩` pulls `Spa(B, B⁺)` into `R(T/s)` automatically
   carries `A_U⁺` into `B⁺`, by `comap_mem_spa_completedPlusSubring` and Wedhorn's Proposition
   7.52(1) (`IsRingOfIntegralElements.mem_of_forall_vle_one`).
2. **Bundled Lemma 8.1** (`existsUnique_pairHom_of_forall_comap_mem_rationalSubset`,
   `rationalLocalizationLift`): a morphism `φ : (A, A⁺) → (B, B⁺)` into a complete Hausdorff Huber
   pair whose `spaComap` lands in `R(T/s)` factors uniquely through `toCompletionLocHom`.
3. **Geometric base change of rational localisations** (`rationalLocalizationPairMap`): given an
   arbitrary morphism of Huber pairs `f : (A, A⁺) → (B, B⁺)` (with neither `A` nor `B` assumed
   complete) and rational subsets `R(T'/s') ⊆ Spa(B, B⁺)` and `R(T/s) ⊆ Spa(A, A⁺)` such that
   `f.spaComap` maps `R(T'/s')` into `R(T/s)`, there is a unique morphism of rational localisation
   pairs
   ```text
   (A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_V⁺)
   ```
   compatible with `toCompletionLocHom`. Unlike `completionLocPairMap`, this requires no syntactic
   compatibility `f(s) = s'` or `f(T) ⊆ T'`; when those syntactic conditions hold, the two maps
   coincide (`rationalLocalizationPairMap_eq_completionLocPairMap`), and when `f = id` it recovers
   `ringHomOfRationalSubsetSubset`
   (`toRingHom_rationalLocalizationPairMap_eq_ringHomOfRationalSubsetSubset`).
4. **Adicness** (`isAdicHom_rationalLocalizationPairMap`): when `f` is adic, the induced morphism
   `A⟨T/s⟩ →+* B⟨T'/s'⟩` is adic, by `isAdicHom_toCompletionLoc` and `IsAdicHom.of_comp`.

## Main definitions

* `TauCeti.ValuationSpectrum.rationalLocalizationLift`: the unique morphism of Huber pairs
  `(A⟨T/s⟩, A_U⁺) → (B, B⁺)` extending `φ : (A, A⁺) → (B, B⁺)` when `φ.spaComap` lands in `R(T/s)`.
* `TauCeti.ValuationSpectrum.spaRationalLocalizationPairHomeomorph`: the homeomorphism
  `Spa(A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s)` for the bundled `rationalLocalizationPair`.
* `TauCeti.ValuationSpectrum.rationalLocalizationPairMap`: the functorial morphism of rational
  localisation pairs `(A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_V⁺)` induced by `f : (A, A⁺) → (B, B⁺)` when
  `f.spaComap` maps `R(T'/s')` into `R(T/s)`.

## Main results

* `TauCeti.ValuationSpectrum.completedPlusSubring_le_comap_of_forall_comap_mem_rationalSubset`:
  plus-ring preservation for continuous homomorphisms out of `A⟨T/s⟩`.
* `TauCeti.ValuationSpectrum.pairHom_ext_of_comp_toCompletionLocHom`: morphisms out of a rational
  localisation pair into a Hausdorff Huber pair are determined by their restriction to `(A, A⁺)`.
* `TauCeti.ValuationSpectrum.existsUnique_pairHom_of_forall_comap_mem_rationalSubset`: Wedhorn's
  Lemma 8.1 for Huber pairs.
* `TauCeti.ValuationSpectrum.rationalLocalizationPairMap_id`,
  `TauCeti.ValuationSpectrum.rationalLocalizationPairMap_comp`: functoriality of geometric base
  change.
* `TauCeti.ValuationSpectrum.isAdicHom_rationalLocalizationPairMap`: geometric base change of an
  adic morphism is adic.
* `spaRationalLocalizationPairHomeomorph_spaComap_rationalLocalizationPairMap`: across
  `spaRationalLocalizationPairHomeomorph`, the induced map of adic spectra is the restriction of
  `f.spaComap` from `R(T'/s')` to `R(T/s)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1, Proposition 8.2, and
  Proposition 7.52.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition UniformSpace

/-! ### Plus-ring preservation and Lemma 8.1 for Huber pairs -/

section Lift

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Plus-ring preservation for continuous maps out of `A⟨T/s⟩`.** If `g : A⟨T/s⟩ →+* B` is a
continuous ring homomorphism into a Huber ring `B` with ring of integral elements `B⁺` such that
`g ∘ ρ` pulls every point of `Spa(B, B⁺)` into `R(T/s)`, then `g` maps `A_U⁺` into `B⁺`. Neither
completeness nor separation of `B` is required here. -/
theorem completedPlusSubring_le_comap_of_forall_comap_mem_rationalSubset
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {Bplus : Subring B} (hB : IsRingOfIntegralElements Bplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {g : Completion S →+* B}, Continuous g →
      (∀ w ∈ spa Bplus, comap (g.comp (toCompletionLoc P T s S hden)) w ∈
        rationalSubset Aplus T s) →
      completedPlusSubring P Aplus T s S hden ≤ Bplus.comap g := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro g hg hfac x hx
  refine hB.mem_of_forall_vle_one fun w hw ↦ ?_
  have hmem := comap_mem_spa_completedPlusSubring P Aplus T s S hden g hg
    ((mem_spa_iff Bplus w).mp hw).1 (hfac w hw)
  simpa only [comap_vle, map_one] using ((mem_spa_iff _ _).mp hmem).2 x hx

variable [IsHuberRing A] (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-- Morphisms of Huber pairs out of `(A⟨T/s⟩, A_U⁺)` into a Hausdorff Huber pair are determined by
their composition with `toCompletionLocHom`. -/
theorem pairHom_ext_of_comp_toCompletionLocHom {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] [T2Space B] {V : Pair B} :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ {ψ₁ ψ₂ : Pair.Hom (rationalLocalizationPair P U hP T s S hden) V},
      ψ₁.comp (toCompletionLocHom P U hP T s S hden) =
        ψ₂.comp (toCompletionLocHom P U hP T s S hden) →
      ψ₁ = ψ₂ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro ψ₁ ψ₂ hcomp
  refine Pair.Hom.ext (completion_locTopology_ringHom_ext_of_continuous P (T : Set A) s S hden
    ψ₁.toRingHom ψ₂.toRingHom ψ₁.continuous_toRingHom ψ₂.continuous_toRingHom ?_)
  simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
    congrArg Pair.Hom.toRingHom hcomp

/-- **Wedhorn's Lemma 8.1 for Huber pairs.** Let `(B, B⁺)` be a complete Hausdorff Huber pair and
`φ : (A, A⁺) → (B, B⁺)` a morphism of Huber pairs whose induced map on adic spectra lands in the
rational subset `R(T/s)`. Then `φ` extends uniquely across `toCompletionLocHom` to a morphism of
Huber pairs `(A⟨T/s⟩, A_U⁺) → (B, B⁺)`. -/
theorem existsUnique_pairHom_of_forall_comap_mem_rationalSubset {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
    [CompleteSpace B] [T0Space B] (V : Pair B) (φ : Pair.Hom U V)
    (hfac : ∀ w : spa V.plus, φ.spaComap w ∈ Subtype.val ⁻¹' rationalSubset U.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∃! ψ : Pair.Hom (rationalLocalizationPair P U hP T s S hden) V,
      ψ.comp (toCompletionLocHom P U hP T s S hden) = φ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have hfac' : ∀ w ∈ spa V.plus, comap φ.toRingHom w ∈ rationalSubset U.plus T s := fun w hw ↦ by
    simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hfac ⟨w, hw⟩
  obtain ⟨g, ⟨hg_cont, hg_comp⟩, hg_uniq⟩ :=
    existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P U.plus T s S hden V.plus
      V.isRingOfIntegralElements φ.continuous_toRingHom.continuousAt hfac'
  refine ⟨{
    toRingHom := g
    continuous_toRingHom := hg_cont
    map_mem_plus := by
      rw [rationalLocalizationPair_plus]
      exact completedPlusSubring_le_comap_of_forall_comap_mem_rationalSubset P U.plus T s S hden
        V.isRingOfIntegralElements hg_cont (hg_comp.symm ▸ hfac') }, ?_, ?_⟩
  · refine Pair.Hom.ext ?_
    simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using hg_comp
  · intro ψ hψ
    exact Pair.Hom.ext <| hg_uniq ψ.toRingHom ⟨ψ.continuous_toRingHom, by
      simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
        congrArg Pair.Hom.toRingHom hψ⟩

/-- **The Huber-pair lift across a rational localisation** (Wedhorn's Lemma 8.1): the unique
morphism `(A⟨T/s⟩, A_U⁺) → (B, B⁺)` extending `φ : (A, A⁺) → (B, B⁺)` when `φ.spaComap` lands in
`R(T/s)`. -/
noncomputable def rationalLocalizationLift {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B] [T0Space B]
    {V : Pair B} (φ : Pair.Hom U V)
    (hfac : ∀ w : spa V.plus, φ.spaComap w ∈ Subtype.val ⁻¹' rationalSubset U.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Pair.Hom (rationalLocalizationPair P U hP T s S hden) V :=
  (existsUnique_pairHom_of_forall_comap_mem_rationalSubset P U hP T s S hden V φ hfac).choose

/-- `rationalLocalizationLift` restricts along `toCompletionLocHom` to `φ`. -/
@[simp]
theorem rationalLocalizationLift_comp_toCompletionLocHom {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B] [T0Space B]
    {V : Pair B} (φ : Pair.Hom U V)
    (hfac : ∀ w : spa V.plus, φ.spaComap w ∈ Subtype.val ⁻¹' rationalSubset U.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (rationalLocalizationLift P U hP T s S hden φ hfac).comp
      (toCompletionLocHom P U hP T s S hden) = φ :=
  (existsUnique_pairHom_of_forall_comap_mem_rationalSubset P U hP T s S hden V φ
    hfac).choose_spec.1

/-- The underlying ring homomorphism of `rationalLocalizationLift` restricts along
`toCompletionLoc` to `φ.toRingHom`. -/
@[simp]
theorem toRingHom_rationalLocalizationLift_comp_toCompletionLoc {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B]
    [T0Space B] {V : Pair B} (φ : Pair.Hom U V)
    (hfac : ∀ w : spa V.plus, φ.spaComap w ∈ Subtype.val ⁻¹' rationalSubset U.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (rationalLocalizationLift P U hP T s S hden φ hfac).toRingHom.comp
      (toCompletionLoc P T s S hden) = φ.toRingHom := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
    congrArg Pair.Hom.toRingHom (rationalLocalizationLift_comp_toCompletionLocHom P U hP T s S hden
      φ hfac)

/-- Compatibility with `toCompletionLocHom` uniquely characterizes `rationalLocalizationLift`. -/
theorem eq_rationalLocalizationLift {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B] [T0Space B]
    {V : Pair B} (φ : Pair.Hom U V)
    (hfac : ∀ w : spa V.plus, φ.spaComap w ∈ Subtype.val ⁻¹' rationalSubset U.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ ψ : Pair.Hom (rationalLocalizationPair P U hP T s S hden) V,
      ψ.comp (toCompletionLocHom P U hP T s S hden) = φ →
      ψ = rationalLocalizationLift P U hP T s S hden φ hfac :=
  (existsUnique_pairHom_of_forall_comap_mem_rationalSubset P U hP T s S hden V φ
    hfac).choose_spec.2

/-- The homeomorphism `Spa(A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s)` for the bundled `rationalLocalizationPair`,
transporting `spaCompletedLocalizationHomeomorph` across `rationalLocalizationPair_plus`. -/
noncomputable def spaRationalLocalizationPairHomeomorph :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    spa (rationalLocalizationPair P U hP T s S hden).plus ≃ₜ
      (Subtype.val ⁻¹' rationalSubset U.plus T s : Set (spa U.plus)) :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  (Homeomorph.setCongr (congrArg spa (rationalLocalizationPair_plus P U hP T s S hden))).trans
    (spaCompletedLocalizationHomeomorph P U.plus hP T s S hden)

/-- The underlying valuation in `Spv A` of `spaRationalLocalizationPairHomeomorph … w` is pulled
back along `toCompletionLoc`. -/
@[simp]
theorem spaRationalLocalizationPairHomeomorph_val_val :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ w : spa (rationalLocalizationPair P U hP T s S hden).plus,
      ((spaRationalLocalizationPairHomeomorph P U hP T s S hden w : spa U.plus) : Spv A) =
        comap (toCompletionLoc P T s S hden) w.1 := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro w
  simp only [spaRationalLocalizationPairHomeomorph, Homeomorph.trans_apply,
    Homeomorph.setCongr_apply, spaCompletedLocalizationHomeomorph_apply,
    spaLocToRationalSubset_val, spaComapLoc_val]

/-- Pullback along `spaRationalLocalizationPairHomeomorph` bijects rational subsets of `Spa(A, A⁺)`
contained in `R(T/s)` onto `spaRationalFamily` of `rationalLocalizationPair`. -/
theorem bijOn_preimage_spaRationalLocalizationPairHomeomorph_spaRationalFamily
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Set.BijOn
      (fun W : Set (spa U.plus) ↦
        spaRationalLocalizationPairHomeomorph P U hP T s S hden ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily U.plus | W ⊆ Subtype.val ⁻¹' rationalSubset U.plus T s}
      (spaRationalFamily (rationalLocalizationPair P U hP T s S hden).plus) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have aux : ∀ (Aplus' : Subring (Completion S))
      (h : Aplus' = completedPlusSubring P U.plus T s S hden),
      Set.BijOn
        (fun W : Set (spa U.plus) ↦
          ((Homeomorph.setCongr (congrArg spa h)).trans
            (spaCompletedLocalizationHomeomorph P U.plus hP T s S hden)) ⁻¹' (Subtype.val ⁻¹' W))
        {W ∈ spaRationalFamily U.plus | W ⊆ Subtype.val ⁻¹' rationalSubset U.plus T s}
        (spaRationalFamily Aplus') := by
    rintro _ rfl
    exact bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily P U.plus hP T s hT S
      hden
  exact aux _ (rationalLocalizationPair_plus P U hP T s S hden)

/-- Every point of `Spa(A⟨T/s⟩, A_U⁺)` maps under `(toCompletionLocHom …).spaComap` into the
rational subset `R(T/s)`. -/
theorem toCompletionLocHom_spaComap_mem_rationalSubset :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∀ w : spa (rationalLocalizationPair P U hP T s S hden).plus,
      (toCompletionLocHom P U hP T s S hden).spaComap w ∈
        Subtype.val ⁻¹' rationalSubset U.plus T s := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  intro w
  change ((toCompletionLocHom P U hP T s S hden).spaComap w).1 ∈ rationalSubset U.plus T s
  rw [Pair.Hom.spaComap_val, toRingHom_toCompletionLocHom]
  simpa only [spaComapLoc_val] using spaComapLoc_mem_rationalSubset P U.plus T s S hden
    ⟨w.1, rationalLocalizationPair_plus P U hP T s S hden ▸ w.2⟩

end Lift

/-! ### Geometric base change of rational localisation pairs -/

section BaseChange

variable {A B C : Type*}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- `f.spaComap` maps the rational subset `R(T'/s')` of `Spa(B, B⁺)` into `R(T/s) ⊆ Spa(A, A⁺)`
if and only if `R(T'/s')` is contained in `comap f ⁻¹' R(T/s)` in `Spv B`. -/
theorem mapsTo_spaComap_rationalSubset_iff {U : Pair A} {U' : Pair B} (f : Pair.Hom U U')
    (T : Finset A) (s : A) (T' : Finset B) (s' : B) :
    Set.MapsTo f.spaComap (Subtype.val ⁻¹' rationalSubset U'.plus T' s')
        (Subtype.val ⁻¹' rationalSubset U.plus T s) ↔
      rationalSubset U'.plus T' s' ⊆ comap f.toRingHom ⁻¹' rationalSubset U.plus T s := by
  constructor
  · intro hf v hv
    have hv_spa : v ∈ spa U'.plus := rationalSubset_subset_spa U'.plus T' s' hv
    simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hf (x := ⟨v, hv_spa⟩) hv
  · intro hsub x hx
    simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hsub hx

variable (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

section Map

variable (P' : PairOfDefinition B) (U' : Pair B) (hP' : P'.ringOfDefinition ≤ U'.plus)
  (f : Pair.Hom U U') (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (hf : Set.MapsTo f.spaComap (Subtype.val ⁻¹' rationalSubset U'.plus T' s')
    (Subtype.val ⁻¹' rationalSubset U.plus T s))

include hf

/-- **Geometric base change of rational localisation pairs.** Given `f : (A, A⁺) → (B, B⁺)` such
that `f.spaComap` maps `R(T'/s')` into `R(T/s)`, this is the unique morphism of Huber pairs
`(A⟨T/s⟩, A_U⁺) → (B⟨T'/s'⟩, B_V⁺)` compatible with `toCompletionLocHom`. Neither `A` nor `B` is
assumed complete. -/
noncomputable def rationalLocalizationPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    Pair.Hom (rationalLocalizationPair P U hP T s S hden)
      (rationalLocalizationPair P' U' hP' T' s' S' hden') :=
  letI := locUniformSpace P' T' s' S' hden'
  letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  letI := isHuberRing_completion_locTopology P' T' s' S' hden'
  rationalLocalizationLift P U hP T s S hden
    ((toCompletionLocHom P' U' hP' T' s' S' hden').comp f)
    (fun w ↦ by
      rw [Pair.Hom.spaComap_comp, Function.comp_apply]
      exact hf (toCompletionLocHom_spaComap_mem_rationalSubset P' U' hP' T' s' S' hden' w))

/-- `rationalLocalizationPairMap` commutes with `toCompletionLocHom`. -/
@[simp]
theorem rationalLocalizationPairMap_comp_toCompletionLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf).comp
        (toCompletionLocHom P U hP T s S hden) =
      (toCompletionLocHom P' U' hP' T' s' S' hden').comp f := by
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  exact rationalLocalizationLift_comp_toCompletionLocHom P U hP T s S hden _ _

/-- The underlying ring homomorphism of `rationalLocalizationPairMap` commutes with
`toCompletionLoc`. -/
@[simp]
theorem toRingHom_rationalLocalizationPairMap_comp_toCompletionLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf).toRingHom.comp
        (toCompletionLoc P T s S hden) =
      (toCompletionLoc P' T' s' S' hden').comp f.toRingHom := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
    congrArg Pair.Hom.toRingHom
      (rationalLocalizationPairMap_comp_toCompletionLocHom P U hP T s S hden P' U' hP' f T' s' S'
        hden' hf)

/-- Pointwise evaluation of `rationalLocalizationPairMap` on elements from `A`. -/
@[simp]
theorem rationalLocalizationPairMap_algebraMap (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf).toRingHom
        (algebraMap A S a : Completion S) =
      (algebraMap B S' (f.toRingHom a) : Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  rw [← toCompletionLoc_apply P T s S hden, ← toCompletionLoc_apply P' T' s' S' hden']
  exact RingHom.congr_fun
    (toRingHom_rationalLocalizationPairMap_comp_toCompletionLoc P U hP T s S hden P' U' hP' f T' s'
      S' hden' hf) a

/-- Compatibility with `toCompletionLocHom` uniquely determines `rationalLocalizationPairMap`. -/
theorem eq_rationalLocalizationPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    ∀ ψ : Pair.Hom (rationalLocalizationPair P U hP T s S hden)
        (rationalLocalizationPair P' U' hP' T' s' S' hden'),
      ψ.comp (toCompletionLocHom P U hP T s S hden) =
        (toCompletionLocHom P' U' hP' T' s' S' hden').comp f →
      ψ = rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf := by
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  exact eq_rationalLocalizationLift P U hP T s S hden _ _

/-- **Geometric base change of an adic morphism is adic.** If `f : (A, A⁺) → (B, B⁺)` has an adic
underlying ring homomorphism, then the induced homomorphism `A⟨T/s⟩ →+* B⟨T'/s'⟩` is also adic. -/
theorem isAdicHom_rationalLocalizationPairMap [IsAdicHom f.toRingHom] :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    IsAdicHom
      (rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf).toRingHom := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  set ψ := rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf
  have hadic : IsAdicHom (ψ.toRingHom.comp (toCompletionLoc P T s S hden)) := by
    rw [toRingHom_rationalLocalizationPairMap_comp_toCompletionLoc]
    exact (isAdicHom_toCompletionLoc P' T' s' S' hden').comp inferInstance
  exact IsAdicHom.of_comp hadic (continuous_toCompletionLoc P T s S hden) ψ.continuous_toRingHom

/-- When `f(s) = s'` and `f(T) ⊆ T'`, `rationalLocalizationPairMap` coincides with the syntactic
base change `completionLocPairMap`. -/
theorem rationalLocalizationPairMap_eq_completionLocPairMap (hs : f.toRingHom s = s')
    (hT : ∀ t ∈ T, f.toRingHom t ∈ T') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf =
      completionLocPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hs hT := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  exact (eq_rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf _
    (completionLocPairMap_comp_toCompletionLocHom P U hP T s S hden P' U' hP' f T' s' S' hden' hs
      hT)).symm

/-- Across `spaRationalLocalizationPairHomeomorph`, `(rationalLocalizationPairMap …).spaComap` is
the restriction `hf.restrict f.spaComap …` of `f.spaComap` from `R(T'/s')` to `R(T/s)`. -/
theorem spaRationalLocalizationPairHomeomorph_spaComap_rationalLocalizationPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    ∀ w : spa (rationalLocalizationPair P' U' hP' T' s' S' hden').plus,
      spaRationalLocalizationPairHomeomorph P U hP T s S hden
          ((rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf).spaComap
            w) =
        hf.restrict f.spaComap _ _
          (spaRationalLocalizationPairHomeomorph P' U' hP' T' s' S' hden' w) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  refine fun w ↦ Subtype.ext (Subtype.ext ?_)
  change (spaRationalLocalizationPairHomeomorph P U hP T s S hden
      ((rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf).spaComap
        w)).1.1 =
    (f.spaComap (spaRationalLocalizationPairHomeomorph P' U' hP' T' s' S' hden' w).1).1
  simp only [spaRationalLocalizationPairHomeomorph_val_val, Pair.Hom.spaComap_val]
  rw [← Function.comp_apply (f := comap (toCompletionLoc P T s S hden)), ← comap_comp,
    toRingHom_rationalLocalizationPairMap_comp_toCompletionLoc, comap_comp, Function.comp_apply]

/-- Geometric base change is functorial with respect to composition of morphisms of Huber pairs. -/
@[simp]
theorem rationalLocalizationPairMap_comp
    (P'' : PairOfDefinition C) (U'' : Pair C) (hP'' : P''.ringOfDefinition ≤ U''.plus)
    (g : Pair.Hom U' U'') (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
    [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P'' T'' s'' S'')
    (hg : Set.MapsTo g.spaComap (Subtype.val ⁻¹' rationalSubset U''.plus T'' s'')
      (Subtype.val ⁻¹' rationalSubset U'.plus T' s')) :
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
    (rationalLocalizationPairMap P' U' hP' T' s' S' hden' P'' U'' hP'' g T'' s'' S'' hden''
        hg).comp
      (rationalLocalizationPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hf) =
      rationalLocalizationPairMap P U hP T s S hden P'' U'' hP'' (g.comp f) T'' s'' S'' hden''
        (by rw [Pair.Hom.spaComap_comp]; exact hf.comp hg) := by
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
  refine eq_rationalLocalizationPairMap P U hP T s S hden P'' U'' hP'' (g.comp f) T'' s'' S''
    hden'' (by rw [Pair.Hom.spaComap_comp]; exact hf.comp hg) _ ?_
  rw [Pair.Hom.comp_assoc, rationalLocalizationPairMap_comp_toCompletionLocHom,
    ← Pair.Hom.comp_assoc, rationalLocalizationPairMap_comp_toCompletionLocHom, Pair.Hom.comp_assoc]

end Map

/-- Geometric base change of the identity morphism on the same presentation is the identity. -/
@[simp]
theorem rationalLocalizationPairMap_id
    (hid : Set.MapsTo (Pair.Hom.id U).spaComap (Subtype.val ⁻¹' rationalSubset U.plus T s)
      (Subtype.val ⁻¹' rationalSubset U.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    rationalLocalizationPairMap P U hP T s S hden P U hP (Pair.Hom.id U) T s S hden hid =
      Pair.Hom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  exact (eq_rationalLocalizationPairMap P U hP T s S hden P U hP (Pair.Hom.id U) T s S hden hid
    (Pair.Hom.id _) (by rw [Pair.Hom.id_comp, Pair.Hom.comp_id])).symm

/-- For the identity morphism on `(A, A⁺)`, the underlying ring homomorphism of
`rationalLocalizationPairMap` recovers `ringHomOfRationalSubsetSubset`. -/
theorem toRingHom_rationalLocalizationPairMap_eq_ringHomOfRationalSubsetSubset
    (T₁ : Finset A) (s₁ : A) (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away s₁ S₁]
    (hden₁ : HasDenominatorPower P T₁ s₁ S₁)
    (hsub : rationalSubset U.plus T₁ s₁ ⊆ rationalSubset U.plus T s)
    (hid : Set.MapsTo (Pair.Hom.id U).spaComap (Subtype.val ⁻¹' rationalSubset U.plus T₁ s₁)
      (Subtype.val ⁻¹' rationalSubset U.plus T s)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P T₁ s₁ S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P T₁ s₁ S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P T₁ s₁ S₁ hden₁
    letI := isHuberRing_completion_locTopology P T₁ s₁ S₁ hden₁
    (rationalLocalizationPairMap P U hP T s S hden P U hP (Pair.Hom.id U) T₁ s₁ S₁ hden₁
      hid).toRingHom =
      ringHomOfRationalSubsetSubset P U.plus
        U.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden T₁ s₁ S₁ hden₁ hsub := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P T₁ s₁ S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P T₁ s₁ S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P T₁ s₁ S₁ hden₁
  have _ := isHuberRing_completion_locTopology P T₁ s₁ S₁ hden₁
  refine completion_locTopology_ringHom_ext_of_continuous P (T : Set A) s S hden _ _
    (rationalLocalizationPairMap P U hP T s S hden P U hP (Pair.Hom.id U) T₁ s₁ S₁ hden₁
      hid).continuous_toRingHom
    (by
      rw [← pairHomOfRationalSubsetSubset_toRingHom (hIplus := fun j _ ↦ hP j.2)]
      exact (pairHomOfRationalSubsetSubset P U.plus (fun j _ ↦ hP j.2)
        U.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden T₁ s₁ S₁ hden₁
        hsub).continuous_toRingHom) ?_
  rw [toRingHom_rationalLocalizationPairMap_comp_toCompletionLoc, Pair.Hom.toRingHom_id,
    RingHom.comp_id,
    ringHomOfRationalSubsetSubset_comp_toCompletionLoc P U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden T₁ s₁ S₁ hden₁ hsub]

end BaseChange

end TauCeti.ValuationSpectrum

end
