/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Extension
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Normal
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.RingTheory.CohenMacaulay.Normal
import TauCeti.RingTheory.Japanese
import TauCeti.RingTheory.IntegralClosure.ReducedArtinian
import TauCeti.RingTheory.Localization.Integral

/-!
# Finite normal algebras and covers of the punctured spectrum

Let `A` be a Noetherian local ring with maximal ideal `𝔪` and punctured spectrum
`U = Spec A ∖ {𝔪}`. A *finite normal punctured-étale* `A`-algebra is a finite `A`-algebra `B`
which is normal (every localization at a prime is an integrally closed domain), torsion free as
an `A`-module, and étale over `A` at every prime not lying over `𝔪`. Restricting `Spec B` to `U`
gives a finite étale cover of `U`, and this is functorial in `B`, contravariantly.

When `A` is an integrally closed domain of dimension at least two, this restriction functor is
fully faithful. The reason is the algebraic Hartogs property: `B` is recovered as the ring of
functions on the preimage of `U` in `Spec B`
(`TauCeti.IsLocalRing.isIso_appTop_pullback_fst_puncturedSpectrum`), so every
morphism over `U` between restrictions extends uniquely across the closed fibre
(`TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop`).

When `A` is an integrally closed domain, of any dimension, the functor is also essentially
surjective. In dimension at least two, for a finite étale cover `V` of `U`, the ring of sections
`B = Γ(V, 𝒪_V)` is finite and torsion free over `A` (`TauCeti.IsLocalRing.finite_sections`), and
`V` is the restriction of `Spec B` (`TauCeti.IsLocalRing.isPullback_puncturedSpectrum_toSpecΓ`).
Hence `B` is étale over `A` at the primes over `U`, and restriction of sections from `Spec B` to
the preimage of `U` is bijective, so `B` is normal by the algebraic Hartogs argument of
`TauCeti.AlgebraicGeometry.Spec.isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt`.
In dimension at most one the sections need not be finite: for a discrete valuation ring `U` is
the generic point and `Γ(V, 𝒪_V)` is a finite étale algebra `L` over the fraction field. Instead
`U` is a basic open `D(t)` (`TauCeti.IsLocalRing.exists_puncturedSpectrum_eq_basicOpen`), `L` is
finite étale over `A_t`, and `B` is the integral closure of `A` in `L`. As `A_t` is the fraction
field of `A` or the zero ring, `B` is finite over `A`
(`TauCeti.Ring.finite_integralClosure_of_etale`) and normal, being integrally closed in the
reduced Artinian ring `L` (`IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime`).
Finally `L = A_t ⊗[A] B`, so `V` is the restriction of `Spec B`
(`TauCeti.AlgebraicGeometry.Spec.isPullback_toSpecΓ_of_isPushout`).

Together these give the anti-equivalence between finite étale covers of `U` and finite normal
punctured-étale `A`-algebras (Stacks, Lemma 58.20.3 (0BM9)). Torsion freeness is needed and is
missing from the Stacks statement: for `A` normal of dimension at least two, the algebra
`A × A/𝔪` is finite, normal and étale away from `𝔪`, but its restriction to `U` is that of `A`,
so the functor would not be faithful on it.

If purity holds for `A` (`TauCeti.IsLocalRing.PurityHolds A`), every finite étale cover of `U`
extends to a finite étale scheme over `Spec A`, so its ring of sections is finite étale over `A`
when `A` has depth at least two (Stacks, Lemma 58.20.2 (0BLK)). When a finite algebra `B`, étale
at every prime not lying over `𝔪`, is recovered from its sections over the preimage of `U`, this
shows that `B` itself is étale over `A`. For a finite torsion-free algebra `B` whose localizations
at maximal ideals are normal domains, over a Noetherian normal local domain `A` of dimension at
least two, both the depth bound and the recovery of `B` from its sections hold. So purity for the
punctured spectrum of `A` implies purity for finite normal `A`-algebras: this is how part (2) of
Stacks, Lemma 58.21.3 (0BMA), purity for regular local rings in its algebraic form, follows from
part (1), purity of the punctured spectrum. Conversely, by essential surjectivity, purity for
finite normal `A`-algebras implies purity for `A`.

## Main definitions

* `TauCeti.IsLocalRing.finiteNormalPuncturedEtale`: the finite normal torsion-free `A`-algebras
  which are étale at every prime not over the maximal ideal.
* `TauCeti.IsLocalRing.FiniteNormalPuncturedEtaleAlg`: the full subcategory of `CommAlgCat A` on
  these algebras.
* `TauCeti.IsLocalRing.restrictPuncturedSpec`: the functor sending `B` to the restriction of
  `Spec B` to the punctured spectrum.
* `TauCeti.IsLocalRing.sectionsAlg`: the ring of sections of a finite étale cover of the
  punctured spectrum, as a finite normal punctured-étale algebra.
* `TauCeti.IsLocalRing.sectionsAlgMap`: restriction of sections along a morphism of finite étale
  covers of the punctured spectrum.
* `TauCeti.IsLocalRing.restrictPuncturedSpecSectionsAlgIso`: a finite étale cover of the
  punctured spectrum is the restriction of the spectrum of its ring of sections.
* `TauCeti.IsLocalRing.finiteNormalEquiv`: the inverse equivalence of `restrictPuncturedSpec`,
  from finite étale covers of the punctured spectrum to finite normal punctured-étale algebras,
  sending a cover to its ring of sections and a morphism to restriction of sections.

## Main results

* `TauCeti.IsLocalRing.etale_pullback_snd_puncturedSpectrum`: the restriction of `Spec B` to the
  punctured spectrum is étale if `B` is finitely presented and étale at every prime not over the
  maximal ideal.
* `TauCeti.IsLocalRing.isEtaleAt_of_isPullback_puncturedSpectrum`: conversely, if an étale
  scheme over the punctured spectrum is the restriction of `Spec B`, then `B` is étale at every
  prime not over the maximal ideal.
* `TauCeti.IsLocalRing.restrictPuncturedSpec.fullyFaithful`: restriction to the punctured spectrum
  is fully faithful on finite normal punctured-étale algebras.
* `TauCeti.IsLocalRing.finiteNormalPuncturedEtale_sections`: the ring of sections of a finite
  étale cover of the punctured spectrum is a finite normal punctured-étale algebra.
* `TauCeti.IsLocalRing.restrictPuncturedSpec_essSurj`: over a Noetherian normal local domain of
  any dimension, every finite étale cover of the punctured spectrum is the restriction of a finite
  normal punctured-étale algebra.
* `TauCeti.Algebra.etale_of_finiteNormal_of_purityHolds`: over a Noetherian normal local domain of
  dimension at least two for which purity holds, a finite torsion-free algebra with normal
  localizations at maximal ideals, étale at every prime not lying over the closed point, is
  étale.
* `TauCeti.IsLocalRing.purityHolds_iff_forall_etale`: over a Noetherian normal local domain of
  dimension at least two, purity holds if and only if every finite normal punctured-étale algebra
  is étale.

## References

* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
* [The Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The finite `A`-algebras `B` which are normal (every localization at a prime is an integrally
closed domain), torsion free as `A`-modules, and étale over `A` at every prime not lying over the
maximal ideal of `A`. -/
def finiteNormalPuncturedEtale : ObjectProperty (CommAlgCat.{u} A) := fun B ↦
  Module.Finite A B ∧ Module.IsTorsionFree A B ∧
    (∀ (𝔮 : Ideal B) [𝔮.IsPrime],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮)) ∧
    ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A 𝔮

/-- Unfolding of `finiteNormalPuncturedEtale`. -/
theorem finiteNormalPuncturedEtale_iff (B : CommAlgCat.{u} A) :
    finiteNormalPuncturedEtale A B ↔
      Module.Finite A B ∧ Module.IsTorsionFree A B ∧
        (∀ (𝔮 : Ideal B) [𝔮.IsPrime],
          IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮)) ∧
        ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A 𝔮 :=
  Iff.rfl

/-- Finite normal torsion-free `A`-algebras étale away from the maximal ideal, with all
`A`-algebra homomorphisms as morphisms. -/
abbrev FiniteNormalPuncturedEtaleAlg := (finiteNormalPuncturedEtale A).FullSubcategory

variable {A} in
/-- If `B` is finitely presented over `A` and étale over `A` at every prime not lying over the
maximal ideal, then the restriction of `Spec B ⟶ Spec A` to the punctured spectrum is étale. -/
theorem etale_pullback_snd_puncturedSpectrum {B : Type u} [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B]
    (h : ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A 𝔮) :
    Etale (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (puncturedSpectrum A).ι) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  set U := puncturedSpectrum A
  -- Instance search does not derive this from `HasRingHomProperty @Etale RingHom.Etale` by itself.
  have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  suffices Etale (pullback.fst g U.ι ≫ g) by
    rw [pullback.condition] at this
    exact Etale.of_comp _ U.ι
  -- Each point lies over a prime of `B` not over the maximal ideal, where `g` is étale nearby.
  have key (x : ↑(pullback g U.ι)) : ∃ V : (pullback g U.ι).Opens,
      x ∈ V ∧ Etale (V.ι ≫ pullback.fst g U.ι ≫ g) := by
    let q : PrimeSpectrum B := pullback.fst g U.ι x
    have hq : g q ∈ U := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact (pullback.snd g U.ι x).property
    obtain ⟨O, hqO, hO⟩ := (Scheme.Hom.etaleAt_spec_iff q).mpr <| h q.asIdeal fun he ↦
      (mem_puncturedSpectrum_iff A (g q)).mp hq (PrimeSpectrum.ext he)
    refine ⟨pullback.fst g U.ι ⁻¹ᵁ O, hqO, ?_⟩
    have : IsOpenImmersion ((pullback.fst g U.ι).resLE O _ le_rfl) := by
      have : IsOpenImmersion ((pullback.fst g U.ι).resLE O _ le_rfl ≫ O.ι) := by
        rw [Scheme.Hom.resLE_comp_ι]
        infer_instance
      exact .of_comp _ O.ι
    rw [← Scheme.Hom.resLE_comp_ι_assoc (e := le_rfl)]
    exact IsZariskiLocalAtSource.comp hO _
  exact IsZariskiLocalAtSource.of_forall_exists_ι_comp key

variable {A} in
/-- If an étale scheme `V` over the punctured spectrum is the restriction of `Spec B ⟶ Spec A` for
a finitely presented `A`-algebra `B`, then `B` is étale over `A` at every prime not lying over the
maximal ideal. This is a converse of `etale_pullback_snd_puncturedSpectrum`. -/
theorem isEtaleAt_of_isPullback_puncturedSpectrum {B : Type u} [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] {V : Scheme.{u}} {f : V ⟶ (puncturedSpectrum A).toScheme}
    [Etale f] {i : V ⟶ Spec (.of B)}
    (hpb : IsPullback f i (puncturedSpectrum A).ι (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮.under A ≠ maximalIdeal A) : Algebra.IsEtaleAt A 𝔮 := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  set U := puncturedSpectrum A
  -- Instance search does not derive `RespectsIso` for `Etale` at a fixed universe.
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- The restriction of `g` over `U` is isomorphic to the étale `f`.
  have : Etale (g ∣_ U) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale
      (hpb.isoIsPullback _ _ (isPullback_morphismRestrict g U)).hom, hpb.isoIsPullback_hom_fst]
    infer_instance
  exact (Scheme.Hom.etaleAt_spec_iff ⟨𝔮, ‹_›⟩).mp <| not_not.mp <|
    mt Scheme.Hom.mem_nonEtaleLocus_iff.mpr <| Set.disjoint_left.mp
      ((g.etale_morphismRestrict_iff U).mp this) ((mem_preimage_puncturedSpectrum_iff A _).mpr h𝔮)

variable [IsNoetherianRing A]

/-- Restriction to the punctured spectrum, as a functor from finite normal torsion-free
`A`-algebras étale away from the maximal ideal to finite étale covers of the punctured spectrum.
It sends `B` to the base change of `Spec B ⟶ Spec A` along the inclusion of the punctured
spectrum. -/
@[expose] def restrictPuncturedSpec :
    (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ ⥤ FiniteEtaleScheme (puncturedSpectrum A).toScheme :=
  (finiteEtaleSchemeProperty _).lift
    ((finiteNormalPuncturedEtale A).ι.op ⋙ algSpec (.of A) ⋙
      Over.pullback (puncturedSpectrum A).ι) fun B ↦ by
    obtain ⟨hfin, -, -, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.unop.property
    have : Algebra.FinitePresentation A B.unop.obj :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B.unop.obj))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
    have hfin' : IsFinite (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B.unop.obj)))
        (puncturedSpectrum A).ι) := inferInstance
    simp only [finiteEtaleSchemeProperty_iff, Functor.comp_obj, Over.pullback_obj_hom,
      algSpec_obj_hom, Functor.op_obj, ObjectProperty.ι_obj]
    exact ⟨hfin', etale_pullback_snd_puncturedSpectrum (B := B.unop.obj) het⟩

/-- Forgetting finiteness and étaleness, `restrictPuncturedSpec` is Mathlib's `algSpec` followed
by base change to the punctured spectrum. -/
theorem restrictPuncturedSpec_comp_ι :
    restrictPuncturedSpec A ⋙ (finiteEtaleSchemeProperty _).ι =
      (finiteNormalPuncturedEtale A).ι.op ⋙ algSpec (.of A) ⋙
        Over.pullback (puncturedSpectrum A).ι :=
  (rfl)

/-- The scheme over the punctured spectrum underlying `restrictPuncturedSpec A B` is the base
change of `Spec B` along the inclusion of the punctured spectrum. -/
@[simp]
theorem restrictPuncturedSpec_obj_obj (B : (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ) :
    ((restrictPuncturedSpec A).obj B).obj =
      (Over.pullback (puncturedSpectrum A).ι).obj ((algSpec (.of A)).obj (.op B.unop.obj)) :=
  (rfl)

/-- On morphisms, `restrictPuncturedSpec` is `algSpec` followed by base change to the punctured
spectrum. -/
@[simp]
theorem restrictPuncturedSpec_map_hom {B C : (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ} (f : B ⟶ C) :
    ((restrictPuncturedSpec A).map f).hom =
      (Over.pullback (puncturedSpectrum A).ι).map
        ((algSpec (.of A)).map ((finiteNormalPuncturedEtale A).ι.op.map f)) :=
  (rfl)

variable {A}

private theorem restrictPuncturedSpec_map_bijective [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) (B C : (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ) :
    Function.Bijective ((restrictPuncturedSpec A).map : (B ⟶ C) → _) := by
  obtain ⟨_, _, hnormal, -⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.unop.property
  have : IsAffine ((algSpec (.of A)).obj (.op C.unop.obj)).left := isAffine_Spec _
  -- `restrictPuncturedSpec` is `algSpec` followed by base change, up to full subcategories.
  have h₁ := (((finiteNormalPuncturedEtale A).fullyFaithfulι.op).comp
    (algSpec.fullyFaithful (R := .of A))).map_bijective B C
  have h₂ := TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop
    (puncturedSpectrum A).ι (Y := (algSpec (.of A)).obj (.op B.unop.obj))
    (Y' := (algSpec (.of A)).obj (.op C.unop.obj))
    (by
      rw [algSpec_obj_hom]
      exact isIso_appTop_pullback_fst_puncturedSpectrum A hdim fun 𝔮 _ ↦ hnormal 𝔮)
  have hcomp : ((finiteEtaleSchemeProperty _).ι.map ∘ (restrictPuncturedSpec A).map :
      (B ⟶ C) → _) = (fun g ↦ (Over.pullback (puncturedSpectrum A).ι).map g) ∘
        ((finiteNormalPuncturedEtale A).ι.op ⋙ algSpec (.of A)).map := by
    funext f
    simp only [Function.comp_apply, ObjectProperty.ι_map, Functor.comp_map]
    exact restrictPuncturedSpec_map_hom A f
  rw [← Function.Bijective.of_comp_iff'
    ((finiteEtaleSchemeProperty _).fullyFaithfulι.map_bijective _ _), hcomp]
  exact h₂.comp h₁

/-- Over a Noetherian integrally closed local domain of dimension at least two, restriction to
the punctured spectrum is fully faithful on finite normal torsion-free algebras étale away from
the maximal ideal: morphisms over the punctured spectrum between the restrictions of `Spec C` and
`Spec B` correspond to `A`-algebra homomorphisms `B ⟶ C`. -/
@[stacks 0BM9 "full faithfulness, with `B` torsion free"]
def restrictPuncturedSpec.fullyFaithful [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) : (restrictPuncturedSpec A).FullyFaithful where
  preimage {B C} := (Equiv.ofBijective _ (restrictPuncturedSpec_map_bijective hdim B C)).symm
  map_preimage {B C} :=
    (Equiv.ofBijective _ (restrictPuncturedSpec_map_bijective hdim B C)).apply_symm_apply
  preimage_map {B C} :=
    (Equiv.ofBijective _ (restrictPuncturedSpec_map_bijective hdim B C)).symm_apply_apply

variable [IsDomain A] [IsIntegrallyClosed A]

/-- Let `A` be a Noetherian integrally closed local domain of dimension at least two and `V` a
finite étale cover of its punctured spectrum. The ring of sections `Γ(V, 𝒪_V)`, an `A`-algebra
through `V ⟶ U ⟶ Spec A`, is a finite normal torsion-free `A`-algebra which is étale over `A` at
every prime not lying over the maximal ideal. -/
theorem finiteNormalPuncturedEtale_sections (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
    finiteNormalPuncturedEtale A (.of A Γ(V.obj.left, ⊤)) := by
  set φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
  let := φ.hom.toAlgebra
  let U := puncturedSpectrum A
  let B := Γ(V.obj.left, ⊤)
  let g := Spec.map φ
  have hdepth := two_le_depth_of_isIntegrallyClosed hdim
  have : Module.Finite A B := finite_sections A hdepth V
  have : Module.IsTorsionFree A B := isTorsionFree_sections A V
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- Over `U`, the morphism `Spec B ⟶ Spec A` is the finite étale `V ⟶ U`.
  have hpb := isPullback_puncturedSpectrum_toSpecΓ A hdepth V.obj.hom
  let e := hpb.isoIsPullback _ _ (isPullback_morphismRestrict g U)
  -- As `V ≅ W` over `Spec B`, restriction of sections from `Spec B` to `W` is bijective.
  have hbij : Function.Bijective (g ⁻¹ᵁ U).ι.appTop := by
    have : IsIso ((g ⁻¹ᵁ U).ι.appTop ≫ e.hom.appTop) := by
      rw [← Scheme.Hom.comp_appTop, hpb.isoIsPullback_hom_snd, Scheme.toSpecΓ_appTop]
      infer_instance
    -- Instance search knows that isomorphisms induce isomorphisms on `app ⊤ = appTop`.
    have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact (ConcreteCategory.isIso_iff_bijective _).mp (IsIso.of_isIso_comp_right _ e.hom.appTop)
  rw [Scheme.Opens.ι_appTop] at hbij
  -- So `B` is étale over `A` at every point of the preimage `W` of `U` in `Spec B`.
  have het (q : PrimeSpectrum B) (hq : q ∈ (g ⁻¹ᵁ U).ι ''ᵁ ⊤) : Algebra.IsEtaleAt A q.asIdeal :=
    isEtaleAt_of_isPullback_puncturedSpectrum hpb q.asIdeal
      ((mem_preimage_puncturedSpectrum_iff A q).mp (by rwa [Scheme.Opens.ι_image_top] at hq))
  exact ⟨inferInstance, inferInstance, fun 𝔮 _ ↦
    AlgebraicGeometry.Spec.isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt
      _ het hbij 𝔮, fun 𝔮 _ h𝔮 ↦ isEtaleAt_of_isPullback_puncturedSpectrum hpb 𝔮 h𝔮⟩

/-- The ring of sections `Γ(V, 𝒪_V)` of a finite étale cover `V` of the punctured spectrum, an
`A`-algebra through `V ⟶ U ⟶ Spec A`, as a finite normal punctured-étale `A`-algebra
(`finiteNormalPuncturedEtale_sections`). -/
@[expose] def sectionsAlg (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) : FiniteNormalPuncturedEtaleAlg A :=
  letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
    (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
  ⟨.of A Γ(V.obj.left, ⊤), finiteNormalPuncturedEtale_sections hdim V⟩

/-- The algebra underlying `sectionsAlg hdim V` is `Γ(V, 𝒪_V)`. -/
@[simp]
theorem sectionsAlg_obj (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (sectionsAlg hdim V).obj =
      letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
        (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
      CommAlgCat.of A Γ(V.obj.left, ⊤) :=
  (rfl)

/-- The `A`-algebra homomorphism `Γ(W, 𝒪_W) ⟶ Γ(V, 𝒪_V)` of rings of sections induced by a
morphism `f : V ⟶ W` of finite étale covers of the punctured spectrum, given by Mathlib's
algebra-valued global sections functor `algΓ`. -/
def sectionsAlgMap (hdim : 2 ≤ ringKrullDim A)
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme} (f : V ⟶ W) :
    sectionsAlg hdim W ⟶ sectionsAlg hdim V :=
  ObjectProperty.homMk ((algΓ (.of A)).map ((Over.map (puncturedSpectrum A).ι).map f.hom)).unop

/-- `sectionsAlgMap hdim f` is restriction of sections along `f`. -/
@[simp]
theorem sectionsAlgMap_hom_apply (hdim : 2 ≤ ringKrullDim A)
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme} (f : V ⟶ W) (x : Γ(W.obj.left, ⊤)) :
    (sectionsAlgMap hdim f).hom.hom x = f.hom.left.appTop.hom x :=
  (rfl)

/-- Restriction of sections along the identity is the identity. -/
@[simp]
theorem sectionsAlgMap_id (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    sectionsAlgMap hdim (𝟙 V) = 𝟙 _ := by
  ext; rfl

/-- Restriction of sections along a composite `f ≫ g` is restriction along `g` followed by
restriction along `f`. -/
@[simp, reassoc]
theorem sectionsAlgMap_comp (hdim : 2 ≤ ringKrullDim A)
    {V W X : FiniteEtaleScheme (puncturedSpectrum A).toScheme} (f : V ⟶ W) (g : W ⟶ X) :
    sectionsAlgMap hdim (f ≫ g) = sectionsAlgMap hdim g ≫ sectionsAlgMap hdim f := by
  ext; rfl

/-- A finite étale cover `V` of the punctured spectrum is the restriction of the spectrum of its
ring of sections `sectionsAlg hdim V`. -/
def restrictPuncturedSpecSectionsAlgIso (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (restrictPuncturedSpec A).obj (.op (sectionsAlg hdim V)) ≅ V :=
  let h := (isPullback_puncturedSpectrum_toSpecΓ A (two_le_depth_of_isIntegrallyClosed hdim)
    V.obj.hom).flip
  ObjectProperty.isoMk _ (Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd)

/-- The first component of `V ⟶ Spec Γ(V, 𝒪_V) ×_{Spec A} U`, the inverse of
`restrictPuncturedSpecSectionsAlgIso`, is the canonical morphism `V ⟶ Spec Γ(V, 𝒪_V)`. -/
@[simp]
theorem restrictPuncturedSpecSectionsAlgIso_inv_hom_left_fst (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (restrictPuncturedSpecSectionsAlgIso hdim V).inv.hom.left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (sectionsAlg hdim V).obj)))
          (puncturedSpectrum A).ι =
      V.obj.left.toSpecΓ :=
  IsPullback.isoPullback_hom_fst _

/-- The second component of `V ⟶ Spec Γ(V, 𝒪_V) ×_{Spec A} U`, the inverse of
`restrictPuncturedSpecSectionsAlgIso`, is the structure morphism `V ⟶ U`. -/
@[simp]
theorem restrictPuncturedSpecSectionsAlgIso_inv_hom_left_snd (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (restrictPuncturedSpecSectionsAlgIso hdim V).inv.hom.left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A (sectionsAlg hdim V).obj)))
          (puncturedSpectrum A).ι =
      V.obj.hom :=
  IsPullback.isoPullback_hom_snd _

/-- The isomorphisms `restrictPuncturedSpecSectionsAlgIso` are natural in the cover. -/
@[reassoc]
theorem restrictPuncturedSpecSectionsAlgIso_hom_naturality (hdim : 2 ≤ ringKrullDim A)
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme} (f : V ⟶ W) :
    (restrictPuncturedSpec A).map (sectionsAlgMap hdim f).op ≫
        (restrictPuncturedSpecSectionsAlgIso hdim W).hom =
      (restrictPuncturedSpecSectionsAlgIso hdim V).hom ≫ f := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  ext : 2
  have hV₁ := restrictPuncturedSpecSectionsAlgIso_inv_hom_left_fst hdim V
  have hV₂ := restrictPuncturedSpecSectionsAlgIso_inv_hom_left_snd hdim V
  have hW₁ := restrictPuncturedSpecSectionsAlgIso_inv_hom_left_fst hdim W
  have hW₂ := restrictPuncturedSpecSectionsAlgIso_inv_hom_left_snd hdim W
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, restrictPuncturedSpec_map_hom,
    Over.comp_left, Over.pullback_map_left]
  -- The objects of `restrictPuncturedSpec A` are pullbacks only after unfolding the functor, so
  -- the composites are reassociated with `erw` and explicit `Eq.trans` chains.
  refine pullback.hom_ext ?_ ?_
  · erw [Category.assoc, pullback.lift_fst]
    refine (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hV₁).trans <|
      .trans ?_ (Category.assoc _ _ _).symm
    exact (Scheme.toSpecΓ_naturality f.hom.left).symm.trans (congrArg (f.hom.left ≫ ·) hW₁).symm
  · erw [Category.assoc, pullback.lift_snd]
    exact hV₂.trans <| (Over.w f.hom).symm.trans <|
      (congrArg (f.hom.left ≫ ·) hW₂).symm.trans (Category.assoc _ _ _).symm

/-- For `t` as in `exists_puncturedSpectrum_eq_basicOpen`, so that `A_t` is either the zero ring or
the fraction field of `A`, let `L` be a finite étale algebra over `A_t`. Then the integral closure
of `A` in `L` is finite over `A`, and `L` is a reduced Artinian ring. -/
private theorem finite_integralClosure_and_isArtinianRing_and_isReduced {t : A}
    (hdvd : ∀ a : A, a ≠ 0 → ∃ n : ℕ, a ∣ t ^ n) (C L : Type u) [CommRing C] [CommRing L]
    [Algebra A C] [Algebra C L] [Algebra A L] [IsScalarTower A C L] [IsLocalization.Away t C]
    [Module.Finite C L] [Algebra.Etale C L] :
    Module.Finite A (integralClosure A L) ∧ IsArtinianRing L ∧ IsReduced L := by
  rcases eq_or_ne t 0 with rfl | ht0
  · -- For `t = 0` the localization `A_t`, hence `L`, is the zero ring.
    have : Subsingleton L := by
      have := (IsLocalization.Away.algebraMap_isUnit (0 : A) (S := C)).map (algebraMap C L)
      rw [map_zero, map_zero, isUnit_zero_iff] at this
      exact subsingleton_of_zero_eq_one this
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFractionRing A C := IsLocalization.of_le_of_exists_dvd (.powers t) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht0) fun a ha ↦ by
      obtain ⟨n, hn⟩ := hdvd a (nonZeroDivisors.ne_zero ha)
      exact ⟨t ^ n, ⟨n, rfl⟩, hn⟩
  let : Field C := IsFractionRing.toField A
  exact ⟨TauCeti.Ring.finite_integralClosure_of_etale C L, IsArtinianRing.of_finite C L,
    Algebra.FormallyUnramified.isReduced_of_field C L⟩

/-- Over a Noetherian integrally closed local domain of dimension at most one, a finite étale cover
`V` of the punctured spectrum is the restriction of `Spec B` for `B` the integral closure of `A` in
the ring of sections `Γ(V, 𝒪_V)`. -/
private theorem restrictPuncturedSpec_essImage_of_ringKrullDim_le_one (hdim : ringKrullDim A ≤ 1)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (restrictPuncturedSpec A).essImage V := by
  obtain ⟨t, -, hU, hdvd⟩ := exists_puncturedSpectrum_eq_basicOpen A hdim
  let U := puncturedSpectrum A
  -- `U = D(t)` is affine with ring of functions `C = A_t`, over which `L = Γ(V, 𝒪_V)` is finite
  -- étale, as `V` is affine.
  let L := Γ(V.obj.left, ⊤)
  let C := Γ(U.toScheme, ⊤)
  let : Algebra A C := ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom.toAlgebra
  let : Algebra C L := V.obj.hom.appTop.hom.toAlgebra
  let : Algebra A L := ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ U.ι).appTop).hom.toAlgebra
  have : IsScalarTower A C L := .of_algebraMap_eq' <| by
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_assoc]
  have : IsLocalization.Away t C := AlgebraicGeometry.Spec.isLocalization_away_of_eq_basicOpen hU
  have : IsAffine U.toScheme := by
    have h := (isAffineOpen_top (Spec (.of A))).basicOpen ((Scheme.ΓSpecIso (.of A)).inv t)
    rwa [basicOpen_eq_of_affine, ← hU] at h
  have : IsAffine V.obj.left := isAffine_of_isAffineHom V.obj.hom
  have : Module.Finite C L := V.obj.hom.finite_appTop
  have : Algebra.Etale C L := HasRingHomProperty.appTop @Etale V.obj.hom inferInstance
  have : Module.IsTorsionFree A L := isTorsionFree_sections A V
  -- `L` is the localization of the integral closure `B` of `A` in `L` at `t`, so `L = C ⊗[A] B`
  -- and `V` is the restriction of `Spec B`.
  let B := integralClosure A L
  have : IsLocalization (Algebra.algebraMapSubmonoid B (.powers t)) L :=
    TauCeti.IsIntegralClosure.isLocalization_of_isIntegral C
  have : Algebra.IsPushout A C B L := (Algebra.isPushout_of_isLocalization (.powers t) C B L).symm
  have hpb := AlgebraicGeometry.Spec.isPullback_toSpecΓ_of_isPushout V.obj.hom
    (CommRingCat.isPushout_of_isPushout A C B L)
  -- `B` is finite over `A`, and normal as it is integrally closed in the reduced Artinian `L`.
  obtain ⟨_, _, _⟩ := finite_integralClosure_and_isArtinianRing_and_isReduced hdvd C L
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let B' : FiniteNormalPuncturedEtaleAlg A := ⟨.of A B, inferInstance, inferInstance,
    fun 𝔮 _ ↦ ⟨IsIntegrallyClosedIn.isDomain_localization_atPrime L 𝔮,
      IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime L 𝔮⟩,
    fun 𝔮 _ h𝔮 ↦ isEtaleAt_of_isPullback_puncturedSpectrum hpb 𝔮 h𝔮⟩
  exact ⟨.op B', ⟨ObjectProperty.isoMk _
    (Over.isoMk hpb.flip.isoPullback.symm hpb.flip.isoPullback_inv_snd)⟩⟩

/-- **Finite étale covers of the punctured spectrum come from finite normal algebras.** Over a
Noetherian integrally closed local domain, every finite étale cover of the punctured spectrum is
the restriction of `Spec B` for a finite normal torsion-free `A`-algebra `B` étale away from the
maximal ideal. In dimension at least two `B` is the ring of sections of the cover
(`restrictPuncturedSpecSectionsAlgIso`); in dimension at most one it is the integral closure of
`A` in that ring. -/
@[stacks 0BM9 "essential surjectivity, with `B` torsion free"]
theorem restrictPuncturedSpec_essSurj : (restrictPuncturedSpec A).EssSurj where
  mem_essImage V := by
    rcases le_or_gt (ringKrullDim A) 1 with hdim | hdim
    · exact restrictPuncturedSpec_essImage_of_ringKrullDim_le_one hdim V
    · -- The dimension is some `n : ℕ∞` with `1 < n`, so `2 ≤ n`.
      obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hdim)
      rw [← hn, ← WithBot.coe_one, WithBot.coe_lt_coe] at hdim
      have hdim : 2 ≤ ringKrullDim A := by
        rw [← hn, ← WithBot.coe_ofNat, WithBot.coe_le_coe]
        exact Order.add_one_le_of_lt hdim
      exact ⟨.op (sectionsAlg hdim V), ⟨restrictPuncturedSpecSectionsAlgIso hdim V⟩⟩

/-- Over a Noetherian integrally closed local domain of dimension at least two, restriction to the
punctured spectrum is an equivalence from finite normal torsion-free algebras étale away from the
maximal ideal, with arrows reversed, to finite étale covers of the punctured spectrum. -/
theorem restrictPuncturedSpec_isEquivalence (hdim : 2 ≤ ringKrullDim A) :
    (restrictPuncturedSpec A).IsEquivalence where
  faithful := (restrictPuncturedSpec.fullyFaithful hdim).faithful
  full := (restrictPuncturedSpec.fullyFaithful hdim).full
  essSurj := restrictPuncturedSpec_essSurj

/-- **Finite étale covers of the punctured spectrum are finite normal algebras.** Over a
Noetherian integrally closed local domain `A` of dimension at least two, the category of finite
étale covers of the punctured spectrum is anti-equivalent to the category of finite normal
torsion-free `A`-algebras étale at every prime not lying over the maximal ideal. The functor
sends a cover `V` to its ring of sections `sectionsAlg hdim V` (`finiteNormalEquiv_functor_obj`)
and a morphism to restriction of sections (`finiteNormalEquiv_functor_map`), and the inverse is
`restrictPuncturedSpec`, restriction of `Spec B` to the punctured spectrum. -/
@[stacks 0BM9 "with `B` torsion free", expose]
def finiteNormalEquiv (hdim : 2 ≤ ringKrullDim A) :
    FiniteEtaleScheme (puncturedSpectrum A).toScheme ≌ (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ :=
  haveI := restrictPuncturedSpec_isEquivalence hdim
  let e := (restrictPuncturedSpec A).asEquivalence.symm
  -- The rings of sections functor, a right inverse of `e.inverse = restrictPuncturedSpec A`.
  let F : FiniteEtaleScheme (puncturedSpectrum A).toScheme ⥤ (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ :=
    { obj V := .op (sectionsAlg hdim V)
      map f := (sectionsAlgMap hdim f).op
      map_id V := Quiver.Hom.unop_inj <| sectionsAlgMap_id hdim V
      map_comp f g := Quiver.Hom.unop_inj <| sectionsAlgMap_comp hdim f g }
  let η : F ⋙ e.inverse ≅ 𝟭 _ := NatIso.ofComponents (restrictPuncturedSpecSectionsAlgIso hdim)
    fun f ↦ restrictPuncturedSpecSectionsAlgIso_hom_naturality hdim f
  -- Replace the forward functor by `F ≅ F ⋙ e.inverse ⋙ e.functor ≅ e.functor`.
  e.changeFunctor <| (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight η.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.counitIso ≪≫ Functor.rightUnitor _

/-- The functor of `finiteNormalEquiv` sends a finite étale cover of the punctured spectrum to its
ring of sections. -/
@[simp]
theorem finiteNormalEquiv_functor_obj (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (finiteNormalEquiv hdim).functor.obj V = .op (sectionsAlg hdim V) :=
  (rfl)

/-- The functor of `finiteNormalEquiv` sends a morphism `f : V ⟶ W` of finite étale covers of the
punctured spectrum to restriction of sections along `f`. -/
@[simp]
theorem finiteNormalEquiv_functor_map (hdim : 2 ≤ ringKrullDim A)
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme} (f : V ⟶ W) :
    (finiteNormalEquiv hdim).functor.map f = (sectionsAlgMap hdim f).op :=
  (rfl)

/-- The inverse of `finiteNormalEquiv` is restriction to the punctured spectrum. -/
@[simp]
theorem finiteNormalEquiv_inverse (hdim : 2 ≤ ringKrullDim A) :
    (finiteNormalEquiv hdim).inverse = restrictPuncturedSpec A :=
  (rfl)

end TauCeti.IsLocalRing

namespace TauCeti.Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
  [IsNoetherianRing A] [Module.Finite A B]

/-- **Purity for finite normal algebras from purity of the punctured spectrum.** Let `A` be a
Noetherian normal local domain of dimension at least two for which purity holds: every finite
étale cover of its punctured spectrum extends to a finite étale scheme over `Spec A`. Then a finite
torsion-free `A`-algebra whose localizations at maximal ideals are normal domains, and which is
étale over `A` at every prime not lying over the maximal ideal, is étale over `A`. -/
@[stacks 0BMA "(1) implies (2), with B torsion free over A"]
theorem etale_of_finiteNormal_of_purityHolds [IsDomain A] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A B] (hpurity : IsLocalRing.PurityHolds A)
    (hdim : 2 ≤ ringKrullDim A)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (hetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  let W := Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ IsLocalRing.puncturedSpectrum A
  refine etale_of_purityHolds_of_bijective hpurity (two_le_depth_of_isIntegrallyClosed hdim)
    ?_ hetale
  rw [Scheme.Opens.ι_appTop]
  refine AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegrallyClosed hdim hnormal
    (W.ι ''ᵁ ⊤) fun p hp ↦ ?_
  rw [Scheme.Opens.ι_image_top]
  exact (IsLocalRing.mem_preimage_puncturedSpectrum_iff A p).mpr hp

end TauCeti.Algebra

namespace TauCeti.IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A]

/-- **Purity for a normal local ring in terms of finite normal algebras.** Let `A` be a Noetherian
integrally closed local domain of dimension at least two. Purity holds for `A`, that is, every
finite étale cover of the punctured spectrum extends to a finite étale scheme over `Spec A`, if and
only if every finite normal torsion-free `A`-algebra which is étale at every prime not lying over
the maximal ideal is étale over `A`. -/
@[stacks 0BMA "(1) iff (2), with `B` torsion free over `A`"]
theorem purityHolds_iff_forall_etale (hdim : 2 ≤ ringKrullDim A) :
    PurityHolds A ↔ ∀ B : FiniteNormalPuncturedEtaleAlg A, Algebra.Etale A B.obj := by
  refine ⟨fun hpurity B ↦ ?_, fun h ↦ (purityHolds_iff A).mpr fun V ↦ ?_⟩
  · obtain ⟨_, _, hnormal, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.property
    exact TauCeti.Algebra.etale_of_finiteNormal_of_purityHolds hpurity hdim
      (fun 𝔮 _ ↦ hnormal 𝔮) het
  · -- The sections of `V` form a finite normal algebra, which is étale by assumption.
    exact (extends_iff_sections_etale A (two_le_depth_of_isIntegrallyClosed hdim) V).mpr
      (h (sectionsAlg hdim V))

end TauCeti.IsLocalRing
