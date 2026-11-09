/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Extension
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Normal
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.RingTheory.CohenMacaulay.Normal

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

The functor is also essentially surjective, so it is an anti-equivalence between finite normal
punctured-étale `A`-algebras and finite étale covers of `U` (Stacks, Lemma 58.20.3 (0BM9)). A
cover `V` is the restriction of `Spec B` for its ring of sections `B = Γ(V, 𝒪_V)`
(`TauCeti.IsLocalRing.isPullback_puncturedSpectrum_toSpecΓ`), and `B` is a finite normal
punctured-étale algebra: it is finite by the trace-form argument of
`TauCeti.IsLocalRing.finite_sections`, torsion free because `V` is flat over `Spec A`, étale at
the points of `Spec B` over `U` because `V` is étale over `U`, and normal because sections of
`Spec B` over the preimage of `U` are the sections of `V`, which come from `B` (the étale form
`isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt` of algebraic Hartogs).
Torsion freeness is needed and is missing from the Stacks statement: for `A` normal of dimension
at least two, the algebra `A × A/𝔪` is finite, normal and étale away from `𝔪`, but its
restriction to `U` is that of `A`, so the functor would not be faithful on it.

If purity holds for `A` (`TauCeti.IsLocalRing.PurityHolds A`), every finite étale cover of `U`
extends to a finite étale scheme over `Spec A`, so its ring of sections is finite étale over `A`
when `A` has depth at least two (Stacks, Lemma 58.20.2 (0BLK)). When a finite algebra `B`, étale
at every prime not lying over `𝔪`, is recovered from its sections over the preimage of `U`, this
shows that `B` itself is étale over `A`. For a finite torsion-free algebra `B` whose localizations
at maximal ideals are normal domains, over a Noetherian normal local domain `A` of dimension at
least two, both the depth bound and the recovery of `B` from its sections hold. So purity for the
punctured spectrum of `A` implies purity for finite normal `A`-algebras: this is how part (2) of
Stacks, Lemma 58.21.3 (0BMA), purity for regular local rings in its algebraic form, follows from
part (1), purity of the punctured spectrum. Conversely, by the anti-equivalence a cover of `U`
extends exactly when its ring of sections is étale over `A`, so the two forms of purity are
equivalent.

## Main definitions

* `TauCeti.IsLocalRing.finiteNormalPuncturedEtale`: the finite normal torsion-free `A`-algebras
  which are étale at every prime not over the maximal ideal.
* `TauCeti.IsLocalRing.FiniteNormalPuncturedEtaleAlg`: the full subcategory of `CommAlgCat A` on
  these algebras.
* `TauCeti.IsLocalRing.restrictPuncturedSpec`: the functor sending `B` to the restriction of
  `Spec B` to the punctured spectrum.
* `TauCeti.IsLocalRing.puncturedSectionsAlg`: the ring of sections of a finite étale cover of the
  punctured spectrum, as a finite normal punctured-étale algebra.
* `TauCeti.IsLocalRing.finiteNormalEquiv`: the anti-equivalence between finite étale covers of the
  punctured spectrum and finite normal punctured-étale algebras.

## Main results

* `TauCeti.IsLocalRing.etale_pullback_snd_puncturedSpectrum`: the restriction of `Spec B` to the
  punctured spectrum is étale if `B` is finitely presented and étale at every prime not over the
  maximal ideal.
* `TauCeti.IsLocalRing.restrictPuncturedSpec.fullyFaithful`: restriction to the punctured spectrum
  is fully faithful on finite normal punctured-étale algebras.
* `TauCeti.IsLocalRing.finiteNormalPuncturedEtale_algΓ`: the ring of sections of a finite étale
  cover of the punctured spectrum is a finite normal punctured-étale algebra.
* `TauCeti.IsLocalRing.restrictPuncturedSpec_essSurj`: every finite étale cover of the punctured
  spectrum is the restriction of the spectrum of its ring of sections.
* `TauCeti.IsLocalRing.extends_iff_etale_puncturedSectionsAlg`: a cover extends across the closed
  point if and only if its ring of sections is étale.
* `TauCeti.Algebra.etale_of_finiteNormal_of_purityHolds`: over a Noetherian normal local domain of
  dimension at least two for which purity holds, a finite torsion-free algebra with normal
  localizations at maximal ideals, étale at every prime not lying over the closed point, is
  étale.
* `TauCeti.IsLocalRing.purityHolds_iff_forall_etale`: over such a ring, purity holds if and only
  if every finite normal punctured-étale algebra is étale.

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
      exact (pullback.snd g U.ι x).2
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
  choose V hxV hV using key
  exact IsZariskiLocalAtSource.of_iSup_eq_top V
    (top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) hV

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

/-- Let `A` be a Noetherian integrally closed local domain of dimension at least two and `V` a
finite étale cover of its punctured spectrum. The ring of sections `Γ(V, 𝒪_V)`, an `A`-algebra
through `V ⟶ U ⟶ Spec A`, is finite, torsion free and normal over `A`, and étale over `A` at every
prime not lying over the maximal ideal. -/
@[stacks 0BM9 "the sections of a cover are a finite normal algebra, with `B` torsion free"]
theorem finiteNormalPuncturedEtale_algΓ [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    finiteNormalPuncturedEtale A
      ((algΓ (.of A)).obj ((Over.map (puncturedSpectrum A).ι).obj V.obj)).unop := by
  let U := puncturedSpectrum A
  let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ U.ι).appTop
  let := φ.hom.toAlgebra
  let B := Γ(V.obj.left, ⊤)
  -- The algebra structure of `algΓ` on `B` is the one induced by `φ`.
  suffices finiteNormalPuncturedEtale A (CommAlgCat.of A B) from this
  have hdepth := two_le_depth_of_isIntegrallyClosed hdim
  have : Module.Finite A B := finite_sections A hdepth V
  have : Module.IsTorsionFree A B := isTorsionFree_sections A V
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- `V` is the restriction of `Spec B` to `U`; write `W` for the preimage of `U` in `Spec B`.
  let g := Spec.map φ
  let W := g ⁻¹ᵁ U
  have h := (isPullback_puncturedSpectrum_toSpecΓ A hdepth V.obj.hom).flip
  -- So `Spec B ⟶ Spec A` is étale over `U`, that is, at the points of `W`.
  have : Etale (pullback.snd g U.ι) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  have hW : Etale (W.ι ≫ g) := by
    rw [← morphismRestrict_ι, morphismRestrict]
    infer_instance
  have het (q : PrimeSpectrum B) (hq : q ∈ W) : Algebra.IsEtaleAt A q.asIdeal :=
    (Scheme.Hom.etaleAt_spec_iff q).mp ⟨W, hq, hW⟩
  -- Restriction of sections of `Spec B` to `W` is bijective, since `V ⟶ Spec B` induces an
  -- isomorphism on global sections.
  have : IsIso (pullback.fst g U.ι).appTop := by
    have : IsIso h.isoPullback.inv.appTop := Scheme.Γ.map_isIso h.isoPullback.inv.op
    rw [← h.isoPullback_inv_fst, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    infer_instance
  have : IsIso W.ι.appTop := by
    have : IsIso (pullbackRestrictIsoRestrict g U).inv.appTop :=
      Scheme.Γ.map_isIso (pullbackRestrictIsoRestrict g U).inv.op
    rw [← pullbackRestrictIsoRestrict_inv_fst, Scheme.Hom.comp_appTop]
    infer_instance
  rw [Scheme.Opens.ι_appTop] at this
  have hbij := (ConcreteCategory.isIso_iff_bijective _).mp this
  refine ⟨‹_›, ‹_›, fun q _ ↦ ?_, fun q _ hq ↦ het ⟨q, ‹_›⟩ ?_⟩
  · exact AlgebraicGeometry.Spec.isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt
      (A := A) (B := B) (W.ι ''ᵁ ⊤) (fun p hp ↦ het p (by rwa [Scheme.Opens.ι_image_top] at hp))
      hbij q
  · exact (mem_preimage_puncturedSpectrum_iff A (B := B) ⟨q, ‹_›⟩).mpr hq

/-- The ring of sections of a finite étale cover `V` of the punctured spectrum, as a finite normal
torsion-free `A`-algebra étale away from the maximal ideal. -/
def puncturedSectionsAlg [IsDomain A] [IsIntegrallyClosed A] (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) : FiniteNormalPuncturedEtaleAlg A :=
  ⟨((algΓ (.of A)).obj ((Over.map (puncturedSpectrum A).ι).obj V.obj)).unop,
    finiteNormalPuncturedEtale_algΓ hdim V⟩

/-- The algebra underlying `puncturedSectionsAlg hdim V` is `Γ(V, 𝒪_V)`, with the `A`-algebra
structure given by Mathlib's `algΓ`. -/
@[simp]
theorem puncturedSectionsAlg_obj [IsDomain A] [IsIntegrallyClosed A] (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (puncturedSectionsAlg hdim V).obj =
      ((algΓ (.of A)).obj ((Over.map (puncturedSpectrum A).ι).obj V.obj)).unop :=
  (rfl)

/-- A finite étale cover `V` of the punctured spectrum is the restriction of the spectrum of its
ring of sections. -/
def restrictPuncturedSpecSectionsIso [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (restrictPuncturedSpec A).obj (.op (puncturedSectionsAlg hdim V)) ≅ V :=
  let h := (isPullback_puncturedSpectrum_toSpecΓ A
    (two_le_depth_of_isIntegrallyClosed hdim) V.obj.hom).flip
  ObjectProperty.isoMk _ (Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd)

/-- Over a Noetherian integrally closed local domain of dimension at least two, every finite
étale cover of the punctured spectrum is the restriction of `Spec B` for a finite normal
torsion-free `A`-algebra `B` étale away from the maximal ideal, namely its ring of sections. -/
@[stacks 0BM9 "essential surjectivity, with `B` torsion free"]
theorem restrictPuncturedSpec_essSurj [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) : (restrictPuncturedSpec A).EssSurj where
  mem_essImage V := ⟨_, ⟨restrictPuncturedSpecSectionsIso hdim V⟩⟩

/-- Restriction to the punctured spectrum is an equivalence from finite normal torsion-free
algebras étale away from the maximal ideal, with arrows reversed, to finite étale covers of the
punctured spectrum. -/
theorem restrictPuncturedSpec_isEquivalence [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) : (restrictPuncturedSpec A).IsEquivalence where
  faithful := (restrictPuncturedSpec.fullyFaithful hdim).faithful
  full := (restrictPuncturedSpec.fullyFaithful hdim).full
  essSurj := restrictPuncturedSpec_essSurj hdim

/-- **Finite étale covers of the punctured spectrum are finite normal algebras.** Over a
Noetherian integrally closed local domain `A` of dimension at least two, finite étale covers of
the punctured spectrum are anti-equivalent to finite normal torsion-free `A`-algebras étale at
every prime not lying over the maximal ideal. The inverse is `restrictPuncturedSpec`, which
restricts `Spec B` to the punctured spectrum, and the functor sends a cover to its ring of sections
(`TauCeti.IsLocalRing.finiteNormalEquivFunctorObjIso`). -/
@[stacks 0BM9 "with `B` torsion free"]
def finiteNormalEquiv [IsDomain A] [IsIntegrallyClosed A] (hdim : 2 ≤ ringKrullDim A) :
    FiniteEtaleScheme (puncturedSpectrum A).toScheme ≌ (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ :=
  have := restrictPuncturedSpec_isEquivalence hdim
  (restrictPuncturedSpec A).asEquivalence.symm

/-- The inverse of `finiteNormalEquiv` restricts `Spec B` to the punctured spectrum. -/
@[simp]
theorem finiteNormalEquiv_inverse [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) : (finiteNormalEquiv hdim).inverse = restrictPuncturedSpec A :=
  (rfl)

/-- The functor of `finiteNormalEquiv` sends a finite étale cover of the punctured spectrum to its
ring of sections. -/
def finiteNormalEquivFunctorObjIso [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (finiteNormalEquiv hdim).functor.obj V ≅ .op (puncturedSectionsAlg hdim V) :=
  (restrictPuncturedSpec.fullyFaithful hdim).preimageIso
    (((finiteNormalEquiv hdim).unitIso.app V).symm ≪≫
      (restrictPuncturedSpecSectionsIso hdim V).symm)

/-- Over a Noetherian integrally closed local domain of dimension at least two, a finite étale
cover of the punctured spectrum extends to a finite étale scheme over `Spec A` if and only if its
ring of sections is étale over `A`. -/
@[stacks 0BM9 "extension criterion"]
theorem extends_iff_etale_puncturedSectionsAlg [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      Algebra.Etale A (puncturedSectionsAlg hdim V).obj :=
  (extends_iff_sections_finiteEtale A (two_le_depth_of_isIntegrallyClosed hdim) V).trans
    ⟨And.right, fun h ↦ ⟨(puncturedSectionsAlg hdim V).property.1, h⟩⟩

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

/-- **The two forms of purity agree.** Over a Noetherian integrally closed local domain of
dimension at least two, every finite étale cover of the punctured spectrum extends to a finite
étale scheme over `Spec A` if and only if every finite normal torsion-free `A`-algebra which is
étale at every prime not lying over the maximal ideal is étale over `A`. -/
@[stacks 0BMA "(1) is equivalent to (2), with B torsion free over A"]
theorem purityHolds_iff_forall_etale (hdim : 2 ≤ ringKrullDim A) :
    PurityHolds A ↔ ∀ B : FiniteNormalPuncturedEtaleAlg A, Algebra.Etale A B.obj := by
  refine ⟨fun hpurity B ↦ ?_, fun h ↦ (purityHolds_iff A).mpr fun V ↦
    (extends_iff_etale_puncturedSectionsAlg hdim V).mpr (h _)⟩
  obtain ⟨_, _, hnormal, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.property
  exact Algebra.etale_of_finiteNormal_of_purityHolds hpurity hdim (fun 𝔮 _ ↦ hnormal 𝔮) het

end TauCeti.IsLocalRing
