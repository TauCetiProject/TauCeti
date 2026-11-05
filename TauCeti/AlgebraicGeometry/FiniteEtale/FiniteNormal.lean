/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections

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

This is the full faithfulness half of the anti-equivalence between finite étale covers of `U` and
finite normal punctured-étale `A`-algebras (Stacks, Lemma 58.20.3 (0BM9)). Torsion freeness is
needed and is missing from the Stacks statement: for `A` normal of dimension at least two, the
algebra `A × A/𝔪` is finite, normal and étale away from `𝔪`, but its restriction to `U` is that of
`A`, so the functor would not be faithful on it.

## Main definitions

* `TauCeti.IsLocalRing.finiteNormalPuncturedEtale`: the finite normal torsion-free `A`-algebras
  which are étale at every prime not over the maximal ideal.
* `TauCeti.IsLocalRing.FiniteNormalPuncturedEtaleAlg`: the full subcategory of `CommAlgCat A` on
  these algebras.
* `TauCeti.IsLocalRing.restrictPuncturedSpec`: the functor sending `B` to the restriction of
  `Spec B` to the punctured spectrum.

## Main results

* `TauCeti.IsLocalRing.etale_pullback_snd_puncturedSpectrum`: the restriction of `Spec B` to the
  punctured spectrum is étale if `B` is finitely presented and étale at every prime not over the
  maximal ideal.
* `TauCeti.IsLocalRing.restrictPuncturedSpec.fullyFaithful`: restriction to the punctured spectrum
  is fully faithful on finite normal punctured-étale algebras.

## References

* [The Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
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

end TauCeti.IsLocalRing
