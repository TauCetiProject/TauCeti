/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import TauCeti.AlgebraicGeometry.Cover.Sigma
import TauCeti.AlgebraicGeometry.Sites.BigZariski
import TauCeti.AlgebraicGeometry.Sites.QuasiCompact
import TauCeti.CategoryTheory.Sites.Descent.IsPrestack
import TauCeti.CategoryTheory.Sites.Descent.IsStack
import TauCeti.CategoryTheory.Sites.Descent.Precoverage
import TauCeti.CategoryTheory.Sites.Sieves.Basic

/-!
# Stacks for the quasi-compact topology

Let `P : MorphismProperty Scheme.{u}` be a multiplicative morphism property that is stable under
base change and Zariski-local at the source (for example, `Flat` for the fpqc topology). This file
shows that a pseudofunctor `F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat` is a prestack (resp. a
stack) for `Scheme.propQCTopology P` if and only if it is a prestack (resp. a stack) for the big
Zariski topology `Scheme.zariskiTopology` and satisfies `F.IsPrestackFor` (resp. `F.IsStackFor`)
for every single-morphism `P`-covering `{Spec S ⟶ Spec R}` of affine schemes.

The statements and proof structure (reduction to affine targets via `affineOneHypercover` and
`affineCover`, refinement to a finite affine covering via `QuasiCompactCover.exists_hom`, and
consolidation into a single affine morphism via `Sigma.desc` and `isoSpec`) adapt Christian
Merten's sheaf-of-types characterization `AlgebraicGeometry.isSheaf_type_propQCTopology_iff` in
`Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact` to prestacks and stacks.

## Main results

* `TauCeti.AlgebraicGeometry.isPrestack_propQCTopology_iff`: characterization of prestacks for
  `Scheme.propQCTopology P`.
* `TauCeti.AlgebraicGeometry.isStack_propQCTopology_iff`: characterization of stacks for
  `Scheme.propQCTopology P`.

## References

* Christian Merten, `AlgebraicGeometry.isSheaf_type_propQCTopology_iff` in
  `Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact`.
* The Stacks Project, Section 34.9, *The fpqc topology*, Tag 022H.
* The Stacks Project, Section 35.5, *Descent of quasi-coherent modules*, Tag 023T.
-/

public section

universe w v u

open CategoryTheory Limits Bicategory Pseudofunctor

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

private lemma sieve_generate_pullback₂ {K : Precoverage Scheme.{u}} [K.IsStableUnderBaseChange]
    {S T : Scheme.{u}} (𝒰 : Scheme.Cover.{w} K T) (h : S ⟶ T) :
    (Sieve.generate 𝒰.presieve₀).pullback h = Sieve.generate (𝒰.pullback₂ h).presieve₀ := by
  rw [Precoverage.ZeroHypercover.pullback₂_toPreZeroHypercover,
    PreZeroHypercover.presieve₀_pullback₁]
  dsimp only [PreZeroHypercover.presieve₀]
  rw [← Sieve.ofArrows, ← Sieve.pullbackArrows_comm]

private lemma presieve₀_pullback₂ {K : Precoverage Scheme.{u}} [K.IsStableUnderBaseChange]
    {S T : Scheme.{u}} (𝒰 : Scheme.Cover.{w} K T) (h : S ⟶ T) :
    (𝒰.pullback₂ h).presieve₀ =
      Presieve.ofArrows (fun i ↦ pullback (𝒰.f i) h) (fun i ↦ pullback.snd (𝒰.f i) h) := by
  rw [Precoverage.ZeroHypercover.pullback₂_toPreZeroHypercover,
    PreZeroHypercover.presieve₀_pullback₁]
  dsimp only [PreZeroHypercover.presieve₀]
  rw [Presieve.ofArrows_pullback]

private lemma isPrestackFor_pullback₂_of_isAffine
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v, w}}
    (haff_case : ∀ (R : CommRingCat.{u}) (𝒰 : Scheme.Cover.{u} (propQCPrecoverage P) (Spec R)),
      (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ → F.IsPrestackFor 𝒰.presieve₀)
    {T : Scheme.{u}} [IsAffine T] (𝒰 : Scheme.Cover.{u} (precoverage P) T)
    (haff : ∀ i, IsAffine (𝒰.X i)) [Finite 𝒰.I₀]
    {A : CommRingCat.{u}} (h : Spec A ⟶ T) :
    F.IsPrestackFor (𝒰.pullback₂ h).presieve₀ := by
  have hfin : Finite (𝒰.pullback₂ h).I₀ := by
    rw [Precoverage.ZeroHypercover.pullback₂_toPreZeroHypercover,
      PreZeroHypercover.pullback₂_I₀]
    infer_instance
  have haff' : ∀ j, IsAffine ((𝒰.pullback₂ h).X j) := Cover.isAffine_pullback₂ 𝒰 h haff
  have hqc : ∀ j, AlgebraicGeometry.QuasiCompact ((𝒰.pullback₂ h).f j) :=
    Cover.quasiCompact_pullback₂ 𝒰 h haff
  let _ : QuasiCompactCover (𝒰.pullback₂ h).toPreZeroHypercover := .of_finite
  rw [← Cover.ofQuasiCompactCover_presieve₀ (𝒰.pullback₂ h)]
  exact haff_case A (.ofQuasiCompactCover (𝒰.pullback₂ h))
    ⟨Cover.isAffine_ofQuasiCompactCover _ haff', Cover.finite_ofQuasiCompactCover _⟩

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
  [P.IsMultiplicative] [IsZariskiLocalAtSource P]

/-- A pseudofunctor on schemes is a prestack for `Scheme.propQCTopology P` if and only if it is a
prestack for the big Zariski topology and satisfies descent of morphisms for every single-morphism
`P`-covering `Spec S ⟶ Spec R` of affine schemes. -/
theorem isPrestack_propQCTopology_iff (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v, w}) :
    F.IsPrestack (propQCTopology P) ↔
      F.IsPrestack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          F.IsPrestackFor (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨IsPrestack.of_le (zariskiTopology_le_propQCTopology (P := P)),
    fun {R S} f hf _ ↦
      F.isPrestackFor _ ((Spec.map f).generate_singleton_mem_propQCTopology hf)⟩,
    fun ⟨hzar, hff⟩ ↦ ?_⟩
  have := hzar
  refine IsPrestack.of_precoverage_of_small.{u} fun T (𝒰 : Scheme.Cover.{u} _ T) ↦ ?_
  wlog hT : ∃ R : CommRingCat.{u}, T = Spec R generalizing T
  · have hpull {V : Scheme.{u}} (h : V ⟶ T) (hV : ∃ A : CommRingCat.{u}, V = Spec A) :
        F.IsPrestackFor ((Sieve.generate 𝒰.presieve₀).pullback h).arrows := by
      rw [sieve_generate_pullback₂, IsPrestackFor_generate_iff]
      exact this _ (𝒰.pullback₂ h) hV
    refine IsPrestackFor.of_pullback T.affineOneHypercover (fun i ↦ ?_) (fun i j k _ _ _ _ h ↦ ?_)
    · exact hpull (T.affineOneHypercover.f i)
        ⟨T.affineOpenCover.X i, AffineOpenCover.openCover_X T.affineOpenCover i⟩
    · exact (hpull (T.affineOneHypercover.p₁ k ≫ T.affineOneHypercover.f i)
        (T.exists_spec_affineOneHypercover_Y k)).hom_ext h
  obtain ⟨R, rfl⟩ := hT
  wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
  · obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have hpull {V : Scheme.{u}} (h : V ⟶ Spec R) (hV : ∃ A : CommRingCat.{u}, V = Spec A) :
        F.IsPrestackFor ((Sieve.ofArrows 𝒱.cover.X 𝒱.cover.f).pullback h).arrows := by
      obtain ⟨A, rfl⟩ := hV
      have _ : Finite 𝒱.cover.I₀ := AffineCover.finite_cover 𝒱
      have hs : (Sieve.ofArrows 𝒱.cover.X 𝒱.cover.f).pullback h =
          Sieve.generate (𝒱.cover.pullback₂ h).presieve₀ := by
        simpa only [Sieve.ofArrows, PreZeroHypercover.presieve₀] using
          sieve_generate_pullback₂ 𝒱.cover h
      rw [hs, IsPrestackFor_generate_iff]
      exact isPrestackFor_pullback₂_of_isAffine this 𝒱.cover
        (AffineCover.isAffine_cover 𝒱) h
    rw [← IsPrestackFor_generate_iff]
    refine ((IsPrestackFor_generate_iff F _).2
      (this R (.ofQuasiCompactCover 𝒱.cover)
        ⟨AffineCover.isAffine_ofQuasiCompactCover 𝒱,
          AffineCover.finite_ofQuasiCompactCover 𝒱⟩)).of_le'
      f.sieve₀_le_sieve₀ fun V g _ M N φ ψ h ↦ ?_
    refine (F.isPrestackFor (Presieve.ofArrows V.affineCover.X V.affineCover.f)
      V.affineCover.mem_grothendieckTopology).hom_ext fun Z _ ⟨i⟩ ↦ ?_
    refine (hpull (V.affineCover.f i ≫ g)
      ⟨V.affineOpenCover.X i, AffineOpenCover.openCover_X V.affineOpenCover i⟩).hom_ext
      fun W s hs ↦ ?_
    rw [Sieve.pullback_comp] at hs
    simpa using h _ hs
  obtain ⟨S, φ, e, hP, hsurj, hφ⟩ := Cover.exists_specMap_sigma 𝒰.forgetQc h𝒰.1 h𝒰.2
  have hp : F.IsPrestackFor (.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f)) := by
    have hsieve : Sieve.generate (.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f)) =
        Sieve.generate (.singleton (Spec.map φ)) := by
      rw [Presieve.ofArrows_pUnit, ← Sieve.generate_singleton_comp_of_isIso e.hom, ← hφ]
    rw [← IsPrestackFor_generate_iff, hsieve, IsPrestackFor_generate_iff]
    exact hff φ hP hsurj
  have hcomp := hp.comp (fun _ i ↦ Sigma.ι 𝒰.X i)
    (fun _ ↦ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology)
  rw [Presieve.ofArrows_sigma_ι_comp_desc] at hcomp
  exact hcomp

/-- A pseudofunctor on schemes is a stack for `Scheme.propQCTopology P` if and only if it is a
stack for the big Zariski topology and has effective descent for every single-morphism `P`-covering
`Spec S ⟶ Spec R` of affine schemes. -/
theorem isStack_propQCTopology_iff (F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{v, w}) :
    F.IsStack (propQCTopology P) ↔
      F.IsStack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          F.IsStackFor (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨IsStack.of_le (zariskiTopology_le_propQCTopology (P := P)),
    fun {R S} f hf _ ↦ F.isStackFor _ ((Spec.map f).generate_singleton_mem_propQCTopology hf)⟩,
    fun ⟨hzar, hff⟩ ↦ ?_⟩
  have := hzar
  have : F.IsPrestack (propQCTopology P) :=
    (isPrestack_propQCTopology_iff F).2
      ⟨hzar.toIsPrestack, fun f hf hs ↦ (hff f hf hs).isPrestackFor⟩
  refine IsStack.of_precoverage_of_small.{u} fun T (𝒰 : Scheme.Cover.{u} _ T) ↦ ?_
  wlog hT : ∃ R : CommRingCat.{u}, T = Spec R generalizing T
  · refine IsStackFor.of_pullback (J := propQCTopology P)
      (Precoverage.generate_mem_toGrothendieck 𝒰.mem₀)
      (zariskiTopology_le_propQCTopology _ T.affineCover.mem_grothendieckTopology)
      (F.isStackFor _ (by simpa using T.affineCover.mem_grothendieckTopology)) fun a ↦ ?_
    rw [← presieve₀_pullback₂]
    exact this _ (𝒰.pullback₂ (T.affineCover.f a))
      ⟨T.affineOpenCover.X a, AffineOpenCover.openCover_X T.affineOpenCover a⟩
  obtain ⟨R, rfl⟩ := hT
  wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
  · obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have h𝒱 := this R (.ofQuasiCompactCover 𝒱.cover)
      ⟨AffineCover.isAffine_ofQuasiCompactCover 𝒱, AffineCover.finite_ofQuasiCompactCover 𝒱⟩
    rw [← IsStackFor_generate_iff] at h𝒱 ⊢
    exact h𝒱.of_le' F 𝒱.cover.mem_propQCTopology f.sieve₀_le_sieve₀
  obtain ⟨S, φ, e, hP, hsurj, hφ⟩ := Cover.exists_specMap_sigma 𝒰.forgetQc h𝒰.1 h𝒰.2
  have hp : F.IsStackFor (.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f)) := by
    have hsieve : Sieve.generate (.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f)) =
        Sieve.generate (.singleton (Spec.map φ)) := by
      rw [Presieve.ofArrows_pUnit, ← Sieve.generate_singleton_comp_of_isIso e.hom, ← hφ]
    rw [← IsStackFor_generate_iff, hsieve, IsStackFor_generate_iff]
    exact hff φ hP hsurj
  have hcomp := hp.comp (J := Scheme.zariskiTopology) (fun _ i ↦ Sigma.ι 𝒰.X i)
    (fun _ ↦ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology)
    (fun _ ↦ (IsStackFor_generate_iff F _).1
      (F.isStackFor' _ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology))
  rw [Presieve.ofArrows_sigma_ι_comp_desc] at hcomp
  exact hcomp

end TauCeti.AlgebraicGeometry
