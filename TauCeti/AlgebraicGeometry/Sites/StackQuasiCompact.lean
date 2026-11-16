/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import TauCeti.CategoryTheory.Sites.Descent.IsPrestack
import TauCeti.CategoryTheory.Sites.Descent.IsStack
import TauCeti.CategoryTheory.Sites.Descent.Precoverage

/-!
# Stacks for the quasi-compact topology

Let `P : MorphismProperty Scheme.{u}` be a multiplicative morphism property that is stable under
base change and Zariski-local at the source (for example, `Flat` for the fpqc topology). This file
shows that a pseudofunctor `F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat` is a prestack (resp. a
stack) for `Scheme.propQCTopology P` if and only if it is a prestack (resp. a stack) for the big
Zariski topology `Scheme.zariskiTopology` and satisfies `F.IsPrestackFor` (resp. `F.IsStackFor`)
for every single-morphism `P`-covering `{Spec S ⟶ Spec R}` of affine schemes.

The statements and proof structure (reduction to affine targets via `affineOneHypercover`,
refinement to a finite affine covering via `QuasiCompactCover.exists_hom`, and consolidation into a
single affine morphism via `Sigma.desc` and `isoSpec`) adapt Christian Merten's sheaf-of-types
characterization `AlgebraicGeometry.isSheaf_type_propQCTopology_iff` in
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

private lemma sieve_singleton_iso_comp {X X' S : Scheme.{u}} (e : X ≅ X') (f : X ⟶ S) :
    Sieve.generate (.singleton (e.inv ≫ f)) =
      Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ X) (fun _ ↦ f) := by
  ext Z g
  constructor
  · rintro ⟨_, a, _, ⟨⟩, rfl⟩
    exact ⟨X, a ≫ e.inv, f, Presieve.ofArrows.mk PUnit.unit, Category.assoc _ _ _⟩
  · rintro ⟨_, a, _, ⟨_⟩, rfl⟩
    exact ⟨X', a ≫ e.hom, e.inv ≫ f, Presieve.singleton_self _, by simp⟩

private lemma sieve_comp_sigma_ι {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) :
    Sieve.ofArrows (fun jk : Σ _ : PUnit.{u + 1}, ι ↦ X jk.2)
      (fun jk ↦ Sigma.ι X jk.2 ≫ Sigma.desc f) = Sieve.ofArrows X f := by
  ext Z g
  constructor
  · rintro ⟨_, a, _, ⟨⟨_, i⟩⟩, rfl⟩
    exact ⟨X i, a, f i, Presieve.ofArrows.mk i, by simp⟩
  · rintro ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨X i, a, Sigma.ι X i ≫ Sigma.desc f,
      Presieve.ofArrows.mk (⟨PUnit.unit, i⟩ : Σ _ : PUnit.{u + 1}, ι), by simp⟩

private lemma exists_specMap_sigma {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
    {R : CommRingCat.{u}} (𝒰 : Scheme.Cover.{u} (propQCPrecoverage P) (Spec R))
    (haff : ∀ i, IsAffine (𝒰.X i)) (hfin : Finite 𝒰.I₀) :
    ∃ (S : CommRingCat.{u}) (φ : R ⟶ S), P (Spec.map φ) ∧ Surjective (Spec.map φ) ∧
      Sieve.generate (.singleton (Spec.map φ)) =
        Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f) := by
  have : IsAffine (𝒰.forgetQc.sigma.X default) := inferInstanceAs <| IsAffine (∐ 𝒰.X)
  let q : Spec _ ⟶ Spec R :=
    (𝒰.forgetQc.sigma.X default).isoSpec.inv ≫ 𝒰.forgetQc.sigma.f default
  obtain ⟨φ, hφ⟩ := Spec.map_surjective q
  have hP : P (Spec.map φ) := by
    simpa only [hφ, q] using IsZariskiLocalAtSource.comp (𝒰.forgetQc.sigma.map_prop default) _
  have hsurj : Surjective (Spec.map φ) := by
    have : Surjective (𝒰.forgetQc.sigma.f default) :=
      inferInstanceAs <| Surjective (Sigma.desc 𝒰.forgetQc.f)
    rw [hφ]
    infer_instance
  refine ⟨_, φ, hP, hsurj, ?_⟩
  rw [hφ]
  exact sieve_singleton_iso_comp (𝒰.forgetQc.sigma.X default).isoSpec (Sigma.desc 𝒰.f)

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
  · refine IsPrestackFor.of_pullback T.affineOneHypercover (fun i ↦ ?_) (fun i j k ↦ ?_)
    · rw [PreZeroHypercover.presieve₀, ← Sieve.ofArrows, ← Sieve.pullbackArrows_comm,
        ← Presieve.ofArrows_pullback, IsPrestackFor_generate_iff]
      exact this _ (𝒰.pullback₂ (T.affineCover.f i)) ⟨_, rfl⟩
    · rw [PreZeroHypercover.presieve₀, ← Sieve.ofArrows, ← Sieve.pullbackArrows_comm,
        ← Presieve.ofArrows_pullback, IsPrestackFor_generate_iff]
      exact this _ (𝒰.pullback₂ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hT
  wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
  · obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have hpull {A : CommRingCat.{u}} (h : Spec A ⟶ Spec R) :
        F.IsPrestackFor ((Sieve.ofArrows 𝒱.cover.X 𝒱.cover.f).pullback h).arrows := by
      rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback, IsPrestackFor_generate_iff]
      let 𝒰' := 𝒱.cover.pullback₂ h
      have _ : Finite 𝒰'.I₀ := hfin
      have haff : ∀ j, IsAffine (𝒰'.X j) := fun j ↦ by
        have _ : IsAffine (𝒱.cover.X j) := inferInstanceAs <| IsAffine (Spec _)
        exact inferInstanceAs <| IsAffine (pullback (𝒱.cover.f j) h)
      have _ : ∀ j, QuasiCompact (𝒰'.f j) := fun _ ↦ inferInstance
      exact this A (.ofQuasiCompactCover 𝒰' (qc := .of_finite)) ⟨haff, hfin⟩
    rw [← IsPrestackFor_generate_iff]
    refine ((IsPrestackFor_generate_iff F _).2
      (this R (.ofQuasiCompactCover 𝒱.cover)
        ⟨fun _ ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩)).of_le'
      f.sieve₀_le_sieve₀ fun V g _ ↦ ?_
    refine IsPrestackFor.of_pullback' V.affineOneHypercover (fun i ↦ ?_) (fun i j k ↦ ?_)
    · rw [← Sieve.pullback_comp]
      exact hpull (V.affineCover.f i ≫ g)
    · rw [← Sieve.pullback_comp]
      exact hpull ((V.affineOneHypercover.p₁ k ≫ V.affineOneHypercover.f i) ≫ g)
  obtain ⟨S, φ, hP, hsurj, hsieve⟩ := exists_specMap_sigma 𝒰 h𝒰.1 h𝒰.2
  have hp := (F.isPrestackFor_iff_of_sieve_eq hsieve).1 (hff φ hP hsurj)
  have hcomp := hp.comp (fun _ i ↦ Sigma.ι 𝒰.X i)
    (fun _ ↦ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology)
  exact (F.isPrestackFor_iff_of_sieve_eq (sieve_comp_sigma_ι 𝒰.f)).1 hcomp

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
    exact this _ (𝒰.pullback₂ (T.affineCover.f a)) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hT
  wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
  · obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have h𝒱 := this R (.ofQuasiCompactCover 𝒱.cover)
      ⟨fun _ ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    rw [← IsStackFor_generate_iff] at h𝒱 ⊢
    exact h𝒱.of_le' F 𝒱.cover.mem_propQCTopology f.sieve₀_le_sieve₀
  obtain ⟨S, φ, hP, hsurj, hsieve⟩ := exists_specMap_sigma 𝒰 h𝒰.1 h𝒰.2
  have hp := (F.isStackFor_iff_of_sieve_eq hsieve).1 (hff φ hP hsurj)
  have hcomp := hp.comp (J := Scheme.zariskiTopology) (fun _ i ↦ Sigma.ι 𝒰.X i)
    (fun _ ↦ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology)
    (fun _ ↦ (IsStackFor_generate_iff F _).1
      (F.isStackFor' _ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology))
  exact (F.isStackFor_iff_of_sieve_eq (sieve_comp_sigma_ι 𝒰.f)).1 hcomp

end TauCeti.AlgebraicGeometry
