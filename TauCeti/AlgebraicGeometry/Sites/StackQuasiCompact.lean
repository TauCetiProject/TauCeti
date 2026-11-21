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
      rw [PreZeroHypercover.presieve₀, ← Sieve.ofArrows, ← Sieve.pullbackArrows_comm,
        ← Presieve.ofArrows_pullback, IsPrestackFor_generate_iff]
      exact this _ (𝒰.pullback₂ h) hV
    refine IsPrestackFor.of_pullback T.affineOneHypercover (fun i ↦ ?_) (fun i j k _ _ _ _ h ↦ ?_)
    · exact hpull (T.affineOneHypercover.f i)
        ⟨T.affineOpenCover.X i, AffineOpenCover.openCover_X T.affineOpenCover i⟩
    · refine (hpull (T.affineOneHypercover.p₁ k ≫ T.affineOneHypercover.f i) (by
        dsimp only [Scheme.affineOneHypercover,
          GrothendieckTopology.OneHypercover.mk'_toPreOneHypercover,
          PreZeroHypercover.refineOneHypercover_Y]
        exact ⟨_, AffineOpenCover.openCover_X
          (pullback (T.affineCover.f i) (T.affineCover.f j)).affineOpenCover k⟩)).hom_ext h
  obtain ⟨R, rfl⟩ := hT
  wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
  · obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have hpull {V : Scheme.{u}} (h : V ⟶ Spec R) (hV : ∃ A : CommRingCat.{u}, V = Spec A) :
        F.IsPrestackFor ((Sieve.ofArrows 𝒱.cover.X 𝒱.cover.f).pullback h).arrows := by
      rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback, IsPrestackFor_generate_iff]
      obtain ⟨A, rfl⟩ := hV
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
      f.sieve₀_le_sieve₀ fun V g _ M N φ ψ h ↦ ?_
    refine (F.isPrestackFor' _ V.affineCover.mem_grothendieckTopology).hom_ext fun Z r hr ↦ ?_
    obtain ⟨_, a, _, ⟨i⟩, rfl⟩ := hr
    have hfi : (F.map (V.affineCover.f i).op.toLoc).toFunctor.map φ =
        (F.map (V.affineCover.f i).op.toLoc).toFunctor.map ψ := by
      refine (hpull (V.affineCover.f i ≫ g)
        ⟨V.affineOpenCover.X i, AffineOpenCover.openCover_X V.affineOpenCover i⟩).hom_ext
        fun W s hs ↦ ?_
      rw [Sieve.pullback_comp] at hs
      rw [← F.mapComp'_naturality_1 (V.affineCover.f i).op.toLoc s.op.toLoc
          (s ≫ V.affineCover.f i).op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]),
        h _ hs,
        F.mapComp'_naturality_1 (V.affineCover.f i).op.toLoc s.op.toLoc
          (s ≫ V.affineCover.f i).op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])]
    rw [← F.mapComp'_naturality_2 (V.affineCover.f i).op.toLoc a.op.toLoc
        (a ≫ V.affineCover.f i).op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]),
      hfi,
      F.mapComp'_naturality_2 (V.affineCover.f i).op.toLoc a.op.toLoc
        (a ≫ V.affineCover.f i).op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])]
  obtain ⟨S, φ, e, hP, hsurj, hφ⟩ := Cover.exists_specMap_sigma 𝒰.forgetQc h𝒰.1 h𝒰.2
  have hp : F.IsPrestackFor (.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f)) := by
    rw [Presieve.ofArrows_pUnit.{0}, ← IsPrestackFor_generate_iff,
      ← Sieve.generate_singleton_comp_of_isIso e.hom (Sigma.desc 𝒰.f), ← hφ,
      IsPrestackFor_generate_iff]
    exact hff φ hP hsurj
  have hcomp := hp.comp (fun _ i ↦ Sigma.ι 𝒰.X i)
    (fun _ ↦ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology)
  simp only [Sigma.ι_comp_desc] at hcomp
  have hsnd : Function.Surjective (@Sigma.snd PUnit.{1} fun _ ↦ 𝒰.I₀) :=
    fun i ↦ ⟨⟨PUnit.unit, i⟩, rfl⟩
  rwa [PreZeroHypercover.presieve₀,
    ← Presieve.ofArrows_comp_eq_of_surjective 𝒰.f hsnd]

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
    exact this _ (𝒰.pullback₂ (T.affineCover.f a))
      ⟨T.affineOpenCover.X a, AffineOpenCover.openCover_X T.affineOpenCover a⟩
  obtain ⟨R, rfl⟩ := hT
  wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
  · obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have h𝒱 := this R (.ofQuasiCompactCover 𝒱.cover)
      ⟨fun _ ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    rw [← IsStackFor_generate_iff] at h𝒱 ⊢
    exact h𝒱.of_le' F 𝒱.cover.mem_propQCTopology f.sieve₀_le_sieve₀
  obtain ⟨S, φ, e, hP, hsurj, hφ⟩ := Cover.exists_specMap_sigma 𝒰.forgetQc h𝒰.1 h𝒰.2
  have hp : F.IsStackFor (.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒰.X) (fun _ ↦ Sigma.desc 𝒰.f)) := by
    rw [Presieve.ofArrows_pUnit.{0}, ← IsStackFor_generate_iff,
      ← Sieve.generate_singleton_comp_of_isIso e.hom (Sigma.desc 𝒰.f), ← hφ,
      IsStackFor_generate_iff]
    exact hff φ hP hsurj
  have hcomp := hp.comp (J := Scheme.zariskiTopology) (fun _ i ↦ Sigma.ι 𝒰.X i)
    (fun _ ↦ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology)
    (fun _ ↦ (IsStackFor_generate_iff F _).1
      (F.isStackFor' _ (sigmaOpenCover 𝒰.X).mem_grothendieckTopology))
  simp only [Sigma.ι_comp_desc] at hcomp
  have hsnd : Function.Surjective (@Sigma.snd PUnit.{1} fun _ ↦ 𝒰.I₀) :=
    fun i ↦ ⟨⟨PUnit.unit, i⟩, rfl⟩
  rwa [PreZeroHypercover.presieve₀,
    ← Presieve.ofArrows_comp_eq_of_surjective 𝒰.f hsnd]

end TauCeti.AlgebraicGeometry
