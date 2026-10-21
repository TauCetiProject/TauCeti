/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
public import TauCeti.Topology.PL.Map

/-!
# Piecewise-linear homeomorphisms of weak polyhedra

This file packages a homeomorphism between the weak polyhedra of two precomplexes together with
ambient coordinate formulas that are piecewise linear on their realised coordinate images. The
package is independent of any particular subdivision construction, so stellar moves and other
realization-level constructions can reuse the same relation and its symmetry and composition laws.
-/

public section

open Set TauCeti AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι κ ν : Type*}

/-- The ambient coordinate image of the weak polyhedron of `A`. -/
abbrev realizedCoords (A : PreAbstractSimplicialComplex ι) : Set (ι → ℝ) :=
  range fun x : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} =>
    (x.1.1 : ι → ℝ)

/-- `A` and `B` have homeomorphic weak polyhedra via some `e` such that `e` and `e.symm` extend to
maps between their ambient coordinate spaces that are piecewise linear on the respective
coordinate images. The complexes may have different vertex types. -/
def PLHomeomorphic (A : PreAbstractSimplicialComplex ι)
    (B : PreAbstractSimplicialComplex κ) : Prop :=
  ∃ e : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex κ) // x.1.support ∈ B},
    ∃ f : (ι → ℝ) → (κ → ℝ), ∃ g : (κ → ℝ) → (ι → ℝ),
      IsPLOn f (realizedCoords A) ∧
      IsPLOn g (realizedCoords B) ∧
      (∀ x, f (x.1.1 : ι → ℝ) = (e x).1.1) ∧
      (∀ y, g (y.1.1 : κ → ℝ) = (e.symm y).1.1)

/-- The witness characterization of `PLHomeomorphic`. -/
theorem plHomeomorphic_iff {A : PreAbstractSimplicialComplex ι}
    {B : PreAbstractSimplicialComplex κ} :
    PLHomeomorphic A B ↔
      ∃ e : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
          {x : Realization (⊤ : AbstractSimplicialComplex κ) // x.1.support ∈ B},
        ∃ f : (ι → ℝ) → (κ → ℝ), ∃ g : (κ → ℝ) → (ι → ℝ),
          IsPLOn f (realizedCoords A) ∧
          IsPLOn g (realizedCoords B) ∧
          (∀ x, f (x.1.1 : ι → ℝ) = (e x).1.1) ∧
          (∀ y, g (y.1.1 : κ → ℝ) = (e.symm y).1.1) := Iff.rfl

/-- Construct a `PLHomeomorphic` witness from its homeomorphism and coordinate formulas. -/
theorem PLHomeomorphic.intro {A : PreAbstractSimplicialComplex ι}
    {B : PreAbstractSimplicialComplex κ}
    (e : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ A} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex κ) // x.1.support ∈ B})
    (f : (ι → ℝ) → (κ → ℝ)) (g : (κ → ℝ) → (ι → ℝ))
    (hf : IsPLOn f (realizedCoords A))
    (hg : IsPLOn g (realizedCoords B))
    (he : ∀ x, f (x.1.1 : ι → ℝ) = (e x).1.1)
    (heinv : ∀ y, g (y.1.1 : κ → ℝ) = (e.symm y).1.1) :
    PLHomeomorphic A B :=
  plHomeomorphic_iff.mpr ⟨e, f, g, hf, hg, he, heinv⟩

/-- Reflexivity of `PLHomeomorphic`. -/
theorem PLHomeomorphic.refl (A : PreAbstractSimplicialComplex ι) :
    PLHomeomorphic A A :=
  PLHomeomorphic.intro (Homeomorph.refl _) id id (isPLOn_id _) (isPLOn_id _)
    (fun _ => rfl) (fun _ => rfl)

/-- Symmetry of `PLHomeomorphic`. -/
theorem PLHomeomorphic.symm {A : PreAbstractSimplicialComplex ι}
    {B : PreAbstractSimplicialComplex κ}
    (h : PLHomeomorphic A B) : PLHomeomorphic B A := by
  rcases plHomeomorphic_iff.mp h with ⟨e, f, g, hf, hg, he, heinv⟩
  exact PLHomeomorphic.intro e.symm g f hg hf heinv he

/-- Transitivity of `PLHomeomorphic`. -/
theorem PLHomeomorphic.trans {A : PreAbstractSimplicialComplex ι}
    {B : PreAbstractSimplicialComplex κ} {C : PreAbstractSimplicialComplex ν}
    (hAB : PLHomeomorphic A B) (hBC : PLHomeomorphic B C) :
    PLHomeomorphic A C := by
  rcases plHomeomorphic_iff.mp hAB with ⟨e₁, f₁, g₁, hf₁, hg₁, he₁, he₁inv⟩
  rcases plHomeomorphic_iff.mp hBC with ⟨e₂, f₂, g₂, hf₂, hg₂, he₂, he₂inv⟩
  have hmap₁ : realizedCoords A ⊆ f₁ ⁻¹' realizedCoords B := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e₁ x, (he₁ x).symm⟩
  have hmap₂ : realizedCoords C ⊆ g₂ ⁻¹' realizedCoords B := by
    rintro _ ⟨y, rfl⟩
    exact ⟨e₂.symm y, (he₂inv y).symm⟩
  refine PLHomeomorphic.intro (e₁.trans e₂) (f₂ ∘ f₁) (g₁ ∘ g₂)
    (hf₂.comp hf₁ hmap₁) (hg₁.comp hg₂ hmap₂) ?_ ?_
  · intro x
    simp only [Function.comp_apply, he₁ x, he₂ (e₁ x), Homeomorph.trans_apply]
  · intro y
    simp only [Function.comp_apply, he₂inv y, he₁inv (e₂.symm y), Homeomorph.symm_trans_apply]

end PreAbstractSimplicialComplex
