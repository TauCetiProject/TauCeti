/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Projection lemmas for quasi-compact covers

This file complements `Mathlib.AlgebraicGeometry.Sites.QuasiCompact` by exposing the index,
component, morphism, and presieve projections of
`AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover`, together with finiteness, affineness, and
quasi-compactness preservation lemmas for `Cover.ofQuasiCompactCover`,
`Scheme.AffineCover.cover`, and `Cover.pullback₂`.

## Main results

* `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_I₀`,
  `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_X`,
  `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_f`,
  `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_presieve₀`: projections of
  `Cover.ofQuasiCompactCover`.
* `AlgebraicGeometry.Scheme.Cover.finite_ofQuasiCompactCover`,
  `AlgebraicGeometry.Scheme.Cover.isAffine_ofQuasiCompactCover`: finiteness and affineness of
  components are preserved by `Cover.ofQuasiCompactCover`.
* `AlgebraicGeometry.Scheme.AffineCover.finite_cover`,
  `AlgebraicGeometry.Scheme.AffineCover.isAffine_cover`,
  `AlgebraicGeometry.Scheme.AffineCover.finite_ofQuasiCompactCover`,
  `AlgebraicGeometry.Scheme.AffineCover.isAffine_ofQuasiCompactCover`: a finite affine cover of an
  affine scheme yields a finite affine `P`-cover and a quasi-compact cover with finite index type
  and affine components.
* `AlgebraicGeometry.Scheme.Cover.isAffine_pullback₂`,
  `AlgebraicGeometry.Scheme.Cover.quasiCompact_pullback₂`: pulling back a cover with affine
  components over an affine target along a morphism from an affine scheme preserves affineness of
  components and yields quasi-compact covering morphisms.
-/

public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

/-- The index type of `Cover.ofQuasiCompactCover 𝒰` is the index type of `𝒰`. -/
lemma Cover.ofQuasiCompactCover_I₀ (𝒰 : Scheme.Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    (Cover.ofQuasiCompactCover 𝒰).I₀ = 𝒰.I₀ :=
  rfl

/-- The covering objects of `Cover.ofQuasiCompactCover 𝒰` are those of `𝒰`. -/
lemma Cover.ofQuasiCompactCover_X (𝒰 : Scheme.Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    (Cover.ofQuasiCompactCover 𝒰).X = 𝒰.X :=
  rfl

/-- The covering morphisms of `Cover.ofQuasiCompactCover 𝒰` are those of `𝒰`. -/
lemma Cover.ofQuasiCompactCover_f (𝒰 : Scheme.Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    (Cover.ofQuasiCompactCover 𝒰).f = 𝒰.f :=
  rfl

/-- The presieve of `Cover.ofQuasiCompactCover 𝒰` is the presieve of `𝒰`. -/
lemma Cover.ofQuasiCompactCover_presieve₀ (𝒰 : Scheme.Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    (Cover.ofQuasiCompactCover 𝒰).presieve₀ = 𝒰.presieve₀ :=
  rfl

/-- If `𝒰` has a finite index type, then so does `Cover.ofQuasiCompactCover 𝒰`. -/
lemma Cover.finite_ofQuasiCompactCover (𝒰 : Scheme.Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] [hfin : Finite 𝒰.I₀] :
    Finite (Cover.ofQuasiCompactCover 𝒰).I₀ := by
  rw [Cover.ofQuasiCompactCover_I₀]
  exact hfin

/-- If every component of `𝒰` is affine, then every component of `Cover.ofQuasiCompactCover 𝒰` is
affine. -/
lemma Cover.isAffine_ofQuasiCompactCover (𝒰 : Scheme.Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] (haff : ∀ j, IsAffine (𝒰.X j))
    (j : (Cover.ofQuasiCompactCover 𝒰).I₀) :
    IsAffine ((Cover.ofQuasiCompactCover 𝒰).X j) := by
  rw [Cover.ofQuasiCompactCover_X]
  exact haff j

/-- A finite affine cover `𝒱` yields a `P`-cover `𝒱.cover` with finite index type. -/
lemma AffineCover.finite_cover (𝒱 : Scheme.AffineCover.{w} P S) [hfin : Finite 𝒱.I₀] :
    Finite 𝒱.cover.I₀ := by
  rw [AffineCover.cover_I₀]
  exact hfin

/-- Every component of `𝒱.cover` for an affine cover `𝒱` is affine. -/
lemma AffineCover.isAffine_cover (𝒱 : Scheme.AffineCover.{w} P S) (j : 𝒱.cover.I₀) :
    IsAffine (𝒱.cover.X j) := by
  have : ∀ i : 𝒱.I₀, IsAffine (𝒱.cover.X i) := fun i ↦ by
    rw [AffineCover.cover_X]
    infer_instance
  exact this j

/-- A finite affine cover `𝒱` of an affine scheme yields a quasi-compact cover with finite index
type. -/
lemma AffineCover.finite_ofQuasiCompactCover [IsAffine S] (𝒱 : Scheme.AffineCover.{w} P S)
    [Finite 𝒱.I₀] :
    Finite (Cover.ofQuasiCompactCover 𝒱.cover).I₀ := by
  have := AffineCover.finite_cover 𝒱
  exact Cover.finite_ofQuasiCompactCover 𝒱.cover

/-- A finite affine cover `𝒱` of an affine scheme yields a quasi-compact cover with affine
components. -/
lemma AffineCover.isAffine_ofQuasiCompactCover [IsAffine S] (𝒱 : Scheme.AffineCover.{w} P S)
    [Finite 𝒱.I₀] (j : (Cover.ofQuasiCompactCover 𝒱.cover).I₀) :
    IsAffine ((Cover.ofQuasiCompactCover 𝒱.cover).X j) :=
  Cover.isAffine_ofQuasiCompactCover 𝒱.cover (AffineCover.isAffine_cover 𝒱) j

/-- Pulling back a cover with affine components over an affine target along a morphism from an
affine scheme yields a cover with affine components. -/
lemma Cover.isAffine_pullback₂ {K : Precoverage Scheme.{u}} [K.IsStableUnderBaseChange]
    {T : Scheme.{u}} (𝒰 : Scheme.Cover.{w} K T) (h : S ⟶ T) [IsAffine S] [IsAffine T]
    (haff : ∀ i, IsAffine (𝒰.X i)) (j : (𝒰.pullback₂ h).I₀) :
    IsAffine ((𝒰.pullback₂ h).X j) := by
  have : ∀ i : 𝒰.I₀, IsAffine ((𝒰.toPreZeroHypercover.pullback₂ h).X i) := fun i ↦ by
    rw [PreZeroHypercover.pullback₂_X]
    have := haff i
    infer_instance
  exact this j

/-- Pulling back a cover with affine components over an affine target along a morphism from an
affine scheme yields quasi-compact covering morphisms. -/
lemma Cover.quasiCompact_pullback₂ {K : Precoverage Scheme.{u}} [K.IsStableUnderBaseChange]
    {T : Scheme.{u}} (𝒰 : Scheme.Cover.{w} K T) (h : S ⟶ T) [IsAffine S] [IsAffine T]
    (haff : ∀ i, IsAffine (𝒰.X i)) (j : (𝒰.pullback₂ h).I₀) :
    AlgebraicGeometry.QuasiCompact ((𝒰.pullback₂ h).f j) := by
  have : IsAffine ((𝒰.pullback₂ h).X j) := Cover.isAffine_pullback₂ 𝒰 h haff j
  exact quasiCompact_of_compactSpace _

end AlgebraicGeometry.Scheme
