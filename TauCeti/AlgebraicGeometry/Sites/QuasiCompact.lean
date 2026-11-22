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
component, and morphism projections of `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover`,
together with finiteness and affineness preservation lemmas for `Cover.ofQuasiCompactCover` and
`Scheme.AffineCover.cover`.

## Main results

* `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_I₀`,
  `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_X`,
  `AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover_f`: projections of
  `Cover.ofQuasiCompactCover`.
* `AlgebraicGeometry.Scheme.Cover.finite_ofQuasiCompactCover`,
  `AlgebraicGeometry.Scheme.Cover.isAffine_ofQuasiCompactCover`: finiteness and affineness of
  components are preserved by `Cover.ofQuasiCompactCover`.
* `AlgebraicGeometry.Scheme.AffineCover.finite_ofQuasiCompactCover`,
  `AlgebraicGeometry.Scheme.AffineCover.isAffine_ofQuasiCompactCover`: a finite affine cover of an
  affine scheme yields a quasi-compact cover with finite index type and affine components.
-/

public section

universe w u

open CategoryTheory

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

/-- A finite affine cover `𝒱` of an affine scheme yields a quasi-compact cover with finite index
type. -/
lemma AffineCover.finite_ofQuasiCompactCover [IsAffine S] (𝒱 : Scheme.AffineCover.{w} P S)
    [hfin : Finite 𝒱.I₀] :
    Finite (Cover.ofQuasiCompactCover 𝒱.cover).I₀ := by
  rw [Cover.ofQuasiCompactCover_I₀, AffineCover.cover_I₀]
  exact hfin

/-- A finite affine cover `𝒱` of an affine scheme yields a quasi-compact cover with affine
components. -/
lemma AffineCover.isAffine_ofQuasiCompactCover [IsAffine S] (𝒱 : Scheme.AffineCover.{w} P S)
    [Finite 𝒱.I₀] (j : (Cover.ofQuasiCompactCover 𝒱.cover).I₀) :
    IsAffine ((Cover.ofQuasiCompactCover 𝒱.cover).X j) := by
  have haff : ∀ i : 𝒱.I₀, IsAffine (𝒱.cover.X i) := fun i ↦ by
    rw [AffineCover.cover_X]
    infer_instance
  exact Cover.isAffine_ofQuasiCompactCover 𝒱.cover haff j

end AlgebraicGeometry.Scheme
