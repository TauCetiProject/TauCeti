/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Quasi-compact cover pullback lemmas

This file complements `Mathlib.AlgebraicGeometry.Sites.QuasiCompact` by showing that pulling back
a cover with affine components over an affine target along a morphism from an affine scheme
preserves affineness of components (`Cover.isAffine_pullback₂`) and yields quasi-compact covering
morphisms (`Cover.quasiCompact_pullback₂`).

## Main results

* `AlgebraicGeometry.Scheme.Cover.isAffine_pullback₂`,
  `AlgebraicGeometry.Scheme.Cover.quasiCompact_pullback₂`: pulling back a cover with affine
  components over an affine target along a morphism from an affine scheme preserves affineness of
  components and yields quasi-compact covering morphisms.
-/

public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Pulling back a cover with affine components over an affine target along a morphism from an
affine scheme yields a cover with affine components. -/
lemma Cover.isAffine_pullback₂ {K : Precoverage Scheme.{u}} [K.IsStableUnderBaseChange]
    {T : Scheme.{u}} (𝒰 : Scheme.Cover.{w} K T) (h : S ⟶ T) [IsAffine S] [IsAffine T]
    (haff : ∀ i, IsAffine (𝒰.X i)) (j : (𝒰.pullback₂ h).I₀) :
    IsAffine ((𝒰.pullback₂ h).X j) := by
  -- `(𝒰.pullback₂ h).I₀` is definitionally `𝒰.I₀` (`PreZeroHypercover.pullback₂_I₀`), so
  -- quantifying over `i : 𝒰.I₀` lets `PreZeroHypercover.pullback₂_X` rewrite and matches `j`.
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
