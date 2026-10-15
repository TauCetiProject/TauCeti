/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Separatedness from an open cover of the source

A morphism `f : X ⟶ S` is separated when its diagonal `X ⟶ X ×_S X` is a closed immersion.
Given an open cover `{Uᵢ}` of `X`, the products `Uᵢ ×_S Uⱼ` cover `X ×_S X`, and the diagonal
restricted over `Uᵢ ×_S Uⱼ` is the canonical map `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ` from the intersection of
the two pieces (`pullback.mapDesc`). Over `Uᵢ ×_S Uᵢ` this map is the diagonal of `Uᵢ ⟶ S`. So `f`
is separated as soon as each piece is separated over `S` and the maps `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ` for
distinct pieces are closed immersions. When the pieces and `S` are affine and `Uᵢ ×_X Uⱼ` is affine,
the latter is the classical condition that the functions on `Uᵢ` and `Uⱼ` generate the functions on
the intersection.

This is the shape of Mathlib's proof that `Proj` is separated
(`AlgebraicGeometry.Proj.isSeparated`), with the computation on its affine charts abstracted away.
Mathlib's `AffineTargetMorphismProperty.diagonal_of_openCover_source` is the analogue for an affine
target and affine pieces, phrased for affine-target properties and asking for every pair of pieces;
here the target is arbitrary, and the pairs of equal pieces are replaced by the separatedness of
each piece over the target. It is the criterion used to show that a scheme glued from two affine
charts, such as the two-chart model of an algebraic function field, is separated.

Separated morphisms compose, so a scheme separated over a separated scheme is itself separated;
in particular a scheme proper over a separated base, such as a field, is a separated scheme.

## Main results

* `AlgebraicGeometry.IsSeparated.of_openCover`: `f` is separated if each piece of an open cover of
  its source is separated over the target and the pieces meet in closed subschemes of their
  products over the target.
* `AlgebraicGeometry.Scheme.IsSeparated.of_isSeparated`: the source of a separated morphism to a
  separated scheme is a separated scheme.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **Separatedness from an open cover of the source.** If every piece `Uᵢ` of an open cover of
`X` is separated over `S`, and for distinct pieces the canonical map `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ` is a
closed immersion, then `f : X ⟶ S` is separated. -/
theorem IsSeparated.of_openCover (f : X ⟶ S) (𝒰 : X.OpenCover) [∀ i, IsSeparated (𝒰.f i ≫ f)]
    (H : ∀ i j, i ≠ j → IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) :
    IsSeparated f := by
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f f) ?_⟩
  rintro ⟨i, j⟩
  -- Over `Uᵢ ×_S Uⱼ`, the diagonal of `f` is the base change of `Uᵢ ×_X Uⱼ ⟶ Uᵢ ×_S Uⱼ`.
  have h := pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) f
  -- `Cover.pullbackHom` is by definition `pullback.snd`, and the pieces of `openCoverOfLeftRight`
  -- are by definition these `pullback.map`s; but its index type is `𝒰.I₀ × 𝒰.I₀` only up to
  -- unfolding `Cover.copy`, which blocks rewriting, so `change` states the unfolded goal.
  change IsClosedImmersion (pullback.snd (pullback.diagonal f)
    (pullback.map (𝒰.f i ≫ f) (𝒰.f j ≫ f) f f (𝒰.f i) (𝒰.f j) (𝟙 S) (by simp) (by simp)))
  rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
  obtain rfl | hij := eq_or_ne i j
  · -- For a single piece, the map is the diagonal of `Uᵢ ⟶ S`, up to the isomorphism
    -- `Uᵢ ≅ Uᵢ ×_X Uᵢ` given by the diagonal of the open immersion `Uᵢ ⟶ X`.
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (pullback.diagonal (𝒰.f i))]
    convert (inferInstance : IsClosedImmersion (pullback.diagonal (𝒰.f i ≫ f))) using 1
    ext <;> simp
  · exact H i j hij

/-- **A scheme separated over a separated scheme is separated.** If `f : X ⟶ S` is separated and
`S` is a separated scheme, then so is `X`, since `X ⟶ ⊤_ Scheme` factors as `f` followed by the
separated morphism `S ⟶ ⊤_ Scheme`. For instance, a scheme proper over a field is separated. -/
theorem Scheme.IsSeparated.of_isSeparated (f : X ⟶ S) [IsSeparated f] [S.IsSeparated] :
    X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end AlgebraicGeometry
