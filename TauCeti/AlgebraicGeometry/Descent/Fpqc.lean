/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Affine
public import TauCeti.CategoryTheory.EffectiveEpi.Refinement
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Affine descent along fpqc morphisms over an affine base

For a flat quasi-compact morphism `p : S' ⟶ S` with affine target, every descent
datum on a scheme affine over `S'` has an affine model over `S`. The source `S'` need not be
affine or quasi-separated. Replace it by a finite disjoint union of affine opens, apply affine
descent along the composite cover, and recover the original datum by cover refinement.

The comparison is an isomorphism of descent data, so it includes the cocycle. When `p` is
surjective, uniqueness of the model is supplied by `TauCeti.DescentDatum.Hom.descendIso`.

## References

* [The Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.DescentDatum

universe u

/-- **Affine descent along a flat quasi-compact morphism over an affine base.**
A scheme affine over `S'`, with a descent datum relative to a flat quasi-compact `p : S' ⟶ S`,
descends to an affine scheme over `S` when `S` is affine.
No affineness hypothesis on `p` is needed. -/
theorem exists_isAffine_baseChange_hom_isIso_of_quasiCompact
    {S S' : Scheme.{u}} {p : S' ⟶ S} [IsAffine S] [Flat p] [QuasiCompact p]
    {X : Over S'} [IsAffineHom X.hom] (D : DescentDatum p X) :
    ∃ X₀ : Over S, IsAffine X₀.left ∧ ∃ f : Hom (baseChange p X₀) D, IsIso f.hom := by
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace p
  -- Name the locality and identity instances explicitly so elaboration need not identify
  -- the eta-expanded morphism properties during typeclass search.
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities (@Etale.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  obtain ⟨T, q, hsurj, hetale, haffine⟩ :=
    S'.exists_hom_isAffine_of_isZariskiLocalAtSource @Etale
  have : Surjective q := hsurj
  have : Etale q := hetale
  have : IsAffine T := haffine
  have : IsAffine ((Over.pullback q).obj X).left :=
    IsAffine.of_isPullback (IsPullback.of_hasPullback X.hom q).flip
  obtain ⟨X₀, hX₀, f, hf⟩ := exists_isAffine_baseChange_hom_isIso (D.refine q)
  exact ⟨X₀, hX₀, (D.exists_baseChange_hom_isIso_iff_refine q X₀).mpr ⟨f, hf⟩⟩

end TauCeti.DescentDatum
