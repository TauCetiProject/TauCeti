/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Affine
public import TauCeti.AlgebraicGeometry.Descent.Gluing
public import TauCeti.AlgebraicGeometry.Descent.MorphismProperty
public import TauCeti.CategoryTheory.EffectiveEpi.Refinement
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Descent of schemes affine over the cover along fpqc morphisms

For a flat quasi-compact morphism `p : S' ⟶ S` with affine target, every descent
datum on a scheme affine over `S'` has an affine model over `S`. The source `S'` need not be
affine or quasi-separated. Replace it by a finite disjoint union of affine opens, apply affine
descent along the composite cover, and recover the original datum by cover refinement.

Over an arbitrary base, for `p` moreover surjective, apply this over each affine open `U` of `S`,
to the base change of the datum along `U ×_S S' ⟶ U`, and glue the resulting models over `U`
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_forall_affineOpens_pullbackAlong`). The
glued model is affine over `S`, and it inherits every property of `X ⟶ S'` satisfying fpqc
descent (`TauCeti.DescentDatum.Hom.mem_of_descendsAlong`): a descent datum on a closed subscheme
of `S'`, or on a scheme finite over `S'`, descends to a closed subscheme of `S`, or to a scheme
finite over `S`.

The comparison is an isomorphism of descent data, so it includes the cocycle. When `p` is
surjective, uniqueness of the model is supplied by `TauCeti.DescentDatum.Hom.descendIso`.

## Main results

* `TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso_of_quasiCompact`: affine descent
  along a flat quasi-compact morphism with affine target.
* `TauCeti.DescentDatum.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact`: **effective
  descent for schemes affine over the cover** along a surjective, flat and quasi-compact morphism,
  over an arbitrary base.
* `TauCeti.DescentDatum.exists_isClosedImmersion_baseChange_hom_isIso_of_quasiCompact` and
  `TauCeti.DescentDatum.exists_isFinite_baseChange_hom_isIso_of_quasiCompact`: effective descent
  for closed subschemes and for finite schemes.

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

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [Surjective p] [Flat p] [QuasiCompact p] {X : Over S'}
  (D : DescentDatum p X)

/-- **Effective descent for schemes affine over the cover** (Stacks, Tag 0245). Let
`p : S' ⟶ S` be surjective, flat and quasi-compact, over an arbitrary base `S`. Every descent datum
relative to `p` on a scheme affine over `S'` is isomorphic to the canonical descent datum on the
base change of a scheme affine over `S`. -/
theorem exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact [IsAffineHom X.hom] :
    ∃ X₀ : Over S, IsAffineHom X₀.hom ∧ ∃ f : Hom (baseChange p X₀) D, IsIso f.hom := by
  obtain ⟨X₀, f, hf⟩ := exists_baseChange_hom_isIso_of_forall_affineOpens_pullbackAlong fun U ↦ by
    -- Over an affine open `U`, the base change of `D` acts on a scheme affine over `U ×_S S'`,
    -- relative to the flat quasi-compact morphism `U ×_S S' ⟶ U` with affine target.
    have : IsAffineHom (pullbackAlongObj (p := p) U.1.ι X).hom := by
      simp only [pullbackAlongObj, Over.pullback_obj_hom]
      -- Mathlib has no instance for base changes of affine morphisms, so stability under base
      -- change is applied by name.
      exact isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
    have : IsAffine U.1.toScheme := U.2
    obtain ⟨Y₀, -, f, hf⟩ :=
      exists_isAffine_baseChange_hom_isIso_of_quasiCompact (D.pullbackAlong U.1.ι)
    exact ⟨Y₀, f, hf⟩
  exact ⟨X₀, f.mem_of_descendsAlong (P := @IsAffineHom) inferInstance, f, hf⟩

/-- **Effective descent for closed subschemes.** For `p : S' ⟶ S` surjective, flat and
quasi-compact, a descent datum relative to `p` on a closed subscheme of `S'` is isomorphic to the
canonical descent datum on the base change of a closed subscheme of `S`. -/
theorem exists_isClosedImmersion_baseChange_hom_isIso_of_quasiCompact [IsClosedImmersion X.hom] :
    ∃ X₀ : Over S, IsClosedImmersion X₀.hom ∧ ∃ f : Hom (baseChange p X₀) D, IsIso f.hom := by
  obtain ⟨X₀, -, f, hf⟩ := D.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact
  exact ⟨X₀, f.mem_of_descendsAlong (P := @IsClosedImmersion) inferInstance, f, hf⟩

/-- **Effective descent for finite schemes.** For `p : S' ⟶ S` surjective, flat and quasi-compact,
a descent datum relative to `p` on a scheme finite over `S'` is isomorphic to the canonical descent
datum on the base change of a scheme finite over `S`. -/
theorem exists_isFinite_baseChange_hom_isIso_of_quasiCompact [IsFinite X.hom] :
    ∃ X₀ : Over S, IsFinite X₀.hom ∧ ∃ f : Hom (baseChange p X₀) D, IsIso f.hom := by
  obtain ⟨X₀, -, f, hf⟩ := D.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact
  exact ⟨X₀, f.mem_of_descendsAlong (P := @IsFinite) inferInstance, f, hf⟩

end TauCeti.DescentDatum
