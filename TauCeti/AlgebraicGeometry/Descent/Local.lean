/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import TauCeti.AlgebraicGeometry.Morphisms.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum

/-!
# Isomorphisms of descent data are local on the base

Let `p : S' ⟶ S` be a morphism of schemes. A morphism `f` of descent data relative to `p`
(`TauCeti.DescentDatum.Hom`) is an isomorphism as soon as its base changes
`f.pullbackAlong (𝒰.f i)` along the members of an open cover `𝒰` of `S` are. Combined with
`TauCeti.DescentDatum.baseChangePullbackAlongHom`, which identifies the base change of a
canonical descent datum with a canonical descent datum, this reduces showing that a comparison
morphism between a descent datum and a canonical descent datum `baseChange p X₀` is an
isomorphism, over an arbitrary base `S`, to the same question over the members of an affine open
cover of `S`, where effective descent for affine schemes applies
(`TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso_pullbackAlong`).

## Main statements

* `TauCeti.DescentDatum.Hom.isIso_hom_iff_of_openCover`: a morphism of descent data relative to
  `p : S' ⟶ S` is an isomorphism if and only if its base change along every member of an open
  cover of `S` is.

## References

* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

/-- **Isomorphisms of descent data are local on the base.** A morphism `f` of descent data
relative to `p : S' ⟶ S` is an isomorphism over `S'` if and only if, for an open cover `𝒰` of
`S`, each base change `f.pullbackAlong (𝒰.f i)` is an isomorphism over `Uᵢ ×_S S'`. -/
theorem DescentDatum.Hom.isIso_hom_iff_of_openCover {S S' : Scheme.{u}} {p : S' ⟶ S}
    {X Y : Over S'} {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    (𝒰 : S.OpenCover) : IsIso f.hom ↔ ∀ i, IsIso (f.pullbackAlong (𝒰.f i)).hom := by
  -- The open subschemes `Uᵢ ×_S S'` cover `S'`, and `f.pullbackAlong (𝒰.f i)` is the base
  -- change of `f` along `Uᵢ ×_S S' ⟶ S'`. The members of `𝒰.pullback₂ p` are by definition the
  -- projections `pullback.snd (𝒰.f i) p`, indexed by the index type of `𝒰`.
  have key := IsZariskiLocalAtTarget.iff_of_openCover_overPullback
    (P := MorphismProperty.isomorphisms Scheme) (𝒰.pullback₂ p) f.hom
  simp only [MorphismProperty.isomorphisms.iff] at key
  simp only [Hom.pullbackAlong_hom, ← isIso_iff_of_reflects_iso _ (Over.forget _)]
  exact key

end TauCeti
