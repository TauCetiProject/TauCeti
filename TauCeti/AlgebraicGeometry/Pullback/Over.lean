/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finiteness and quasi-compactness under `Over.pullback` of schemes

Mathlib proves stability of `LocallyOfFiniteType` and `QuasiCompact` under `Limits.pullback`,
which yields `LocallyOfFiniteType (pullback.snd Y.hom f)` and `CompactSpace (pullback Y.hom f)`
directly. Because `CategoryTheory.Over.pullback` is not reducible, typeclass search on objects of
`Over S'` obtained via `(Over.pullback f).obj Y` does not unfold the underlying scheme or
structure morphism automatically. This file registers the corresponding instances on
`((Over.pullback f).obj Y).hom` and `((Over.pullback f).obj Y).left` for arbitrary base-change
morphisms of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.locallyOfFiniteType_over_pullback_obj_hom`: base change along any
  morphism of schemes preserves `LocallyOfFiniteType` on structure morphisms in `Over`.
* `TauCeti.AlgebraicGeometry.compactSpace_over_pullback_obj_left`: base change along a
  quasi-compact morphism of schemes preserves `CompactSpace` on underlying schemes in `Over`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- Base change along any morphism of schemes preserves `LocallyOfFiniteType` of the structure
morphism of an object in `Over S`. -/
instance locallyOfFiniteType_over_pullback_obj_hom {S S' : Scheme.{u}} (f : S' ⟶ S)
    (Y : Over S) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType ((Over.pullback f).obj Y).hom := by
  dsimp only [Over.pullback, Over.mk_hom]
  infer_instance

/-- Base change along a quasi-compact morphism of schemes preserves quasi-compactness of the
underlying topological space of an object in `Over S`. -/
instance compactSpace_over_pullback_obj_left {S S' : Scheme.{u}} (f : S' ⟶ S) [QuasiCompact f]
    (Y : Over S) [CompactSpace Y.left] :
    CompactSpace ((Over.pullback f).obj Y).left := by
  dsimp only [Over.pullback, Over.mk_left]
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst Y.hom f)

end AlgebraicGeometry

end TauCeti
