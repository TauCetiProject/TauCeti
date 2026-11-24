/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.Irreducible
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Krull dimension is a birational invariant over a field

Two birational schemes share an isomorphic dense open subscheme. For irreducible schemes locally of
finite type over a field, any nonempty open subscheme has the full Krull dimension of the ambient
scheme
(`TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType`), so
birational irreducible schemes locally of finite type over a field have the same Krull dimension.

## Main results

* `AlgebraicGeometry.Scheme.Birational.topologicalKrullDim_eq_of_locallyOfFiniteType`: birational
  irreducible schemes locally of finite type over a field have equal Krull dimension.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Birational

universe u

/-- Birational irreducible schemes locally of finite type over a field have the same Krull
dimension: they share an isomorphic nonempty open subscheme, which has the full dimension of
each. -/
theorem topologicalKrullDim_eq_of_locallyOfFiniteType {k : Type u} [Field k]
    {X Y : Scheme.{u}} (h : X.Birational Y) [IrreducibleSpace Y]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  have : IrreducibleSpace X := h.irreducibleSpace
  obtain ⟨e⟩ := h
  have : Nonempty (e.source : Scheme.{u}) := e.dense_source.nonempty.to_subtype
  have : Nonempty (e.target : Scheme.{u}) := e.dense_target.nonempty.to_subtype
  exact (topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType f
      e.source.ι.isOpenEmbedding).symm.trans <|
    e.iso.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans <|
      topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType g
        e.target.ι.isOpenEmbedding

end AlgebraicGeometry.Scheme.Birational
