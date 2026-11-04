/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import TauCeti.RingTheory.Syntomic.Descent

/-!
# Syntomic morphisms satisfy fpqc descent

A morphism whose base change along a surjective, flat and quasi-compact morphism is syntomic of
relative dimension `n` is itself syntomic of relative dimension `n`. The affine statement is the
codescent of locally standard syntomic ring maps along faithfully flat ring maps
(`TauCeti.codescendsAlong_locally_isStandardSyntomicOfRelativeDimension_faithfullyFlat`), and
Mathlib's `AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat` globalizes it.

In particular syntomicity of fixed relative dimension is local on the base for the étale and the
fppf topologies.
-/

public section

open CategoryTheory MorphismProperty AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- **Syntomic morphisms satisfy fpqc descent.** Syntomicity of relative dimension `n` descends
along surjective, flat, quasi-compact morphisms. -/
instance SyntomicOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasicompact
    (n : ℕ) :
    MorphismProperty.DescendsAlong (@SyntomicOfRelativeDimension.{u} n)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat
    (codescendsAlong_locally_isStandardSyntomicOfRelativeDimension_faithfullyFlat n)

end TauCeti.AlgebraicGeometry
