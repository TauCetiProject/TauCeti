/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms are syntomic

A smooth morphism of relative dimension `n` is syntomic of relative dimension `n` over an
arbitrary scheme base. Its standard smooth affine charts are standard syntomic charts of the
same dimension. In particular, smooth relative curves satisfy the complete-intersection
condition in the singular-locus characterization of nodal families.

The comparison is a low-priority instance, so the syntomic base-change and locality API applies
to smooth morphisms without separately choosing complete-intersection presentations.

## Main results

* `TauCeti.AlgebraicGeometry.SyntomicOfRelativeDimension.of_smoothOfRelativeDimension`:
  smooth morphisms are syntomic with the same relative dimension.

## References

* [Stacks Project, Lemma 10.137.9, Tag 00TA](https://stacks.math.columbia.edu/tag/00TA):
  smooth ring maps are syntomic. The algebraic comparison is provided by
  `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.of_standardSmooth`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A smooth morphism of relative dimension `n` is syntomic of relative dimension `n`. -/
instance (priority := low) SyntomicOfRelativeDimension.of_smoothOfRelativeDimension
    {n : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension n f] :
    SyntomicOfRelativeDimension n f where
  exists_isStandardSyntomicOfRelativeDimension x := by
    obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hx, e, h.isStandardSyntomicOfRelativeDimension⟩

end TauCeti.AlgebraicGeometry
