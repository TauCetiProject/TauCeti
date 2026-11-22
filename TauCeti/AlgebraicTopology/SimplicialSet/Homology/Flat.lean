/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Simplicial chains with flat coefficients

For a flat module `M` over a commutative ring `R`, the simplicial chain modules
`Cₙ(X; M) = ⨁ M`, one copy of `M` for each `n`-simplex of `X`, are flat
(`SSet.flat_chainComplex_X`), as direct sums of flat modules. This is the flat counterpart of
`SSet.projective_chainComplex_X`.
-/

public section

open CategoryTheory

open scoped Simplicial

universe w

namespace SSet

/-- The simplicial chain modules `Cₙ(X; M) = ⨁ M` with flat coefficients `M` are flat. -/
instance flat_chainComplex_X {R : Type w} [CommRing R] (X : SSet.{w}) (M : ModuleCat.{w} R)
    [Module.Flat R M] (n : ℕ) : Module.Flat R ((X.chainComplex M).X n) := by
  classical
  -- `Cₙ(X; M)` is by definition the coproduct of copies of `M` indexed by the `n`-simplices.
  exact .of_linearEquiv (ModuleCat.coprodIsoDirectSum fun _ : X _⦋n⦌ ↦ M).toLinearEquiv

end SSet
