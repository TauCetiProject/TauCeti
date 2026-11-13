/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Algebra.GroupAction.Prod

/-!
# Smooth independent product actions

The independent product of actions by `C^n` maps acts by `C^n` maps on the product manifold.
Use `open scoped TauCeti.IndependentProd` for the coordinatewise action and its smoothness
instance. The action uses the original manifold structures and the product model with corners.
-/

public section

open scoped Manifold ContDiff TauCeti.IndependentProd

namespace TauCeti.IndependentProd

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M N G K : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [Monoid G] [Monoid K]
  [MulAction G M] [MulAction K N] {n : ℕ∞ω}

/-- Independent products of `C^n` action maps are `C^n`. -/
@[to_additive /-- Independent products of `C^n` additive action maps are `C^n`. -/]
scoped instance contMDiffConstSMul [ContMDiffConstSMul I n G M] [ContMDiffConstSMul J n K N] :
    ContMDiffConstSMul (I.prod J) n (G × K) (M × N) where
  contMDiff_const_smul g := (contMDiff_const_smul g.1).prodMap (contMDiff_const_smul g.2)

end TauCeti.IndependentProd
