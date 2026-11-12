/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.CStarAlgebra.Unitary.Basic

/-!
# Compactness of finite-dimensional unitary operators

`Unitary.compactSpace_continuousLinearMap` gives compactness of the unitary operators on a
finite-dimensional inner product space over an `RCLike` field, including dimension zero.
This supplies the compact typical fiber of orthonormal frame bundles. The explicit
`CompleteSpace V` assumption supplies the adjoint star structure over a variable scalar field.
-/

public section

/-- The unitary operators of a finite-dimensional inner product space form a compact space. -/
instance Unitary.compactSpace_continuousLinearMap
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V] [FiniteDimensional 𝕜 V] : CompactSpace (unitary (V →L[𝕜] V)) := by
  have : ProperSpace (V →L[𝕜] V) := FiniteDimensional.proper_rclike 𝕜 _
  infer_instance
