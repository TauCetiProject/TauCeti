/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smoothness of basis coordinates

The coordinates of a `C^n` map into a finite-dimensional space in any basis are `C^n`
(`Module.Basis.contDiffOn_repr_apply`), since each coordinate is a continuous linear functional.
In particular so are the entries of the matrix of a `C^n` operator-valued map.
-/

public section

namespace Module.Basis

variable {𝕜 E F κ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {n : WithTop ℕ∞} {U : Set E} {f : E → F}

/-- The coordinates in a basis of a `C^n` map into a finite-dimensional space are `C^n`. -/
theorem contDiffOn_repr_apply (b : Basis κ 𝕜 F) (hf : ContDiffOn 𝕜 n f U) (m : κ) :
    ContDiffOn 𝕜 n (fun x ↦ b.repr (f x) m) U :=
  (b.coord m).toContinuousLinearMap.contDiff.comp_contDiffOn hf

end Module.Basis
