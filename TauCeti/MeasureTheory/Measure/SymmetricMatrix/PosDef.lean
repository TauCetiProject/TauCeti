/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The positive-definite cone is open and measurable

On the symmetric subspace, positive definiteness cuts out an open subset by
`Matrix.isOpen_setOf_posDef_selfAdjoint`.

The Wishart densities are supported on this cone, so its measurability is part of the
carrier API.

The cone is also packaged as a subtype, `TauCeti.PosDefMatrix`, which is the carrier the
Wishart and Cholesky APIs are stated on.

## Main declarations

* `TauCeti.PosDefMatrix` — the positive-definite cone in the space of real symmetric matrices.
* `TauCeti.measurableSet_posDefMatrix` — the positive-definite cone is measurable.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- The cone of positive-definite real symmetric matrices of size `p`. -/
abbrev PosDefMatrix (p : ℕ) :=
  {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) //
    (A : Matrix (Fin p) (Fin p) ℝ).PosDef}

/-- The positive-definite cone is measurable in the symmetric subspace. -/
theorem measurableSet_posDefMatrix (p : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have h : IsOpen {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := Matrix.isOpen_setOf_posDef_selfAdjoint
  exact h.measurableSet

end TauCeti
