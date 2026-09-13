/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Determinant
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank

/-!
# Symmetric matrices and their Lebesgue measure

This module re-exports the symmetric-matrix API: the carrier
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)` with its Frobenius structure and
upper-triangular coordinates (`TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic`), the
positive-definite cone (`TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef`), the coordinate
Lebesgue measure `TauCeti.symmetricLebesgue`
(`TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue`), the congruence action and its
Jacobian (`TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence`), the closedness of the rank
sublevel sets (`TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank`), and the nullity of the
singular matrices (`TauCeti.MeasureTheory.Measure.SymmetricMatrix.Determinant`). It declares
nothing of its own.
-/
