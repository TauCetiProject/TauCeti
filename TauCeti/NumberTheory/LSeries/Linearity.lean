/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Nonzero-scalar invariance of the abscissa of absolute convergence

Scaling the coefficients of a Dirichlet series by a nonzero complex constant leaves the set of
points of absolute convergence unchanged (`LSeriesSummable.smul_iff`), and therefore preserves
`LSeries.abscissaOfAbsConv` (`TauCeti.LSeries.abscissaOfAbsConv_smul_of_ne_zero`).
-/

public section

namespace TauCeti.LSeries

/-- Scaling the coefficients of a Dirichlet series by a nonzero complex constant does not change
its abscissa of absolute convergence. -/
theorem abscissaOfAbsConv_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (f : ℕ → ℂ) :
    _root_.LSeries.abscissaOfAbsConv (c • f) = _root_.LSeries.abscissaOfAbsConv f := by
  simp only [_root_.LSeries.abscissaOfAbsConv, LSeriesSummable.smul_iff hc]

end TauCeti.LSeries
