/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# Polynomial Gauss norms as suprema

The finite-support definition of the polynomial Gauss norm agrees with the supremum over
all coefficients. This allows coefficientwise local height formulas to use the Gauss norm's
multiplicativity at nonarchimedean places.
-/

public section

namespace Polynomial

/-- A polynomial Gauss norm is the supremum over all weighted coefficients, including the
zero coefficients outside its support. -/
theorem gaussNorm_eq_iSup {R F : Type*} [Semiring R] [FunLike F R ℝ]
    [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (p : R[X]) (v : F) {c : ℝ}
    (hc : 0 ≤ c) : p.gaussNorm v c = ⨆ i : ℕ, v (p.coeff i) * c ^ i := by
  rw [← gaussNorm_coe_powerSeries v p hc, PowerSeries.gaussNorm_eq]
  simp only [coeff_coe]

end Polynomial
