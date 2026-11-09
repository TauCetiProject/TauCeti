/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Divisibility of differences of compositions

Mathlib's `Polynomial.sub_dvd_eval_sub` says that `a - b` divides `p.eval a - p.eval b`. Applied
over the polynomial ring itself it gives `s - r ∣ p.comp s - p.comp r` for polynomials `s` and `r`
(`Polynomial.sub_dvd_comp_sub`).
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- `s - r` divides `p.comp s - p.comp r`. -/
theorem sub_dvd_comp_sub (p s r : R[X]) : s - r ∣ p.comp s - p.comp r := by
  simpa [eval_map, comp] using sub_dvd_eval_sub s r (p.map C)

end Polynomial
