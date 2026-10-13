/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# The elliptic curve 11.a2

This file defines the integral Weierstrass equation of the elliptic curve with LMFDB label 11.a2
(Cremona label 11a1), for reuse across worked examples.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., the tables, curve 11A1.
* The L-functions and modular forms database, elliptic curve 11.a2.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-- The curve 11.a2, `y² + y = x³ - x² - 10 x - 20`, as an integral Weierstrass model. -/
abbrev curve11a2 : WeierstrassCurve ℤ := ⟨0, -1, 1, -10, -20⟩

/-- The discriminant of `y² + y = x³ - x² - 10 x - 20` is `-11⁵`. -/
@[simp]
theorem Δ_curve11a2 : curve11a2.Δ = -11 ^ 5 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- 11.a2 is an elliptic curve over `ℚ`. -/
instance : (curve11a2.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve11a2]
  norm_num

end TauCeti.WorkedExamples
