/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# The elliptic curve 37.a1

This file defines the integral Weierstrass equation of the elliptic curve with LMFDB label 37.a1
(Cremona label 37a1), for reuse across worked examples.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., the tables, curve 37A1.
* The L-functions and modular forms database, elliptic curve 37.a1.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-- The curve 37.a1, `y² + y = x³ - x`, as an integral Weierstrass model. -/
abbrev curve37a1 : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-- The discriminant of `y² + y = x³ - x` is `37`. -/
theorem Δ_curve37a1 : curve37a1.Δ = 37 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- 37.a1 is an elliptic curve over `ℚ`. -/
instance : (curve37a1.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve37a1]
  norm_num

end TauCeti.WorkedExamples
