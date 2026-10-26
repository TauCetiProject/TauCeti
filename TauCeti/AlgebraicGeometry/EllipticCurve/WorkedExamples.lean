/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Elliptic curves for worked examples

This file defines integral Weierstrass equations of elliptic curves over `ℚ` that are used across
several worked examples, together with the affine equations of their rational points and their
basic invariants:

| LMFDB label | Cremona label | `[a₁, a₂, a₃, a₄, a₆]` | `Δ` | `c₄` |
|---|---|---|---|---|
| 11.a2 | 11a1 | `[0, -1, 1, -10, -20]` | `-11⁵` | `2⁴ · 31` |
| 37.a1 | 37a1 | `[0, 0, 1, -1, 0]` | `37` | `2⁴ · 3` |

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., the tables, curves 11A1 and
  37A1.
* The L-functions and modular forms database, elliptic curves 11.a2 and 37.a1.
-/

public section

open WeierstrassCurve

namespace TauCeti.WorkedExamples

/-! ### The curve 11.a2 (Cremona 11a1) -/

/-- The curve 11.a2, `y² + y = x³ - x² - 10 x - 20`, as an integral Weierstrass model. -/
abbrev curve11a2 : WeierstrassCurve ℤ := ⟨0, -1, 1, -10, -20⟩

/-- The rational points of 11.a2 are the solutions of `y² + y = x³ - x² - 10 x - 20`. -/
theorem equation_curve11a2_iff (x y : ℚ) :
    (curve11a2.baseChange ℚ).toAffine.Equation x y ↔ y ^ 2 + y = x ^ 3 - x ^ 2 - 10 * x - 20 := by
  rw [Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero,
    map_one, map_neg, map_ofNat]
  constructor <;> intro h <;> linear_combination h

/-- The discriminant of `y² + y = x³ - x² - 10 x - 20` is `-11⁵`. -/
@[simp]
theorem Δ_curve11a2 : curve11a2.Δ = -11 ^ 5 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- The invariant `c₄` of `y² + y = x³ - x² - 10 x - 20` is `496 = 2⁴ · 31`. -/
@[simp]
theorem c₄_curve11a2 : curve11a2.c₄ = 496 := by
  simp [c₄, b₂, b₄]

/-- 11.a2 is an elliptic curve over `ℚ`. -/
instance : (curve11a2.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve11a2]
  norm_num

/-! ### The curve 37.a1 -/

/-- The curve 37.a1, `y² + y = x³ - x`, as an integral Weierstrass model. -/
abbrev curve37a1 : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-- The rational points of 37.a1 are the solutions of `y² + y = x³ - x`. -/
theorem equation_curve37a1_iff (x y : ℚ) :
    (curve37a1.baseChange ℚ).toAffine.Equation x y ↔ y ^ 2 + y = x ^ 3 - x := by
  rw [Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero,
    map_one, map_neg]
  constructor <;> intro h <;> linear_combination h

/-- The discriminant of `y² + y = x³ - x` is `37`. -/
@[simp]
theorem Δ_curve37a1 : curve37a1.Δ = 37 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- The invariant `c₄` of `y² + y = x³ - x` is `48 = 2⁴ · 3`. -/
@[simp]
theorem c₄_curve37a1 : curve37a1.c₄ = 48 := by
  simp [c₄, b₂, b₄]

/-- 37.a1 is an elliptic curve over `ℚ`. -/
instance : (curve37a1.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve37a1]
  norm_num

end TauCeti.WorkedExamples
