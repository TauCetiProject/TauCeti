/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The addition formula and the monotonicity of the hyperbolic tangent

Mathlib's `Analysis/Complex/Trigonometric.lean` defines `Real.sinh`, `Real.cosh` and `Real.tanh`
and proves the two addition formulae `Real.sinh_add` and `Real.cosh_add`, but records none for
`Real.tanh`; `Analysis/SpecialFunctions/Artanh.lean` inverts `Real.tanh` on `(-1, 1)` and proves
that the inverse is strictly monotone, but does not state the monotonicity of `Real.tanh`
itself. This file supplies both.

## Main declarations

* `Real.tanh_add` — `tanh (a + b) = (tanh a + tanh b) / (1 + tanh a * tanh b)`: the hyperbolic
  tangent of a sum is the Möbius sum of the hyperbolic tangents.
* `Real.tanh_strictMono` and `Real.tanh_lt_tanh_iff` — `Real.tanh` is strictly monotone, so it
  compares two real numbers exactly as they compare.

The formula is the quotient of the other two, both sides carrying the factor
`cosh a * cosh b`, which is nonzero because `Real.cosh` is positive.

Where it is used: `TauCeti/Analysis/SpecialFunctions/Artanh.lean` inverts it into the additive
law of `Real.artanh`, which carries the Möbius addition of `(-1, 1)` to the addition of `ℝ`;
that law is in turn what makes the hyperbolic distance of the complex unit disc a metric, the
subject of layer L2 of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`).
-/

public section

namespace TauCeti

/-- **Addition formula for the hyperbolic tangent.** `Real.tanh (a + b)` is the Möbius sum
`(tanh a + tanh b) / (1 + tanh a * tanh b)`.

The pinned Mathlib has `Real.sinh_add` and `Real.cosh_add` but no addition formula for
`Real.tanh`. This one is their quotient, both sides of which carry the same factor: by those two
formulae `tanh a + tanh b = sinh (a + b) / (cosh a * cosh b)` and
`1 + tanh a * tanh b = cosh (a + b) / (cosh a * cosh b)`, and the right-hand denominator is
positive, so dividing cancels `cosh a * cosh b` and leaves `tanh (a + b)`. -/
theorem _root_.Real.tanh_add (a b : ℝ) :
    Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b) := by
  have ha : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  have hb : Real.cosh b ≠ 0 := (Real.cosh_pos b).ne'
  have hc : Real.cosh (a + b) ≠ 0 := (Real.cosh_pos _).ne'
  have hnum : Real.tanh a + Real.tanh b
      = Real.sinh (a + b) / (Real.cosh a * Real.cosh b) := by
    rw [Real.sinh_add, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hden : 1 + Real.tanh a * Real.tanh b
      = Real.cosh (a + b) / (Real.cosh a * Real.cosh b) := by
    rw [Real.cosh_add, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hne : 1 + Real.tanh a * Real.tanh b ≠ 0 := by
    rw [hden]
    exact div_ne_zero hc (mul_ne_zero ha hb)
  rw [eq_div_iff hne, hnum, hden, Real.tanh_eq_sinh_div_cosh (a + b)]
  field_simp

/-- **The hyperbolic tangent is strictly monotone.** It is inverted on its range `(-1, 1)` by
the strictly monotone `Real.artanh`, so it cannot reverse a strict inequality. -/
theorem _root_.Real.tanh_strictMono : StrictMono Real.tanh := by
  intro a b hab
  have ha : Real.tanh a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
  have hb : Real.tanh b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩
  by_contra h
  rw [not_lt] at h
  have hba := (Real.artanh_le_artanh_iff hb ha).mpr h
  rw [Real.artanh_tanh, Real.artanh_tanh] at hba
  exact absurd hab (not_lt.mpr hba)

/-- The hyperbolic tangent compares two real numbers exactly as they compare. -/
@[simp]
theorem _root_.Real.tanh_lt_tanh_iff {a b : ℝ} : Real.tanh a < Real.tanh b ↔ a < b :=
  Real.tanh_strictMono.lt_iff_lt

end TauCeti
