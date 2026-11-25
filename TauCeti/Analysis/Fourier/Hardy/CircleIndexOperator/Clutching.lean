/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Affine
public import TauCeti.Analysis.Fourier.Hardy.CircleIndexOperator.AffineClutching
public import TauCeti.Analysis.Fourier.Hardy.CircleIndexOperator.Symbol
public import TauCeti.Topology.Circle.Degree.Square
import TauCeti.Topology.Circle.Metric

/-!
# Clutching and winding for the full circle index symbol

The scalar of the full Fourier index symbol descends to the period-one cylinder. At normalized
covector `s` the actual frequency is `2 * s`. Its affine homotopy to
`circleIndexAffineScalar` has norm at least one on both closed ends of the cylinder, uniformly
in the cutoff and time. The oriented rectangle therefore supplies boundary data for the symbol.
Its top edge runs once around the circle in the direction of decreasing position, giving the
actual symbol winding number `-1`.

The rectangle and its orientation follow Atiyah–Singer, *The Index of Elliptic Operators: I*,
§8, pp. 525–526, Fig. 3. The comparison outside the strip is adapted from
`CirclePointThom.lean` in the Lean-Atiyah-Singer formalization by Alpha Squared Labs and Codex.
[Atiyah–Singer I](https://doi.org/10.2307/1970715)
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
-/

public section

noncomputable section

namespace TauCeti

local notation "ι" => OrthonormalBasis.repr (OrthonormalBasis.singleton (Fin 1) ℝ)

variable (ρ : FrequencyCutoff (CoordinateSpace 1))

/-- The straight-line homotopy from the actual full symbol to the affine representative has
norm at least one on both ends of the cylinder, including the two edges of the strip. -/
theorem one_le_norm_affine_circleIndexSymbolScalar (t : unitInterval) (z : Circle) {s : ℝ}
    (hs : 1 ≤ |s|) :
    1 ≤ ‖ContinuousMap.Homotopy.affine (circleIndexSymbolScalar ρ) circleIndexAffineScalar
      (t, z, s)‖ := by
  rw [ContinuousMap.Homotopy.affine_apply, AffineMap.lineMap_apply_module,
    circleIndexAffineScalar_apply]
  simp only [Complex.real_smul]
  rcases le_abs.mp hs with h | h
  case' inl =>
    rw [circleIndexSymbolScalar_of_one_le ρ z h]
    convert Circle.one_le_norm_lineMap_of_one_le 1 z (t := 1 + t * (s - 1) / 2)
      (le_add_of_nonneg_right <| div_nonneg (mul_nonneg t.property.1 (sub_nonneg.mpr h))
        zero_le_two) using 2
  case' inr =>
    rw [circleIndexSymbolScalar_of_le_half ρ z (by linarith)]
    convert Circle.one_le_norm_lineMap_of_one_le z 1 (t := 1 + t * (-1 - s) / 2)
      (le_add_of_nonneg_right <| div_nonneg (mul_nonneg t.property.1 (by linarith)) zero_le_two)
      using 2
  all_goals
    simp [AffineMap.lineMap_apply_module, Complex.real_smul]
    ring

/-- The direction of the full symbol on the square, with value `1` at its zeros.
The scalar has norm one on the boundary, where its phase gives the winding number. -/
def circleIndexBoundaryPhase (y : Fin 2 → unitInterval) : Circle :=
  Circle.exp (Complex.arg ((circleFourierIndexSymbol ρ).toSymbol.coefficient
    (ι (y 0), ι (2 * (2 * (y 1 : ℝ) - 1))) 1))

/-- In cylinder coordinates the phase is the direction of the scalar wherever it is nonzero.
On the boundary the scalar has norm one. At a zero, `Complex.arg 0 = 0` gives phase `1`. -/
theorem circleIndexBoundaryPhase_apply (y : Fin 2 → unitInterval) :
    circleIndexBoundaryPhase ρ y = Circle.exp (Complex.arg (circleIndexSymbolScalar ρ
      (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1))) := by
  rw [circleIndexBoundaryPhase, coefficient_toSymbol_circleFourierIndexSymbol_apply_one]

/-- On the boundary the actual scalar already has norm one, so taking its phase preserves it. -/
@[simp] theorem coe_circleIndexBoundaryPhase {y : Fin 2 → unitInterval}
    (hy : y ∈ Cube.boundary (Fin 2)) :
    (circleIndexBoundaryPhase ρ y : ℂ) = circleIndexSymbolScalar ρ
      (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1) := by
  have hnorm : ‖circleIndexSymbolScalar ρ
      (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1)‖ = 1 := by
    obtain ⟨i, hi | hi⟩ := hy <;> fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
      norm_num [hi, -Circle.coe_exp]
  rw [circleIndexBoundaryPhase_apply, Circle.coe_exp]
  simpa only [hnorm, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I
    (circleIndexSymbolScalar ρ (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1))

/-- The phase is continuous along the entire boundary, including where it crosses `-1`. -/
theorem continuousOn_circleIndexBoundaryPhase :
    ContinuousOn (circleIndexBoundaryPhase ρ) (Cube.boundary (Fin 2)) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  exact ((circleIndexSymbolScalar ρ).continuous.comp (by fun_prop)).continuousOn.congr
    fun _ hy ↦ coe_circleIndexBoundaryPhase ρ hy

/-- The full circle index symbol has winding number `-1` on the counterclockwise rectangle.
The three constant edges have lift zero, and the top lift increases by `2π` before its
orientation is reversed. -/
@[simp] theorem squareBoundaryDegree_circleIndexBoundaryPhase :
    squareBoundaryDegree (circleIndexBoundaryPhase ρ) = -1 := by
  have h := squareBoundaryDegree_mul_two_pi_eq (continuousOn_circleIndexBoundaryPhase ρ)
    (θB := fun _ ↦ 0) (θR := fun _ ↦ 0) (θT := fun x ↦ 2 * Real.pi * (x : ℝ))
    (θL := fun _ ↦ 0) continuous_const continuous_const (by fun_prop) continuous_const
    (fun x ↦ by simp [circleIndexBoundaryPhase_apply])
    (fun x ↦ by simp [circleIndexBoundaryPhase_apply])
    (fun x ↦ by norm_num [circleIndexBoundaryPhase_apply, -Circle.coe_exp])
    (fun x ↦ by simp [circleIndexBoundaryPhase_apply])
  apply squareBoundaryDegree_eq_of_mul_two_pi
  simpa using h

end TauCeti
