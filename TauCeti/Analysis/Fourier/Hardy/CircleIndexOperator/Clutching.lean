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
public import TauCeti.Topology.Circle.Loop
import TauCeti.Topology.Circle.Metric

/-!
# Clutching and winding for the full circle index symbol

The scalar of the full Fourier index symbol descends to the period-one cylinder. At normalized
covector `s` the actual frequency is `2 * s`. Its affine homotopy to
`circleIndexAffineScalar` has norm at least one on both closed ends of the cylinder, uniformly
in the cutoff and time. These estimates give nonvanishing on the two horizontal edges of the
rectangle. Both vertical edges have circle position `1`, where the scalar is identically `1`.
The top edge runs once around the circle in the direction of decreasing position, giving the
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
theorem one_le_norm_homotopyAffine_circleIndexSymbolScalar (t : unitInterval) (z : Circle) {s : ℝ}
    (hs : 1 ≤ |s|) :
    1 ≤ ‖ContinuousMap.Homotopy.affine (circleIndexSymbolScalar ρ) circleIndexAffineScalar
      (t, z, s)‖ := by
  rw [ContinuousMap.Homotopy.affine_apply, circleIndexAffineScalar_eq_lineMap]
  rcases le_abs.mp hs with h | h
  · rw [circleIndexSymbolScalar_of_one_le ρ z h]
    have hchord :
        AffineMap.lineMap (z : ℂ) (AffineMap.lineMap 1 (z : ℂ) ((1 + s) / 2)) (t : ℝ) =
          AffineMap.lineMap 1 (z : ℂ) (1 + (t : ℝ) * (s - 1) / 2) := by
      rw [← AffineMap.lineMap_apply_one_sub (z : ℂ) 1, AffineMap.lineMap_lineMap_right,
        ← AffineMap.lineMap_apply_one_sub (1 : ℂ) (z : ℂ)]
      congr 1
      ring
    rw [hchord]
    exact Circle.one_le_norm_lineMap_of_one_le 1 z (by
      linarith [mul_nonneg t.property.1 (sub_nonneg.mpr h)])
  · rw [circleIndexSymbolScalar_of_le_half ρ z (by linarith)]
    have hchord :
        AffineMap.lineMap (1 : ℂ) (AffineMap.lineMap 1 (z : ℂ) ((1 + s) / 2)) (t : ℝ) =
          AffineMap.lineMap (z : ℂ) 1 (1 - (t : ℝ) * (1 + s) / 2) := by
      rw [AffineMap.lineMap_lineMap_right, ← AffineMap.lineMap_apply_one_sub (z : ℂ) 1]
      congr 1
      ring
    rw [hchord]
    exact Circle.one_le_norm_lineMap_of_one_le z 1 (by
      have hs₀ : 1 + s ≤ 0 := by linarith
      linarith [mul_nonpos_of_nonneg_of_nonpos t.property.1 hs₀])

/-- Outside the strip `Circle × [-1, 1]`, the homotopy from the full symbol to the affine
representative has invertible values at every time. -/
theorem isUnit_homotopyAffine_circleIndexSymbolScalar_of_notMem
    (t : unitInterval) (p : Circle × ℝ)
    (hp : p ∉ (Set.univ : Set Circle) ×ˢ Set.Icc (-1 : ℝ) 1) :
    IsUnit (ContinuousMap.Homotopy.affine (circleIndexSymbolScalar ρ) circleIndexAffineScalar
      (t, p)) := by
  have hs : 1 < |p.2| := lt_of_not_ge fun h ↦
    hp (Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_Icc.mpr (abs_le.mp h)⟩)
  have hnorm := one_le_norm_homotopyAffine_circleIndexSymbolScalar ρ t p.1 hs.le
  exact isUnit_iff_ne_zero.mpr (norm_pos_iff.mp (zero_lt_one.trans_le hnorm))

/-- The full symbol scalar on the unit square, with normalized covector ranging from `-1` to `1`.
The position variable traverses one period. -/
def circleIndexSquareScalar : C(Fin 2 → unitInterval, ℂ) :=
  (circleIndexSymbolScalar ρ).comp
    ⟨fun y ↦ (unitToCircle (y 0), 2 * (y 1 : ℝ) - 1), by fun_prop⟩

/-- The square coordinates give the position on the circle and its normalized covector. -/
@[simp] theorem circleIndexSquareScalar_apply (y : Fin 2 → unitInterval) :
    circleIndexSquareScalar ρ y = circleIndexSymbolScalar ρ
      (unitToCircle (y 0), 2 * (y 1 : ℝ) - 1) := (rfl)

private theorem squareScalar_bottom {y : Fin 2 → unitInterval} (h : y 1 = 0) :
    circleIndexSquareScalar ρ y = 1 := by simp [h]

private theorem squareScalar_top {y : Fin 2 → unitInterval} (h : y 1 = 1) :
    circleIndexSquareScalar ρ y = (unitToCircle (y 0) : ℂ) := by
  norm_num [h]

private theorem squareScalar_vertical {y : Fin 2 → unitInterval} (h : y 0 = 0 ∨ y 0 = 1) :
    circleIndexSquareScalar ρ y = 1 := by
  rcases h with h | h <;> simp [h]

private theorem norm_squareScalar_of_mem_boundary {y : Fin 2 → unitInterval}
    (hy : y ∈ Cube.boundary (Fin 2)) : ‖circleIndexSquareScalar ρ y‖ = 1 := by
  obtain ⟨i, hi⟩ := hy
  fin_cases i
  · rw [squareScalar_vertical ρ (by simpa using hi), norm_one]
  · rcases hi with hi | hi
    · rw [squareScalar_bottom ρ (by simpa using hi), norm_one]
    · rw [squareScalar_top ρ (by simpa using hi), Circle.norm_coe]

/-- The circle-valued phase of the full symbol on the square, with value `1` at its zeros. -/
def circleIndexSquarePhase (y : Fin 2 → unitInterval) : Circle :=
  Circle.phase (circleIndexSquareScalar ρ y) 1

/-- The phase is the circle direction of the scalar on the square. -/
theorem circleIndexSquarePhase_eq_phase (y : Fin 2 → unitInterval) :
    circleIndexSquarePhase ρ y =
      Circle.phase (circleIndexSquareScalar ρ y) 1 :=
  (rfl)

/-- At a zero of the square scalar the phase is `1`. -/
@[simp] theorem circleIndexSquarePhase_of_scalar_eq_zero {y : Fin 2 → unitInterval}
    (hy : circleIndexSquareScalar ρ y = 0) : circleIndexSquarePhase ρ y = 1 := by
  rw [circleIndexSquarePhase_eq_phase, hy,
    Circle.phase_zero]

/-- The phase of the actual coefficient at frequency twice the normalized covector. -/
theorem circleIndexSquarePhase_apply (y : Fin 2 → unitInterval) :
    circleIndexSquarePhase ρ y = Circle.phase
      ((circleFourierIndexSymbol ρ).toSymbol.coefficient
        (ι (y 0), ι (2 * (2 * (y 1 : ℝ) - 1))) 1) 1 := by
  rw [circleIndexSquarePhase_eq_phase,
    coefficient_toSymbol_circleFourierIndexSymbol_apply_one,
    circleIndexSquareScalar_apply, unitToCircle_apply]

/-- On the boundary the scalar has norm one, so taking its phase preserves it. -/
@[simp] theorem coe_circleIndexSquarePhase_of_mem_boundary {y : Fin 2 → unitInterval}
    (hy : y ∈ Cube.boundary (Fin 2)) :
    (circleIndexSquarePhase ρ y : ℂ) = circleIndexSquareScalar ρ y := by
  have hn := norm_squareScalar_of_mem_boundary ρ hy
  have hz : circleIndexSquareScalar ρ y ≠ 0 := norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero)
  rw [circleIndexSquarePhase_eq_phase,
    Circle.coe_phase_of_ne_zero _ hz, hn,
    Complex.ofReal_one, div_one]

/-- The phase is continuous wherever the scalar on the square is nonzero. -/
theorem continuousOn_circleIndexSquarePhase_of_scalar_ne_zero :
    ContinuousOn (circleIndexSquarePhase ρ) {y | circleIndexSquareScalar ρ y ≠ 0} :=
  (circleIndexSquareScalar ρ).continuous.continuousOn.circlePhase 1 fun _ hy ↦ hy

/-- The phase is continuous on the entire boundary, including points with phase `-1`. -/
theorem continuousOn_circleIndexSquarePhase :
    ContinuousOn (circleIndexSquarePhase ρ) (Cube.boundary (Fin 2)) :=
  (continuousOn_circleIndexSquarePhase_of_scalar_ne_zero ρ).mono fun _ hy ↦
    norm_ne_zero_iff.mp ((norm_squareScalar_of_mem_boundary ρ hy).trans_ne one_ne_zero)

/-- The bottom edge has constant phase. -/
@[simp] theorem circleIndexSquarePhase_bottom (x : unitInterval) :
    circleIndexSquarePhase ρ ![x, 0] = 1 := by
  apply Circle.ext
  have hy : ![x, 0] ∈ Cube.boundary (Fin 2) :=
    Cube.mem_boundary_of_apply_eq_zero_or_eq_one (i := 1) (Or.inl (by simp))
  rw [coe_circleIndexSquarePhase_of_mem_boundary ρ hy, squareScalar_bottom ρ (by simp)]
  simp only [Circle.coe_one]

/-- The right edge has constant phase. -/
@[simp] theorem circleIndexSquarePhase_right (x : unitInterval) :
    circleIndexSquarePhase ρ ![1, x] = 1 := by
  apply Circle.ext
  have hy : ![1, x] ∈ Cube.boundary (Fin 2) :=
    Cube.mem_boundary_of_apply_eq_zero_or_eq_one (i := 0) (Or.inr (by simp))
  rw [coe_circleIndexSquarePhase_of_mem_boundary ρ hy,
    squareScalar_vertical ρ (Or.inr (by simp))]
  simp only [Circle.coe_one]

/-- The top edge follows the circle character in increasing position. -/
@[simp] theorem circleIndexSquarePhase_top (x : unitInterval) :
    circleIndexSquarePhase ρ ![x, 1] = Circle.exp (2 * Real.pi * x) := by
  apply Circle.ext
  have hy : ![x, 1] ∈ Cube.boundary (Fin 2) :=
    Cube.mem_boundary_of_apply_eq_zero_or_eq_one (i := 1) (Or.inr (by simp))
  rw [coe_circleIndexSquarePhase_of_mem_boundary ρ hy, squareScalar_top ρ (by simp)]
  simp only [Matrix.cons_val_zero, unitToCircle_apply]

/-- The left edge has constant phase. -/
@[simp] theorem circleIndexSquarePhase_left (x : unitInterval) :
    circleIndexSquarePhase ρ ![0, x] = 1 := by
  apply Circle.ext
  have hy : ![0, x] ∈ Cube.boundary (Fin 2) :=
    Cube.mem_boundary_of_apply_eq_zero_or_eq_one (i := 0) (Or.inl (by simp))
  rw [coe_circleIndexSquarePhase_of_mem_boundary ρ hy,
    squareScalar_vertical ρ (Or.inl (by simp))]
  simp only [Circle.coe_one]

/-- The full circle index symbol has winding number `-1` on the counterclockwise rectangle.
The three constant edges have lift zero, and the top lift increases by `2π` before its
orientation is reversed. -/
@[simp] theorem squareBoundaryDegree_circleIndexSquarePhase :
    squareBoundaryDegree (circleIndexSquarePhase ρ) = -1 := by
  have h := squareBoundaryDegree_mul_two_pi_eq (continuousOn_circleIndexSquarePhase ρ)
    (θB := fun _ ↦ 0) (θR := fun _ ↦ 0) (θT := fun x ↦ 2 * Real.pi * (x : ℝ))
    (θL := fun _ ↦ 0) continuous_const continuous_const (by fun_prop) continuous_const
    (fun x ↦ by simp) (fun x ↦ by simp) (fun x ↦ by simp) (fun x ↦ by simp)
  apply squareBoundaryDegree_eq_of_mul_two_pi
  simpa using h

end TauCeti
