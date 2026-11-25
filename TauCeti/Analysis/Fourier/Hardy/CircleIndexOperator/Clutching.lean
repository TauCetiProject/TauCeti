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
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

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

/-- The scalar of the full Fourier index symbol on the cylinder, with frequency `2 * s`. -/
def circleIndexSymbolScalar : C(Circle × ℝ, ℂ) where
  toFun p := 1 + ((p.1 : ℂ) - 1) *
    (circleHardyProjectionSymbol ρ).toSymbol.coefficient (ι 0, ι (2 * p.2)) 1
  continuous_toFun := by
    have hξ : Continuous (fun p : Circle × ℝ ↦ ι (2 * p.2)) :=
      (ι).continuous.comp (continuous_const.mul continuous_snd)
    have hc := (circleHardyProjectionSymbol ρ).toSymbol.continuous_coefficient_slice (ι 0)
    exact continuous_const.add ((continuous_subtypeVal.comp continuous_fst).sub
      continuous_const |>.mul ((hc.comp hξ).clm_apply continuous_const))

/-- The continuous cylinder scalar interpolates the two branches using the cutoff on the
positive frequency axis. -/
theorem circleIndexSymbolScalar_apply (z : Circle) (s : ℝ) :
    circleIndexSymbolScalar ρ (z, s) =
      1 + ((z : ℂ) - 1) * (if 0 < s then (ρ (ι (2 * s)) : ℂ) else 0) := by
  by_cases hs : 0 < s <;> simp [circleIndexSymbolScalar, hs]

/-- Evaluating the full symbol on the scalar `1` gives the cylinder scalar at every real
position and frequency. The first Fourier character has period one. -/
theorem coefficient_circleFourierIndexSymbol_apply_one (x s : ℝ) :
    (circleFourierIndexSymbol ρ).toSymbol.coefficient (ι x, ι (2 * s)) 1 =
      circleIndexSymbolScalar ρ (Circle.exp (2 * Real.pi * x), s) := by
  rw [circleIndexSymbolScalar_apply, coefficient_toSymbol_circleFourierIndexSymbol]
  simp only [LinearIsometryEquiv.symm_apply_apply, fourier_coe_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Int.cast_one, Complex.ofReal_one, mul_one, div_one,
    Circle.coe_exp, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_pos_iff_of_pos_left (zero_lt_two : (0 : ℝ) < 2)]
  ring_nf

/-- Above the circle identity the cylinder scalar is constant. -/
@[simp] theorem circleIndexSymbolScalar_one_left (s : ℝ) :
    circleIndexSymbolScalar ρ (1, s) = 1 := by simp [circleIndexSymbolScalar_apply]

/-- For `s ≤ 1 / 2` (Fourier frequency `2 * s ≤ 1`), the cylinder scalar is `1`. -/
theorem circleIndexSymbolScalar_of_le_half (z : Circle) {s : ℝ} (hs : s ≤ 1 / 2) :
    circleIndexSymbolScalar ρ (z, s) = 1 := by
  rw [circleIndexSymbolScalar_apply]
  split_ifs with hp
  · have h := ρ.apply_eq_zero_of_norm_le_one (ξ := ι (2 * s)) (by
      refine ((ι).norm_map (2 * s)).le.trans ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith)
    simp [h]
  · simp

/-- For `1 ≤ s` (Fourier frequency `2 ≤ 2 * s`), the cylinder scalar is `z`. -/
theorem circleIndexSymbolScalar_of_one_le (z : Circle) {s : ℝ} (hs : 1 ≤ s) :
    circleIndexSymbolScalar ρ (z, s) = z := by
  have h := ρ.apply_eq_one_of_two_le_norm (ξ := ι (2 * s)) (by
    refine le_trans ?_ ((ι).norm_map (2 * s)).ge
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith)
  simp [circleIndexSymbolScalar_apply, ite_eq_left (by linarith : 0 < s), h]

/-- The straight-line homotopy from the actual full symbol to the affine representative has
norm at least one on both ends of the cylinder, including the two edges of the strip. -/
theorem one_le_norm_affine_circleIndexSymbolScalar (t : unitInterval) (z : Circle) {s : ℝ}
    (hs : 1 ≤ |s|) :
    1 ≤ ‖ContinuousMap.Homotopy.affine (circleIndexSymbolScalar ρ) circleIndexAffineScalar
      (t, z, s)‖ := by
  have bound (a b : Circle) (k : ℝ) (hk : 0 ≤ k) :
      1 ≤ ‖((1 + k : ℝ) : ℂ) * a - (k : ℂ) * b‖ := by
    have h := norm_sub_norm_le (((1 + k : ℝ) : ℂ) * a) ((k : ℂ) * b)
    simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hk, abs_of_nonneg (add_nonneg zero_le_one hk)] at h
    linarith
  rw [ContinuousMap.Homotopy.affine_apply]
  rw [AffineMap.lineMap_apply_module, circleIndexAffineScalar_apply]
  simp only [Complex.real_smul]
  obtain hs | hs := le_abs.mp hs
  · rw [circleIndexSymbolScalar_of_one_le ρ z hs]
    convert bound z 1 (t * (s - 1) / 2)
      (div_nonneg (mul_nonneg t.property.1 (by linarith)) (by norm_num)) using 2
    push_cast
    simp
    ring
  · rw [circleIndexSymbolScalar_of_le_half ρ z (by linarith)]
    convert bound 1 z (t * (-1 - s) / 2)
      (div_nonneg (mul_nonneg t.property.1 (by linarith)) (by norm_num)) using 2
    push_cast
    simp
    ring

/-- The phase of the actual symbol on the square of positions and normalized frequencies.
Only its restriction to the boundary enters the degree. -/
def circleIndexBoundaryPhase (y : Fin 2 → unitInterval) : Circle :=
  Circle.exp (Complex.arg ((circleFourierIndexSymbol ρ).toSymbol.coefficient
    (ι (y 0), ι (2 * (2 * (y 1 : ℝ) - 1))) 1))

/-- In cylinder coordinates the phase is the direction of the descended full symbol. -/
theorem circleIndexBoundaryPhase_apply (y : Fin 2 → unitInterval) :
    circleIndexBoundaryPhase ρ y = Circle.exp (Complex.arg (circleIndexSymbolScalar ρ
      (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1))) := by
  rw [circleIndexBoundaryPhase, coefficient_circleFourierIndexSymbol_apply_one]

/-- On the boundary the actual scalar already has norm one, so taking its phase preserves it. -/
theorem coe_circleIndexBoundaryPhase {y : Fin 2 → unitInterval} (hy : y ∈ Cube.boundary (Fin 2)) :
    (circleIndexBoundaryPhase ρ y : ℂ) = circleIndexSymbolScalar ρ
      (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1) := by
  have hnorm : ‖circleIndexSymbolScalar ρ
      (Circle.exp (2 * Real.pi * y 0), 2 * (y 1 : ℝ) - 1)‖ = 1 := by
    obtain ⟨i, hi | hi⟩ := hy <;> fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hi
    · simp [hi]
    · simp [hi, circleIndexSymbolScalar_of_le_half ρ _ (s := -1) (by norm_num)]
    · simp [hi]
    · simp [-Circle.coe_exp, hi, (by norm_num : (2 : ℝ) - 1 = 1),
        circleIndexSymbolScalar_of_one_le ρ _ (s := 1) le_rfl]
  rw [circleIndexBoundaryPhase_apply, Circle.coe_exp, Complex.exp_arg_mul_I (norm_ne_zero_iff.mp
    (hnorm.trans_ne one_ne_zero)), hnorm]
  simp

/-- The phase is continuous along the entire boundary, including where it crosses `-1`. -/
theorem continuousOn_circleIndexBoundaryPhase :
    ContinuousOn (circleIndexBoundaryPhase ρ) (Cube.boundary (Fin 2)) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  exact ((circleIndexSymbolScalar ρ).continuous.comp (by fun_prop)).continuousOn.congr
    fun _ hy ↦ coe_circleIndexBoundaryPhase ρ hy

/-- The full circle index symbol has winding number `-1` on the counterclockwise rectangle.
The three constant edges have lift zero, and the top lift increases by `2π` before its
orientation is reversed. -/
theorem squareBoundaryDegree_circleFourierIndexSymbol :
    squareBoundaryDegree (circleIndexBoundaryPhase ρ) = -1 := by
  have h := squareBoundaryDegree_mul_two_pi_eq (continuousOn_circleIndexBoundaryPhase ρ)
    (θB := fun _ ↦ 0) (θR := fun _ ↦ 0) (θT := fun x ↦ 2 * Real.pi * (x : ℝ))
    (θL := fun _ ↦ 0) continuous_const continuous_const (by fun_prop) continuous_const
    (fun x ↦ by simp [circleIndexBoundaryPhase_apply,
      circleIndexSymbolScalar_of_le_half ρ _ (s := -1) (by norm_num)])
    (fun x ↦ by simp [circleIndexBoundaryPhase_apply])
    (fun x ↦ by simp [-Circle.coe_exp, circleIndexBoundaryPhase_apply,
      (by norm_num : (2 : ℝ) - 1 = 1), circleIndexSymbolScalar_of_one_le ρ _ (s := 1) le_rfl])
    (fun x ↦ by simp [circleIndexBoundaryPhase_apply])
  have hdeg : (squareBoundaryDegree (circleIndexBoundaryPhase ρ) : ℝ) * (2 * Real.pi) =
      (-1 : ℝ) * (2 * Real.pi) := by simpa using h
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hdeg

end TauCeti
