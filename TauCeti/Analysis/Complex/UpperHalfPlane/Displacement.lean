/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Dilation
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Displacements and commutator traces in `SL(2, ℝ)`

For `g = !![a, b; c, d] ∈ SL(2, ℝ)` the hyperbolic distance moved by the base point `I` is
determined by the sum of the squares of the entries:
`cosh (dist (g • I) I) = (a² + b² + c² + d²) / 2`.

From this we compute two quantities attached to an element `g` fixing a point `z ∈ ℍ`, that is,
an elliptic element or `±1`. Write `κ = (4 - tr² g) / 2`, so that `κ = 2 sin² θ` when `g` acts as
the rotation through angle `2θ` about `z`.

* **Displacement.** `g` moves a point `w` a distance `δ` with
  `cosh δ = 1 + κ sinh² (dist w z)`. This is the hyperbolic law of cosines for the isosceles
  triangle `z, w, g • w`.
* **Commutator trace.** For every `h ∈ SL(2, ℝ)`,
  `tr ⁅g, h⁆ = 2 + κ (cosh (dist (h • z) z) - 1)`.

Both are proved by conjugating `z` to `I`, where `g` becomes `!![a, b; -b, a]` with
`a² + b² = 1`. They are the computations behind Jørgensen's inequality for elliptic elements.

For arbitrary `g, h ∈ SL(2, ℝ)` and `z ∈ ℍ`, the displacements `δ_g = dist (g • z) z` and
`δ_h = dist (h • z) z` bound the traces appearing in Jørgensen's inequality:

* `tr² g - 4 ≤ 2 (cosh δ_g - 1)`;
* `|tr ⁅g, h⁆ - 2| ≤ 4 (cosh δ_g cosh δ_h - 1)`.

At `z = I`, write `g = p + q J + r S₁ + s S₂` with `J` the rotation generator and `S₁`, `S₂`
the traceless symmetric matrices `!![1, 0; 0, -1]` and `!![0, 1; 1, 0]`. Then
`cosh δ_g = 1 + 2 (r² + s²)`, and `tr ⁅g, h⁆ - 2 = -det (g h - h g)` is
`4 ((q' s - q s')² + (q r' - q' r)² - (r s' - s r')²)`, which vanishes when both elements are
rotations about `I`. These bounds feed the Margulis lemma for Fuchsian groups.

Two further computations concern elements translating along the imaginary axis or reversing it.
The dilation `z ↦ exp s * z` moves `z` a distance `δ` with
`cosh δ = 1 + (cosh s - 1) (1 + (Re z / Im z)²)`; the quantity `1 + (Re z / Im z)²` is
`cosh² ρ` for the distance `ρ` from `z` to the axis. An antidiagonal matrix `!![0, b; c, 0]`,
which exchanges the endpoints `0` and `∞` of the axis, moves `z` a distance `δ` with
`cosh δ ≥ 1 + 2 (Re z / Im z)²`, that is `δ ≥ 2 ρ`. Thus points far from the axis are moved far
by both kinds of element, except by dilations with `s` close to `0`.

## Main results

* `Matrix.SpecialLinearGroup.cosh_dist_smul_I`: the distance moved by `I`.
* `Matrix.SpecialLinearGroup.cosh_dist_smul_of_smul_eq_self`: the displacement of a point by an
  element fixing `z`.
* `Matrix.SpecialLinearGroup.cosh_dist_dilation_smul`: the displacement of a point by a dilation,
  at least `|s|` by `Matrix.SpecialLinearGroup.abs_le_dist_dilation_smul`.
* `Matrix.SpecialLinearGroup.abs_le_dist_conj_dilation_smul`,
  `Matrix.SpecialLinearGroup.dist_conj_dilation_smul_smul_I`: the same for a conjugate
  `σ (z ↦ exp s * z) σ⁻¹` in `PSL(2, ℝ)`, translating along the geodesic through `σ • I`.
* `Matrix.SpecialLinearGroup.one_add_two_mul_sq_le_cosh_dist_smul`: a lower bound for the
  displacement of a point by an antidiagonal matrix.
* `Matrix.SpecialLinearGroup.trace_commutatorElement_of_smul_eq_self`: the trace of a commutator
  with an element fixing `z`.
* `Matrix.SpecialLinearGroup.trace_sq_sub_four_le`: the trace of an element is controlled by the
  distance it moves any point.
* `Matrix.SpecialLinearGroup.abs_trace_commutatorElement_sub_two_le`: the trace of a commutator is
  controlled by the distances its two factors move a common point.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 7 (the hyperbolic metric and the trigonometry of hyperbolic
  triangles).
-/

public section

open UpperHalfPlane
open scoped MatrixGroups commutatorElement

namespace Matrix.SpecialLinearGroup

/-- **The distance moved by `I`.** For `g = !![a, b; c, d] ∈ SL(2, ℝ)`,
`cosh (dist (g • I) I) = (a² + b² + c² + d²) / 2`. -/
theorem cosh_dist_smul_I (g : SL(2, ℝ)) :
    Real.cosh (dist (g • I) I) = (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) / 2 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hz : ((g • I : ℍ) : ℂ) = (g 0 0 * Complex.I + g 0 1) / (g 1 0 * Complex.I + g 1 1) := by
    simp [coe_specialLinearGroup_apply]
  have hD : g 1 1 ^ 2 + g 1 0 ^ 2 ≠ 0 := by
    intro h
    have h0 : g 1 0 = 0 := by nlinarith
    have h1 : g 1 1 = 0 := by nlinarith
    rw [h0, h1] at hdet
    simp at hdet
  have hre : (g • I).re = (g 0 0 * g 1 0 + g 0 1 * g 1 1) / (g 1 1 ^ 2 + g 1 0 ^ 2) := by
    rw [← coe_re, hz, Complex.div_re]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, zero_add, Complex.normSq_apply,
      Complex.add_im, Complex.mul_im, add_zero]
    field_simp
    ring
  have him : (g • I).im = 1 / (g 1 1 ^ 2 + g 1 0 ^ 2) := by
    rw [MulAction.compHom_smul_def, im_smul_eq_div_normSq]
    simp [denom, Complex.normSq_apply, sq]
  rw [cosh_dist', hre, him]
  simp only [I_re, sub_zero, one_div, inv_pow, I_im, one_pow, mul_one]
  field_simp
  linear_combination -(g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1) * hdet

/-- The base-point displacement of a conjugate of `k = !![a, b; -b, a]`:
`N(B k B⁻¹) - 2 = b² (N(B)² - 4)`, where `N` is the sum of the squares of the entries. -/
private theorem sumSq_conj {B k : SL(2, ℝ)} (h₁₁ : k 1 1 = k 0 0) (h₁₀ : k 1 0 = -k 0 1)
    (hab : k 0 0 ^ 2 + k 0 1 ^ 2 = 1) :
    (B * k * B⁻¹) 0 0 ^ 2 + (B * k * B⁻¹) 0 1 ^ 2 + (B * k * B⁻¹) 1 0 ^ 2 +
        (B * k * B⁻¹) 1 1 ^ 2 - 2 =
      k 0 1 ^ 2 * ((B 0 0 ^ 2 + B 0 1 ^ 2 + B 1 0 ^ 2 + B 1 1 ^ 2) ^ 2 - 4) := by
  have hdet := B.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [coe_mul, coe_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, h₁₁, h₁₀]
  linear_combination (2 - 4 * k 0 1 ^ 2) * (B 0 0 * B 1 1 - B 0 1 * B 1 0 + 1) * hdet +
    2 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) ^ 2 * hab

/-- **Displacement by an element fixing a point.** If `g ∈ SL(2, ℝ)` fixes `z ∈ ℍ`, it moves
every `w ∈ ℍ` a hyperbolic distance `δ` with `cosh δ = 1 + (4 - tr² g) / 2 · sinh² (dist w z)`.
For `g` acting as the rotation through angle `2θ` about `z` this is
`cosh δ = 1 + 2 sin² θ sinh² (dist w z)`. -/
theorem cosh_dist_smul_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z) (w : ℍ) :
    Real.cosh (dist (g • w) w) =
      1 + (4 - (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2 * Real.sinh (dist w z) ^ 2 := by
  obtain ⟨P, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  obtain ⟨Q, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I w
  -- move `z` to `I`, where `g` becomes `k = !![a, b; -b, a]`
  set k := P⁻¹ * g * P with hk
  have hkI : k • I = I := by
    rw [hk, mul_smul, mul_smul, hz, inv_smul_smul]
  obtain ⟨h₁₁, h₁₀⟩ := (smul_I_eq_I_iff k).1 hkI
  have hab := sq_add_sq_eq_one_of_smul_I_eq_I hkI
  have hg : g = P * k * P⁻¹ := by
    rw [hk]
    group
  have hconj : Q⁻¹ * P * k * (Q⁻¹ * P)⁻¹ = Q⁻¹ * g * Q := by
    rw [hg]
    group
  have hdist₁ : dist (g • Q • I) (Q • I) = dist (((Q⁻¹ * P) * k * (Q⁻¹ * P)⁻¹) • I) I := by
    rw [← dist_smul Q⁻¹, inv_smul_smul, hconj, mul_smul, mul_smul]
  have hdist₂ : dist (Q • I) (P • I) = dist ((Q⁻¹ * P) • I) I := by
    rw [dist_comm, ← dist_smul Q⁻¹, ← mul_smul, inv_smul_smul]
  rw [hdist₁, hdist₂, Real.sinh_sq, cosh_dist_smul_I, cosh_dist_smul_I, hg, trace_mul_mul_inv,
    Matrix.trace_fin_two, h₁₁]
  have := sumSq_conj (B := Q⁻¹ * P) h₁₁ h₁₀ hab
  linear_combination this / 2 +
    (((Q⁻¹ * P) 0 0 ^ 2 + (Q⁻¹ * P) 0 1 ^ 2 + (Q⁻¹ * P) 1 0 ^ 2 + (Q⁻¹ * P) 1 1 ^ 2) ^ 2 / 2 - 2) *
      hab

/-- **The trace of a commutator with an element fixing a point.** If `g ∈ SL(2, ℝ)` fixes
`z ∈ ℍ`, then for every `h ∈ SL(2, ℝ)`,
`tr ⁅g, h⁆ = 2 + (4 - tr² g) / 2 · (cosh (dist (h • z) z) - 1)`. -/
theorem trace_commutatorElement_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z)
    (h : SL(2, ℝ)) :
    ((⁅g, h⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 + (4 - (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2 *
        (Real.cosh (dist (h • z) z) - 1) := by
  obtain ⟨P, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  -- move `z` to `I`, where `g` becomes `k = !![a, b; -b, a]` and `h` becomes `X`
  set k := P⁻¹ * g * P with hk
  set X := P⁻¹ * h * P with hX
  have hkI : k • I = I := by
    rw [hk, mul_smul, mul_smul, hz, inv_smul_smul]
  obtain ⟨h₁₁, h₁₀⟩ := (smul_I_eq_I_iff k).1 hkI
  have hab := sq_add_sq_eq_one_of_smul_I_eq_I hkI
  have hcomm : ⁅g, h⁆ = P * ⁅k, X⁆ * P⁻¹ := by
    simp only [hk, hX, commutatorElement_def]
    group
  have hdist : dist (h • P • I) (P • I) = dist (X • I) I := by
    simpa [hX] using (TauCeti.dist_conj_smul P⁻¹ h I).symm
  have hg : P * k * P⁻¹ = g := by
    rw [hk]
    group
  have htr : (g : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * k 0 0 := by
    rw [← hg, trace_mul_mul_inv, Matrix.trace_fin_two, h₁₁]
    ring
  have hdet := X.det_coe
  rw [Matrix.det_fin_two] at hdet
  rw [hcomm, trace_mul_mul_inv, hdist, cosh_dist_smul_I, htr]
  simp only [commutatorElement_def, coe_mul, coe_inv, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.trace_fin_two, h₁₁,
    h₁₀]
  linear_combination 2 * k 0 0 ^ 2 * hdet + (X 0 0 ^ 2 + X 0 1 ^ 2 + X 1 0 ^ 2 + X 1 1 ^ 2) * hab

/-- The commutator of a noncentral element fixing `z` with an element moving `z` is
hyperbolic, with trace strictly greater than two. -/
theorem two_lt_trace_commutatorElement_of_smul_eq_self {g h : SL(2, ℝ)} {z : ℍ}
    (hz : g • z = z) (hg : (g : PSL(2, ℝ)) ≠ 1) (hh : h • z ≠ z) :
    2 < ((⁅g, h⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
  have hell := (Matrix.isElliptic_iff_abs_trace_lt_two g.det_coe).mp
    (isElliptic_of_smul_eq_self_of_ne_one hz hg)
  have hκ : 0 < (4 - (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) / 2 := by
    nlinarith [sq_abs (g : Matrix (Fin 2) (Fin 2) ℝ).trace,
      abs_nonneg (g : Matrix (Fin 2) (Fin 2) ℝ).trace]
  rw [trace_commutatorElement_of_smul_eq_self hz]
  have := mul_pos hκ (sub_pos.mpr (Real.one_lt_cosh.mpr (dist_ne_zero.mpr hh)))
  linarith

/-! ### Bounds from the displacement of a point -/

/-- The polynomial inequality behind `abs_trace_commutatorElement_sub_two_le`, in the coordinates
`g = p + q J + r S₁ + s S₂` adapted to the rotations about `I`: the determinant condition is
`p² + q² - r² - s² = 1`, the displacement of `I` is `cosh δ = p² + q² + r² + s²`, and the commutator
trace is `tr ⁅g, h⁆ = 2 + 4 ((q' s - q s')² + (q r' - q' r)² - (r s' - s r')²)`. -/
private theorem abs_commutator_sub_le {p q r s p' q' r' s' : ℝ}
    (h : p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2 = 1) (h' : p' ^ 2 + q' ^ 2 - r' ^ 2 - s' ^ 2 = 1) :
    |(q' * s - q * s') ^ 2 + (q * r' - q' * r) ^ 2 - (r * s' - s * r') ^ 2| ≤
      (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * (p' ^ 2 + q' ^ 2 + r' ^ 2 + s' ^ 2) - 1 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (q' * s - q * s'), sq_nonneg (q * r' - q' * r),
      sq_nonneg (r * r' + s * s'), sq_nonneg r, sq_nonneg s, sq_nonneg r', sq_nonneg s',
      mul_nonneg (add_nonneg (sq_nonneg r) (sq_nonneg s))
        (add_nonneg (sq_nonneg r') (sq_nonneg s'))]
  · have hsos : (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * (p' ^ 2 + q' ^ 2 + r' ^ 2 + s' ^ 2) - 1 -
        ((q' * s - q * s') ^ 2 + (q * r' - q' * r) ^ 2 - (r * s' - s * r') ^ 2) =
        2 * (r ^ 2 + s ^ 2) * p' ^ 2 + 2 * (r' ^ 2 + s' ^ 2) * p ^ 2 + (q' * s + q * s') ^ 2 +
          (q * r' + q' * r) ^ 2 + (r * s' - s * r') ^ 2 := by
      linear_combination (p' ^ 2 + q' ^ 2 - r' ^ 2 - s' ^ 2) * h + h'
    nlinarith [hsos, sq_nonneg p, sq_nonneg p', sq_nonneg (q' * s + q * s'),
      sq_nonneg (q * r' + q' * r), sq_nonneg (r * s' - s * r'),
      mul_nonneg (add_nonneg (sq_nonneg r) (sq_nonneg s)) (sq_nonneg p'),
      mul_nonneg (add_nonneg (sq_nonneg r') (sq_nonneg s')) (sq_nonneg p)]

/-- The case `z = I` of `trace_sq_sub_four_le`. -/
private theorem trace_sq_sub_four_le_of_I (g : SL(2, ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4 ≤ 2 * (Real.cosh (dist (g • I) I) - 1) := by
  have hg := g.det_coe
  rw [Matrix.det_fin_two] at hg
  rw [cosh_dist_smul_I, Matrix.trace_fin_two]
  nlinarith [sq_nonneg (g 0 1 - g 1 0)]

/-- The case `z = I` of `abs_trace_commutatorElement_sub_two_le`. -/
private theorem abs_trace_commutatorElement_sub_two_le_of_I (g h : SL(2, ℝ)) :
    |((⁅g, h⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| ≤
      4 * (Real.cosh (dist (g • I) I) * Real.cosh (dist (h • I) I) - 1) := by
  have hg := g.det_coe
  have hh := h.det_coe
  rw [Matrix.det_fin_two] at hg hh
  have key := abs_commutator_sub_le
    (p := (g 0 0 + g 1 1) / 2) (q := (g 1 0 - g 0 1) / 2) (r := (g 0 0 - g 1 1) / 2)
    (s := (g 0 1 + g 1 0) / 2) (p' := (h 0 0 + h 1 1) / 2) (q' := (h 1 0 - h 0 1) / 2)
    (r' := (h 0 0 - h 1 1) / 2) (s' := (h 0 1 + h 1 0) / 2)
    (by linear_combination hg) (by linear_combination hh)
  rw [trace_commutatorElement_sub_two_fin_two, Matrix.det_fin_two, cosh_dist_smul_I,
    cosh_dist_smul_I]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  -- both sides are `4` times the two sides of `key`, as polynomials in the entries
  rw [abs_le] at key ⊢
  constructor <;> linarith [key.1, key.2]

/-- **The trace of an element and the displacement of a point.** For `g ∈ SL(2, ℝ)` and `z ∈ ℍ`,
`tr² g - 4 ≤ 2 (cosh (dist (g • z) z) - 1)`. In particular an element moving some point a small
distance has trace close to `±2` unless it is elliptic. -/
theorem trace_sq_sub_four_le (g : SL(2, ℝ)) (z : ℍ) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4 ≤ 2 * (Real.cosh (dist (g • z) z) - 1) := by
  obtain ⟨P, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  have htr : (g : Matrix (Fin 2) (Fin 2) ℝ).trace = ((P⁻¹ * g * P : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).trace := by
    simpa using (trace_mul_mul_inv P⁻¹ g).symm
  -- moving the base point `P • I` to `I` conjugates `g` by `P`
  rw [← inv_inv P, ← TauCeti.dist_conj_smul, inv_inv, htr]
  exact trace_sq_sub_four_le_of_I _

/-- **The commutator trace and the displacement of a point.** For `g, h ∈ SL(2, ℝ)` and `z ∈ ℍ`,
`|tr ⁅g, h⁆ - 2| ≤ 4 (cosh (dist (g • z) z) cosh (dist (h • z) z) - 1)`. Thus two elements both
moving a common point a small distance have commutator trace close to `2`, whatever their
rotational parts are. -/
theorem abs_trace_commutatorElement_sub_two_le (g h : SL(2, ℝ)) (z : ℍ) :
    |((⁅g, h⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| ≤
      4 * (Real.cosh (dist (g • z) z) * Real.cosh (dist (h • z) z) - 1) := by
  obtain ⟨P, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  have hcomm : ⁅g, h⁆ = P * ⁅P⁻¹ * g * P, P⁻¹ * h * P⁆ * P⁻¹ := by
    simp only [commutatorElement_def]
    group
  -- moving the base point `P • I` to `I` conjugates `g` and `h` by `P`
  rw [← inv_inv P, ← TauCeti.dist_conj_smul, ← TauCeti.dist_conj_smul, inv_inv, hcomm,
    trace_mul_mul_inv]
  exact abs_trace_commutatorElement_sub_two_le_of_I _ _

/-- **Displacement by a dilation.** The dilation `z ↦ exp s * z` moves `z ∈ ℍ` a hyperbolic
distance `δ` with `cosh δ = 1 + (cosh s - 1) (1 + (Re z / Im z)²)`. In particular it moves every
point of the imaginary axis the distance `|s|`, and every other point at least as far. -/
theorem cosh_dist_dilation_smul (s : ℝ) (z : ℍ) :
    Real.cosh (dist (dilation s • z) z) = 1 + (Real.cosh s - 1) * (1 + (z.re / z.im) ^ 2) := by
  have hre : (dilation s • z).re = Real.exp s * z.re := by
    rw [← UpperHalfPlane.coe_re, TauCeti.UpperHalfPlane.coe_dilation_smul, Complex.re_ofReal_mul,
      UpperHalfPlane.coe_re]
  have him : (dilation s • z).im = Real.exp s * z.im := by
    rw [← UpperHalfPlane.coe_im, TauCeti.UpperHalfPlane.coe_dilation_smul, Complex.im_ofReal_mul,
      UpperHalfPlane.coe_im]
  have hy := z.im_pos
  have he := Real.exp_pos s
  rw [cosh_dist', hre, him, Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

/-- The dilation `z ↦ exp s * z` moves every point of `ℍ` at least the distance `|s|`. -/
theorem abs_le_dist_dilation_smul (s : ℝ) (z : ℍ) : |s| ≤ dist (dilation s • z) z := by
  have h : Real.cosh |s| ≤ Real.cosh (dist (dilation s • z) z) := by
    rw [Real.cosh_abs, cosh_dist_dilation_smul]
    nlinarith [Real.one_le_cosh s, sq_nonneg (z.re / z.im)]
  simpa [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.1 h

/-- The dilation `z ↦ exp s * z` moves `I` exactly the distance `|s|`. -/
@[simp]
theorem dist_dilation_smul_I (s : ℝ) : dist (dilation s • I) I = |s| := by
  rw [← TauCeti.UpperHalfPlane.geodesicLine_one_eq_dilation_smul_I, ← one_smul PSL(2, ℝ) I,
    ← TauCeti.UpperHalfPlane.geodesicLine_zero, TauCeti.UpperHalfPlane.dist_geodesicLine, sub_zero]

/-- A conjugate `σ (z ↦ exp s * z) σ⁻¹` in `PSL(2, ℝ)` moves every point of `ℍ` at least the
distance `|s|`. -/
theorem abs_le_dist_conj_dilation_smul (σ : PSL(2, ℝ)) (s : ℝ) (z : ℍ) :
    |s| ≤ dist ((σ * ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) • z) z := by
  rw [TauCeti.dist_conj_smul, UpperHalfPlane.pslMk_smul]
  exact abs_le_dist_dilation_smul s _

/-- A conjugate `σ (z ↦ exp s * z) σ⁻¹` in `PSL(2, ℝ)` moves `σ • I` exactly the distance `|s|`. -/
theorem dist_conj_dilation_smul_smul_I (σ : PSL(2, ℝ)) (s : ℝ) :
    dist ((σ * ((dilation s : SL(2, ℝ)) : PSL(2, ℝ)) * σ⁻¹) • σ • I) (σ • I) = |s| := by
  rw [TauCeti.dist_conj_smul, inv_smul_smul, UpperHalfPlane.pslMk_smul, dist_dilation_smul_I]

/-- **Displacement by an antidiagonal matrix.** A matrix `g = !![0, b; c, 0] ∈ SL(2, ℝ)`, acting as
`z ↦ -b² / z` and so exchanging the endpoints `0` and `∞` of the imaginary axis, moves `z ∈ ℍ` a
hyperbolic distance `δ` with `cosh δ ≥ 1 + 2 (Re z / Im z)²`. -/
theorem one_add_two_mul_sq_le_cosh_dist_smul {g : SL(2, ℝ)} (h₀₀ : g 0 0 = 0) (h₁₁ : g 1 1 = 0)
    (z : ℍ) : 1 + 2 * (z.re / z.im) ^ 2 ≤ Real.cosh (dist (g • z) z) := by
  have hdet : g 0 1 * g 1 0 = -1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two, h₀₀, h₁₁] at this
    linarith
  have hb : g 0 1 ≠ 0 := by
    rintro h
    simp [h] at hdet
  have hc : g 1 0 ≠ 0 := by
    rintro h
    simp [h] at hdet
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hcoe : ((g • z : ℍ) : ℂ) = -(g 0 1 ^ 2 : ℝ) / z := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [h₀₀, h₁₁]
    have hc' : (g 1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
    field_simp
    have : ((g 0 1 : ℝ) : ℂ) * (g 1 0 : ℂ) = -1 := by exact_mod_cast hdet
    push_cast
    linear_combination (z : ℂ) * (g 0 1 : ℂ) * this
  have hre : (g • z).re = -(g 0 1 ^ 2) * z.re / (z.re ^ 2 + z.im ^ 2) := by
    rw [← UpperHalfPlane.coe_re, hcoe]
    simp only [Complex.div_re, Complex.neg_re, Complex.ofReal_re, coe_re, neg_mul,
      Complex.normSq_apply, coe_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul,
      zero_div, add_zero]
    ring
  have him : (g • z).im = g 0 1 ^ 2 * z.im / (z.re ^ 2 + z.im ^ 2) := by
    rw [← UpperHalfPlane.coe_im, hcoe]
    simp only [Complex.div_im, Complex.neg_im, Complex.ofReal_im, neg_zero, coe_re, zero_mul,
      Complex.normSq_apply, coe_im, zero_div, Complex.neg_re, Complex.ofReal_re, neg_mul, zero_sub]
    ring
  have hy := z.im_pos
  have hb2 : 0 < g 0 1 ^ 2 := by positivity
  have hr : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  rw [cosh_dist', hre, him, le_div_iff₀ (by positivity), div_pow]
  field_simp
  -- the difference of the two sides is a positive multiple of `(|z|² - b²)²`
  nlinarith [sq_nonneg (z.re ^ 2 + z.im ^ 2 - g 0 1 ^ 2), mul_pos hr hy]

end Matrix.SpecialLinearGroup
