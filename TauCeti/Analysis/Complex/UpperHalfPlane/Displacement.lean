/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

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

## Main results

* `Matrix.SpecialLinearGroup.cosh_dist_smul_I`: the distance moved by `I`.
* `Matrix.SpecialLinearGroup.cosh_dist_smul_of_smul_eq_self`: the displacement of a point by an
  element fixing `z`.
* `Matrix.SpecialLinearGroup.trace_commutatorElement_of_smul_eq_self`: the trace of a commutator
  with an element fixing `z`.

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
    rw [← dist_smul P⁻¹, inv_smul_smul, ← mul_smul, ← mul_smul, hX, mul_assoc]
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

end Matrix.SpecialLinearGroup
