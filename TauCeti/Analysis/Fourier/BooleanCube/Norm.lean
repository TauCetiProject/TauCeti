/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.BooleanCube.Walsh
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# `L^p` norms on the Boolean cube

For a real exponent `p` and a real function `f` on a finite cube `ι → ZMod 2` with the uniform
probability measure, `cubeNorm p f = (𝔼 x, |f x| ^ p) ^ p⁻¹` is the `L^p` norm of `f`. These
normalized norms are the ones in which the noise operator contracts and in which the
hypercontractive inequality on the cube is stated.

## Main definitions

* `TauCeti.cubeNorm p f`: the `L^p` norm of a real function on the cube.

## Main results

* `TauCeti.cubeNorm_le_cubeNorm`: for `0 < p ≤ q`, `cubeNorm p f ≤ cubeNorm q f`, because the
  measure is a probability measure.
* `TauCeti.cubeNorm_add_le`: Minkowski's inequality `cubeNorm p (f + g) ≤ cubeNorm p f +
  cubeNorm p g` for `1 ≤ p`.
* `TauCeti.cubeNorm_walsh`: Walsh characters have norm `1`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Section 1.4.
-/

public section

open Finset Real
open scoped BigOperators

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `L^p` norm `(𝔼 x, |f x| ^ p) ^ p⁻¹` of a real function on the cube, for the uniform
probability measure. It is a norm for `1 ≤ p`. -/
noncomputable def cubeNorm (p : ℝ) (f : (ι → ZMod 2) → ℝ) : ℝ :=
  (𝔼 x, |f x| ^ p) ^ p⁻¹

lemma cubeNorm_def (p : ℝ) (f : (ι → ZMod 2) → ℝ) :
    cubeNorm p f = (𝔼 x, |f x| ^ p) ^ p⁻¹ := (rfl)

lemma cubeNorm_nonneg (p : ℝ) (f : (ι → ZMod 2) → ℝ) : 0 ≤ cubeNorm p f :=
  rpow_nonneg (expect_nonneg fun _ _ ↦ rpow_nonneg (abs_nonneg _) _) _

/-- The `L^2` norm squared is the mean square. -/
lemma cubeNorm_two_sq (f : (ι → ZMod 2) → ℝ) : cubeNorm 2 f ^ 2 = 𝔼 x, f x ^ 2 := by
  have h : 0 ≤ 𝔼 x, f x ^ 2 := expect_nonneg fun _ _ ↦ sq_nonneg _
  simp_rw [cubeNorm_def, rpow_two, sq_abs]
  exact_mod_cast rpow_inv_natCast_pow h two_ne_zero

/-- A Walsh character has norm `1` in every `L^p`. -/
@[simp] lemma cubeNorm_walsh (p : ℝ) (S : Finset ι) : cubeNorm p (walsh S) = 1 := by
  simp [cubeNorm_def]

/-- The norm is absolutely homogeneous. -/
lemma cubeNorm_smul {p : ℝ} (hp : p ≠ 0) (c : ℝ) (f : (ι → ZMod 2) → ℝ) :
    cubeNorm p (c • f) = |c| * cubeNorm p f := by
  simp_rw [cubeNorm_def, Pi.smul_apply, smul_eq_mul, abs_mul,
    mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_expect]
  rw [mul_rpow (rpow_nonneg (abs_nonneg _) _)
      (expect_nonneg fun _ _ ↦ rpow_nonneg (abs_nonneg _) _),
    rpow_rpow_inv (abs_nonneg _) hp]

/-- **Monotonicity in the exponent.** On the cube with its uniform probability measure, the
`L^p` norm increases with `p`. -/
theorem cubeNorm_le_cubeNorm {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (f : (ι → ZMod 2) → ℝ) :
    cubeNorm p f ≤ cubeNorm q f := by
  have hq : 0 < q := hp.trans_le hpq
  set N : ℝ := (Fintype.card (ι → ZMod 2) : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  have hA : 0 ≤ 𝔼 x, |f x| ^ p := expect_nonneg fun _ _ ↦ rpow_nonneg (abs_nonneg _) _
  -- Jensen's inequality for the convex function `t ↦ t ^ (q / p)` and the uniform weights.
  have hJ : (𝔼 x, |f x| ^ p) ^ (q / p) ≤ 𝔼 x, |f x| ^ q := by
    have h := rpow_arith_mean_le_arith_mean_rpow univ (fun _ ↦ N⁻¹) (fun x ↦ |f x| ^ p)
      (fun _ _ ↦ inv_nonneg.2 hN.le) (by simp [N])
      (fun _ _ ↦ rpow_nonneg (abs_nonneg _) _) ((one_le_div hp).2 hpq)
    simp_rw [← rpow_mul (abs_nonneg _), mul_div_cancel₀ q hp.ne', ← mul_sum] at h
    simpa only [Fintype.expect_eq_sum_div_card, inv_mul_eq_div, N] using h
  calc cubeNorm p f = ((𝔼 x, |f x| ^ p) ^ (q / p)) ^ q⁻¹ := by
        rw [cubeNorm_def, ← rpow_mul hA, div_mul_eq_mul_div, mul_inv_cancel₀ hq.ne', one_div]
    _ ≤ cubeNorm q f := rpow_le_rpow (rpow_nonneg hA _) hJ (inv_nonneg.2 hq.le)

/-- **Minkowski's inequality** on the cube: for `1 ≤ p`, the `L^p` norm satisfies the triangle
inequality. -/
theorem cubeNorm_add_le {p : ℝ} (hp : 1 ≤ p) (f g : (ι → ZMod 2) → ℝ) :
    cubeNorm p (f + g) ≤ cubeNorm p f + cubeNorm p g := by
  have hN : (0 : ℝ) < Fintype.card (ι → ZMod 2) := Nat.cast_pos.2 Fintype.card_pos
  have h := Lp_add_le univ f g hp
  simp_rw [cubeNorm_def, Pi.add_apply, Fintype.expect_eq_sum_div_card,
    div_rpow (sum_nonneg fun _ _ ↦ rpow_nonneg (abs_nonneg _) _) hN.le, ← add_div, ← one_div]
  gcongr

end TauCeti
