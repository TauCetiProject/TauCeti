/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The Green kernel and the Poisson kernel of the Euclidean unit ball

This file constructs the Dirichlet Green kernel of the unit ball of `ℝⁿ` by the method of
images.  For a pole `x` in the ball, the corrector

`φˣ(y) = Φ(‖x‖ (y - x*))`, with `x* = x / ‖x‖²`,

is the Newtonian kernel `Φ` with its pole at the reflection of `x` through the unit sphere,
rescaled so that it agrees with `Φ(y - x)` on the sphere.  It is harmonic away from the reflected
pole, in particular on a neighbourhood of the closed ball, so the Green kernel

`G(x, y) = Φ(y - x) - φˣ(y)`

is harmonic in `y` away from the pole and vanishes for `‖y‖ = 1`.  The corrector is written
through the identity `‖‖x‖ y - x / ‖x‖‖² = ‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1`, whose right-hand side is
defined at `x = 0` as well, where the corrector is the constant value of `Φ` on the unit sphere.

The outward normal derivative of `G(x, ·)` on the unit sphere is the negative of the **Poisson
kernel** of the ball,

`K(x, y) = (1 - ‖x‖²) / (n ωₙ ‖x - y‖ⁿ)`,

where `ωₙ` is the volume of the unit ball.  This is the boundary term of Green's representation
formula on the ball, and the kernel of the Poisson integral solving the Dirichlet problem for the
Laplacian there.

The kernel is normalized for the negative Laplacian, as `TauCeti.newtonianKernel` is.  In
dimension two that kernel vanishes identically, so the planar case is instead
`TauCeti.planarGreenKernel`, built from the logarithmic kernel.

## Main declarations

* `TauCeti.ballGreenCorrector`: the reflected Newtonian kernel correcting the boundary values.
* `TauCeti.ballGreenKernel`: the Dirichlet Green kernel of the unit ball.
* `TauCeti.ballGreenKernel_comm`: symmetry of the Green kernel in its two arguments.
* `TauCeti.harmonicAt_ballGreenKernel`: harmonicity in `y` away from the pole.
* `TauCeti.ballGreenKernel_eq_zero_of_norm_eq_one_left`,
  `TauCeti.ballGreenKernel_eq_zero_of_norm_eq_one_right`: vanishing when either argument lies on
  the unit sphere.
* `TauCeti.ballGreenKernel_pos`: positivity inside the ball outside dimension two.
* `TauCeti.ballPoissonKernel`: the Poisson kernel of the unit ball.
* `TauCeti.fderiv_ballGreenKernel_normal`: the outward normal derivative of the Green kernel on
  the unit sphere is the negative Poisson kernel.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.4 (Green's function for a ball).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.5.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric

open scoped RealInnerProductSpace

/-! ### Reflection through the unit sphere -/

section Reflection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The squared length of `‖x‖ • y - x / ‖x‖`, which is `‖x‖ ‖y - x*‖` for the reflection
`x* = x / ‖x‖²` of `x` through the unit sphere.  The right-hand side is a polynomial in `x` and
`y`, defined at `x = 0` as well. -/
theorem norm_sq_norm_smul_sub_inv_norm_smul {x : F} (hx : x ≠ 0) (y : F) :
    ‖‖x‖ • y - ‖x‖⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, real_inner_comm x y]
  simp only [norm_smul, Real.norm_eq_abs, abs_norm, abs_inv, mul_pow, inv_pow]
  field_simp

/-- The reflection polynomial `‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1` is at least `(1 - ‖x‖ ‖y‖)²`. -/
theorem one_sub_norm_mul_norm_sq_le (x y : F) :
    (1 - ‖x‖ * ‖y‖) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 := by
  nlinarith [real_inner_le_norm x y]

/-- The reflection polynomial is positive unless `‖x‖ ‖y‖ = 1`; in particular it is positive
whenever one of `x`, `y` lies in the open unit ball and the other in the closed one. -/
theorem norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos {x y : F} (h : ‖x‖ * ‖y‖ ≠ 1) :
    0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 :=
  (sq_pos_iff.mpr (sub_ne_zero.mpr h.symm)).trans_le (one_sub_norm_mul_norm_sq_le x y)

/-- On the unit sphere, the reflection polynomial is the squared distance to the pole. -/
theorem norm_sub_sq_eq_of_norm_eq_one (x : F) {y : F} (hy : ‖y‖ = 1) :
    ‖y - x‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 := by
  rw [norm_sub_sq_real, hy, real_inner_comm x y]
  ring

end Reflection

/-! ### The corrector -/

variable {n : ℕ}

/-- The corrector of the Green kernel of the unit ball with pole `x`: the Newtonian kernel with
its pole at the reflection `x / ‖x‖²` of `x` through the unit sphere, dilated by `‖x‖` so that it
matches the Newtonian kernel with pole `x` on the sphere.  It is written through the reflection
polynomial `‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1`, so at `x = 0` it is the constant value of the Newtonian
kernel on the unit sphere rather than a separate case. -/
def ballGreenCorrector (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
    (‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) ^ ((2 - (n : ℝ)) / 2)

/-- The defining formula for the corrector. -/
theorem ballGreenCorrector_def (x y : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n x y =
      ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) ^ ((2 - (n : ℝ)) / 2) := by
  rw [ballGreenCorrector]

/-- The corrector is symmetric in the pole and the variable. -/
theorem ballGreenCorrector_comm (x y : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n x y = ballGreenCorrector n y x := by
  rw [ballGreenCorrector_def, ballGreenCorrector_def, real_inner_comm, mul_comm (‖x‖ ^ 2)]

/-- Away from the pole `x = 0`, the corrector is the Newtonian kernel evaluated at
`‖x‖ • y - x / ‖x‖`, that is, the method-of-images formula `Φ(‖x‖ (y - x*))`. -/
theorem ballGreenCorrector_eq_newtonianKernel {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n x y = newtonianKernel n (‖x‖ • y - ‖x‖⁻¹ • x) := by
  rw [ballGreenCorrector_def, newtonianKernel_def, ← norm_sq_norm_smul_sub_inv_norm_smul hx y,
    norm_rpow_eq_norm_sq_rpow]

/-- At the pole `x = 0`, the corrector is the constant value of the Newtonian kernel on the unit
sphere. -/
@[simp]
theorem ballGreenCorrector_zero_left (y : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n 0 y =
      ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ := by
  simp [ballGreenCorrector_def]

/-- At the center `y = 0`, the corrector is the constant value of the Newtonian kernel on the unit
sphere. -/
@[simp]
theorem ballGreenCorrector_zero_right (x : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n x 0 =
      ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ := by
  rw [ballGreenCorrector_comm, ballGreenCorrector_zero_left]

/-- For `y` on the unit sphere, the corrector agrees with the Newtonian kernel with pole `x`. -/
@[simp]
theorem ballGreenCorrector_eq_newtonianKernel_sub_of_norm_eq_one_right
    (x : EuclideanSpace ℝ (Fin n)) {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) :
    ballGreenCorrector n x y = newtonianKernel n (y - x) := by
  rw [ballGreenCorrector_def, newtonianKernel_def, ← norm_sub_sq_eq_of_norm_eq_one x hy,
    norm_rpow_eq_norm_sq_rpow]

/-- For a pole `x` on the unit sphere, the corrector agrees with the Newtonian kernel with
pole `x`. -/
@[simp]
theorem ballGreenCorrector_eq_newtonianKernel_sub_of_norm_eq_one_left
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) (y : EuclideanSpace ℝ (Fin n)) :
    ballGreenCorrector n x y = newtonianKernel n (y - x) := by
  rw [ballGreenCorrector_comm, ballGreenCorrector_eq_newtonianKernel_sub_of_norm_eq_one_right y hx,
    newtonianKernel_sub_comm]

/-- The corrector is harmonic in `y` wherever the reflection polynomial
`‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1` is positive, that is, away from the reflected pole `x / ‖x‖²`; by
`norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos` this holds wherever `‖x‖ ‖y‖ ≠ 1`, in
particular on a neighbourhood of the closed unit ball when the pole `x` lies in the open ball. -/
theorem harmonicAt_ballGreenCorrector {x y : EuclideanSpace ℝ (Fin n)}
    (h : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) :
    HarmonicAt (ballGreenCorrector n x) y := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hfun : ballGreenCorrector n 0 = fun _ =>
        ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ := by
      funext z
      exact ballGreenCorrector_zero_left z
    rw [hfun]
    exact harmonicAt_const _
  · have hfun : ballGreenCorrector n x =
        fun z => newtonianKernel n (-(‖x‖⁻¹ • x) + ‖x‖ • z) := by
      funext z
      rw [ballGreenCorrector_eq_newtonianKernel hx, sub_eq_neg_add]
    have hne : -(‖x‖⁻¹ • x) + ‖x‖ • y ≠ 0 := by
      intro hzero
      have hsq := norm_sq_norm_smul_sub_inv_norm_smul hx y
      rw [sub_eq_neg_add, hzero, norm_zero] at hsq
      exact h.ne' (by simpa using hsq.symm)
    rw [hfun]
    exact (harmonicAt_comp_const_add_smul_iff (-(‖x‖⁻¹ • x)) (norm_ne_zero_iff.mpr hx)).2
      (harmonicAt_newtonianKernel n hne)

/-- The scalar identity turning the derivative of the corrector into the normalization of the
derivative of the Newtonian kernel. -/
private theorem inv_mul_div_two_mul_two (hn : n ≠ 2) (w : ℝ) :
    ((n : ℝ) * ((n : ℝ) - 2) * w)⁻¹ * ((2 - (n : ℝ)) / 2) * 2 = -((n : ℝ) * w)⁻¹ := by
  have hn2 : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rcases eq_or_ne (n : ℝ) 0 with hn0 | hn0
  · simp [hn0]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  field_simp
  ring

/-- The Fréchet derivative of the corrector in `y`, wherever the reflection polynomial
`‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1` is positive. -/
theorem hasFDerivAt_ballGreenCorrector (hn : n ≠ 2) {x y : EuclideanSpace ℝ (Fin n)}
    (h : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) :
    HasFDerivAt (ballGreenCorrector n x)
      ((-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
          (‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) ^ (-(n : ℝ) / 2)) •
        (‖x‖ ^ 2 • innerSL ℝ y - innerSL ℝ x)) y := by
  have hpoly : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖x‖ ^ 2 * ‖z‖ ^ 2 - 2 * ⟪x, z⟫_ℝ + 1)
      (‖x‖ ^ 2 • (2 • innerSL ℝ y) - (2 : ℝ) • innerSL ℝ x) y := by
    have h₁ := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (‖x‖ ^ 2)
    have h₂ := ((innerSL ℝ x).hasFDerivAt (x := y)).const_mul (2 : ℝ)
    simpa only [smul_eq_mul, innerSL_apply_apply, Pi.sub_apply] using (h₁.sub h₂).add_const 1
  have hfun : ballGreenCorrector n x = fun z =>
      ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ ^ 2 * ‖z‖ ^ 2 - 2 * ⟪x, z⟫_ℝ + 1) ^ ((2 - (n : ℝ)) / 2) := by
    funext z
    exact ballGreenCorrector_def x z
  rw [hfun]
  refine ((hpoly.rpow_const (Or.inl h.ne')).const_mul _).congr_fderiv ?_
  have hexp : (2 - (n : ℝ)) / 2 - 1 = -(n : ℝ) / 2 := by ring
  rw [hexp]
  ext v
  simp only [smul_apply, sub_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    innerSL_apply_apply]
  have := inv_mul_div_two_mul_two hn
    (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))
  linear_combination
    ((‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) ^ (-(n : ℝ) / 2) *
      (‖x‖ ^ 2 * ⟪y, v⟫_ℝ - ⟪x, v⟫_ℝ)) * this

/-! ### The Green kernel -/

/-- The Dirichlet Green kernel of the Euclidean unit ball with pole `x`: the Newtonian kernel
with pole `x`, corrected by the reflected kernel so that the difference vanishes on the unit
sphere.  For a pole in the open ball it is harmonic in `y` away from `x`. -/
def ballGreenKernel (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  newtonianKernel n (y - x) - ballGreenCorrector n x y

/-- The defining formula for the Green kernel of the unit ball. -/
theorem ballGreenKernel_def (x y : EuclideanSpace ℝ (Fin n)) :
    ballGreenKernel n x y = newtonianKernel n (y - x) - ballGreenCorrector n x y := by
  rw [ballGreenKernel]

/-- The Green kernel with pole `x`, as a function of the variable. -/
private theorem ballGreenKernel_fun (x : EuclideanSpace ℝ (Fin n)) :
    ballGreenKernel n x = fun z => newtonianKernel n (z - x) - ballGreenCorrector n x z := by
  funext z
  exact ballGreenKernel_def x z

/-- The Green kernel of the unit ball is symmetric in the pole and the variable. -/
theorem ballGreenKernel_comm (x y : EuclideanSpace ℝ (Fin n)) :
    ballGreenKernel n x y = ballGreenKernel n y x := by
  rw [ballGreenKernel_def, ballGreenKernel_def, newtonianKernel_sub_comm,
    ballGreenCorrector_comm]

/-- The Green kernel of the unit ball vanishes for `y` on the unit sphere. -/
@[simp]
theorem ballGreenKernel_eq_zero_of_norm_eq_one_right (x : EuclideanSpace ℝ (Fin n))
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) :
    ballGreenKernel n x y = 0 := by
  rw [ballGreenKernel_def, ballGreenCorrector_eq_newtonianKernel_sub_of_norm_eq_one_right x hy,
    sub_self]

/-- The Green kernel of the unit ball vanishes for a pole `x` on the unit sphere. -/
@[simp]
theorem ballGreenKernel_eq_zero_of_norm_eq_one_left {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    ballGreenKernel n x y = 0 := by
  rw [ballGreenKernel_comm, ballGreenKernel_eq_zero_of_norm_eq_one_right y hx]

/-- The Green kernel of the unit ball is harmonic in `y` away from the pole, wherever the
reflection polynomial `‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1` is positive. -/
theorem harmonicAt_ballGreenKernel {x y : EuclideanSpace ℝ (Fin n)} (hxy : y ≠ x)
    (h : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) :
    HarmonicAt (ballGreenKernel n x) y := by
  rw [ballGreenKernel_fun]
  exact (harmonicAt_newtonianKernel_sub n hxy).sub (harmonicAt_ballGreenCorrector h)

/-- For a pole in the open unit ball, the Green kernel is harmonic on the punctured ball. -/
theorem harmonicOnNhd_ballGreenKernel {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    HarmonicOnNhd (ballGreenKernel n x) (ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ {x}) := by
  intro y hy
  rw [Set.mem_sdiff, mem_ball_zero_iff, Set.mem_singleton_iff] at hy
  exact harmonicAt_ballGreenKernel hy.2 (norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos
    ((mul_le_of_le_one_right (norm_nonneg x) hy.1.le).trans_lt hx).ne)

/-- Outside dimension two, the Green kernel of the unit ball is positive inside the ball away
from the pole. -/
theorem ballGreenKernel_pos (hn : n ≠ 2) {x y : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1)
    (hy : ‖y‖ < 1) (hxy : y ≠ x) :
    0 < ballGreenKernel n x y := by
  have hω := volume_real_unitBall_pos n
  have hsub : 0 < ‖y - x‖ ^ 2 := by
    have : y - x ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  have hlt : ‖y - x‖ ^ 2 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 := by
    have hx' : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hy' : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    rw [norm_sub_sq_real, real_inner_comm x y]
    nlinarith [mul_pos hx' hy']
  rw [ballGreenKernel_def, ballGreenCorrector_def, newtonianKernel_def,
    norm_rpow_eq_norm_sq_rpow, ← mul_sub]
  obtain hn1 | hn3 : n = 1 ∨ 3 ≤ n := by
    have := nontrivial_of_ne y x hxy
    have : 0 < n := by simpa using Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Fin n))
    omega
  · have hn1ℝ : (n : ℝ) = 1 := by exact_mod_cast hn1
    have hc : (n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) < 0 := by
      rw [hn1ℝ]
      linarith
    have hexp : (0 : ℝ) < (2 - (n : ℝ)) / 2 := by
      rw [hn1ℝ]
      norm_num
    exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr hc)
      (sub_neg.mpr (Real.rpow_lt_rpow hsub.le hlt hexp))
  · have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hc : 0 < ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ := by
      have hnpos : (0 : ℝ) < n := by linarith
      have hnsub : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      positivity
    have hexp : (2 - (n : ℝ)) / 2 < 0 := by linarith
    exact mul_pos hc (sub_pos.mpr (Real.rpow_lt_rpow_of_neg hsub hlt hexp))

/-- The Fréchet derivative of the Green kernel of the unit ball in `y`, away from the pole and
wherever the reflection polynomial `‖x‖² ‖y‖² - 2 ⟪x, y⟫ + 1` is positive. -/
theorem hasFDerivAt_ballGreenKernel (hn : n ≠ 2) {x y : EuclideanSpace ℝ (Fin n)} (hxy : y ≠ x)
    (h : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) :
    HasFDerivAt (ballGreenKernel n x)
      ((-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
          ‖y - x‖ ^ (-(n : ℝ))) • innerSL ℝ (y - x) -
        (-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
          (‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1) ^ (-(n : ℝ) / 2)) •
        (‖x‖ ^ 2 • innerSL ℝ y - innerSL ℝ x)) y := by
  rw [ballGreenKernel_fun]
  exact (hasFDerivAt_newtonianKernel_sub n hn hxy).sub (hasFDerivAt_ballGreenCorrector hn h)

/-! ### The Poisson kernel -/

/-- The Poisson kernel of the Euclidean unit ball,

`K(x, y) = (1 - ‖x‖²) / (n ωₙ ‖x - y‖ⁿ)`,

for `x` in the ball and `y` on the unit sphere; `ωₙ` is the volume of the unit ball.  It is the
negative outward normal derivative of the Green kernel `ballGreenKernel n x` on the sphere. -/
def ballPoissonKernel (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 - ‖x‖ ^ 2) /
    ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ‖x - y‖ ^ n)

/-- The defining formula for the Poisson kernel of the unit ball. -/
theorem ballPoissonKernel_def (x y : EuclideanSpace ℝ (Fin n)) :
    ballPoissonKernel n x y =
      (1 - ‖x‖ ^ 2) /
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ‖x - y‖ ^ n) := by
  rw [ballPoissonKernel]

/-- The Poisson kernel of the unit ball is positive for a pole in the open ball and any other
point. -/
theorem ballPoissonKernel_pos {x y : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) (hxy : x ≠ y) :
    0 < ballPoissonKernel n x y := by
  have := nontrivial_of_ne x y hxy
  have hn : 0 < n := by simpa using Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Fin n))
  have hω := volume_real_unitBall_pos n
  have hsub : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hx' : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  rw [ballPoissonKernel_def]
  positivity

/-- The Poisson kernel with a pole in the open ball is positive on the unit sphere. -/
theorem ballPoissonKernel_pos_on_sphere (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1)
    (y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    0 < ballPoissonKernel n x y := by
  apply ballPoissonKernel_pos hx
  intro h
  have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere y
  rw [h] at hx
  linarith

/-- The Poisson kernel is continuous as a function of the boundary point when its pole
lies off the unit sphere. -/
theorem continuous_ballPoissonKernel_on_sphere
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≠ 1) :
    Continuous (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ballPoissonKernel n x y) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hy : ‖(y : EuclideanSpace ℝ (Fin 0))‖ = 1 := norm_eq_of_mem_sphere y
    have hy0 : (y : EuclideanSpace ℝ (Fin 0)) = 0 := Subsingleton.elim _ _
    simp [hy0] at hy
  have hxy : x ≠ (y : EuclideanSpace ℝ (Fin n)) := by
    intro h
    have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere y
    rw [h] at hx
    exact hx hy
  have hden : (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
      ‖x - (y : EuclideanSpace ℝ (Fin n))‖ ^ n ≠ 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hvol := volume_real_unitBall_pos n
    have hnorm : 0 < ‖x - (y : EuclideanSpace ℝ (Fin n))‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    positivity
  simp only [ballPoissonKernel_def]
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact hden

/-- The Poisson kernel is integrable over any subset of the sphere when its pole
lies off the sphere. -/
theorem integrableOn_ballPoissonKernel
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≠ 1)
    (s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    IntegrableOn (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ballPoissonKernel n x y) s volume.toSphere := by
  have hint : Integrable (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ballPoissonKernel n x y) volume.toSphere := by
    simpa only [integrableOn_univ] using
      (continuous_ballPoissonKernel_on_sphere x hx).continuousOn.integrableOn_compact
        isCompact_univ
  exact hint.integrableOn

/-- **The Poisson kernel is the normal derivative of the Green kernel.**  On the unit sphere, the
derivative of the Green kernel with pole `x` off the sphere, taken in the direction of the outward
unit normal `y`, is the negative of the Poisson kernel. -/
theorem fderiv_ballGreenKernel_normal (hn : n ≠ 2) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ≠ 1) (hy : ‖y‖ = 1) :
    fderiv ℝ (ballGreenKernel n x) y y = -ballPoissonKernel n x y := by
  have hxy : y ≠ x := by
    rintro rfl
    exact hx hy
  have h : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 :=
    norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos (by rw [hy, mul_one]; exact hx)
  have hsub : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [(hasFDerivAt_ballGreenKernel hn hxy h).fderiv, ← norm_sub_sq_eq_of_norm_eq_one x hy,
    ballPoissonKernel_def, norm_sub_rev x y]
  have hpow : (‖y - x‖ ^ 2) ^ (-(n : ℝ) / 2) = ‖y - x‖ ^ (-(n : ℝ)) :=
    (norm_rpow_eq_norm_sq_rpow (y - x) _).symm
  have hinv : ‖y - x‖ ^ (-(n : ℝ)) = (‖y - x‖ ^ n)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  simp only [sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, inner_sub_left,
    real_inner_self_eq_norm_sq, hy, real_inner_comm y x, hpow, hinv]
  rw [div_eq_mul_inv, mul_inv]
  ring

/-- The radial derivative of the Green kernel of the unit ball at a boundary point `y`, along the
ray from the center through `y`, is the negative of the Poisson kernel. -/
theorem hasDerivAt_ballGreenKernel_radial (hn : n ≠ 2) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ≠ 1) (hy : ‖y‖ = 1) :
    HasDerivAt (fun t : ℝ => ballGreenKernel n x (t • y)) (-ballPoissonKernel n x y) 1 := by
  have hxy : y ≠ x := by
    rintro rfl
    exact hx hy
  have h : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + 1 :=
    norm_sq_mul_norm_sq_sub_two_mul_inner_add_one_pos (by rw [hy, mul_one]; exact hx)
  have hG := hasFDerivAt_ballGreenKernel hn hxy h
  have hcurve : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have hG' : HasFDerivAt (ballGreenKernel n x) (fderiv ℝ (ballGreenKernel n x) y)
      ((fun t : ℝ => t • y) 1) := by
    simpa only [one_smul] using hG.differentiableAt.hasFDerivAt
  have hcomp := hG'.comp_hasDerivAt (1 : ℝ) hcurve
  rw [← fderiv_ballGreenKernel_normal hn hx hy]
  exact hcomp

end TauCeti

end
