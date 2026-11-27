/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta
public import TauCeti.NumberTheory.LSeries.ThetaInversion

/-!
# Dirichlet theta sums in residue-class coordinates

A positive-index Gaussian theta sum of matching parity can be expressed as a finite
linear combination of Hurwitz theta kernels. This lets the Mellin transforms of the
Hurwitz kernels be used for the same theta sums that occur in quadratic-twist estimates.
The formula keeps the zero-index correction, including for the character of level one.

The normalization is that of `New.hasMellin_thetaSeries_char` in `Lib/Analytic/DirichletTheta`
of lsernau/grh-lean (`72fead1`), with the square-root weight kept separate.
-/

public section

open TauCeti HurwitzZeta

namespace DirichletCharacter

/-- Split a positive-index Dirichlet theta sum into the Hurwitz theta kernels of the residue
classes, subtracting the zero-index term of the bilateral sum. The degree of the Gaussian
weight must agree with the parity of the character and be either zero or one. -/
theorem gaussianDirichletTheta_eq_residue_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {j : ℕ} (hj : j ≤ 1) (hpar : χ (-1) = (-1) ^ j) {t : ℝ} (ht : t ≠ 0) :
    gaussianDirichletTheta j (fun n ↦ χ (n : ZMod N)) t =
      (((N : ℝ) * t : ℂ) ^ j * ∑ a : ZMod N, χ a *
        (if j = 0 then (evenKernel (ZMod.toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)
          else (oddKernel (ZMod.toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)) -
        χ 0 * (if j = 0 then 1 else 0)) / 2 := by
  have h := ZMod.tsum_periodic_gaussian_eq_residue_sum (χ : ZMod N → ℂ) hj t
  rw [χ.tsum_gaussian_eq_add_two_mul_tsum_succ hpar ht,
    ← gaussianDirichletTheta_def j (fun n ↦ χ (n : ZMod N)) t] at h
  have hzero : ((0 ^ j * Real.exp (-Real.pi * (0 : ℝ) ^ 2) : ℝ) : ℂ) =
      if j = 0 then 1 else 0 := by
    by_cases hz : j = 0 <;> simp [hz, zero_pow]
  rw [hzero] at h
  rw [← h]
  ring

end DirichletCharacter
