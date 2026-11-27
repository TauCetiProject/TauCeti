/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta
public import TauCeti.NumberTheory.LSeries.ThetaInversion

/-!
# Dirichlet theta sums as sums of Hurwitz kernels

A positive-index Gaussian theta sum with character coefficients can be expressed as a
finite sum of Hurwitz theta kernels. The character's parity determines the kernel, and
in even degree the zero term must be removed. This identifies the kernel in the Mellin
representation of a completed Dirichlet L-function with its positive-index series.

The normalization is that of `New.hasMellin_thetaSeries_char` in
`grh/src/Lib/Analytic/DirichletTheta.lean` of lsernau/grh-lean (revision `72fead1`),
with the square-root factor left out of the theta sum.
-/

public section

open Finset HurwitzZeta Set TauCeti

namespace DirichletCharacter

/-- Group the positive-index theta sum of a Dirichlet character into residue classes using
Hurwitz kernels, removing the contribution at zero in the even case. -/
theorem gaussianDirichletTheta_eq_hurwitz_sum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {j : ℕ} (hj : j ≤ 1) (hpar : χ (-1) = (-1) ^ j) {t : ℝ} (ht : t ≠ 0) :
    gaussianDirichletTheta j (fun n ↦ χ n) t =
      ((((N : ℝ) * t) ^ j : ℝ) : ℂ) / 2 *
        ∑ a : ZMod N, χ a *
          ((if j = 0 then evenKernel else oddKernel) (ZMod.toAddCircle a) ((N * t) ^ 2) : ℂ)
      - (if j = 0 then χ 0 else 0) / 2 := by
  have h := (ZMod.hasSum_periodic_gaussian_residue_sum χ hj ht).tsum_eq
  rw [χ.tsum_gaussian_eq_zero_add_two_mul_tsum_succ hpar ht] at h
  rw [gaussianDirichletTheta_def]
  push_cast at h ⊢
  linear_combination h / 2

/-- At a nontrivial modulus the zero term vanishes. The positive-index theta sum and the
weighted Hurwitz kernel sum then agree on the positive axis, the domain of Mellin integration. -/
theorem eqOn_gaussianDirichletTheta_hurwitz_sum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) {j : ℕ} (hj : j ≤ 1)
    (hpar : χ (-1) = (-1) ^ j) :
    EqOn (gaussianDirichletTheta j (fun n ↦ χ n))
      (fun t ↦ ((((N : ℝ) * t) ^ j : ℝ) : ℂ) / 2 *
        ∑ a : ZMod N, χ a *
          ((if j = 0 then evenKernel else oddKernel) (ZMod.toAddCircle a) ((N * t) ^ 2) : ℂ))
      (Ioi 0) := by
  intro t ht
  simp [χ.gaussianDirichletTheta_eq_hurwitz_sum hj hpar (mem_Ioi.mp ht).ne', χ.map_zero' hN]

end DirichletCharacter
