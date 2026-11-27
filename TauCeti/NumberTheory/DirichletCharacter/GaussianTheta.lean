/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.LSeries.GaussianTheta
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.DirichletCharacter.PartialSum

/-!
# Small-scale bounds for Dirichlet theta series

For a nonprincipal character, cancellation over each period bounds the unnormalized Gaussian
sum by the modulus, uniformly in the positive scale. In the square-root normalization this
controls the series at zero, where the absolute termwise estimate would grow as `1 / √u`.
The result applies to imprimitive characters and either Gaussian parity.

## References

* The small-scale bound used in `New.norm_gaussianTheta_char_le` in
  `grh/src/Lib/Analytic/DirichletTheta.lean` of <https://github.com/lsernau/grh-lean>, revision
  `72fead102f663d5c7a407964a13dc0cf9d977207`. Here the bound follows from Abel summation rather
  than Poisson summation.
-/

public section

open Filter MeasureTheory Real
open scoped Topology

namespace DirichletCharacter

open TauCeti

/-- The unnormalized Gaussian theta sum of a nonprincipal character is bounded by its modulus
at every positive scale, without a primitivity or parity-matching hypothesis. -/
theorem norm_gaussianTheta_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (j : Fin 2) {u : ℝ} (hu : 0 < u) :
    ‖gaussianTheta j (fun n ↦ χ n) u‖ ≤ N := by
  have hχ0 : χ (0 : ZMod N) = 0 := χ.map_zero' (by rintro rfl; exact hχ (Subsingleton.elim _ _))
  have hpartial (n : ℕ) : ‖∑ k ∈ Finset.Icc 0 n, χ k‖ ≤ (N : ℝ) := by
    simpa [Finset.Icc_eq_cons_Ioc n.zero_le, ← Finset.Icc_add_one_left_eq_Ioc, hχ0] using
      χ.norm_sum_Icc_le_level hχ n
  let f (t : ℝ) : ℂ := gaussianMonomial j (t * u)
  have hderiv (t : ℝ) : HasDerivAt f ((deriv (gaussianMonomial j) (t * u) * u : ℝ) : ℂ) t := by
    have hm : HasDerivAt (fun t ↦ t * u) u t := by simpa using (hasDerivAt_id t).mul_const u
    exact ((differentiable_gaussianMonomial j (t * u)).hasDerivAt.comp t hm).ofReal_comp
  have hdf : deriv f = fun t ↦ ((deriv (gaussianMonomial j) (t * u) * u : ℝ) : ℂ) :=
    funext fun t ↦ (hderiv t).deriv
  have hi : IntegrableOn (deriv f) (Set.Ici 0) := by
    have hs := (integrableOn_Ioi_comp_mul_right_iff (deriv (gaussianMonomial j)) 0 hu).2
      (by simpa only [zero_mul] using integrableOn_deriv_gaussianMonomial j)
    rw [integrableOn_Ici_iff_integrableOn_Ioi, hdf]
    exact (hs.mul_const u).ofReal
  have ht : Tendsto f atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, Complex.ofReal_zero, f] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_gaussianMonomial_atTop_zero j).comp (tendsto_id.atTop_mul_const hu))
  have hnormDeriv (t : ℝ) : ‖deriv f t‖ = u * ‖deriv (gaussianMonomial j) (t * u)‖ := by
    simp only [hdf, Complex.norm_real, norm_mul, norm_of_nonneg hu.le]
    exact mul_comm _ _
  -- The factor `u` from the chain rule cancels the Jacobian of the rescaling.
  have hb : (∫ t in Set.Ioi 0, ‖deriv f t‖) ≤ 1 := by
    simp_rw [hnormDeriv]
    rw [integral_const_mul, ← smul_eq_mul,
      integral_comp_mul_right_Ioi' (fun t ↦ ‖deriv (gaussianMonomial j) t‖) 0 hu, zero_mul]
    exact integral_norm_deriv_gaussianMonomial_le j
  obtain ⟨L, hL, hnorm⟩ := exists_tendsto_sum_mul_and_norm_le
    (f := f) hpartial (fun t _ ↦ (hderiv t).differentiableAt) hi ht
  have hs : Summable (fun n : ℕ ↦ χ n * (gaussianMonomial j (n * u) : ℂ)) :=
    summable_pnat_iff_summable_nat.mp <|
      summable_gaussianTheta (j := j) (c := fun n ↦ χ n) (fun n ↦ χ.norm_le_one _) hu
  have heq : (∑' n : ℕ, χ n * (gaussianMonomial j (n * u) : ℂ)) =
      gaussianTheta j (fun n ↦ χ n) u := by
    rw [gaussianTheta_def]
    simpa only [hs.tsum_eq_zero_add, Nat.cast_zero, hχ0, zero_mul, zero_add] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ χ n * (gaussianMonomial j (n * u) : ℂ))).symm
  have htheta : Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 0 n, χ k * (gaussianMonomial j (k * u) : ℂ)) atTop
      (𝓝 (gaussianTheta j (fun n ↦ χ n) u)) := by
    simpa only [Function.comp_def, Nat.range_succ_eq_Icc_zero, heq] using
      hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  rw [tendsto_nhds_unique htheta hL]
  exact hnorm.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hb)

/-- A nonprincipal character's square-root-normalized Gaussian theta series is bounded by
`N √u`. At nonpositive scales the square-root normalization makes the series vanish. -/
theorem norm_gaussianThetaSeries_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (j : Fin 2) (u : ℝ) :
    ‖gaussianThetaSeries j (fun n ↦ χ n) u‖ ≤ (N : ℝ) * √u := by
  obtain hu | hu := le_or_gt u 0
  · simp [gaussianThetaSeries_def, sqrt_eq_zero_of_nonpos hu]
  rw [gaussianThetaSeries_def, norm_mul, Complex.norm_real,
    norm_of_nonneg (sqrt_nonneg u), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (χ.norm_gaussianTheta_le_of_ne_one hχ j hu) (sqrt_nonneg u)

end DirichletCharacter
