/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta.Basic

import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.RealFactor

/-!
# The Gaussian Mellin factor on vertical strips

The Mellin transform of the even or odd Gaussian is half the corresponding shifted real
archimedean gamma factor. It is holomorphic and nonzero on its half-plane of convergence.
On any closed vertical strip in this half-plane, its norm is bounded by the larger of its two
real endpoint norms. In particular the bound on `1/2 ≤ re s ≤ 2` is independent of the height,
as needed when applying three-lines interpolation to mollified Dirichlet L-functions.

## Reference

`lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
`grh/src/Lib/Analytic/DirichletTheta.lean` (`New.gaussianMellin_eq` and the strip bound in
`New.gaussianMellin_differentiableOn_and_bdd`).
-/

public section

open Complex Set

namespace TauCeti

variable {j : Fin 2} {s : ℂ}

/-- The Gaussian Mellin factor has no zeros on its half-plane of convergence. -/
theorem gaussianMellin_ne_zero (hs : -(j.val : ℝ) < s.re) : gaussianMellin j s ≠ 0 := by
  rw [gaussianMellin_eq_Gammaℝ_div_two hs]
  exact div_ne_zero (Gammaℝ_ne_zero_of_re_pos (by simp; linarith)) two_ne_zero

/-- The Gaussian Mellin factor is holomorphic on its half-plane of convergence. -/
theorem analyticOnNhd_gaussianMellin (j : Fin 2) :
    AnalyticOnNhd ℂ (gaussianMellin j) {z | -(j.val : ℝ) < z.re} := by
  have hopen : IsOpen {z : ℂ | -(j.val : ℝ) < z.re} :=
    isOpen_lt continuous_const continuous_re
  refine AnalyticOnNhd.congr hopen (f := fun z ↦ Gammaℝ (z + j.val) / 2) ?_ ?_
  · intro z hz
    have hz' : -(j.val : ℝ) < z.re := hz
    have hΓ := analyticAt_Gammaℝ_of_ne_zero
      (Gammaℝ_ne_zero_of_re_pos (s := z + j.val) (by simp; linarith))
    have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w + j.val) z := by fun_prop
    exact (hΓ.comp (f := fun w : ℂ ↦ w + j.val) (x := z) hshift).div_const
  · intro z hz
    exact (gaussianMellin_eq_Gammaℝ_div_two hz).symm

/-- The largest norm of the Gaussian Mellin factor on a closed strip within the convergence
half-plane is attained at one of the two real endpoints. -/
theorem norm_gaussianMellin_le_max {a b : ℝ} (ha : -(j.val : ℝ) < a) (hs : s.re ∈ Icc a b) :
    ‖gaussianMellin j s‖ ≤ max ‖gaussianMellin j (a : ℂ)‖ ‖gaussianMellin j (b : ℂ)‖ := by
  have hb := ha.trans_le (hs.1.trans hs.2)
  rw [gaussianMellin_eq_Gammaℝ_div_two (ha.trans_le hs.1),
    gaussianMellin_eq_Gammaℝ_div_two (by simpa using ha),
    gaussianMellin_eq_Gammaℝ_div_two (by simpa using hb)]
  simp only [Complex.norm_div, norm_ofNat, ← ofReal_natCast, ← ofReal_add,
    max_div_div_right (zero_le_two : 0 ≤ (2 : ℝ))]
  have hΓ : (s + (j.val : ℂ)).re ∈ Icc (a + j.val) (b + j.val) := by
    simpa only [add_re, natCast_re, mem_Icc, add_le_add_iff_right] using hs
  exact div_le_div_of_nonneg_right
    (norm_Gammaℝ_le_max_of_re_mem_Icc (by linarith) hΓ) zero_le_two

end TauCeti
