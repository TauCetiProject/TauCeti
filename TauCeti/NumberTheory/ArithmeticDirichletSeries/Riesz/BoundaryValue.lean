/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.RealRegularPart

/-!
# Removing the apparent pole in a real Riesz remainder transform

For real coefficients, an analytic regular part `G` of a compensated Dirichlet series has
`G(1)` real. Thus the real subtraction constant in the Riesz remainder gives the removable
quotient `(G(s)/s - re G(1))/(s - 1)`, with value `G′(1) - G(1)` at `1`.

The normalization occurs in `New.integral_primeRemainder` in the shorter GRH formalization
(lsernau/grh-lean, `grh/src/New/Reduction/Zeros/PrimeError.lean`, revision `72fead1`).
-/

public section

open Filter Set
open scoped Topology

/-- The real-part subtraction in the Riesz remainder transform removes the apparent pole at
`1` when `G` is analytic there and agrees just to the right on the real axis with a real
Dirichlet series minus a real counterterm. The filled-in value is `G′(1) - G(1)`. -/
theorem AnalyticAt.update_riesz_quotient_of_LSeries {a : ℕ → ℝ} {C : ℝ → ℝ} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 1)
    (h : ∀ᶠ x : ℝ in 𝓝[>] 1, G x = _root_.LSeries (fun n ↦ (a n : ℂ)) x - (C x : ℂ)) :
    AnalyticAt ℂ (Function.update (fun s : ℂ ↦ (G s / s - ((G 1).re : ℂ)) / (s - 1))
      1 (deriv G 1 - G 1)) 1 := by
  classical
  have him : (G 1).im = 0 :=
    ContinuousAt.im_eq_zero_of_eventuallyEq_LSeries_sub_ofReal
      (by simpa only [Complex.ofReal_one] using hG.continuousAt) h
  have hreal : ((G 1).re : ℂ) = G 1 := Complex.conj_eq_iff_re.mp <|
    Complex.conj_eq_iff_im.mpr him
  have hdiv : AnalyticAt ℂ (fun s : ℂ ↦ G s / s) 1 :=
    hG.fun_div analyticAt_id one_ne_zero
  have heq : dslope (fun s : ℂ ↦ G s / s) 1 =
      Function.update (fun s : ℂ ↦ (G s / s - ((G 1).re : ℂ)) / (s - 1))
        1 (deriv G 1 - G 1) := by
    refine Function.eq_update_iff.mpr ⟨?_, ?_⟩
    · rw [dslope_same]
      simpa only [id_eq, deriv_id, mul_one, one_pow, div_one] using
        deriv_fun_div hG.differentiableAt differentiableAt_id one_ne_zero
    · intro s hs
      rw [dslope_of_ne _ (mem_compl_singleton_iff.mp hs), slope_def_field, div_one, hreal]
  rw [← heq]
  exact hdiv.dslope 1
