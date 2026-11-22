/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quadratic

/-!
# Strict convexity of `W₂ ^ 2` on a Euclidean space

On a finite-dimensional real inner product space `E`, strict convexity of the quadratic transport
cost for a finite `c - c`-regular source (`TauCeti.IsCCRegular.transportCost_smul_add_smul_lt`)
transfers directly to `ν ↦ W₂(μ, ν) ^ 2` on targets at finite `W₂` distance from `μ` via
`W₂(μ, ν) ^ 2 = 2 * transportCost (‖x - y‖ ^ 2 / 2) μ ν`. In particular, via the sufficient
conditions in `TauCeti.Analysis.Convex.CCHypersurface.Regular`, `ν ↦ W₂(μ, ν) ^ 2` is strictly
convex on targets at finite `W₂` distance from `μ` whenever `μ` is finite and gives zero mass to
globally Lipschitz graphs over hyperplanes, vanishes on Borel sets with `dimH A + 1 ≤ finrank ℝ E`
or small sets (`dimH A ≤ finrank ℝ E - 1`, Agueh–Carlier §3.1), or is absolutely continuous with
respect to an additive Haar measure.

## Main statements

* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt` — strict convexity of `ν ↦ W₂(μ, ν) ^ 2`
  on targets at finite `W₂` distance from a finite `c - c`-regular `μ` (covering null Lipschitz
  graphs, small Hausdorff dimension, and laws absolutely continuous with respect to an additive Haar
  measure).

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, §3.1 (Definition 3.2 and the proof of Proposition 3.5).
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` is regular.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for a `c - c`-regular `μ`.** On a finite-dimensional
real inner product space, let `μ` be a finite `c - c`-regular measure (in particular, a finite
measure absolutely continuous with respect to an additive Haar measure), and let `ν₀ ≠ ν₁` be
measures at finite `W₂` distance from `μ`. For nonzero weights with `a + b = 1`,
`W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt {μ ν₀ ν₁ : Measure E} [IsFiniteMeasure μ]
    (hμ : IsCCRegular μ) {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 := by
  have hfin₀ := transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top h₀
  have hfin₁ := transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top h₁
  rw [wassersteinEDist_two_sq_eq_two_mul_transportCost,
    wassersteinEDist_two_sq_eq_two_mul_transportCost,
    wassersteinEDist_two_sq_eq_two_mul_transportCost,
    mul_left_comm a 2, mul_left_comm b 2, ← mul_add]
  exact ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top
    (hμ.transportCost_smul_add_smul_lt hab ha hb hfin₀ hfin₁ hne)

end TauCeti
