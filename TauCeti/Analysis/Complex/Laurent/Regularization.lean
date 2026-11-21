/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Basic
import TauCeti.MeasureTheory.Integral.Circle.Integral

/-!
# Laurent coefficients of power-regularized maps

For a Banach-valued function `f`, clearing a pole by `(z - c)^N` shifts its Laurent coefficients
into the Taylor coefficients of the regularized function. The circle integral computes these
coefficients without using the value of `f` at `c`. Continuous linear maps commute with the
coefficient extraction; in particular a bounded-operator coefficient can be evaluated on a
vector, or composed with fixed bounded operators, before or after computing the circle integral.

We use Mathlib's Cauchy power series and `TauCeti.circleLaurentCoeff`, with the normalization
`1/(2πi)` as in Conway, *Functions of One Complex Variable I*, Chapters IV–V.
-/

public section

open Metric Set

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous linear maps commute with Laurent coefficient extraction on a circle on which
the function is integrable. -/
@[simp]
theorem map_circleLaurentCoeff (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (k : ℤ) :
    L (TauCeti.circleLaurentCoeff f c r k) =
      TauCeti.circleLaurentCoeff (fun z ↦ L (f z)) c r k := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [TauCeti.circleLaurentCoeff_def]
  have hc : c ∉ sphere c |r| := by simpa [eq_comm] using hr
  simp only [TauCeti.circleLaurentCoeff_def, map_smul,
    ← L.circleIntegral_comp_comm (hf.sub_zpow_smul (-k - 1) hc)]

end ContinuousLinearMap

namespace HasFPowerSeriesAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f g : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {c : ℂ} {r : ℝ} {N : ℕ}

/-- If `g` agrees with the power-regularization `(z - c)^N • f z` on the integrating circle,
and is holomorphic inside and continuous on the closed disc, its `k`-th Taylor coefficient is
the Laurent coefficient of `f` of degree `k - N` on that circle. -/
theorem circleLaurentCoeff_eq_coeff_of_eqOn (hp : HasFPowerSeriesAt g p c) (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball c r))
    (hfg : EqOn g (fun z ↦ (z - c) ^ N • f z) (sphere c r)) (k : ℕ) :
    TauCeti.circleLaurentCoeff f c r ((k : ℤ) - N) = p.coeff k := by
  let R : NNReal := ⟨r, hr.le⟩
  have hC : HasFPowerSeriesAt g (cauchyPowerSeries g c r) c :=
    (hg.hasFPowerSeriesOnBall (R := R) hr).hasFPowerSeriesAt
  have hshift := TauCeti.circleLaurentCoeff_sub_zpow_smul_apply f c r (N : ℤ) (k : ℤ)
  simp only [zpow_natCast] at hshift
  rw [← hshift, ← TauCeti.circleLaurentCoeff_congr hr.le hfg,
    TauCeti.circleLaurentCoeff_natCast, hC.eq_formalMultilinearSeries hp]

end HasFPowerSeriesAt
