/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
import TauCeti.Analysis.Complex.Poisson.Boundary

/-!
# The boundary Poisson formula for Hardy functions

The holomorphic disk function of a boundary Hardy function is its Poisson integral against
normalized Haar measure. The boundary function need only belong to `L²`; no continuous
boundary representative is assumed. This formula is the linear input to constructing a
harmonic majorant from the squared boundary modulus.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Chapter 3, Theorem 3.1.
-/

public section

open Complex MeasureTheory

namespace TauCeti.HardySpace

variable (x : HardySpace) {w : ℂ}

/-- **The boundary Poisson formula.** The disk function of an arbitrary `L²` Hardy function
is its Poisson integral over the circle with normalized Haar measure. -/
theorem integral_poissonKernel_smul_eq_diskFunction (hw : ‖w‖ < 1) :
    (∫ t : UnitAddCircle, poissonKernel 0 w (AddCircle.toCircle t) •
      (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t ∂AddCircle.haarAddCircle) =
      x.diskFunction w := by
  have h := x.differentiableOn_diskFunction.integral_poissonKernel_smul_eq_of_tendsto_eLpNorm
    (T := 1) (p := 2) (g := (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))
    (by norm_num) (by simpa using x.tendsto_eLpNorm_diskFunction_sub)
    (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
  simpa using h

end TauCeti.HardySpace
