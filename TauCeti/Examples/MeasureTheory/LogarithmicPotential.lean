/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Basic

/-!
# Logarithmic-potential regression

The complex logarithmic potential has the stated derivative below the real axis as well as above.
-/

open MeasureTheory

example (μ : Measure ℝ) [IsFiniteMeasure μ] {s : Set ℝ} (hs : IsCompact s)
    (hμ : μ.restrict s = μ) {z : ℂ} (hz : z.im < 0) :
    HasDerivAt (fun w : ℂ ↦ ∫ y : ℝ, Complex.log (w - y) ∂μ)
      (-MeasureTheory.resolventTransform μ z) z :=
  Measure.hasDerivAt_integral_clog_sub_of_im_ne_zero μ hs hμ hz.ne
