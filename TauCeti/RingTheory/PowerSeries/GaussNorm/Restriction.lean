/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Radius restriction in exponential coordinates

Bounded weighted coefficient norms at `b ^ τ` give restrictedness at `b ^ σ` when
`1 < b` and `σ < τ`. This expresses radius restriction in the logarithmic coordinates
used to compare Gauss norms with Newton supporting values.
-/

public section

namespace PowerSeries.HasGaussNorm

/-- Bounded weighted coefficient norms at `b ^ τ`, with `1 < b`, give restrictedness at
every radius `b ^ σ` with `σ < τ`. -/
theorem isRestricted_rpow_of_lt {R : Type*} [NormedRing R] {f : PowerSeries R} {b σ τ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ τ)) (hb : 1 < b) (hστ : σ < τ) :
    f.IsRestricted (b ^ σ) := by
  apply hf.isRestricted_of_abs_lt
  rw [abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)]
  exact (Real.rpow_lt_rpow_left_iff hb).mpr hστ

end PowerSeries.HasGaussNorm
