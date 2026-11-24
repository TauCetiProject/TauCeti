/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Limits in `Lᵖ` for comparable measures agree almost everywhere

If a family `w j` converges to `f` in `Lᵖ(μ)` and to `g` in `Lᵖ(ν)` along a nontrivial filter,
where `μ ≤ ν` and `p ≠ 0`, then `f = g` `μ`-almost everywhere
(`MeasureTheory.ae_eq_of_tendsto_eLpNorm_sub`).
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X} {F : Type*} [NormedAddCommGroup F]
  {p : ℝ≥0∞}

/-- If `w j` converges to `f` in `Lᵖ(μ)` and to `g` in `Lᵖ(ν)` along a nontrivial filter, where
`μ ≤ ν` and `p ≠ 0`, then `f = g` `μ`-almost everywhere. -/
theorem ae_eq_of_tendsto_eLpNorm_sub {ι : Type*} {l : Filter ι} [l.NeBot]
    (hp : p ≠ 0) (hμν : μ ≤ ν) {w : ι → X → F} {f g : X → F}
    (hwf : Tendsto (fun j => eLpNorm (w j - f) p μ) l (𝓝 0))
    (hwg : Tendsto (fun j => eLpNorm (w j - g) p ν) l (𝓝 0)) :
    f =ᵐ[μ] g := by
  have hle (j : ι) : eLpNorm (f - g) p μ ≤
      ENNReal.LpAddConst p * (eLpNorm (w j - f) p μ + eLpNorm (w j - g) p ν) := by
    calc eLpNorm (f - g) p μ = eLpNorm ((w j - g) - (w j - f)) p μ := by
          rw [sub_sub_sub_cancel_left]
      _ ≤ ENNReal.LpAddConst p * (eLpNorm (w j - g) p μ + eLpNorm (w j - f) p μ) :=
          eLpNorm_sub_le' p
      _ ≤ _ := by
          rw [add_comm (eLpNorm (w j - f) p μ)]
          gcongr
  have h0 : eLpNorm (f - g) p μ = 0 := by
    have hlim := ENNReal.Tendsto.const_mul (hwf.add hwg)
      (.inr (ENNReal.LpAddConst_lt_top p).ne)
    rw [add_zero, mul_zero] at hlim
    exact le_antisymm (ge_of_tendsto' hlim hle) zero_le
  filter_upwards [(eLpNorm_eq_zero_iff hp).1 h0] with y hy
  simpa [sub_eq_zero] using hy

end MeasureTheory
