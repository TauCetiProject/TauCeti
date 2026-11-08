/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Limits in `Lᵖ` on nested sets agree almost everywhere

If a family `w j` converges to `f` in `Lᵖ(A)` and to `g` in `Lᵖ(B)` along a nontrivial filter,
where `A ⊆ B`, then `f = g` almost everywhere on `A`
(`MeasureTheory.ae_eq_restrict_of_tendsto_eLpNorm_sub`).
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Type*} [NormedAddCommGroup F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If `w j` converges to `f` in `Lᵖ(A)` and to `g` in `Lᵖ(B)` along a nontrivial filter, where
`A ⊆ B`, then `f = g` almost everywhere on `A`. -/
theorem ae_eq_restrict_of_tendsto_eLpNorm_sub {ι : Type*} {l : Filter ι} [l.NeBot]
    {A B : Set X} (hAB : A ⊆ B) {w : ι → X → F} {f g : X → F}
    (hwf : Tendsto (fun j => eLpNorm (w j - f) p (μ.restrict A)) l (𝓝 0))
    (hwg : Tendsto (fun j => eLpNorm (w j - g) p (μ.restrict B)) l (𝓝 0)) :
    f =ᵐ[μ.restrict A] g := by
  have hle (j : ι) : eLpNorm (f - g) p (μ.restrict A) ≤
      eLpNorm (w j - f) p (μ.restrict A) + eLpNorm (w j - g) p (μ.restrict B) := by
    calc eLpNorm (f - g) p (μ.restrict A)
        = eLpNorm ((w j - g) - (w j - f)) p (μ.restrict A) := by rw [sub_sub_sub_cancel_left]
      _ ≤ eLpNorm (w j - g) p (μ.restrict A) + eLpNorm (w j - f) p (μ.restrict A) :=
          eLpNorm_sub_le Fact.out
      _ ≤ _ := by
          rw [add_comm]
          gcongr
  have h0 : eLpNorm (f - g) p (μ.restrict A) = 0 :=
    le_antisymm (ge_of_tendsto' (by simpa using hwf.add hwg) hle) zero_le
  filter_upwards [(eLpNorm_eq_zero_iff (zero_lt_one.trans_le Fact.out).ne').1 h0] with y hy
  simpa [sub_eq_zero] using hy

end MeasureTheory
