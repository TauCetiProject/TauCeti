/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Dominated convergence in `Lᵖ` for eventually equal approximations

For a finite nonzero exponent `q`, if the functions `f n` eventually agree with `g` at almost
every point and the errors `‖f n - g‖` are eventually dominated by a fixed multiple of `‖g‖`,
where `g ∈ Lᵖ`, then `f n → g` in the `Lᵖ` seminorm.  This is the shape produced by truncating a
function by cutoffs that are eventually `1` on every bounded set.

## Main declarations

* `TauCeti.tendsto_eLpNorm_sub_of_eventually_eq`: the convergence `eLpNorm (f n - g) q m → 0`.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped ENNReal Topology

/-- **Dominated convergence in `Lᵖ`.** For a finite nonzero exponent, if `f n` eventually agrees
with `g` at almost every point and `‖f n - g‖` is eventually dominated by a fixed multiple of
`‖g‖`, where `g ∈ Lᵖ`, then `f n → g` in the `Lᵖ` seminorm.  Both the measurability of `f n` and
the domination are only needed eventually along `l`. -/
theorem tendsto_eLpNorm_sub_of_eventually_eq {α ι F : Type*} [MeasurableSpace α]
    {m : Measure α} [NormedAddCommGroup F] {l : Filter ι} [l.IsCountablyGenerated] {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hq : q ≠ ∞) {f : ι → α → F} {g : α → F}
    (hf : ∀ᶠ n in l, AEStronglyMeasurable (f n) m) (hg : MemLp g q m)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ n in l, ∀ᵐ x ∂m, ‖f n x - g x‖ ≤ C * ‖g x‖)
    (hlim : ∀ᵐ x ∂m, ∀ᶠ n in l, f n x = g x) :
    Tendsto (fun n => eLpNorm (f n - g) q m) l (𝓝 0) := by
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq]
  have hlint : Tendsto (fun n => ∫⁻ x, ‖(f n - g) x‖ₑ ^ q.toReal ∂m) l (𝓝 0) := by
    have hdom := tendsto_lintegral_filter_of_dominated_convergence' (μ := m)
      (F := fun n x => ‖(f n - g) x‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun x => (ENNReal.ofReal C * ‖g x‖ₑ) ^ q.toReal)
      (hf.mono fun n hn => (hn.sub hg.1).enorm.pow_const _)
      (hbound.mono fun _ hn => hn.mono fun x hx => by
        refine ENNReal.rpow_le_rpow ?_ hr.le
        rw [Pi.sub_apply, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal hx)
      (by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hq hg.2).ne)
      (hlim.mono fun x hx => tendsto_const_nhds.congr' (hx.mono fun n hn => by
        simp [hn, ENNReal.zero_rpow_of_pos hr]))
    simpa only [lintegral_zero] using hdom
  have h0 : (0 : ℝ≥0∞) ^ (1 / q.toReal) = 0 := ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)
  simpa only [h0] using hlint.ennrpow_const (1 / q.toReal)

end TauCeti
