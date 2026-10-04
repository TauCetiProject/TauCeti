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
# Dominated convergence in `Lᵖ`

For a finite nonzero exponent `q`, if the functions `f n` converge to `g` almost everywhere
and the errors `‖f n - g‖ₑ` are eventually dominated by a fixed nonnegative multiple of the
enorm of a `MemLp` function, then `f n → g` in the `Lᵖ` seminorm. In particular, this applies
when truncating a function by cutoffs that are eventually `1` on every bounded set.
The dominating function's codomain only needs a topology and an extended norm.

## Main declarations

* `TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto`: the convergence `eLpNorm (f n - g) q m → 0`.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped NNReal ENNReal Topology

/-- **Dominated convergence in `Lᵖ`.** For a finite nonzero exponent, if `f n` converges to `g`
at almost every point and `‖f n - g‖ₑ` is eventually dominated by a fixed nonnegative multiple
of the enorm of a `MemLp` function, then `f n → g` in the `Lᵖ` seminorm.
The dominating function may take values in any topological space with an extended norm.
Both the measurability of `f n` and the domination are only needed eventually along `l`.
The limit needs only to be a.e. strongly
measurable; the dominating function supplies the integrability of the errors. -/
theorem tendsto_eLpNorm_sub_of_ae_tendsto {α ι F G : Type*} [MeasurableSpace α]
    {m : Measure α} [SeminormedAddGroup F] [IsTopologicalAddGroup F]
    [TopologicalSpace G] [ENorm G]
    {l : Filter ι} [l.IsCountablyGenerated] {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hq : q ≠ ∞) {f : ι → α → F} {g : α → F}
    (hf : ∀ᶠ n in l, AEStronglyMeasurable (f n) m) (hg : AEStronglyMeasurable g m)
    {bound : α → G} (hb : MemLp bound q m)
    {C : ℝ≥0} (hbound : ∀ᶠ n in l, ∀ᵐ x ∂m, ‖f n x - g x‖ₑ ≤ C * ‖bound x‖ₑ)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) q m) l (𝓝 0) := by
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  refine Tendsto.congr' (hf.mono fun n hn =>
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq (hn.sub hg)).symm) ?_
  have hlint : Tendsto (fun n => ∫⁻ x, ‖(f n - g) x‖ₑ ^ q.toReal ∂m) l (𝓝 0) := by
    have hdom := tendsto_lintegral_filter_of_dominated_convergence' (μ := m)
      (F := fun n x => ‖(f n - g) x‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun x => ((C : ℝ≥0∞) * ‖bound x‖ₑ) ^ q.toReal)
      (hf.mono fun n hn => (hn.sub hg).enorm.pow_const _)
      (hbound.mono fun _ hn => hn.mono fun _ hx => ENNReal.rpow_le_rpow hx hr.le)
      (by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.coe_ne_top)]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.coe_ne_top)
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hq hb).ne)
      (hlim.mono fun x hx => by
        simpa [enorm_eq_nnnorm, ENNReal.zero_rpow_of_pos hr] using
          (hx.sub (tendsto_const_nhds (x := g x))).enorm.ennrpow_const q.toReal)
    simpa only [lintegral_zero] using hdom
  have h0 : (0 : ℝ≥0∞) ^ (1 / q.toReal) = 0 := ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)
  simpa only [h0] using hlint.ennrpow_const (1 / q.toReal)

end TauCeti
