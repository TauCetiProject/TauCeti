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

For a finite exponent `q`, if the functions `f n` converge to `g` almost everywhere
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

/-- **Dominated convergence in `Lᵖ`.** For a finite exponent, if `f n` converges to `g` at almost
every point and `‖f n - g‖ₑ` is eventually dominated by a fixed nonnegative multiple of the enorm
of a `MemLp` function, then `f n → g` in the `Lᵖ` seminorm.
The dominating function may take values in any topological space with an extended norm.
Both the measurability of `f n` and the domination are only needed eventually along `l`, and `g`
is not assumed to be measurable: if `l ≠ ⊥`, it is the a.e. limit of a sequence `f (u k)` of
a.e. strongly measurable terms, hence a.e. strongly measurable itself, while for `l = ⊥` the
conclusion holds trivially. -/
theorem tendsto_eLpNorm_sub_of_ae_tendsto {α ι F G : Type*} [MeasurableSpace α]
    {m : Measure α} [SeminormedAddGroup F] [IsTopologicalAddGroup F]
    [TopologicalSpace G] [ENorm G]
    {l : Filter ι} [l.IsCountablyGenerated] {q : ℝ≥0∞}
    (hq : q ≠ ∞) {f : ι → α → F} {g : α → F}
    (hf : ∀ᶠ n in l, AEStronglyMeasurable (f n) m)
    {bound : α → G} (hb : MemLp bound q m)
    {C : ℝ≥0} (hbound : ∀ᶠ n in l, ∀ᵐ x ∂m, ‖f n x - g x‖ₑ ≤ C * ‖bound x‖ₑ)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) q m) l (𝓝 0) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hg : AEStronglyMeasurable g m := by
    obtain ⟨u, hu, hum⟩ := exists_seq_forall_of_frequently hf.frequently
    exact aestronglyMeasurable_of_tendsto_ae atTop hum (hlim.mono fun x hx => hx.comp hu)
  have hfg : ∀ᶠ n in l, AEStronglyMeasurable (f n - g) m := hf.mono fun _ hn => hn.sub hg
  rcases eq_or_ne q 0 with rfl | hq0
  · exact tendsto_const_nhds.congr' (hfg.mono fun _ hn => (eLpNorm_exponent_zero hn).symm)
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  refine Tendsto.congr' (hfg.mono fun _ hn =>
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hn).symm) ?_
  have hlint : Tendsto (fun n => ∫⁻ x, ‖(f n - g) x‖ₑ ^ q.toReal ∂m) l (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence'
      (F := fun n x => ‖(f n - g) x‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun x => ((C : ℝ≥0∞) * ‖bound x‖ₑ) ^ q.toReal)
      (hfg.mono fun _ hn => hn.enorm.pow_const _)
      (hbound.mono fun _ hn => hn.mono fun _ hx => ENNReal.rpow_le_rpow hx hr.le)
      (by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
        rw [lintegral_const_mul' _ _ (by simp [hr.le])]
        exact ENNReal.mul_ne_top (by simp [hr.le])
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hq hb).ne)
      (hlim.mono fun x hx => by
        simpa [hr] using (hx.sub (tendsto_const_nhds (x := g x))).enorm.ennrpow_const q.toReal)
  simpa only [ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)] using
    hlint.ennrpow_const (1 / q.toReal)

end TauCeti
