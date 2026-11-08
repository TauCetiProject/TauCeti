/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
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
* `TauCeti.tendsto_eLpNorm_restrict_Ioo`: for a finite exponent, the `Lᵖ` norm of a function on
  the unit interval `(t, t + 1)` tends to zero as `t` tends to infinity in either direction.
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

/-- For a finite exponent `q`, the `Lᵖ` norm of a function on the unit interval `(t, t + 1)`
tends to zero as `t` tends to infinity in either direction. -/
theorem tendsto_eLpNorm_restrict_Ioo {F : Type*} [NormedAddCommGroup F] {μ : Measure ℝ}
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) {g : ℝ → F} (hg : MemLp g q μ) :
    Tendsto (fun t ↦ eLpNorm g q (μ.restrict (Set.Ioo t (t + 1)))) (cocompact ℝ) (𝓝 0) := by
  have : (cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]
    infer_instance
  -- Every point `x` leaves `(t, t + 1)` once `t ∉ [x - 1, x]`.
  have hout (x : ℝ) : ∀ᶠ t in cocompact ℝ, x ∉ Set.Ioo t (t + 1) :=
    Filter.mem_of_superset (isCompact_Icc (a := x - 1) (b := x)).compl_mem_cocompact
      fun t ht hx ↦ ht ⟨by linarith [hx.2], hx.1.le⟩
  have h := tendsto_eLpNorm_sub_of_ae_tendsto (m := μ) (l := cocompact ℝ) (C := 1) hq0 hq
    (f := fun t ↦ (Set.Ioo t (t + 1)).indicator g) (g := 0)
    (Eventually.of_forall fun t ↦ hg.aestronglyMeasurable.indicator measurableSet_Ioo)
    aestronglyMeasurable_zero hg
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
      rw [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul]
      exact enorm_indicator_le_enorm_self _ x)
    (Eventually.of_forall fun x ↦ tendsto_const_nhds.congr' <|
      (hout x).mono fun t ht ↦ (Set.indicator_of_notMem ht g).symm)
  simpa only [sub_zero,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet] using h

end TauCeti
