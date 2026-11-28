/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Dominated convergence in `Lᵖ`

For a countably generated filter `l` and a finite exponent `q`, if functions `f n` are eventually
a.e. strongly measurable, converge to `g` almost everywhere along `l`, and have errors
`‖f n - g‖ₑ` eventually dominated almost everywhere by a fixed nonnegative multiple of the enorm of
a `MemLp` function, then `f n → g` in the `Lᵖ` seminorm
(`TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto`). Likewise, if eventually a.e. strongly measurable
functions `f n` are eventually dominated almost everywhere by a `MemLp` function, then for any
exponent `q` along a countably generated `NeBot` filter the limit `g` lies in `L^q`
(`TauCeti.memLp_of_ae_tendsto`), and when `1 ≤ q < ∞` with `f n` and `g` in `L^q` (`MemLp`), the
classes `(hf n).toLp (f n)` converge to `hg.toLp g` in `Lp F q m`
(`TauCeti.tendsto_toLp_of_ae_tendsto`, and its specialization
`TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le` when `v =ᵐ[μ] u` and `‖us n x‖ ≤ ‖u x‖` a.e. for
every `n`). In particular, this applies when truncating a function by cutoffs that are eventually
`1` on every bounded set. The dominating function's codomain only needs a topology and an extended
norm.

The file also records the reverse Fatou lemma for `Lᵖ` seminorms over sets: the `Lᵖ` seminorms of
a function over measurable sets `s n` have limit superior at most its `Lᵖ` seminorm over
`limsup s n`, the set of points lying in infinitely many `s n`.

## Main declarations

* `TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto`: the convergence `eLpNorm (f n - g) q m → 0`.
* `TauCeti.memLp_of_ae_tendsto`: a dominated almost-everywhere limit along a countably generated
  `NeBot` filter lies in `L^q`.
* `TauCeti.tendsto_toLp_of_ae_tendsto`: dominated convergence in `Lp F q m` for `1 ≤ q < ∞`.
* `TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le`: if `uₙ → u` almost everywhere with
  `‖uₙ‖ ≤ ‖u‖`, then the `Lp` classes of `uₙ` converge to any representative of `u`.
* `TauCeti.tendsto_eLpNorm_restrict_Ioo`: for a finite exponent, the `Lᵖ` norm of a function on
  the unit interval `(t, t + 1)` tends to zero as `t` tends to infinity in either direction.
* `TauCeti.tendsto_eLpNorm_restrict_closedBall`: for a finite exponent and a measure vanishing on
  points, the `Lᵖ` norm of a function on the closed ball of radius `r` about a point tends to zero
  with `r`.
* `TauCeti.limsup_eLpNorm_restrict_le`: `limsup ‖g‖_{Lᵖ(s n)} ≤ ‖g‖_{Lᵖ(limsup s n)}` for
  `0 < p < ∞` when the `s n` lie in a set `t` with `g ∈ Lᵖ(t)`.
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
    (eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq hn).symm) ?_
  have hlint : Tendsto (fun n => ∫⁻ x, ‖(f n - g) x‖ₑ ^ q.toReal ∂m) l (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence'
      (F := fun n x => ‖(f n - g) x‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun x => ((C : ℝ≥0∞) * ‖bound x‖ₑ) ^ q.toReal)
      (hfg.mono fun _ hn => hn.eNorm.pow_const _)
      (hbound.mono fun _ hn => hn.mono fun _ hx => ENNReal.rpow_le_rpow hx hr.le)
      (by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
        rw [lintegral_const_mul' _ _ (by simp [hr.le])]
        exact ENNReal.mul_ne_top (by simp [hr.le])
          (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hq0 hq hb).ne)
      (hlim.mono fun x hx => by
        simpa [hr] using (hx.sub (tendsto_const_nhds (x := g x))).eNorm.ennrpow_const q.toReal)
  simpa only [ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)] using
    hlint.ennrpow_const (1 / q.toReal)

/-- If functions `f n` are eventually a.e. strongly measurable, converge almost everywhere along a
countably generated `NeBot` filter `l` to `g`, and have enorms eventually bounded almost everywhere
by the enorm of a `MemLp` function `bound`, then `g` is in `L^q`. -/
theorem memLp_of_ae_tendsto {α ι F G : Type*} [MeasurableSpace α]
    {m : Measure α} [TopologicalSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    [ContinuousENorm F] [TopologicalSpace G] [ENorm G]
    {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {q : ℝ≥0∞}
    {f : ι → α → F} {g : α → F}
    (hf : ∀ᶠ n in l, AEStronglyMeasurable (f n) m)
    {bound : α → G} (hb : MemLp bound q m)
    (hbound : ∀ᶠ n in l, ∀ᵐ x ∂m, ‖f n x‖ₑ ≤ ‖bound x‖ₑ)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    MemLp g q m := by
  obtain ⟨u, hu, huf⟩ := exists_seq_forall_of_frequently (hf.and hbound).frequently
  have hlim' : ∀ᵐ x ∂m, Tendsto (fun k => f (u k) x) atTop (𝓝 (g x)) :=
    hlim.mono fun x hx => hx.comp hu
  have hg_le : ∀ᵐ x ∂m, ‖g x‖ₑ ≤ ‖bound x‖ₑ := by
    filter_upwards [hlim', ae_all_iff.2 fun k => (huf k).2] with x hx hbx
    exact le_of_tendsto' ((continuous_eNorm.tendsto (g x)).comp hx) hbx
  exact hb.of_le_eNorm
    (aestronglyMeasurable_of_tendsto_ae atTop (fun k => (huf k).1) hlim') hg_le

/-- **Dominated convergence in `Lp`.** For `1 ≤ q < ∞`, if `MemLp` functions `f n` converge almost
everywhere along a countably generated filter `l` to a `MemLp` function `g` and have enorms
eventually dominated almost everywhere by a fixed `MemLp` function `bound`, then
`(hf n).toLp (f n)` converges to `hg.toLp g` in `Lp F q m`. -/
theorem tendsto_toLp_of_ae_tendsto {α ι F G : Type*} [MeasurableSpace α]
    {m : Measure α} [NormedAddCommGroup F]
    [TopologicalSpace G] [ENorm G]
    {l : Filter ι} [l.IsCountablyGenerated] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞)
    {f : ι → α → F} {g : α → F}
    (hf : ∀ n, MemLp (f n) q m) (hg : MemLp g q m)
    {bound : α → G} (hb : MemLp bound q m)
    (hbound : ∀ᶠ n in l, ∀ᵐ x ∂m, ‖f n x‖ₑ ≤ ‖bound x‖ₑ)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  obtain ⟨u, hu, hub⟩ := exists_seq_forall_of_frequently hbound.frequently
  have hg_le : ∀ᵐ x ∂m, ‖g x‖ₑ ≤ ‖bound x‖ₑ := by
    filter_upwards [hlim, ae_all_iff.2 hub] with x hx hbx
    exact le_of_tendsto' (hx.comp hu).eNorm hbx
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg]
  refine tendsto_eLpNorm_sub_of_ae_tendsto hq
    (.of_forall fun n => (hf n).aestronglyMeasurable) hb (C := 2) ?_ hlim
  filter_upwards [hbound] with n hn
  filter_upwards [hn, hg_le] with x hnx hgx
  calc ‖f n x - g x‖ₑ ≤ ‖f n x‖ₑ + ‖g x‖ₑ := eNorm_sub_le
    _ ≤ ‖bound x‖ₑ + ‖bound x‖ₑ := add_le_add hnx hgx
    _ = ((2 : ℝ≥0) : ℝ≥0∞) * ‖bound x‖ₑ := by rw [ENNReal.coe_ofNat, two_mul]

/-- **Dominated convergence in `Lp`.** For a finite exponent `p ≥ 1`, if `uₙ → u` almost
everywhere with `‖uₙ‖ ≤ ‖u‖` almost everywhere, and `v ∈ Lp` is a representative of `u`, then the
`Lp` classes of the `uₙ` converge to `v`. -/
theorem tendsto_toLp_of_ae_tendsto_of_norm_le {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {l : Filter ι} [l.IsCountablyGenerated] {us : ι → α → E} (hus : ∀ n, MemLp (us n) p μ)
    {v : Lp E p μ} {u : α → E} (hv : v =ᵐ[μ] u) (hle : ∀ n, ∀ᵐ x ∂μ, ‖us n x‖ ≤ ‖u x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => us n x) l (𝓝 (u x))) :
    Tendsto (fun n => (hus n).toLp (us n)) l (𝓝 v) := by
  have hu : MemLp u p μ := (Lp.memLp v).ae_eq hv
  have hvu : hu.toLp u = v := Lp.ext (hu.coeFn_toLp.trans hv.symm)
  rw [← hvu]
  exact tendsto_toLp_of_ae_tendsto hp hus hu hu
    (.of_forall fun n => (hle n).mono fun x hx => eNorm_le_iff_norm_le.2 hx) hlim

/-- For a finite exponent `q`, the `Lᵖ` norm of a function on the unit interval `(t, t + 1)`
tends to zero as `t` tends to infinity in either direction. -/
theorem tendsto_eLpNorm_restrict_Ioo {F : Type*} [NormedAddCommGroup F] {μ : Measure ℝ}
    {q : ℝ≥0∞} (hq : q ≠ ∞) {g : ℝ → F} (hg : MemLp g q μ) :
    Tendsto (fun t ↦ eLpNorm g q (μ.restrict (Set.Ioo t (t + 1)))) (cocompact ℝ) (𝓝 0) := by
  have : (cocompact ℝ).IsCountablyGenerated := by
    rw [cocompact_eq_atBot_atTop]
    infer_instance
  -- Every point `x` leaves `(t, t + 1)` once `t ∉ [x - 1, x]`.
  have hout (x : ℝ) : ∀ᶠ t in cocompact ℝ, x ∉ Set.Ioo t (t + 1) :=
    Filter.mem_of_superset (isCompact_Icc (a := x - 1) (b := x)).compl_mem_cocompact
      fun t ht hx ↦ ht ⟨by linarith [hx.2], hx.1.le⟩
  have h := tendsto_eLpNorm_sub_of_ae_tendsto (m := μ) (l := cocompact ℝ) (C := 1) hq
    (f := fun t ↦ (Set.Ioo t (t + 1)).indicator g) (g := 0)
    (Eventually.of_forall fun t ↦ hg.aestronglyMeasurable.indicator measurableSet_Ioo)
    hg
    (Eventually.of_forall fun t ↦ Eventually.of_forall fun x ↦ by
      rw [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul]
      exact eNorm_indicator_le_eNorm_self _ x)
    (Eventually.of_forall fun x ↦ tendsto_const_nhds.congr' <|
      (hout x).mono fun t ht ↦ (Set.indicator_of_notMem ht g).symm)
  simpa only [sub_zero,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet] using h

/-- For a finite exponent `q` and a measure vanishing on points, the `Lᵖ` norm of a function on the
closed ball of radius `r` about a point tends to zero as `r → 0`: off the centre, a point leaves
the ball once `r` is below its distance to the centre, so the cut-off functions tend to zero
almost everywhere, dominated by the function itself. -/
theorem tendsto_eLpNorm_restrict_closedBall {α F : Type*} [MetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [NullSingletonClass μ] [NormedAddCommGroup F]
    {q : ℝ≥0∞} (hq : q ≠ ∞) {g : α → F} (hg : MemLp g q μ) (x : α) :
    Tendsto (fun r ↦ eLpNorm g q (μ.restrict (Metric.closedBall x r))) (𝓝 0) (𝓝 0) := by
  -- almost every point differs from the centre, and leaves the shrinking balls
  have hne : ∀ᵐ y ∂μ, y ≠ x := by
    rw [ae_iff]
    simp
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun r ↦ (Metric.closedBall x r).indicator g y) (𝓝 0)
      (𝓝 ((0 : α → F) y)) := by
    filter_upwards [hne] with y hy
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [gt_mem_nhds (dist_pos.2 hy)] with r hr
    rw [Set.indicator_of_notMem fun h ↦ not_le.2 hr (Metric.mem_closedBall.1 h), Pi.zero_apply]
  have h := tendsto_eLpNorm_sub_of_ae_tendsto (m := μ) (l := 𝓝 (0 : ℝ)) (C := 1) hq
    (f := fun r ↦ (Metric.closedBall x r).indicator g) (g := 0)
    (Eventually.of_forall fun r ↦
      hg.aestronglyMeasurable.indicator Metric.isClosed_closedBall.measurableSet)
    hg
    (Eventually.of_forall fun r ↦ Eventually.of_forall fun y ↦ by
      rw [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul]
      exact eNorm_indicator_le_eNorm_self _ y)
    hlim
  simpa only [sub_zero, eLpNorm_indicator_eq_eLpNorm_restrict
    Metric.isClosed_closedBall.measurableSet.nullMeasurableSet] using h

/-- **The reverse Fatou lemma for `Lᵖ` seminorms over sets.** Let `0 < p < ∞`, let the sets `s n`
be measurable and contained in `t`, and let `g ∈ Lᵖ(t)`. Then the limit superior of the `Lᵖ`
seminorms of `g` over `s n` is at most its `Lᵖ` seminorm over `limsup s n`. -/
theorem limsup_eLpNorm_restrict_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {g : α → E} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) {s : ℕ → Set α}
    {t : Set α} (hg : MemLp g p (μ.restrict t))
    (hs : ∀ n, MeasurableSet (s n)) (hst : ∀ n, s n ⊆ t) :
    limsup (fun n ↦ eLpNorm g p (μ.restrict (s n))) atTop ≤
      eLpNorm g p (μ.restrict (limsup s atTop)) := by
  have hlim : limsup s atTop ⊆ t := fun x hx ↦
    (Filter.mem_limsup_iff_frequently_mem.1 hx).exists.elim fun n hn ↦ hst n hn
  have heq {u : Set α} (hu : u ⊆ t) : eLpNorm g p (μ.restrict u) =
      (∫⁻ x in u, ‖g x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop (hg.aestronglyMeasurable.mono_set hu)
  simp_rw [heq (hst _), heq hlim]
  have hpos : 0 ≤ 1 / p.toReal := by positivity
  have hmap := (ENNReal.monotone_rpow_of_nonneg hpos).map_limsup_of_continuousAt (F := atTop)
    (fun n ↦ ∫⁻ x in s n, ‖g x‖ₑ ^ p.toReal ∂μ) ENNReal.continuous_rpow_const.continuousAt
  rw [Function.comp_def] at hmap
  rw [← hmap]
  exact ENNReal.rpow_le_rpow (limsup_setLIntegral_le (hg.aestronglyMeasurable.eNorm.pow_const _)
    hs hst (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hptop hg.eLpNorm_lt_top).ne) hpos

end TauCeti
