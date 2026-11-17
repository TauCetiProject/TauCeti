/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Normed.Group.UniformContinuity

/-!
# Subsequence upgrade for partition functionals of continuous processes

Many partition limits in stochastic calculus reduce pathwise to deterministic oscillation estimates
once one fixes an almost-everywhere convergent subsequence of an auxiliary functional (such as an
unweighted quadratic sum) and invokes sample-path continuity on a compact set `s` to obtain:

1. a pathwise compact range `[L, R]` containing `X t ω` for all `t ∈ s`, and
2. a vanishing uniform bound `d j → 0` on a finite family of path increments along the subsequence.

`TauCeti.Probability.tendstoInMeasure_of_tendsto_of_continuousOn` packages this Riesz subsequence
extraction, Heine–Cantor uniform continuity, and compact image boundedness into a single principle
yielding `MeasureTheory.TendstoInMeasure` on any finite measure space, with no adaptedness,
martingale, or moment assumption on the process `X`.
`TauCeti.Probability.tendstoInMeasure_of_tendsto_of_continuousOn_range` specializes this principle
to `ℕ`-indexed grids `π n 0, …, π n (k n)` indexed over `Finset.range (k n)`.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter II, §6 and Chapter V, §5.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

/-- Upgrade a pathwise partition limit along subsequences to convergence in measure on a finite
measure space: given a process `X` almost surely continuous on a compact set `s`, finite families
of endpoint pairs `(u n i, v n i)` in `s` with uniformly vanishing distances, and an auxiliary
sequence `Q` converging in measure to `V`, any `AEStronglyMeasurable` sequence `F` that converges
pathwise to `g` whenever `X · ω` is bounded on `s`, the increments `|X (v ·) ω - X (u ·) ω|` are
uniformly bounded by a sequence `d → 0`, and `Q · ω → V ω` also converges to `g` in measure. -/
theorem tendstoInMeasure_of_tendsto_of_continuousOn
    {Ω T E G : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    [PseudoMetricSpace T] [PseudoEMetricSpace E] [PseudoEMetricSpace G]
    {X : T → Ω → ℝ} {s : Set T} (hs : IsCompact s)
    {ι : ℕ → Type*} [∀ n, Finite (ι n)]
    {u v : ∀ n, ι n → T} (hu : ∀ n i, u n i ∈ s) (hv : ∀ n i, v n i ∈ s)
    {δ : ℕ → ℝ} (hmesh : ∀ n i, dist (v n i) (u n i) ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {Q : ℕ → Ω → G} {V : Ω → G} (hV : TendstoInMeasure P Q atTop V)
    {F : ℕ → Ω → E} {g : Ω → E} (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hlim : ∀ (ω : Ω) (idx : ℕ → ℕ) (L R : ℝ) (d : ℕ → ℝ),
      (∀ t ∈ s, X t ω ∈ Icc L R) →
      (∀ j i, |X (v (idx j) i) ω - X (u (idx j) i) ω| ≤ d j) →
      Tendsto d atTop (𝓝 0) →
      Tendsto (fun j ↦ Q (idx j) ω) atTop (𝓝 (V ω)) →
      Tendsto (fun j ↦ F (idx j) ω) atTop (𝓝 (g ω))) :
    TendstoInMeasure P F atTop g := by
  have _ (n : ℕ) : Fintype (ι n) := Fintype.ofFinite (ι n)
  apply (exists_seq_tendstoInMeasure_atTop_iff hF).2
  intro ns hns
  obtain ⟨ms, hms, hQ⟩ := (hV.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hc, hQ] with ω hcω hQω
  let idx := fun j ↦ ns (ms j)
  have hidx : Tendsto idx atTop atTop := hns.tendsto_atTop.comp hms.tendsto_atTop
  obtain ⟨L, hL⟩ := (hs.image_of_continuousOn hcω).bddBelow
  obtain ⟨R, hR⟩ := (hs.image_of_continuousOn hcω).bddAbove
  let e := fun n ↦ Fintype.equivFin (ι n)
  let d := fun j ↦ ‖fun m : Fin (Fintype.card (ι (idx j))) ↦
    X (v (idx j) ((e (idx j)).symm m)) ω - X (u (idx j) ((e (idx j)).symm m)) ω‖
  have hd : Tendsto d atTop (𝓝 0) :=
    (hs.uniformContinuousOn_of_continuous hcω).tendsto_norm_sub_of_dist_le
      (Eventually.of_forall fun j _ ↦ hu (idx j) _)
      (Eventually.of_forall fun j _ ↦ hv (idx j) _)
      (Eventually.of_forall fun j _ ↦ hmesh (idx j) _)
      (hδ.comp hidx)
  refine hlim ω idx L R d
    (fun t ht ↦ ⟨hL ⟨t, ht, rfl⟩, hR ⟨t, ht, rfl⟩⟩)
    (fun j i ↦ ?_) hd
    (by simpa only [Function.comp_apply, idx] using hQω)
  have hnorm := norm_le_pi_norm (fun m : Fin (Fintype.card (ι (idx j))) ↦
    X (v (idx j) ((e (idx j)).symm m)) ω - X (u (idx j) ((e (idx j)).symm m)) ω) (e (idx j) i)
  simpa only [Real.norm_eq_abs, (e (idx j)).symm_apply_apply] using hnorm

/-- Specialization of `tendstoInMeasure_of_tendsto_of_continuousOn` to `ℕ`-indexed grids
`π n 0, π n 1, …, π n (k n)` in `s`: provides the compact range bound on `s` and the vanishing
increment bound `|X (π (idx j) (i + 1)) ω - X (π (idx j) i) ω| ≤ d j` for all `i < k (idx j)`. -/
theorem tendstoInMeasure_of_tendsto_of_continuousOn_range
    {Ω T E G : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    [PseudoMetricSpace T] [PseudoEMetricSpace E] [PseudoEMetricSpace G]
    {X : T → Ω → ℝ} {s : Set T} (hs : IsCompact s)
    {k : ℕ → ℕ} {π : ℕ → ℕ → T} (hmem : ∀ n, ∀ i ≤ k n, π n i ∈ s)
    {δ : ℕ → ℝ} (hmesh : ∀ n, ∀ i < k n, dist (π n (i + 1)) (π n i) ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {Q : ℕ → Ω → G} {V : Ω → G} (hV : TendstoInMeasure P Q atTop V)
    {F : ℕ → Ω → E} {g : Ω → E} (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hlim : ∀ (ω : Ω) (idx : ℕ → ℕ) (L R : ℝ) (d : ℕ → ℝ),
      (∀ t ∈ s, X t ω ∈ Icc L R) →
      (∀ j, ∀ i < k (idx j), |X (π (idx j) (i + 1)) ω - X (π (idx j) i) ω| ≤ d j) →
      Tendsto d atTop (𝓝 0) →
      Tendsto (fun j ↦ Q (idx j) ω) atTop (𝓝 (V ω)) →
      Tendsto (fun j ↦ F (idx j) ω) atTop (𝓝 (g ω))) :
    TendstoInMeasure P F atTop g :=
  tendstoInMeasure_of_tendsto_of_continuousOn hs
    (ι := fun n ↦ Fin (k n))
    (u := fun n i ↦ π n i) (v := fun n i ↦ π n ((i : ℕ) + 1))
    (fun n i ↦ hmem n i i.isLt.le) (fun n i ↦ hmem n ((i : ℕ) + 1) i.isLt)
    (fun n i ↦ hmesh n i i.isLt) hδ hc hV hF
    fun ω idx L R d hLR hd_le hd hQ ↦
      hlim ω idx L R d hLR (fun j i hi ↦ hd_le j ⟨i, hi⟩) hd hQ

end TauCeti.Probability
