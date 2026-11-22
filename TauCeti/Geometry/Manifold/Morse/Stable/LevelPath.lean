/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Compactification
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Trapping
public import TauCeti.Topology.Closure
public import TauCeti.Topology.PathSpace.Moore
import TauCeti.Data.Fin.Basic
import TauCeti.Dynamics.Flow.LevelCrossing
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Topology.Order.OrderClosed

/-!
# Broken trajectories parametrized by the values of `f`

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f`, and `p`, `r` critical points. A broken trajectory from `p` to `r` is a chain of
critical points `p = x 0, …, x k = r` with a trajectory from each `x j` to `x (j + 1)`. The values
of `f` decrease strictly along it, so it meets every level `a` between `f r` and `f p` in exactly
one point: the critical point `x j` if `a = f (x j)`, and otherwise a point of the unique
trajectory of the chain crossing the level `a`. Parametrizing a broken trajectory by the values of
`f` makes it a path from `p` to `r`, and concatenating broken trajectories concatenates these
paths.

Broken trajectories are recorded by their points `w i` on levels `c i`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`); under the Morse–Smale condition
the records of broken trajectories form the compactified space of trajectories from `p` to `r`, the
closure of the records of unbroken ones
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords`). When the levels
are dense in the interval between `f r` and `f p`, the record of a broken trajectory determines its
point on every level `a` (`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint`), and the main result of
this file is that this point depends **continuously on the record and the level together**
(`TauCeti.IsAdaptedPseudoGradient.continuousOn_morseLevelPoint`). So the records carry a continuous
evaluation into the Moore paths from `p` to `r` (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath`):
the point at time `t` of the path of a broken trajectory is its point on the level `f p - t`, and
the path has length `f p - f r`.

For levels `c i` that avoid the level of a critical point `q`, a record of a broken trajectory from
`p` to `q` and one from `q` to `r` concatenate to a record of a broken trajectory from `p` to `r`
(`TauCeti.concatLevelRecords`, `TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`), and when the
levels are dense the Moore path of the concatenation is the concatenation of the Moore paths
(`TauCeti.IsAdaptedPseudoGradient.morseLevelPath_morseRecordsConcat`). These are the evaluation
into Moore paths and the composition maps of the compactified trajectory spaces through which
twisting chain systems give the Barraud–Cornea twisting cocycle
(`TauCeti.TwistingChainSystem.mooreTwistingCocycle`).

The continuity is a consequence of two local estimates for the flow
(`TauCeti.Geometry.Manifold.Morse.PseudoGradient.Trapping`). Let records `w n` of broken
trajectories converge to `w`, and levels `a n` to `a`.

* If the point of `w` on the level `a` is a regular point `m`, take a level `c i` slightly above
  `a` at which `w` is close to `m`. For large `n`, the point of `w n` on `c i` is close to `m`, and
  the point of `w n` on `a n` is reached from it by losing a little height. An orbit starting close
  to the regular point `m` and losing little height stays close to `m`; in particular it cannot
  converge to a critical point, so the broken trajectory `w n` does not break between the two
  levels.
* If the point of `w` on the level `a` is a critical point `q`, the same argument applies from a
  level slightly above `a` to the points of `w n` above the level of `q`, using that an orbit
  starting close to `q` stays close to `q` as long as it is above the level of `q`. Should `w n`
  break between the two levels, at a critical point close to `q`, that critical point is `q`
  itself. The points below the level of `q` are treated backwards in time from a level slightly
  below `a`.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseLevelPoint`: the point on a level of the broken trajectory
  recorded by `w`.
* `TauCeti.IsAdaptedPseudoGradient.morseLevelPath`: the Moore path from `p` to `r` of a record of a
  broken trajectory, its points on the successive levels.
* `TauCeti.concatLevelRecords`: the concatenation of records above and below the level of `q`.
* `TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`: concatenation of records of broken
  trajectories, as a continuous map.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseLevelPoint_eq`: the point on the level `a` is the point of any broken trajectory recorded
  by `w` on that level.
* `apply_morseLevelPoint`, `morseLevelPoint_apply_level`: it lies on the level `a`, and on the
  recorded levels it is the recorded point.
* `continuousOn_morseLevelPoint`: it depends continuously on the record and the level.
* `morseLevelPath_apply`, `length_morseLevelPath`, `source_morseLevelPath`,
  `target_morseLevelPath`: the Moore path of a record.
* `concatLevelRecords_mem`: concatenating records of broken trajectories gives a record of a broken
  trajectory.
* `morseLevelPoint_concatLevelRecords_of_le`, `morseLevelPoint_concatLevelRecords_of_ge`: its points
  are those of the first broken trajectory above the level of `q`, and of the second below.
* `morseLevelPath_morseRecordsConcat`: the Moore path of a concatenation is the concatenation of
  the Moore paths.
* `TauCeti.concatLevelRecords_assoc`: concatenation of records is associative.
* `concatLevelRecords_notMem_morseTrajectoryRecords`: a concatenation at `q ≠ r` is not the record
  of an unbroken trajectory when some level lies between `f q` and `f p`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2, where broken trajectories parametrized by the values of `f` are
  evaluated into Moore paths.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-! ### Points of a chain -/

section Chain

variable {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}

/-- `m` lies on the broken trajectory through the chain `x` made of the orbits of the points
`z j`. -/
private def OnChain (x : Fin (k + 1) → M) (z : Fin k → M) (m : M) : Prop :=
  (∃ l, x l = m) ∨ ∃ j t, hX.flow t (z j) = m

variable {hX}
variable (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
  (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
include hxne hz

/-- The orbit of `z j` lies strictly between the levels of `x (j + 1)` and `x j`. -/
private theorem apply_flow_mem_Ioo (j : Fin k) (t : ℝ) :
    f (hX.flow t (z j)) ∈ Ioo (f (x j.succ)) (f (x j.castSucc)) :=
  hX.mem_Ioo_of_mem_unstableSet_inter_stableSet (hxne j)
    (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t (hz j))

omit hxne in
/-- The level of a point of the chain is not strictly between the levels of the two ends of a
step. -/
private theorem apply_notMem_Ioo (l : Fin (k + 1)) (j : Fin k) :
    f (x l) ∉ Ioo (f (x j.succ)) (f (x j.castSucc)) := fun ⟨h₁, h₂⟩ ↦ by
  have hanti := hX.antitone_apply_of_chain hz
  rcases le_or_gt l j.castSucc with h | h
  · exact (hanti h).not_gt h₂
  · exact (hanti (Fin.castSucc_lt_iff_succ_le.1 h)).not_gt h₁

/-- The level of a point of a broken trajectory lies between the levels of its ends. -/
private theorem apply_mem_Icc_of_onChain {m : M} (hm : hX.OnChain x z m) :
    f m ∈ Icc (f (x (Fin.last k))) (f (x 0)) := by
  have hanti := hX.antitone_apply_of_chain hz
  rcases hm with ⟨l, rfl⟩ | ⟨j, t, rfl⟩
  · exact ⟨hanti (Fin.le_last l), hanti (Fin.zero_le l)⟩
  · have h := apply_flow_mem_Ioo hxne hz j t
    exact ⟨(hanti (Fin.le_last _)).trans h.1.le, h.2.le.trans (hanti (Fin.zero_le _))⟩

/-- **A broken trajectory meets each level at most once.** -/
private theorem eq_of_onChain {m m' : M} (hm : hX.OnChain x z m) (hm' : hX.OnChain x z m')
    (h : f m = f m') : m = m' := by
  rcases hm with ⟨l, rfl⟩ | ⟨j, t, rfl⟩ <;> rcases hm' with ⟨l', rfl⟩ | ⟨j', t', rfl⟩
  · rw [(hX.strictAnti_apply_of_chain hxne hz).injective h]
  · exact absurd (h ▸ apply_flow_mem_Ioo hxne hz j' t') (apply_notMem_Ioo hz l j')
  · exact absurd (h ▸ apply_flow_mem_Ioo hxne hz j t) (apply_notMem_Ioo hz l' j)
  · obtain rfl : j = j' := (hX.antitone_apply_of_chain hz).eq_of_mem_Ioo_of_mem_Icc_fin
      (apply_flow_mem_Ioo hxne hz j t) (h ▸ Ioo_subset_Icc_self (apply_flow_mem_Ioo hxne hz j' t'))
    rw [(hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)).injective h]

omit hxne in
/-- **A broken trajectory meets each level between its ends.** -/
private theorem exists_onChain {a : ℝ} (ha : a ∈ Icc (f (x (Fin.last k))) (f (x 0))) :
    ∃ m, hX.OnChain x z m ∧ f m = a := by
  by_cases hcrit : ∃ l, f (x l) = a
  · obtain ⟨l, hl⟩ := hcrit
    exact ⟨x l, Or.inl ⟨l, rfl⟩, hl⟩
  push Not at hcrit
  obtain ⟨j, hj₁, hj₂⟩ := Fin.exists_succ_lt_lt_castSucc (g := fun l ↦ f (x l)) hcrit
    (lt_of_le_of_ne ha.2 (hcrit 0).symm) (lt_of_le_of_ne ha.1 (hcrit _))
  have hfc := hX.mdifferentiable.continuous
  obtain ⟨t, ht⟩ := Flow.exists_apply_flow_eq_of_mem_unstableSet_inter_stableSet
    (hfc.comp (hX.flow.continuous continuous_id continuous_const)) hfc.continuousAt
    hfc.continuousAt (hz j) ⟨hj₁, hj₂⟩
  exact ⟨_, Or.inr ⟨j, t, rfl⟩, ht⟩

/-- **Going down a broken trajectory.** A point `m` of a broken trajectory below a point `u` of the
orbit of `z j` is either on the forward orbit of `u`, or at most at the level of the end
`x (j + 1)` of that orbit. -/
private theorem onChain_forward {j : Fin k} {s : ℝ} {m : M} (hm : hX.OnChain x z m)
    (hlt : f m < f (hX.flow s (z j))) :
    (∃ t, 0 ≤ t ∧ hX.flow t (hX.flow s (z j)) = m) ∨ f m ≤ f (x j.succ) := by
  have hanti := hX.antitone_apply_of_chain hz
  have hu := apply_flow_mem_Ioo hxne hz j s
  rcases hm with ⟨l, rfl⟩ | ⟨j', t', rfl⟩
  · refine Or.inr (hanti ?_)
    by_contra! h
    exact (hlt.trans hu.2).not_ge (hanti (Fin.le_castSucc_iff.2 h))
  · have hm := apply_flow_mem_Ioo hxne hz j' t'
    rcases lt_trichotomy j' j with h | rfl | h
    · exact absurd (hm.1.trans_le' (hanti (Fin.succ_le_castSucc_iff.2 h))) (hlt.trans hu.2).not_gt
    · refine Or.inl ⟨t' - s, ?_, by rw [← Flow.map_add, sub_add_cancel]⟩
      have := (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet (hxne j') (hz j')).lt_iff_gt.1
        hlt
      linarith
    · exact Or.inr (hm.2.le.trans (hanti (Fin.succ_le_castSucc_iff.2 h)))

/-- **Going up a broken trajectory.** A point `m` of a broken trajectory above a point `u` of the
orbit of `z j` is either on the backward orbit of `u`, or at least at the level of the start `x j`
of that orbit. -/
private theorem onChain_backward {j : Fin k} {s : ℝ} {m : M} (hm : hX.OnChain x z m)
    (hgt : f (hX.flow s (z j)) < f m) :
    (∃ t, 0 ≤ t ∧ hX.flow (-t) (hX.flow s (z j)) = m) ∨ f (x j.castSucc) ≤ f m := by
  have hanti := hX.antitone_apply_of_chain hz
  have hu := apply_flow_mem_Ioo hxne hz j s
  rcases hm with ⟨l, rfl⟩ | ⟨j', t', rfl⟩
  · refine Or.inr (hanti ?_)
    by_contra! h
    exact (hu.1.trans hgt).not_ge (hanti (Fin.castSucc_lt_iff_succ_le.1 h))
  · have hm := apply_flow_mem_Ioo hxne hz j' t'
    rcases lt_trichotomy j' j with h | rfl | h
    · exact Or.inr ((hanti (Fin.succ_le_castSucc_iff.2 h)).trans hm.1.le)
    · refine Or.inl ⟨s - t', ?_, by rw [← Flow.map_add, neg_sub, sub_add_cancel]⟩
      have := (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet (hxne j') (hz j')).lt_iff_gt.1
        hgt
      linarith
    · exact absurd (hm.2.trans_le (hanti (Fin.succ_le_castSucc_iff.2 h))) (hu.1.trans hgt).not_gt

end Chain

/-! ### Records near a point of a broken trajectory -/

section Records

variable {hX} {p r : M} {c : ι → ℝ} {w : ι → M} {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}
  (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
  (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
  (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i)
include hxne hz hw

/-- If the orbit of `z j` stays in `V` for times in `[t₁, t₂]`, then so do the recorded points on
the levels it crosses during that time. -/
private theorem apply_mem_of_mem_Icc {j : Fin k} {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) {V : Set M}
    (hV : ∀ s ∈ Icc t₁ t₂, hX.flow s (z j) ∈ V) {i : ι}
    (hi : c i ∈ Icc (f (hX.flow t₂ (z j))) (f (hX.flow t₁ (z j)))) : w i ∈ V := by
  have hg : Continuous fun t ↦ f (hX.flow t (z j)) :=
    hX.mdifferentiable.continuous.comp (hX.flow.continuous continuous_id continuous_const)
  obtain ⟨s, hs, hsi⟩ := intermediate_value_Icc' ht hg.continuousOn hi
  obtain ⟨hwc, hwz⟩ := hw i
  rw [eq_of_onChain hxne hz (m := w i) (m' := hX.flow s (z j)) (Or.inr hwz) (Or.inr ⟨j, s, rfl⟩)
    (hwc.trans hsi.symm)]
  exact hV s hs

omit hw in
private theorem apply_flow_mem_Ioo_ends (hx0 : x 0 = p) (hxk : x (Fin.last k) = r) (j : Fin k)
    (t : ℝ) : f (hX.flow t (z j)) ∈ Ioo (f r) (f p) := by
  have hanti := hX.antitone_apply_of_chain hz
  have h := apply_flow_mem_Ioo hxne hz j t
  rw [← hx0, ← hxk]
  exact ⟨(hanti (Fin.le_last _)).trans_lt h.1, h.2.trans_le (hanti (Fin.zero_le _))⟩

/-- **Records just above a point of a trajectory of the chain are close to it.** -/
private theorem exists_lt_apply_mem_of_flow (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hx0 : x 0 = p) (hxk : x (Fin.last k) = r) {j : Fin k} {t₀ : ℝ} {V : Set M}
    (hV : V ∈ 𝓝 (hX.flow t₀ (z j))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, c i ∈ Ioo (f (hX.flow t₀ (z j))) (f (hX.flow t₀ (z j)) + δ) ∧ w i ∈ V := by
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1
    ((hX.flow.continuous continuous_id continuous_const).continuousAt.preimage_mem_nhds hV)
  set g := fun t ↦ f (hX.flow t (z j))
  have hlt : g t₀ < g (t₀ - η / 2) := hanti (by linarith)
  obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range
    (lt_min hlt (lt_add_of_pos_right _ hδ))
    fun b hb ↦ hdense ⟨(apply_flow_mem_Ioo_ends hxne hz hx0 hxk j t₀).1.trans hb.1,
      hb.2.trans_le ((min_le_left _ _).trans (apply_flow_mem_Ioo_ends hxne hz hx0 hxk j _).2.le)⟩
  refine ⟨i, ⟨hi.1, hi.2.trans_le (min_le_right _ _)⟩,
    apply_mem_of_mem_Icc hxne hz hw (by linarith : t₀ - η / 2 ≤ t₀) (fun s hs ↦ hηV ?_)
      ⟨hi.1.le, (hi.2.trans_le (min_le_left _ _)).le⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

/-- **Records just above a critical point of the chain are close to it.** -/
private theorem exists_lt_apply_mem_of_succ (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hx0 : x 0 = p) (hxk : x (Fin.last k) = r) {j : Fin k} {V : Set M} (hV : V ∈ 𝓝 (x j.succ))
    {δ : ℝ} (hδ : 0 < δ) : ∃ i, c i ∈ Ioo (f (x j.succ)) (f (x j.succ) + δ) ∧ w i ∈ V := by
  have hlim := Flow.mem_stableSet.1 (hz j).2
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hlim.eventually_mem hV)
  set g := fun t ↦ f (hX.flow t (z j))
  have hT₀l := apply_flow_mem_Ioo hxne hz j T₀
  have hanti := hX.antitone_apply_of_chain hz
  obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range
    (lt_min hT₀l.1 (lt_add_of_pos_right _ hδ))
    fun b hb ↦ hdense ⟨by rw [← hxk]; exact (hanti (Fin.le_last _)).trans_lt hb.1,
      hb.2.trans_le ((min_le_left _ _).trans (apply_flow_mem_Ioo_ends hxne hz hx0 hxk j _).2.le)⟩
  have hglim : Tendsto g atTop (𝓝 (f (x j.succ))) :=
    (hX.mdifferentiable.continuous.tendsto _).comp hlim
  obtain ⟨T₁, hT₁, hT₀₁⟩ := ((hglim.eventually (gt_mem_nhds hi.1)).and
    (eventually_ge_atTop T₀)).exists
  exact ⟨i, ⟨hi.1, hi.2.trans_le (min_le_right _ _)⟩,
    apply_mem_of_mem_Icc hxne hz hw hT₀₁ (fun s hs ↦ hT₀ s hs.1)
      ⟨hT₁.le, (hi.2.trans_le (min_le_left _ _)).le⟩⟩

/-- **Records just below a critical point of the chain are close to it.** -/
private theorem exists_apply_lt_mem_of_castSucc (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hx0 : x 0 = p) (hxk : x (Fin.last k) = r) {j : Fin k} {V : Set M}
    (hV : V ∈ 𝓝 (x j.castSucc)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, c i ∈ Ioo (f (x j.castSucc) - δ) (f (x j.castSucc)) ∧ w i ∈ V := by
  have hlim := Flow.mem_unstableSet.1 (hz j).1
  obtain ⟨T₀, hT₀⟩ := eventually_atBot.1 (hlim.eventually_mem hV)
  set g := fun t ↦ f (hX.flow t (z j))
  have hT₀l := apply_flow_mem_Ioo hxne hz j T₀
  have hanti := hX.antitone_apply_of_chain hz
  obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range
    (max_lt hT₀l.2 (sub_lt_self _ hδ))
    fun b hb ↦ hdense ⟨((apply_flow_mem_Ioo_ends hxne hz hx0 hxk j _).1.trans_le
      (le_max_left _ _)).trans hb.1, by rw [← hx0]; exact hb.2.trans_le (hanti (Fin.zero_le _))⟩
  have hglim : Tendsto g atBot (𝓝 (f (x j.castSucc))) :=
    (hX.mdifferentiable.continuous.tendsto _).comp hlim
  obtain ⟨T₁, hT₁, hT₀₁⟩ := ((hglim.eventually (lt_mem_nhds hi.2)).and
    (eventually_le_atBot T₀)).exists
  exact ⟨i, ⟨(le_max_right _ _).trans_lt hi.1, hi.2⟩,
    apply_mem_of_mem_Icc hxne hz hw hT₀₁ (fun s hs ↦ hT₀ s hs.2)
      ⟨((le_max_left _ _).trans_lt hi.1).le, hT₁.le⟩⟩

end Records

/-! ### Points on the levels of a recorded broken trajectory -/

section LevelPoint

variable {p r : M} {c : ι → ℝ}

/-- `m` is the point on the level `a` of a broken trajectory from `p` to `r` recorded by `w`. -/
private def IsLevelPoint (p r : M) (c : ι → ℝ) (w : ι → M) (a : ℝ) (m : M) : Prop :=
  ∃ (k : ℕ) (x : Fin (k + 1) → M) (z : Fin k → M), x 0 = p ∧ x (Fin.last k) = r ∧
    (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧ (∀ j : Fin k, x j.castSucc ≠ x j.succ) ∧
    (∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) ∧
    (∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i) ∧ hX.OnChain x z m ∧ f m = a

variable {hX} {w : ι → M} {a : ℝ} {m : M}

private theorem IsLevelPoint.mem_Icc (h : hX.IsLevelPoint p r c w a m) : a ∈ Icc (f r) (f p) := by
  obtain ⟨k, x, z, hx0, hxk, -, hxne, hz, -, hm, rfl⟩ := h
  rw [← hx0, ← hxk]
  exact apply_mem_Icc_of_onChain hxne hz hm

private theorem IsLevelPoint.eq_of_eq_top (h : hX.IsLevelPoint p r c w a m) (ha : a = f p) :
    m = p := by
  obtain ⟨k, x, z, hx0, -, -, hxne, hz, -, hm, rfl⟩ := h
  rw [← hx0] at ha ⊢
  exact eq_of_onChain hxne hz hm (Or.inl ⟨0, rfl⟩) ha

private theorem IsLevelPoint.eq_of_eq_bot (h : hX.IsLevelPoint p r c w a m) (ha : a = f r) :
    m = r := by
  obtain ⟨k, x, z, -, hxk, -, hxne, hz, -, hm, rfl⟩ := h
  rw [← hxk] at ha ⊢
  exact eq_of_onChain hxne hz hm (Or.inl ⟨_, rfl⟩) ha

/-- **The forward step of the continuity argument.** Let `m` be the point of a broken trajectory
on the level `a`, below a recorded level `c i`. If the forward orbit of the recorded point `w i`
lies in a closed set `U` as long as it stays above the level `a`, then either `m` lies in `U`, or
the broken trajectory breaks, between the two levels, at a critical point of `U` above `a`. -/
private theorem IsLevelPoint.mem_or_exists_of_lt (h : hX.IsLevelPoint p r c w a m) {i : ι}
    (hlt : a < c i) {U : Set M} (hU : IsClosed U)
    (hstep : ∀ t, 0 ≤ t → a ≤ f (hX.flow t (w i)) → hX.flow t (w i) ∈ U) :
    m ∈ U ∨ ∃ y ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧ a < f y := by
  obtain ⟨k, x, z, -, -, hxc, hxne, hz, hw, hm, rfl⟩ := h
  obtain ⟨hwc, j, s, hs⟩ := hw i
  rw [← hwc, ← hs] at hlt
  rw [← hs] at hstep
  rcases onChain_forward hxne hz hm hlt with ⟨t, ht, rfl⟩ | hle
  · exact Or.inl (hstep t ht le_rfl)
  -- The forward orbit converges to the end `x (j + 1)` of its trajectory, staying above its level.
  have hst := (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ s (hz j)).2
  have hyU : x j.succ ∈ U := hU.mem_of_tendsto (Flow.mem_stableSet.1 hst)
    (eventually_atTop.2 ⟨0, fun t ht ↦ hstep t ht (hle.trans
      (Flow.le_of_mem_stableSet_of_antitone (Flow.isInvariant_stableSet _ _ t hst)
        hX.mdifferentiable.continuous.continuousAt (hX.antitone_flow _)))⟩)
  by_cases heq : f m = f (x j.succ)
  · exact Or.inl (eq_of_onChain hxne hz hm (Or.inl ⟨_, rfl⟩) heq ▸ hyU)
  · exact Or.inr ⟨_, hyU, hxc _, lt_of_le_of_ne hle heq⟩

/-- **The backward step of the continuity argument.** Let `m` be the point of a broken trajectory
on the level `a`, above a recorded level `c i`. If the backward orbit of the recorded point `w i`
lies in a closed set `U` as long as it stays below the level `a`, then either `m` lies in `U`, or
the broken trajectory breaks, between the two levels, at a critical point of `U` below `a`. -/
private theorem IsLevelPoint.mem_or_exists_of_gt (h : hX.IsLevelPoint p r c w a m) {i : ι}
    (hgt : c i < a) {U : Set M} (hU : IsClosed U)
    (hstep : ∀ t, 0 ≤ t → f (hX.flow (-t) (w i)) ≤ a → hX.flow (-t) (w i) ∈ U) :
    m ∈ U ∨ ∃ y ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧ f y < a := by
  obtain ⟨k, x, z, -, -, hxc, hxne, hz, hw, hm, rfl⟩ := h
  obtain ⟨hwc, j, s, hs⟩ := hw i
  rw [← hwc, ← hs] at hgt
  rw [← hs] at hstep
  rcases onChain_backward hxne hz hm hgt with ⟨t, ht, rfl⟩ | hle
  · exact Or.inl (hstep t ht le_rfl)
  -- The backward orbit converges to the start `x j` of its trajectory, staying below its level.
  have hun := (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ s (hz j)).1
  have hyU : x j.castSucc ∈ U := hU.mem_of_tendsto
    ((Flow.mem_unstableSet.1 hun).comp tendsto_neg_atTop_atBot)
    (eventually_atTop.2 ⟨0, fun t ht ↦ hstep t ht
      ((Flow.le_of_mem_unstableSet_of_antitone (Flow.isInvariant_unstableSet _ _ (-t) hun)
        hX.mdifferentiable.continuous.continuousAt (hX.antitone_flow _)).trans hle)⟩)
  by_cases heq : f m = f (x j.castSucc)
  · exact Or.inl (eq_of_onChain hxne hz hm (Or.inl ⟨_, rfl⟩) heq ▸ hyU)
  · exact Or.inr ⟨_, hyU, hxc _, lt_of_le_of_ne hle (Ne.symm heq)⟩

section Continuity

variable {α : Type*} {l : Filter α} {w : α → ι → M} {w₀ : ι → M} (hw : Tendsto w l (𝓝 w₀))
  {a : α → ℝ} {m : α → M} {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M} (hx0 : x 0 = p)
  (hxk : x (Fin.last k) = r)
  (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
  (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
  (hw₀ : ∀ i, f (w₀ i) = c i ∧ ∃ j t, hX.flow t (z j) = w₀ i)
include hw hx0 hxk hxne hz hw₀

/-- **Continuity at a regular point, from above.** If records `w n` of broken trajectories
converge to a record `w₀` of a broken trajectory, and levels `a n` to the level of a regular point
`m₀` of that broken trajectory, then the points of `w n` on the levels `a n` converge to `m₀`. The
records are compared on a recorded level slightly above, where `w₀` is close to `m₀`. -/
private theorem tendsto_of_isLevelPoint_of_flow (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hm : ∀ᶠ n in l, hX.IsLevelPoint p r c (w n) (a n) (m n))
    (hf : IsMorse 𝓘(ℝ, E) f) {j : Fin k} {t₀ : ℝ}
    (ha : Tendsto a l (𝓝 (f (hX.flow t₀ (z j))))) : Tendsto m l (𝓝 (hX.flow t₀ (z j))) := by
  refine tendsto_def.2 fun U hU ↦ ?_
  -- Shrink `U` to a closed neighbourhood containing no critical point.
  have hreg := hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet (hxne j)
    (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t₀ (hz j))
  obtain ⟨U₁, ⟨hU₁, hU₁c⟩, hU₁U⟩ := (closed_nhds_basis _).mem_iff.1
    (inter_mem hU (hf.finite_setOf_mfderiv_eq_zero.isClosed.compl_mem_nhds hreg))
  obtain ⟨V, hV, ε, hε, hVU⟩ := hX.exists_mem_nhds_forall_flow_mem_of_sub_le hreg hU₁
  obtain ⟨i, hi, hwi⟩ := exists_lt_apply_mem_of_flow hxne hz hw₀ hdense hx0 hxk
    (interior_mem_nhds.2 hV) (half_pos hε)
  filter_upwards [hm, (tendsto_pi_nhds.1 hw i).eventually_mem (isOpen_interior.mem_nhds hwi),
    ha.eventually (gt_mem_nhds hi.1),
    ha.eventually (lt_mem_nhds (by linarith [hi.2] : c i - ε < f (hX.flow t₀ (z j))))]
    with n hn hni hnc hnε
  have hwc : f (w n i) = c i := by
    obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hn
    exact (hw' i).1
  rcases hn.mem_or_exists_of_lt hnc hU₁c
    (fun t ht hlev ↦ hVU _ (interior_subset hni) t ht (by rw [hwc]; linarith))
    with h | ⟨y, hy, hyc, -⟩
  · exact (hU₁U h).1
  · exact absurd hyc (hU₁U hy).2

variable {l₀ : Fin (k + 1)} {U : Set M} (hU : U ∈ 𝓝 (x l₀)) (hUc : IsClosed U)
  (honly : ∀ y ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = x l₀)
include hU hUc honly

/-- **Continuity at a critical point, from above.** If records `w n` of broken trajectories
converge to a record `w₀` of a broken trajectory through a critical point `x l₀`, and levels `a n`
to the level of `x l₀`, then the points of `w n` on the levels `a n` at least that of `x l₀` lie,
eventually, in a closed neighbourhood `U` of `x l₀` containing no other critical point. The records
are compared on a recorded level slightly above. -/
private theorem eventually_mem_of_isLevelPoint_of_le
    (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hm : ∀ᶠ n in l, hX.IsLevelPoint p r c (w n) (a n) (m n))
    (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) (ha : Tendsto a l (𝓝 (f (x l₀)))) :
    ∀ᶠ n in l, f (x l₀) ≤ a n → m n ∈ U := by
  obtain ⟨V, hV, hVU⟩ := hX.exists_mem_nhds_forall_flow_mem_of_le (hxc l₀) hU
  rcases Fin.eq_zero_or_eq_succ l₀ with rfl | ⟨j, rfl⟩
  · filter_upwards [hm] with n hn hle
    have hp : a n = f p := le_antisymm hn.mem_Icc.2 ((congrArg f hx0).symm.trans_le hle)
    rw [hn.eq_of_eq_top hp, ← hx0]
    exact mem_of_mem_nhds hU
  obtain ⟨i, hi, hwi⟩ := exists_lt_apply_mem_of_succ hxne hz hw₀ hdense hx0 hxk
    (interior_mem_nhds.2 hV) one_pos
  filter_upwards [hm, (tendsto_pi_nhds.1 hw i).eventually_mem (isOpen_interior.mem_nhds hwi),
    ha.eventually (gt_mem_nhds hi.1)] with n hn hni hnc hle
  rcases hn.mem_or_exists_of_lt hnc hUc
    (fun t ht hlev ↦ hVU _ (interior_subset hni) t ht (hle.trans hlev)) with h | ⟨y, hy, hyc, hlt⟩
  · exact h
  · exact absurd (honly y hy hyc ▸ hlt) hle.not_gt

/-- **Continuity at a critical point, from below.** If records `w n` of broken trajectories
converge to a record `w₀` of a broken trajectory through a critical point `x l₀`, and levels `a n`
to the level of `x l₀`, then the points of `w n` on the levels `a n` at most that of `x l₀` lie,
eventually, in a closed neighbourhood `U` of `x l₀` containing no other critical point. The records
are compared on a recorded level slightly below. -/
private theorem eventually_mem_of_isLevelPoint_of_ge
    (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hm : ∀ᶠ n in l, hX.IsLevelPoint p r c (w n) (a n) (m n)) (hf : IsMorse 𝓘(ℝ, E) f)
    (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) (ha : Tendsto a l (𝓝 (f (x l₀)))) :
    ∀ᶠ n in l, a n ≤ f (x l₀) → m n ∈ U := by
  obtain ⟨V, hV, hVU⟩ := hX.exists_mem_nhds_forall_flow_neg_mem_of_le hf (hxc l₀) hU
  rcases Fin.eq_castSucc_or_eq_last l₀ with ⟨j, rfl⟩ | rfl
  · obtain ⟨i, hi, hwi⟩ := exists_apply_lt_mem_of_castSucc hxne hz hw₀ hdense hx0 hxk
      (interior_mem_nhds.2 hV) one_pos
    filter_upwards [hm, (tendsto_pi_nhds.1 hw i).eventually_mem (isOpen_interior.mem_nhds hwi),
      ha.eventually (lt_mem_nhds hi.2)] with n hn hni hnc hle
    rcases hn.mem_or_exists_of_gt hnc hUc
      (fun t ht hlev ↦ hVU _ (interior_subset hni) t ht (hlev.trans hle)) with h | ⟨y, hy, hyc, hlt⟩
    · exact h
    · exact absurd (honly y hy hyc ▸ hlt) hle.not_gt
  · filter_upwards [hm] with n hn hle
    have hr : a n = f r := le_antisymm (hle.trans_eq (congrArg f hxk)) hn.mem_Icc.1
    rw [hn.eq_of_eq_bot hr, ← hxk]
    exact mem_of_mem_nhds hU

end Continuity

/-- **The points on the levels of recorded broken trajectories depend continuously on the record
and the level.** If records `w n` of broken trajectories converge to a record `w₀`, and levels
`a n` to `a₀`, then the points of `w n` on the levels `a n` converge to the point of `w₀` on the
level `a₀`. -/
private theorem tendsto_of_isLevelPoint (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) {α : Type*} {l : Filter α} {w : α → ι → M}
    {w₀ : ι → M} (hw : Tendsto w l (𝓝 w₀)) {a : α → ℝ} {a₀ : ℝ} (ha : Tendsto a l (𝓝 a₀))
    {m : α → M} (hm : ∀ᶠ n in l, hX.IsLevelPoint p r c (w n) (a n) (m n)) {m₀ : M}
    (hm₀ : hX.IsLevelPoint p r c w₀ a₀ m₀) : Tendsto m l (𝓝 m₀) := by
  obtain ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw₀, hm₀, rfl⟩ := hm₀
  rcases hm₀ with ⟨l₀, rfl⟩ | ⟨j, t₀, rfl⟩
  · -- At a critical point, shrink `U` to a closed neighbourhood containing no other critical
    -- point, and treat the levels above and below that of `x l₀` separately.
    refine tendsto_def.2 fun U hU ↦ ?_
    obtain ⟨U₁, ⟨hU₁, hU₁c⟩, hU₁U⟩ := (closed_nhds_basis (x l₀)).mem_iff.1 (inter_mem hU
      ((hf.finite_setOf_mfderiv_eq_zero.subset sdiff_subset).isClosed.compl_mem_nhds
        fun h ↦ h.2 (mem_singleton _)))
    have honly : ∀ y ∈ U₁, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = x l₀ := fun y hy hyc ↦
      by_contra fun hne ↦ (hU₁U hy).2 ⟨hyc, hne⟩
    filter_upwards [eventually_mem_of_isLevelPoint_of_le hw hx0 hxk hxne hz hw₀ hU₁ hU₁c honly
        hdense hm hxc ha,
      eventually_mem_of_isLevelPoint_of_ge hw hx0 hxk hxne hz hw₀ hU₁ hU₁c honly hdense hm hf hxc
        ha] with n h₁ h₂
    exact (hU₁U ((le_total (f (x l₀)) (a n)).elim h₁ h₂)).1
  · exact tendsto_of_isLevelPoint_of_flow hw hx0 hxk hxne hz hw₀ hdense hm hf ha

/-- The point on a level of a recorded broken trajectory is unique. -/
private theorem IsLevelPoint.unique (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) {m' : M} (h : hX.IsLevelPoint p r c w a m)
    (h' : hX.IsLevelPoint p r c w a m') : m = m' :=
  tendsto_const_nhds_iff.1 <| tendsto_of_isLevelPoint hf hdense (l := (⊤ : Filter Unit))
    tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ ↦ h) h'

open Classical in
variable (hX) in
/-- **The point on the level `a` of the broken trajectory from `p` to `r` recorded by `w`.** It is
`p` above the level of `p` and `r` below the level of `r`. For a record of a broken trajectory on
levels dense between `f r` and `f p`, it is the point of that broken trajectory on the level `a`
(`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint_eq`); for other families `w` it is not
meaningful. -/
noncomputable def morseLevelPoint (p r : M) (c : ι → ℝ) (w : ι → M) (a : ℝ) : M :=
  if f p ≤ a then p else if a ≤ f r then r else
    if h : ∃ m, hX.IsLevelPoint p r c w a m then h.choose else p

/-- The point on a level of a recorded broken trajectory is a point of that broken trajectory, on
the level clamped between the levels of the ends. -/
private theorem isLevelPoint_morseLevelPoint (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c)
    (a : ℝ) : hX.IsLevelPoint p r c w (max (f r) (min a (f p))) (hX.morseLevelPoint p r c w a) := by
  have hrp := hX.value_le_of_mem_morseBrokenTrajectoryRecords hw
  obtain ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  unfold morseLevelPoint
  split_ifs with h₁ h₂ h₃
  · rw [min_eq_right h₁, max_eq_right hrp]
    exact ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hrec, Or.inl ⟨0, hx0⟩, rfl⟩
  · rw [min_eq_left (not_le.1 h₁).le, max_eq_left h₂]
    exact ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hrec, Or.inl ⟨_, hxk⟩, rfl⟩
  · rw [min_eq_left (not_le.1 h₁).le, max_eq_right (not_le.1 h₂).le]
    exact h₃.choose_spec
  · exfalso
    obtain ⟨m, hm, hfm⟩ := exists_onChain hz (a := a)
      ⟨hxk ▸ (not_le.1 h₂).le, hx0 ▸ (not_le.1 h₁).le⟩
    exact h₃ ⟨m, k, x, z, hx0, hxk, hxc, hxne, hz, hrec, hm, hfm⟩

/-- **The point on a level of a recorded broken trajectory.** Let `w` record a broken trajectory
from `p` to `r`, through the chain `x` of critical points and the orbits of the points `z j`, on
levels dense between `f r` and `f p`. Then its point on the level of a point `m` of that broken
trajectory is `m`. -/
theorem morseLevelPoint_eq (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M} (hx0 : x 0 = p) (hxk : x (Fin.last k) = r)
    (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i)
    (hm : (∃ l, x l = m) ∨ ∃ j t, hX.flow t (z j) = m) : hX.morseLevelPoint p r c w (f m) = m := by
  have h : hX.IsLevelPoint p r c w (f m) m := ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw, hm, rfl⟩
  have h' := isLevelPoint_morseLevelPoint
    (hX.mem_morseBrokenTrajectoryRecords.2 ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hw⟩) (f m)
  rw [min_eq_left h.mem_Icc.2, max_eq_right h.mem_Icc.1] at h'
  exact h'.unique hf hdense h

/-- The point on the level `a`, between the levels of the ends, of a recorded broken trajectory
lies on the level `a`. -/
theorem apply_morseLevelPoint (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c)
    (ha : a ∈ Icc (f r) (f p)) : f (hX.morseLevelPoint p r c w a) = a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := isLevelPoint_morseLevelPoint hw a
  rw [h, min_eq_left ha.2, max_eq_right ha.1]

/-- **On a recorded level, the point of a recorded broken trajectory is the recorded point.** -/
theorem morseLevelPoint_apply_level (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c)
    (i : ι) : hX.morseLevelPoint p r c w (c i) = w i := by
  obtain ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  rw [← (hrec i).1]
  exact hX.morseLevelPoint_eq hf hdense hx0 hxk hxc hxne hz hrec (Or.inr (hrec i).2)

/-- Above the level of `p`, the point of a recorded broken trajectory is `p`. -/
theorem morseLevelPoint_of_apply_le (h : f p ≤ a) : hX.morseLevelPoint p r c w a = p := by
  simp only [morseLevelPoint, h, ↓reduceIte]

/-- Below the level of `r`, the point of a recorded broken trajectory is `r`. -/
theorem morseLevelPoint_of_le_apply (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c)
    (h : a ≤ f r) : hX.morseLevelPoint p r c w a = r := by
  by_cases hp : f p ≤ a
  · -- Then `f p = f r`, and the point is `p`, which is also the point on the level of `r`.
    have hrp := hX.value_le_of_mem_morseBrokenTrajectoryRecords hw
    have h' := isLevelPoint_morseLevelPoint hw a
    rw [min_eq_right hp, max_eq_right hrp] at h'
    exact h'.eq_of_eq_bot (le_antisymm (hp.trans h) hrp)
  · simp only [morseLevelPoint, hp, h, ↓reduceIte]

/-- **The points on the levels of recorded broken trajectories depend continuously on the record
and the level together**, for records on levels dense between `f r` and `f p`. -/
theorem continuousOn_morseLevelPoint (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) :
    ContinuousOn (fun q : (ι → M) × ℝ ↦ hX.morseLevelPoint p r c q.1 q.2)
      (hX.morseBrokenTrajectoryRecords p r c ×ˢ univ) := fun q hq ↦
  tendsto_of_isLevelPoint hf hdense ((continuous_fst.tendsto q).mono_left nhdsWithin_le_nhds)
    (((continuous_const.max (continuous_snd.min continuous_const)).tendsto q).mono_left
      nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun q' hq' ↦
      isLevelPoint_morseLevelPoint (mem_prod.1 hq').1 q'.2)
    (isLevelPoint_morseLevelPoint hq.1 q.2)

end LevelPoint

/-! ### The Moore path of a recorded broken trajectory -/

section LevelPath

variable {p r : M} {c : ι → ℝ}

/-- **The Moore path of a recorded broken trajectory.** For records of broken trajectories from
`p` to `r` on levels dense between `f r` and `f p`, the Moore path of length `f p - f r` whose
point at time `t` is the point of the broken trajectory on the level `f p - t`. It runs from `p`
to `r`, and depends continuously on the record. -/
noncomputable def morseLevelPath (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) :
    C(hX.morseBrokenTrajectoryRecords p r c, MoorePath M) where
  toFun w :=
    { toFun := fun t ↦ hX.morseLevelPoint p r c w (f p - t)
      continuous_toFun := (hX.continuousOn_morseLevelPoint hf hdense).comp_continuous
        (continuous_const.prodMk (continuous_const.sub NNReal.continuous_coe))
        fun _ ↦ ⟨w.property, mem_univ _⟩
      length := (f p - f r).toNNReal
      apply_of_length_le' := fun t ht ↦ by
        rw [hX.morseLevelPoint_of_le_apply w.property
            (sub_le_comm.1 (Real.le_coe_toNNReal (f p - f r))),
          hX.morseLevelPoint_of_le_apply w.property
            (by linarith [Real.toNNReal_le_iff_le_coe.1 ht] : f p - t ≤ f r)] }
  continuous_toFun := MoorePath.continuous_iff.2 ⟨continuous_const,
    (hX.continuousOn_morseLevelPoint hf hdense).comp_continuous
      ((continuous_subtypeVal.comp continuous_fst).prodMk
        (continuous_const.sub (NNReal.continuous_coe.comp continuous_snd)))
      fun q ↦ ⟨q.1.property, mem_univ _⟩⟩

variable (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Ioo (f r) (f p) ⊆ closure (range c))
  (w : hX.morseBrokenTrajectoryRecords p r c)

/-- The point at time `t` of the Moore path of a recorded broken trajectory is its point on the
level `f p - t`. -/
@[simp]
theorem morseLevelPath_apply (t : ℝ≥0) :
    hX.morseLevelPath hf hdense w t = hX.morseLevelPoint p r c w (f p - t) :=
  (rfl)

/-- The Moore path of a recorded broken trajectory from `p` to `r` has length `f p - f r`. -/
@[simp]
theorem length_morseLevelPath : (hX.morseLevelPath hf hdense w).length = (f p - f r).toNNReal :=
  (rfl)

/-- The Moore path of a recorded broken trajectory from `p` to `r` starts at `p`. -/
@[simp]
theorem source_morseLevelPath : (hX.morseLevelPath hf hdense w).source = p := by
  rw [MoorePath.source_def, morseLevelPath_apply, NNReal.coe_zero, sub_zero,
    hX.morseLevelPoint_of_apply_le le_rfl]

/-- The Moore path of a recorded broken trajectory from `p` to `r` ends at `r`. -/
@[simp]
theorem target_morseLevelPath : (hX.morseLevelPath hf hdense w).target = r := by
  rw [MoorePath.target_def, morseLevelPath_apply, length_morseLevelPath,
    hX.morseLevelPoint_of_le_apply w.property (sub_le_comm.1 (Real.le_coe_toNNReal (f p - f r)))]

end LevelPath

end IsAdaptedPseudoGradient

/-! ### Concatenation of broken trajectories -/

section Concat

variable {p q r : M} {c : ι → ℝ}

variable (c) in
/-- **Concatenation of records.** Records `w₁` on the levels of `c` between `f q` and `f p` and
`w₂` on those between `f r` and `f q`, none of which is the level of `q`, give the record on the
levels between `f r` and `f p` that is `w₁` above the level of `q` and `w₂` below it. -/
noncomputable def concatLevelRecords (hq : ∀ i, c i ≠ f q) (w₁ : c ⁻¹' Ioo (f q) (f p) → M)
    (w₂ : c ⁻¹' Ioo (f r) (f q) → M) (i : c ⁻¹' Ioo (f r) (f p)) : M :=
  if h : f q < c i then w₁ ⟨i, h, i.property.2⟩
  else w₂ ⟨i, i.property.1, lt_of_le_of_ne (not_lt.1 h) (hq i)⟩

variable (hq : ∀ i, c i ≠ f q) (w₁ : c ⁻¹' Ioo (f q) (f p) → M) (w₂ : c ⁻¹' Ioo (f r) (f q) → M)

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] in
/-- Above the level of `q`, a concatenation of records is the first record. -/
theorem concatLevelRecords_of_lt {i : c ⁻¹' Ioo (f r) (f p)} (h : f q < c i) :
    concatLevelRecords c hq w₁ w₂ i = w₁ ⟨i, h, i.property.2⟩ := by
  simp only [concatLevelRecords, h, ↓reduceDIte]

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] in
/-- Below the level of `q`, a concatenation of records is the second record. -/
theorem concatLevelRecords_of_gt {i : c ⁻¹' Ioo (f r) (f p)} (h : c i < f q) :
    concatLevelRecords c hq w₁ w₂ i = w₂ ⟨i, i.property.1, h⟩ := by
  simp only [concatLevelRecords, h.not_gt, ↓reduceDIte]

omit [CompactSpace M] [T2Space M] in
/-- Concatenation of records is continuous. -/
theorem continuous_concatLevelRecords :
    Continuous fun w : (c ⁻¹' Ioo (f q) (f p) → M) × (c ⁻¹' Ioo (f r) (f q) → M) ↦
      concatLevelRecords c hq w.1 w.2 :=
  continuous_pi fun i ↦ by
    by_cases h : f q < c i
    · simp only [concatLevelRecords, h, ↓reduceDIte]
      exact (continuous_apply _).comp continuous_fst
    · simp only [concatLevelRecords, h, ↓reduceDIte]
      exact (continuous_apply _).comp continuous_snd

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] in
/-- **Concatenation of records is associative.** If `f s ≤ f q` and no level of `c` is the level
of `q` or of `s`, concatenating at `q` and then at `s` is concatenating at `s` and then at `q`. -/
theorem concatLevelRecords_assoc {s : M} (hs : ∀ i, c i ≠ f s) (hsq : f s ≤ f q)
    (a : c ⁻¹' Ioo (f q) (f p) → M) (b : c ⁻¹' Ioo (f s) (f q) → M)
    (d : c ⁻¹' Ioo (f r) (f s) → M) :
    concatLevelRecords c hs (concatLevelRecords c hq a b) d =
      concatLevelRecords c hq a (concatLevelRecords c hs b d) := by
  funext i
  -- Compare the level `c i` with `f q` and `f s`; it is neither of them.
  have := hq i
  have := hs i
  simp only [concatLevelRecords]
  split_ifs <;> first | rfl | (exfalso; grind)

end Concat

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

section Concat

variable {p q r : M} {c : ι → ℝ} (hq : ∀ i, c i ≠ f q) {w₁ : c ⁻¹' Ioo (f q) (f p) → M}
  {w₂ : c ⁻¹' Ioo (f r) (f q) → M}

variable {hX} in
/-- The concatenation of two broken trajectories recorded by `w₁` and `w₂` is recorded by the
concatenation of the records, and contains the points of both. -/
private theorem exists_chain_concatLevelRecords {k₁ : ℕ} {x₁ : Fin (k₁ + 1) → M}
    {z₁ : Fin k₁ → M} (hx0₁ : x₁ 0 = p) (hxk₁ : x₁ (Fin.last k₁) = q)
    (hxc₁ : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x₁ j) = 0)
    (hxne₁ : ∀ j : Fin k₁, x₁ j.castSucc ≠ x₁ j.succ)
    (hz₁ : ∀ j : Fin k₁, z₁ j ∈ hX.flow.unstableSet (x₁ j.castSucc) ∩ hX.flow.stableSet (x₁ j.succ))
    (hw₁ : ∀ i, f (w₁ i) = c i ∧ ∃ j t, hX.flow t (z₁ j) = w₁ i)
    {k₂ : ℕ} {x₂ : Fin (k₂ + 1) → M} {z₂ : Fin k₂ → M} (hx0₂ : x₂ 0 = q)
    (hxk₂ : x₂ (Fin.last k₂) = r) (hxc₂ : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x₂ j) = 0)
    (hxne₂ : ∀ j : Fin k₂, x₂ j.castSucc ≠ x₂ j.succ)
    (hz₂ : ∀ j : Fin k₂, z₂ j ∈ hX.flow.unstableSet (x₂ j.castSucc) ∩ hX.flow.stableSet (x₂ j.succ))
    (hw₂ : ∀ i, f (w₂ i) = c i ∧ ∃ j t, hX.flow t (z₂ j) = w₂ i) :
    ∃ (x : Fin (k₁ + k₂ + 1) → M) (z : Fin (k₁ + k₂) → M), x 0 = p ∧ x (Fin.last _) = r ∧
      (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧ (∀ j : Fin (k₁ + k₂), x j.castSucc ≠ x j.succ) ∧
      (∀ j : Fin (k₁ + k₂),
        z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) ∧
      (∀ i, f (concatLevelRecords c hq w₁ w₂ i) = c i ∧
        ∃ j t, hX.flow t (z j) = concatLevelRecords c hq w₁ w₂ i) ∧
      (∀ m, hX.OnChain x₁ z₁ m → hX.OnChain x z m) ∧
      (∀ m, hX.OnChain x₂ z₂ m → hX.OnChain x z m) := by
  -- The broken trajectory runs through the first one up to `q`, and then through the second one.
  have h₁₂ : x₁ (Fin.last k₁) = x₂ 0 := hxk₁.trans hx0₂.symm
  refine ⟨(Fin.append (Fin.init x₁) x₂ :), Fin.append z₁ z₂,
    (Fin.append_init_zero h₁₂).trans hx0₁, Fin.append_init_last.trans hxk₂,
    fun l ↦ ?_,
    Fin.forall_append_init_castSucc_succ (z₁ := z₁) (z₂ := z₂) (P := fun a b _ ↦ a ≠ b) h₁₂
      hxne₁ hxne₂,
    Fin.forall_append_init_castSucc_succ
      (P := fun a b y ↦ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) h₁₂ hz₁ hz₂,
    fun i ↦ ?_, ?_, ?_⟩
  · rcases Fin.append_init_eq_or_eq l with ⟨l₁, h⟩ | ⟨l₂, h⟩
    · exact h ▸ hxc₁ l₁
    · exact h ▸ hxc₂ l₂
  · by_cases h : f q < c i
    · rw [concatLevelRecords_of_lt hq w₁ w₂ h]
      obtain ⟨hc, j₁, t, ht⟩ := hw₁ ⟨i, h, i.property.2⟩
      exact ⟨hc, Fin.castAdd k₂ j₁, t, by rw [Fin.append_left, ht]⟩
    · rw [concatLevelRecords_of_gt hq w₁ w₂ (lt_of_le_of_ne (not_lt.1 h) (hq i))]
      obtain ⟨hc, j₂, t, ht⟩ := hw₂ ⟨i, i.property.1, lt_of_le_of_ne (not_lt.1 h) (hq i)⟩
      exact ⟨hc, Fin.natAdd k₁ j₂, t, by rw [Fin.append_right, ht]⟩
  · rintro m (⟨l₁, rfl⟩ | ⟨j₁, t, rfl⟩)
    · exact Or.inl ⟨_, Fin.append_init_castLE h₁₂ l₁⟩
    · exact Or.inr ⟨Fin.castAdd k₂ j₁, t, by rw [Fin.append_left]⟩
  · rintro m (⟨l₂, rfl⟩ | ⟨j₂, t, rfl⟩)
    · exact Or.inl ⟨Fin.natAdd k₁ l₂, Fin.append_right _ _ l₂⟩
    · exact Or.inr ⟨Fin.natAdd k₁ j₂, t, by rw [Fin.append_right]⟩

variable (hw₁ : w₁ ∈ hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c))
  (hw₂ : w₂ ∈ hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c))
include hw₁ hw₂

/-- **The concatenation of records of broken trajectories records a broken trajectory.** -/
theorem concatLevelRecords_mem :
    concatLevelRecords c hq w₁ w₂ ∈
      hX.morseBrokenTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) := by
  obtain ⟨k₁, x₁, z₁, hx0₁, hxk₁, hxc₁, hxne₁, hz₁, hrec₁⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₁
  obtain ⟨k₂, x₂, z₂, hx0₂, hxk₂, hxc₂, hxne₂, hz₂, hrec₂⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₂
  obtain ⟨x, z, hx0, hxk, hxc, hxne, hz, hrec, -, -⟩ := exists_chain_concatLevelRecords hq hx0₁ hxk₁
    hxc₁ hxne₁ hz₁ hrec₁ hx0₂ hxk₂ hxc₂ hxne₂ hz₂ hrec₂
  exact hX.mem_morseBrokenTrajectoryRecords.2 ⟨_, x, z, hx0, hxk, hxc, hxne, hz, hrec⟩

/-- **Concatenations are not unbroken.** If `q ≠ r` and some level of `c` lies strictly between
`f q` and `f p`, the concatenation at `q` of records of broken trajectories from `p` to `q` and
from `q` to `r` is not the record of an unbroken trajectory from `p` to `r`. -/
theorem concatLevelRecords_notMem_morseTrajectoryRecords (hqr : q ≠ r) {i₀ : ι}
    (hi₀ : c i₀ ∈ Ioo (f q) (f p)) :
    concatLevelRecords c hq w₁ w₂ ∉
      hX.morseTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) := by
  intro hw
  have hrq := hX.value_lt_of_mem_morseBrokenTrajectoryRecords hqr hw₂
  -- On the level `c i₀`, the unbroken trajectory lies in the stable set of `r`, and the
  -- concatenation is the first record.
  obtain ⟨y, hy, hwy⟩ := hX.mem_morseTrajectoryRecords.1 hw
  obtain ⟨-, t, ht⟩ := hwy ⟨i₀, hrq.trans hi₀.1, hi₀.2⟩
  rw [concatLevelRecords_of_lt hq w₁ w₂ (i := ⟨i₀, hrq.trans hi₀.1, hi₀.2⟩) hi₀.1] at ht
  -- There the first record lies on a component of the first broken trajectory, in the stable set
  -- of a critical point `x j.succ` with `f q ≤ f (x j.succ)`, so not in that of `r`.
  obtain ⟨k, x, z, -, rfl, -, -, hz, hw₁'⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw₁
  obtain ⟨-, j, t', ht'⟩ := hw₁' ⟨i₀, hi₀⟩
  have hxq : f (x (Fin.last k)) ≤ f (x j.succ) := hX.antitone_apply_of_chain hz (Fin.le_last _)
  have hne : x j.succ ≠ r := fun h ↦ (hrq.trans_le hxq).ne' (congrArg f h)
  have h₁ : w₁ ⟨i₀, hi₀⟩ ∈ hX.flow.stableSet (x j.succ) := by
    rw [← ht']
    exact (Flow.apply_mem_stableSet_iff _ t').2 (hz j).2
  have h₂ : w₁ ⟨i₀, hi₀⟩ ∈ hX.flow.stableSet r := by
    rw [← ht]
    exact (Flow.apply_mem_stableSet_iff _ t).2 hy.2
  exact disjoint_left.1 (Flow.disjoint_stableSet hne) h₁ h₂

/-- **Above the level of `q`, the points of a concatenation are those of the first broken
trajectory.** -/
theorem morseLevelPoint_concatLevelRecords_of_le (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range ((c ⁻¹' Ioo (f r) (f p)).domRestrict c)))
    (hdense₁ : Ioo (f q) (f p) ⊆ closure (range ((c ⁻¹' Ioo (f q) (f p)).domRestrict c)))
    {a : ℝ} (ha : f q ≤ a) :
    hX.morseLevelPoint p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) (concatLevelRecords c hq w₁ w₂)
      a = hX.morseLevelPoint p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c) w₁ a := by
  by_cases hpa : f p ≤ a
  · rw [morseLevelPoint_of_apply_le hpa, morseLevelPoint_of_apply_le hpa]
  obtain ⟨k₁, x₁, z₁, hx0₁, hxk₁, hxc₁, hxne₁, hz₁, hrec₁⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₁
  obtain ⟨k₂, x₂, z₂, hx0₂, hxk₂, hxc₂, hxne₂, hz₂, hrec₂⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₂
  obtain ⟨x, z, hx0, hxk, hxc, hxne, hz, hrec, h₁, -⟩ := exists_chain_concatLevelRecords hq hx0₁
    hxk₁ hxc₁ hxne₁ hz₁ hrec₁ hx0₂ hxk₂ hxc₂ hxne₂ hz₂ hrec₂
  obtain ⟨m, hm, rfl⟩ := exists_onChain hz₁ (a := a) ⟨hxk₁ ▸ ha, hx0₁ ▸ (not_le.1 hpa).le⟩
  rw [hX.morseLevelPoint_eq hf hdense hx0 hxk hxc hxne hz hrec (h₁ m hm),
    hX.morseLevelPoint_eq hf hdense₁ hx0₁ hxk₁ hxc₁ hxne₁ hz₁ hrec₁ hm]

/-- **Below the level of `q`, the points of a concatenation are those of the second broken
trajectory.** -/
theorem morseLevelPoint_concatLevelRecords_of_ge (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range ((c ⁻¹' Ioo (f r) (f p)).domRestrict c)))
    (hdense₂ : Ioo (f r) (f q) ⊆ closure (range ((c ⁻¹' Ioo (f r) (f q)).domRestrict c)))
    {a : ℝ} (ha : a ≤ f q) :
    hX.morseLevelPoint p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) (concatLevelRecords c hq w₁ w₂)
      a = hX.morseLevelPoint q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c) w₂ a := by
  by_cases hra : a ≤ f r
  · rw [hX.morseLevelPoint_of_le_apply (hX.concatLevelRecords_mem hq hw₁ hw₂) hra,
      hX.morseLevelPoint_of_le_apply hw₂ hra]
  obtain ⟨k₁, x₁, z₁, hx0₁, hxk₁, hxc₁, hxne₁, hz₁, hrec₁⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₁
  obtain ⟨k₂, x₂, z₂, hx0₂, hxk₂, hxc₂, hxne₂, hz₂, hrec₂⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₂
  obtain ⟨x, z, hx0, hxk, hxc, hxne, hz, hrec, -, h₂⟩ := exists_chain_concatLevelRecords hq hx0₁
    hxk₁ hxc₁ hxne₁ hz₁ hrec₁ hx0₂ hxk₂ hxc₂ hxne₂ hz₂ hrec₂
  obtain ⟨m, hm, rfl⟩ := exists_onChain hz₂ (a := a) ⟨hxk₂ ▸ (not_le.1 hra).le, hx0₂ ▸ ha⟩
  rw [hX.morseLevelPoint_eq hf hdense hx0 hxk hxc hxne hz hrec (h₂ m hm),
    hX.morseLevelPoint_eq hf hdense₂ hx0₂ hxk₂ hxc₂ hxne₂ hz₂ hrec₂ hm]

end Concat

section ConcatPath

variable {p q r : M} {c : ι → ℝ}

/-- **Concatenation of records of broken trajectories**, as a continuous map from pairs of records
of broken trajectories from `p` to `q` and from `q` to `r` to records of broken trajectories from
`p` to `r`, on the levels of `c` between the levels of the ends. -/
noncomputable def morseRecordsConcat (hq : ∀ i, c i ≠ f q) :
    C(hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c) ×
        hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c),
      hX.morseBrokenTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c)) where
  toFun w := ⟨concatLevelRecords c hq w.1.val w.2.val,
    hX.concatLevelRecords_mem hq w.1.property w.2.property⟩
  continuous_toFun := ((continuous_concatLevelRecords hq).comp
    (continuous_subtypeVal.prodMap continuous_subtypeVal)).subtype_mk _

/-- The record underlying a concatenation of records. -/
@[simp]
theorem coe_morseRecordsConcat (hq : ∀ i, c i ≠ f q)
    (w : hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c) ×
      hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c)) :
    (hX.morseRecordsConcat hq w : _ → M) = concatLevelRecords c hq w.1.val w.2.val :=
  (rfl)

/-- **The Moore path of a concatenation of broken trajectories is the concatenation of their Moore
paths**, for levels of `c` that are dense between `f r` and `f p` and avoid the level of `q`. -/
theorem morseLevelPath_morseRecordsConcat (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hq : ∀ i, c i ≠ f q)
    (w : hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c) ×
      hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c)) :
    hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo hdense)
        (hX.morseRecordsConcat hq w) =
      (hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo
          ((Ioo_subset_Ioo_left (hX.value_le_of_mem_morseBrokenTrajectoryRecords
            w.2.property)).trans hdense)) w.1).trans
        (hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo
          ((Ioo_subset_Ioo_right (hX.value_le_of_mem_morseBrokenTrajectoryRecords
            w.1.property)).trans hdense)) w.2)
        (by rw [target_morseLevelPath, source_morseLevelPath]) := by
  have hqp := hX.value_le_of_mem_morseBrokenTrajectoryRecords w.1.property
  have hrq := hX.value_le_of_mem_morseBrokenTrajectoryRecords w.2.property
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo hdense
  have hdense₁ := subset_closure_range_domRestrict_preimage isOpen_Ioo
    ((Ioo_subset_Ioo_left hrq).trans hdense)
  have hdense₂ := subset_closure_range_domRestrict_preimage isOpen_Ioo
    ((Ioo_subset_Ioo_right hqp).trans hdense)
  refine MoorePath.ext ?_ fun t ↦ ?_
  · rw [MoorePath.length_trans, length_morseLevelPath, length_morseLevelPath,
      length_morseLevelPath, ← Real.toNNReal_add (sub_nonneg.2 hqp) (sub_nonneg.2 hrq),
      sub_add_sub_cancel]
  rw [MoorePath.trans_apply, length_morseLevelPath, morseLevelPath_apply]
  split_ifs with ht
  · rw [morseLevelPath_apply]
    exact hX.morseLevelPoint_concatLevelRecords_of_le hq w.1.property w.2.property hf hdense'
      hdense₁ (by linarith [(Real.le_toNNReal_iff_coe_le (sub_nonneg.2 hqp)).1 ht])
  · rw [morseLevelPath_apply, NNReal.coe_sub (not_le.1 ht).le,
      Real.coe_toNNReal _ (sub_nonneg.2 hqp), show f q - (t - (f p - f q)) = f p - t by ring]
    exact hX.morseLevelPoint_concatLevelRecords_of_ge hq w.1.property w.2.property hf hdense'
      hdense₂ (by linarith [(Real.toNNReal_lt_iff_lt_coe (sub_nonneg.2 hqp)).1 (not_le.1 ht)])

end ConcatPath

end IsAdaptedPseudoGradient

end TauCeti
