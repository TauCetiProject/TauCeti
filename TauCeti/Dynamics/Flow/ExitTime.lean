/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import TauCeti.Dynamics.Flow.Basic
import TauCeti.Dynamics.Flow.OmegaLimit

/-!
# Exit times of a flow from a closed set

Let `ϕ` be a flow of `ℝ` on a topological space `α` and let `P` be a subset of `α`. The
**exit time** of a point `x` from `P` (`Flow.exitTime ϕ P x`) is the supremum in `[0, ∞]` of the
times `t ≥ 0` such that the trajectory of `x` stays in `P` during `[0, t]`. It is `0` outside `P`
and on the points of `P` leaving it immediately, and `∞` exactly on the points whose forward orbit
stays in `P` (`Flow.exitTime_eq_top_iff`). Flowing for a time `s` up to the exit time lowers the
exit time by `s` (`Flow.exitTime_apply`). When `P` is closed, the trajectory of a point of `P`
stays in `P` up to and including its exit time (`Flow.le_exitTime_iff`).

These are the data of the index-pair arguments of Conley index theory. For `t ≥ 0` the sets

* `N_t = {x ∈ P | t ≤ exitTime x}` of points staying in `P` for time `t`,
* `E_t = {x ∈ P | exitTime x ≤ t}` of points leaving `P` by time `t`,
* `S⁺ = {x | exitTime x = ∞}` of points whose forward orbit stays in `P`

cover `P` as `P = N_t ∪ E_t` with `S⁺ = ⋂ₜ N_t`. The sets `N_t` and `S⁺` are closed
(`Flow.isClosed_setOf_le_exitTime`, `Flow.isClosed_setOf_exitTime_eq_top`), and so is `E_t` when
the exit time is continuous on `P` as a map to `[0, ∞]` (`Flow.isClosed_setOf_exitTime_le`).
Continuity of the exit time is a genuine hypothesis, to be established for the particular flow
and set: it fails, for instance, when a trajectory touches the boundary of `P` from inside and
only leaves `P` later, since nearby trajectories may leave at the touching time.

The **flow stopped at the exit** (`Flow.stopAtExit ϕ P t`) sends `x` to its position at time
`min t (exitTime x)`. It maps `P` into `P`, it fixes the points of exit time zero, and it maps
`E_t` to points of `P` of exit time zero (`Flow.mapsTo_stopAtExit_setOf_exitTime_le`). When the
exit time is continuous on `P`, it is a continuous self-map of `P` (`Flow.stopAtExitMap`)
homotopic to the identity relative to any set `L` of points of exit time zero
(`Flow.homotopicRel_stopAtExitMap`): flow each point for the fraction `u ∈ [0, 1]` of its stopped
time. When `L` is exactly the set of points of `P` of exit time zero, as for the exit set of the
index pair `(P, L)` in the Conley–Zehnder argument, the stopped flow is therefore a self-map of
the pair `(P, L)` homotopic to the identity relative to `L` which carries `E_t` into `L`.

Finally the forward-trapped set `S⁺` is carried by the flow towards the maximal invariant subset
`Inv(P) = {x | ∀ t, ϕ t x ∈ P}`: when `P` is compact and `α` is Hausdorff, `S⁺` is eventually
carried into every open neighbourhood of `Inv(P)`
(`Flow.eventually_mapsTo_setOf_exitTime_eq_top`), by the attraction of sets eventually mapped
into `P` (`Flow.eventually_mapsTo_of_isCompact_of_isOpen` in
`TauCeti/Dynamics/Flow/OmegaLimit.lean`). On the forward invariant set `S⁺`
(`Flow.isForwardInvariant_setOf_exitTime_eq_top`), each time-`t` map with `t ≥ 0` is homotopic to
the identity (`Flow.homotopic_id_restrict` in `TauCeti/Dynamics/Flow/Basic.lean`).

## Main definitions

* `Flow.exitTime`: the exit time from a set, with values in `[0, ∞]`.
* `Flow.stopAtExit`: the flow stopped on leaving a set.
* `Flow.stopAtExitMap`: the stopped flow as a continuous self-map of a closed set, for a
  continuous exit time.

## Main results

* `Flow.le_exitTime_iff`: from a point of a closed set `P`, the trajectory stays in `P` during
  `[0, t]` exactly when `t` is at most the exit time.
* `Flow.exitTime_apply`: the exit time decreases at unit speed along the trajectory.
* `Flow.isClosed_setOf_le_exitTime`, `Flow.isClosed_setOf_exitTime_le`: the sets `N_t` and `E_t`
  are closed.
* `Flow.homotopicRel_stopAtExitMap`: the stopped flow is homotopic to the identity relative to
  the points of exit time zero.
* `Flow.mapsTo_stopAtExit_setOf_exitTime_le`: the stopped flow at time `t` sends the points
  leaving by time `t` to points of exit time zero.
* `Flow.eventually_mapsTo_setOf_exitTime_eq_top`: for compact `P`, the points whose forward orbit
  stays in `P` eventually enter every open neighbourhood of the maximal invariant subset of `P`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Inventiones Mathematicae 73 (1983), 33–49 (the deformation of an index pair by
  the flow stopped at the exit, and the injectivity of restriction to the invariant set).
* D. Salamon, *Connected simple systems and the Conley index of isolated invariant sets*,
  Transactions of the American Mathematical Society 291 (1985), 1–41 (exit times of index pairs).
-/

public section

open Filter Set
open scoped ENNReal NNReal

namespace Flow

variable {α : Type*} [TopologicalSpace α]

section ExitTime

variable (ϕ : Flow ℝ α) (P : Set α)

/-- The **exit time** of `x` from `P`: the supremum in `[0, ∞]` of the times `t ≥ 0` such that
the trajectory of `x` stays in `P` during `[0, t]`. It is `0` for `x ∉ P`. -/
noncomputable def exitTime (x : α) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : ∀ s ∈ Icc (0 : ℝ) t, ϕ s x ∈ P), (t : ℝ≥0∞)

variable {ϕ P} {x : α}

/-- A time during which the trajectory stays in `P` is at most the exit time. -/
theorem le_exitTime {t : ℝ≥0} (h : ∀ s ∈ Icc (0 : ℝ) t, ϕ s x ∈ P) :
    (t : ℝ≥0∞) ≤ ϕ.exitTime P x :=
  le_iSup₂ (f := fun (t : ℝ≥0) (_ : ∀ s ∈ Icc (0 : ℝ) t, ϕ s x ∈ P) ↦ (t : ℝ≥0∞)) t h

/-- Before its exit time the trajectory lies in `P`. -/
theorem apply_mem_of_lt_exitTime {s : ℝ} (hs₀ : 0 ≤ s) (hs : ENNReal.ofReal s < ϕ.exitTime P x) :
    ϕ s x ∈ P := by
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hs
  obtain ⟨hPt, hst⟩ := lt_iSup_iff.1 ht
  exact hPt s ⟨hs₀, ((ENNReal.ofReal_lt_coe_iff hs₀).1 hst).le⟩

/-- Outside `P` the exit time is zero. -/
theorem exitTime_eq_zero_of_notMem (hx : x ∉ P) : ϕ.exitTime P x = 0 := by
  refine ENNReal.iSup_eq_zero.2 fun t ↦ ENNReal.iSup_eq_zero.2 fun h ↦ absurd ?_ hx
  simpa using h 0 ⟨le_rfl, t.coe_nonneg⟩

/-- **Characterization of the exit time.** From a point of a closed set `P`, the trajectory stays
in `P` during `[0, t]` exactly when `t` is at most the exit time: the supremum defining the exit
time is attained when it is finite. -/
theorem le_exitTime_iff (hP : IsClosed P) (hx : x ∈ P) {t : ℝ≥0} :
    (t : ℝ≥0∞) ≤ ϕ.exitTime P x ↔ ∀ s ∈ Icc (0 : ℝ) t, ϕ s x ∈ P := by
  refine ⟨fun h ↦ ?_, le_exitTime⟩
  -- the times at which the trajectory lies in `P` form a closed set containing `[0, t)` and `0`
  have hA : IsClosed {s : ℝ | ϕ s x ∈ P} :=
    hP.preimage (ϕ.continuous continuous_id continuous_const)
  have hIco : Ico (0 : ℝ) t ⊆ {s : ℝ | ϕ s x ∈ P} := fun s hs ↦
    apply_mem_of_lt_exitTime hs.1 (((ENNReal.ofReal_lt_coe_iff hs.1).2 hs.2).trans_le h)
  rcases eq_or_ne (t : ℝ) 0 with ht | ht
  · intro s hs
    obtain rfl : s = 0 := le_antisymm (ht ▸ hs.2) hs.1
    simpa using hx
  · exact (closure_Ico ht.symm).symm.subset.trans (hA.closure_subset_iff.2 hIco)

/-- From a point of a closed set `P`, the trajectory lies in `P` at every time `s ≥ 0` up to and
including the exit time. -/
theorem apply_mem_of_le_exitTime (hP : IsClosed P) (hx : x ∈ P) {s : ℝ} (hs₀ : 0 ≤ s)
    (hs : ENNReal.ofReal s ≤ ϕ.exitTime P x) : ϕ s x ∈ P :=
  (le_exitTime_iff hP hx).1 hs s ⟨hs₀, (Real.coe_toNNReal s hs₀).ge⟩

/-- The exit time is infinite exactly when the forward orbit stays in `P`. -/
theorem exitTime_eq_top_iff : ϕ.exitTime P x = ∞ ↔ ∀ s : ℝ, 0 ≤ s → ϕ s x ∈ P :=
  ⟨fun h _ hs ↦ apply_mem_of_lt_exitTime hs (h ▸ ENNReal.ofReal_lt_top),
    fun h ↦ ENNReal.eq_top_of_forall_nnreal_le fun _ ↦ le_exitTime fun s hs ↦ h s hs.1⟩

/-- **The exit time decreases at unit speed.** Flowing a point for a time `s` at most its exit time
lowers the exit time by `s`. -/
theorem exitTime_apply {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ϕ.exitTime P x) :
    ϕ.exitTime P (ϕ s x) = ϕ.exitTime P x - s := by
  -- the trajectory of `ϕ s x` during `[0, r]` is that of `x` during `[s, s + r]`, and the
  -- trajectory of `x` lies in `P` during `[0, s)`
  refine le_antisymm (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
    (ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_)
  · rw [ENNReal.le_sub_iff_add_le_left ENNReal.coe_ne_top hs, ← ENNReal.coe_add]
    refine le_exitTime fun q hq ↦ ?_
    rcases lt_or_ge q s with hqs | hsq
    · exact apply_mem_of_lt_exitTime hq.1 (((ENNReal.ofReal_lt_coe_iff hq.1).2 hqs).trans_le hs)
    · have hq' : q - s ≤ r := by push_cast at hq; linarith [hq.2]
      have :=
        apply_mem_of_lt_exitTime (sub_nonneg.2 hsq) ((ENNReal.ofReal_le_coe.2 hq').trans_lt hr)
      rwa [← map_add, sub_add_cancel] at this
  · refine le_exitTime fun q hq ↦ ?_
    rw [← map_add]
    refine apply_mem_of_lt_exitTime (add_nonneg hq.1 s.coe_nonneg)
      (lt_of_le_of_lt ?_ (lt_tsub_iff_left.1 hr))
    rw [← ENNReal.coe_add, ENNReal.ofReal_le_coe]
    push_cast
    linarith [hq.2]

/-- At a finite exit time, the trajectory reaches a point of exit time zero. -/
theorem exitTime_apply_exitTime (h : ϕ.exitTime P x ≠ ∞) :
    ϕ.exitTime P (ϕ (ϕ.exitTime P x).toReal x) = 0 := by
  rw [← ENNReal.coe_toNNReal_eq_toReal, exitTime_apply ENNReal.coe_toNNReal_le_self,
    ENNReal.coe_toNNReal h, tsub_self]

/-- The points of a closed set `P` staying in `P` for time `t` form a closed set. -/
theorem isClosed_setOf_le_exitTime (hP : IsClosed P) (t : ℝ≥0) :
    IsClosed {x ∈ P | (t : ℝ≥0∞) ≤ ϕ.exitTime P x} := by
  have : {x ∈ P | (t : ℝ≥0∞) ≤ ϕ.exitTime P x} = ⋂ s ∈ Icc (0 : ℝ) t, ϕ s ⁻¹' P := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    refine ⟨fun h ↦ (le_exitTime_iff hP h.1).1 h.2, fun h ↦ ?_⟩
    have hx : x ∈ P := by simpa using h 0 ⟨le_rfl, t.coe_nonneg⟩
    exact ⟨hx, (le_exitTime_iff hP hx).2 h⟩
  rw [this]
  exact isClosed_biInter fun s _ ↦ hP.preimage (ϕ.continuous_toFun s)

/-- The points whose forward orbit stays in a closed set `P` form a closed set. -/
theorem isClosed_setOf_exitTime_eq_top (hP : IsClosed P) :
    IsClosed {x | ϕ.exitTime P x = ∞} := by
  have : {x | ϕ.exitTime P x = ∞} = ⋂ s ∈ Ici (0 : ℝ), ϕ s ⁻¹' P := by
    ext x
    simp [exitTime_eq_top_iff]
  rw [this]
  exact isClosed_biInter fun s _ ↦ hP.preimage (ϕ.continuous_toFun s)

/-- If the exit time is continuous on a closed set `P`, the points of `P` leaving it by time `t`
form a closed set. -/
theorem isClosed_setOf_exitTime_le (hP : IsClosed P) (hτ : ContinuousOn (ϕ.exitTime P) P)
    (t : ℝ≥0∞) : IsClosed {x ∈ P | ϕ.exitTime P x ≤ t} :=
  hτ.preimage_isClosed_of_isClosed hP isClosed_Iic

/-- The points whose forward orbit stays in `P` form a forward invariant set. -/
theorem isForwardInvariant_setOf_exitTime_eq_top :
    IsForwardInvariant ϕ {x | ϕ.exitTime P x = ∞} := fun t ht x hx ↦ by
  simp only [mem_ofPred_eq, exitTime_eq_top_iff] at hx ⊢
  intro s hs
  rw [← map_add]
  exact hx _ (add_nonneg hs ht)

end ExitTime

section StopAtExit

variable (ϕ : Flow ℝ α) (P : Set α)

/-- The **flow stopped at the exit** from `P`: the position of `x` at time `min t (exitTime x)`.
Points of `P` flow for time `t`, or until they leave `P` if that happens first. -/
noncomputable def stopAtExit (t : ℝ≥0) (x : α) : α :=
  ϕ (ENNReal.truncateToReal t (ϕ.exitTime P x)) x

variable {ϕ P} {x : α} {t : ℝ≥0}

/-- The stopped flow runs for the time `min t (exitTime x)`. -/
theorem stopAtExit_eq : ϕ.stopAtExit P t x = ϕ (min (t : ℝ≥0∞) (ϕ.exitTime P x)).toReal x := by
  rw [stopAtExit, ENNReal.truncateToReal]

/-- The time `min t (exitTime x)` for which the stopped flow runs is at most the exit time. -/
theorem ofReal_truncateToReal_exitTime_le (t : ℝ≥0) :
    ENNReal.ofReal (ENNReal.truncateToReal t (ϕ.exitTime P x)) ≤ ϕ.exitTime P x := by
  rcases le_total (ϕ.exitTime P x) t with h | h
  · rw [ENNReal.truncateToReal_eq_toReal ENNReal.coe_ne_top h]
    exact ENNReal.ofReal_toReal_le
  · refine (ENNReal.ofReal_le_ofReal (ENNReal.truncateToReal_le ENNReal.coe_ne_top)).trans ?_
    simpa using h

/-- Stopping the flow at time `0` does nothing. -/
@[simp]
theorem stopAtExit_zero : ϕ.stopAtExit P 0 x = x := by
  simp [stopAtExit_eq]

/-- The stopped flow fixes the points of exit time zero. -/
theorem stopAtExit_of_exitTime_eq_zero (h : ϕ.exitTime P x = 0) : ϕ.stopAtExit P t x = x := by
  simp [stopAtExit_eq, h]

/-- For times at most the exit time, the stopped flow is the flow. -/
theorem stopAtExit_of_le_exitTime (h : (t : ℝ≥0∞) ≤ ϕ.exitTime P x) :
    ϕ.stopAtExit P t x = ϕ t x := by
  simp [stopAtExit_eq, min_eq_left h]

/-- For times at least the exit time, the stopped flow is the flow at the exit time. -/
theorem stopAtExit_of_exitTime_le (h : ϕ.exitTime P x ≤ t) :
    ϕ.stopAtExit P t x = ϕ (ϕ.exitTime P x).toReal x := by
  rw [stopAtExit, ENNReal.truncateToReal_eq_toReal ENNReal.coe_ne_top h]

/-- The stopped flow maps a closed set `P` into itself. -/
theorem mapsTo_stopAtExit (hP : IsClosed P) (t : ℝ≥0) : MapsTo (ϕ.stopAtExit P t) P P :=
  fun _ hx ↦ apply_mem_of_le_exitTime hP hx ENNReal.truncateToReal_nonneg
    (ofReal_truncateToReal_exitTime_le _)

/-- **The stopped flow ends at the exit.** At time `t`, the stopped flow sends the points of a
closed set `P` which leave `P` by time `t` to points of `P` of exit time zero. -/
theorem mapsTo_stopAtExit_setOf_exitTime_le (hP : IsClosed P) (t : ℝ≥0) :
    MapsTo (ϕ.stopAtExit P t) {x ∈ P | ϕ.exitTime P x ≤ t} {x ∈ P | ϕ.exitTime P x = 0} :=
  fun x hx ↦ ⟨mapsTo_stopAtExit hP t hx.1, by
    rw [stopAtExit_of_exitTime_le hx.2]
    exact exitTime_apply_exitTime (ne_top_of_le_ne_top ENNReal.coe_ne_top hx.2)⟩

/-- If the exit time is continuous on `P`, so is the stopped flow. -/
theorem continuousOn_stopAtExit (hτ : ContinuousOn (ϕ.exitTime P) P) (t : ℝ≥0) :
    ContinuousOn (ϕ.stopAtExit P t) P :=
  ϕ.cont'.comp_continuousOn
    (((ENNReal.continuous_truncateToReal ENNReal.coe_ne_top).comp_continuousOn hτ).prodMk
      continuousOn_id)

variable (ϕ)

/-- The flow stopped at the exit from a closed set `P` as a continuous self-map of `P`, for an exit
time continuous on `P`. -/
noncomputable def stopAtExitMap (hP : IsClosed P) (hτ : ContinuousOn (ϕ.exitTime P) P)
    (t : ℝ≥0) : C(P, P) where
  toFun x := ⟨ϕ.stopAtExit P t x, mapsTo_stopAtExit hP t x.property⟩
  continuous_toFun :=
    ((continuousOn_iff_continuous_domRestrict.1 (continuousOn_stopAtExit hτ t))).subtype_mk _

@[simp]
theorem coe_stopAtExitMap_apply (hP : IsClosed P) (hτ : ContinuousOn (ϕ.exitTime P) P)
    (t : ℝ≥0) (x : P) : (ϕ.stopAtExitMap hP hτ t x : α) = ϕ.stopAtExit P t x :=
  (rfl)

/-- **The stopped flow is a deformation of `P`.** For an exit time continuous on a closed set `P`,
the stopped flow is homotopic to the identity of `P` relative to any set `L` of points of exit
time zero, through the maps flowing each point for the fraction `u ∈ [0, 1]` of its stopped
time. -/
theorem homotopicRel_stopAtExitMap (hP : IsClosed P) (hτ : ContinuousOn (ϕ.exitTime P) P)
    (t : ℝ≥0) {L : Set α} (hL : ∀ x ∈ L, ϕ.exitTime P x = 0) :
    (ContinuousMap.id P).HomotopicRel (ϕ.stopAtExitMap hP hτ t) {x : P | (x : α) ∈ L} := by
  -- the stopped time of a point of `P`, a continuous function on `P` with values in `[0, t]`
  set T : P → ℝ := fun x ↦ ENNReal.truncateToReal t (ϕ.exitTime P x) with hT
  have hTc : Continuous T :=
    (ENNReal.continuous_truncateToReal ENNReal.coe_ne_top).comp hτ.domRestrict
  have hmem (u : unitInterval) (x : P) : ϕ (u * T x) x ∈ P := by
    refine apply_mem_of_le_exitTime hP x.property
      (mul_nonneg u.property.1 ENNReal.truncateToReal_nonneg) ?_
    calc ENNReal.ofReal (u * T x) ≤ ENNReal.ofReal (T x) := ENNReal.ofReal_le_ofReal
          (mul_le_of_le_one_left ENNReal.truncateToReal_nonneg u.property.2)
      _ ≤ ϕ.exitTime P x := ofReal_truncateToReal_exitTime_le _
  refine ⟨{ toFun := fun p ↦ ⟨ϕ (p.1 * T p.2) p.2, hmem p.1 p.2⟩
            continuous_toFun := (ϕ.continuous
              ((continuous_subtypeVal.comp continuous_fst).mul (hTc.comp continuous_snd))
              (continuous_subtypeVal.comp continuous_snd)).subtype_mk _
            map_zero_left := fun x ↦ by ext; simp
            map_one_left := fun x ↦ by ext; simp [hT, stopAtExit]
            prop' := fun u x hx ↦ by
              ext
              simp [hT, ENNReal.truncateToReal_eq_toReal ENNReal.coe_ne_top, hL x hx] }⟩

end StopAtExit

section Limit

variable {ϕ : Flow ℝ α} {P : Set α}

/-- If `P` is compact in a Hausdorff space, the points whose forward orbit stays in `P` are
eventually carried by the flow into every open neighbourhood of the maximal invariant subset
of `P`. -/
theorem eventually_mapsTo_setOf_exitTime_eq_top [T2Space α] (hP : IsCompact P) {U : Set α}
    (hU : IsOpen U) (hPU : {x | ∀ t, ϕ t x ∈ P} ⊆ U) :
    ∀ᶠ t in atTop, MapsTo (ϕ t) {x | ϕ.exitTime P x = ∞} U :=
  eventually_mapsTo_of_isCompact_of_isOpen hP
    (eventually_ge_atTop 0 |>.mono fun _ ht _ hx ↦ exitTime_eq_top_iff.1 hx _ ht) hU hPU

end Limit

end Flow
