/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.SequentialCompactness
public import TauCeti.Geometry.Manifold.Morse.Stable.TrajectorySpace
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.StrictAnti

/-!
# Compactified spaces of trajectories, recorded on countably many levels

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f`, and `p`, `r` critical points. Choose levels `c i`, for `i` in a type `ι`,
strictly between `f r` and `f p` and containing no critical point. A trajectory from `p` to `r`
crosses each level `c i` exactly once, so it is recorded by the family `w : ι → M` of its points
on the levels (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords`). Its compactified space
is the closure of these records in the compact Hausdorff space `ι → M`; it is compact and
Hausdorff because `ι → M` is. For countable `ι` the space `ι → M` is moreover metrizable, so the
closure is described by limits of sequences.

A *broken trajectory* from `p` to `r` is a chain of critical points `p = x 0, x 1, …, x k = r`,
consecutive ones distinct, with a point `z j` on a trajectory from `x j` to `x (j + 1)` for each
`j`. The values of `f` decrease strictly along the chain, so each level `c i` is crossed by exactly
one component, and a broken trajectory is recorded in the same way, by the points of its
components on the levels (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`). An
unbroken trajectory is a broken one with a single component
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords`).

The main results are:

* **Broken convergence is convergence of the records.** If points `u a` of trajectories converge
  to a broken trajectory in the sense of Morse theory, meaning that for each component `j` the
  points of their orbits at suitable times `s j a` converge to `z j`, then their records converge
  to a record of that broken trajectory
  (`TauCeti.IsAdaptedPseudoGradient.exists_tendsto_mem_morseBrokenTrajectoryRecords`). This needs no
  transversality.
* **The compactification adds only broken trajectories.** Under the Morse–Smale condition every
  point of the closure of the records of unbroken trajectories is the record of a broken
  trajectory (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords_subset`).
  This combines the previous point with the sequential compactness of trajectories,
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_subseq_tendsto_broken`.
* **The unbroken trajectories form the trajectory space.** Reading off the point on any one level
  identifies the records of unbroken trajectories with the level slice
  `W^u(p) ∩ W^s(r) ∩ {f = c i₀}`
  (`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseTrajectoryRecords`), and hence with the
  space of unparametrized trajectories from `p` to `r`
  (`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseTrajectoryRecords_orbitQuotient`).

Under the Morse–Smale condition the index drops strictly along the chain of a broken trajectory
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.strictAnti_manifoldMorseIndex_of_chain`), so a
broken trajectory from `p` to `r` has at most `ind p - ind r` components
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.add_manifoldMorseIndex_le_of_chain`).

This generalizes the compactified space of index-two trajectories of
`TauCeti.Geometry.Manifold.Morse.Boundary.Compactification`, which records them on two levels in
`M × M`, to any index difference and any family of levels, countable for the closure result. That
every broken trajectory is a limit of unbroken ones, and the charts of the compactified space near
broken trajectories, need gluing; beyond index two they are not proved here.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectoryRecords`: the trajectories from `p` to `r`, recorded on the levels `c`.
* `morseBrokenTrajectoryRecords`: the broken trajectories from `p` to `r`, recorded on the
  levels `c`.
* `morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords`: unbroken trajectories are broken
  trajectories with one component.
* `exists_tendsto_mem_morseBrokenTrajectoryRecords`: broken convergence of trajectories gives
  convergence of their records.
* `IsMorseSmale.closure_morseTrajectoryRecords_subset`: the limits of records of trajectories are
  records of broken trajectories.
* `IsMorseSmale.strictAnti_manifoldMorseIndex_of_chain`,
  `IsMorseSmale.add_manifoldMorseIndex_le_of_chain`: the Morse index drops strictly along a broken
  trajectory, which therefore has at most `ind p - ind r` components.
* `exists_homeomorph_morseTrajectoryRecords`,
  `exists_homeomorph_morseTrajectoryRecords_orbitQuotient`:
  the records of unbroken trajectories form a copy of a level slice and of the space of
  unparametrized trajectories.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories and their compactness).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (compactness of spaces of flow lines up to breaking).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The trajectories from `p` to `r` recorded on the levels `c`: the families `w` of points with
`f (w i) = c i` that all lie on the orbit of one point of `W^u(p) ∩ W^s(r)`. -/
def morseTrajectoryRecords (p r : M) (c : ι → ℝ) : Set (ι → M) :=
  {w | ∃ y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r,
    ∀ i, f (w i) = c i ∧ ∃ t, hX.flow t y = w i}

/-- The broken trajectories from `p` to `r` recorded on the levels `c`: the families `w` of points
with `f (w i) = c i` that each lie on a component of one broken trajectory. A broken trajectory is
a chain of critical points `p = x 0, …, x k = r`, consecutive ones distinct, with a point `z j`
of a trajectory from `x j` to `x (j + 1)` for each `j`. -/
def morseBrokenTrajectoryRecords (p r : M) (c : ι → ℝ) : Set (ι → M) :=
  {w | ∃ (k : ℕ) (x : Fin (k + 1) → M) (z : Fin k → M), x 0 = p ∧ x (Fin.last k) = r ∧
    (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧ (∀ j : Fin k, x j.castSucc ≠ x j.succ) ∧
    (∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) ∧
    ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i}

/-- Membership in the records of trajectories. -/
@[simp]
theorem mem_morseTrajectoryRecords {p r : M} {c : ι → ℝ} {w : ι → M} :
    w ∈ hX.morseTrajectoryRecords p r c ↔ ∃ y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r,
      ∀ i, f (w i) = c i ∧ ∃ t, hX.flow t y = w i :=
  Iff.rfl

/-- Membership in the records of broken trajectories. -/
@[simp]
theorem mem_morseBrokenTrajectoryRecords {p r : M} {c : ι → ℝ} {w : ι → M} :
    w ∈ hX.morseBrokenTrajectoryRecords p r c ↔
      ∃ (k : ℕ) (x : Fin (k + 1) → M) (z : Fin k → M), x 0 = p ∧ x (Fin.last k) = r ∧
        (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧ (∀ j : Fin k, x j.castSucc ≠ x j.succ) ∧
        (∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) ∧
        ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i :=
  Iff.rfl

/-- **Unbroken trajectories are broken trajectories with one component.** -/
theorem morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hpr : p ≠ r)
    (c : ι → ℝ) : hX.morseTrajectoryRecords p r c ⊆ hX.morseBrokenTrajectoryRecords p r c := by
  rintro w ⟨y, hy, hw⟩
  refine ⟨1, ![p, r], ![y], rfl, rfl, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun i ↦
    ⟨(hw i).1, 0, (hw i).2⟩⟩ <;> fin_cases j
  exacts [hp, hr, hpr, hy]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Along a chain of critical points from `p` to `r`, every regular level strictly between `f r`
and `f p` lies strictly between the values at the two ends of some step of the chain. -/
private theorem exists_lt_lt_of_chain {p r : M}
    {k : ℕ} {x : Fin (k + 1) → M} (hx0 : x 0 = p) (hxk : x (Fin.last k) = r)
    (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) {c : ℝ}
    (hreg : ∀ y, f y = c → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0) (hc : c ∈ Ioo (f r) (f p)) :
    ∃ j : Fin k, f (x j.succ) < c ∧ c < f (x j.castSucc) :=
  Fin.exists_succ_lt_lt_castSucc (g := fun j ↦ f (x j)) (fun j he ↦ hreg _ he (hxc j))
    (hx0 ▸ hc.2) (hxk ▸ hc.1)

/-- **Broken convergence gives convergence of the records.** Let `x`, `z` be a broken trajectory
from `p` to `r`, and `u a` points converging to it in the sense that for each component `j` the
points of their orbits at the times `s j a` converge to `z j`. If `w a` records the orbit of `u a`
on regular levels `c i` strictly between `f r` and `f p`, then the records `w a` converge to a
record of the broken trajectory: the point of `w a` on the level `c i` converges to the point where
the component crossing that level meets it. -/
theorem exists_tendsto_mem_morseBrokenTrajectoryRecords
    {p r : M} {c : ι → ℝ} (hreg : ∀ i y, f y = c i → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M}
    (hx0 : x 0 = p) (hxk : x (Fin.last k) = r) (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0)
    (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    {α : Type*} {l : Filter α} {u : α → M} {s : Fin k → α → ℝ}
    (hlim : ∀ j, Tendsto (fun a ↦ hX.flow (s j a) (u a)) l (𝓝 (z j)))
    {w : α → ι → M} (hw : ∀ a i, f (w a i) = c i ∧ ∃ t, hX.flow t (u a) = w a i) :
    ∃ w₀ ∈ hX.morseBrokenTrajectoryRecords p r c, Tendsto w l (𝓝 w₀) := by
  choose hwc t ht using hw
  -- For each level, the component crossing it, the time at which it does, and the convergence of
  -- the points of the records on that level.
  have key : ∀ i, ∃ (j : Fin k) (σ : ℝ), f (hX.flow σ (z j)) = c i ∧
      Tendsto (fun a ↦ w a i) l (𝓝 (hX.flow σ (z j))) := by
    intro i
    obtain ⟨j, hlo, hhi⟩ := exists_lt_lt_of_chain hx0 hxk hxc (hreg i) (hc i)
    -- The point of `w a` on the level `c i` is the point of the orbit of the shifted point at the
    -- time `t a i - s j a`.
    have hshift : ∀ a, hX.flow (t a i - s j a) (hX.flow (s j a) (u a)) = w a i := fun a ↦ by
      rw [← Flow.map_add, sub_add_cancel, ht]
    obtain ⟨σ, hσ, hlimσ⟩ := hX.exists_tendsto_flow_of_tendsto (hz j) hlo hhi (hlim j)
      (s := fun a ↦ t a i - s j a) fun a ↦ by rw [hshift]; exact hwc a i
    exact ⟨j, σ, hσ, hlimσ.congr hshift⟩
  choose j σ hσ hlimσ using key
  exact ⟨fun i ↦ hX.flow (σ i) (z (j i)),
    ⟨k, x, z, hx0, hxk, hxc, hxne, hz, fun i ↦ ⟨hσ i, j i, σ i, rfl⟩⟩, tendsto_pi_nhds.2 hlimσ⟩

/-- **The records of unbroken trajectories form a copy of a level slice.** Reading off the point on
the level `c i₀` identifies the records of trajectories from `p` to `r` on levels strictly between
`f r` and `f p` with the level slice `W^u(p) ∩ W^s(r) ∩ {f = c i₀}`. -/
theorem exists_homeomorph_morseTrajectoryRecords {p r : M} (hpr : p ≠ r) {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) (i₀ : ι) :
    ∃ Φ : hX.morseTrajectoryRecords p r c ≃ₜ
        ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {y | f y = c i₀}),
      ∀ w, (Φ w : M) = (w : ι → M) i₀ := by
  set C := hX.flow.unstableSet p ∩ hX.flow.stableSet r
  set S := C ∩ {y | f y = c i₀}
  -- The orbit of each point of `W^u(p) ∩ W^s(r)` meets the level `c i` at the unique time
  -- `τ i y`.
  set τ := fun i ↦ Flow.levelCrossingTime hX.flow f (c i)
  have hanti (y) (hy : y ∈ C) := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr hy
  have hex (i) (y) (hy : y ∈ C) : ∃ t, f (hX.flow t y) = c i :=
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr hy (hc i).1 (hc i).2).exists
  have hτ' (i) (y) (hy : y ∈ C) : f (hX.flow (τ i y) y) = c i :=
    Flow.apply_flow_levelCrossingTime (hex i y hy)
  -- The points on the other levels depend continuously on the point of the level `c i₀`.
  have hg : Continuous fun (y : S) i ↦ hX.flow (τ i y) (y : M) :=
    continuous_pi fun i ↦ hX.flow.continuous ((Flow.continuousOn_levelCrossingTime
      hX.mdifferentiable.continuous.continuousOn hanti (hex i)).comp_continuous
      continuous_subtype_val fun y ↦ y.2.1) continuous_subtype_val
  -- The point on the level `c i₀` is the point itself.
  have hτ₀ (y : S) : τ i₀ y = 0 :=
    (Flow.levelCrossingTime_eq_zero_iff (hanti y y.2.1) (hex i₀ y y.2.1)).2 y.2.2
  -- The point of a record on the level `c i₀` lies in the slice, and determines the record.
  have hmem : ∀ w ∈ hX.morseTrajectoryRecords p r c, w i₀ ∈ S := by
    rintro w ⟨y, hy, hw⟩
    obtain ⟨hwc, t, ht⟩ := hw i₀
    exact ⟨ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hy, hwc⟩
  have hrec : ∀ w ∈ hX.morseTrajectoryRecords p r c, ∀ i, hX.flow (τ i (w i₀)) (w i₀) = w i := by
    intro w hw i
    obtain ⟨y, hy, hw⟩ := hw
    obtain ⟨hwi, t, ht⟩ := hw i
    obtain ⟨-, t₀, ht₀⟩ := hw i₀
    have hflow : hX.flow (t - t₀) (w i₀) = w i := by rw [← ht₀, ← Flow.map_add, sub_add_cancel, ht]
    have hC : w i₀ ∈ C := ht₀ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t₀ hy
    have hτi : t - t₀ = τ i (w i₀) :=
      (Flow.eq_levelCrossingTime_iff (hanti _ hC) (hex i _ hC)).2 (by rw [hflow]; exact hwi)
    rw [← hτi, hflow]
  refine ⟨
    { toFun w := ⟨w.1 i₀, hmem w.1 w.2⟩
      invFun y := ⟨fun i ↦ hX.flow (τ i y) y, y, y.2.1, fun i ↦ ⟨hτ' i y y.2.1, τ i y, rfl⟩⟩
      left_inv w := Subtype.ext (funext (hrec w.1 w.2))
      right_inv y := Subtype.ext (by simp only [hτ₀, Flow.map_zero_apply])
      continuous_toFun := ((continuous_apply i₀).comp continuous_subtype_val).subtype_mk _
      continuous_invFun := hg.subtype_mk _ }, fun w ↦ rfl⟩

/-- **The records of unbroken trajectories form the space of unparametrized trajectories.** For a
nonempty family of levels strictly between `f r` and `f p`, the records of trajectories from `p` to
`r` are homeomorphic to the quotient of `W^u(p) ∩ W^s(r)` by the orbits of the flow. -/
theorem exists_homeomorph_morseTrajectoryRecords_orbitQuotient [Nonempty ι]
    {p r : M} (hpr : p ≠ r) {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) :
    Nonempty
      (hX.morseTrajectoryRecords p r c ≃ₜ Quotient (Flow.connectingOrbitSetoid hX.flow p r)) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨Φ, -⟩ := hX.exists_homeomorph_morseTrajectoryRecords hpr hc i₀
  obtain ⟨e, -⟩ := hX.exists_orbitQuotient_homeomorph_levelSlice hpr (hc i₀)
  exact ⟨Φ.trans e.symm⟩

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X}

/-- **The Morse index drops along a broken trajectory.** Under the Morse–Smale condition, the Morse
indices of the critical points of a broken trajectory decrease strictly. -/
theorem strictAnti_manifoldMorseIndex_of_chain (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M} (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) :
    StrictAnti fun j ↦ manifoldMorseIndex 𝓘(ℝ, E) f (x j) :=
  Fin.strictAnti_iff_succ_lt.2 fun j ↦ h.manifoldMorseIndex_lt hf (hxne j) ⟨z j, hz j⟩

/-- **A broken trajectory has at most `ind p - ind r` components.** Under the Morse–Smale
condition, a broken trajectory from `p` to `r` with `k` components has `k + ind r ≤ ind p`. -/
theorem add_manifoldMorseIndex_le_of_chain (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M} {k : ℕ} {x : Fin (k + 1) → M} {z : Fin k → M} (hx0 : x 0 = p)
    (hxk : x (Fin.last k) = r) (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ)) :
    k + manifoldMorseIndex 𝓘(ℝ, E) f r ≤ manifoldMorseIndex 𝓘(ℝ, E) f p := by
  -- Each step of the chain lowers the index by at least one.
  have := (h.strictAnti_manifoldMorseIndex_of_chain hf hxne hz).add_sub_le_nat
    (Fin.zero_le (Fin.last k))
  simp only [Fin.val_last, Fin.val_zero, Nat.sub_zero, hx0, hxk] at this
  omega

/-- **The compactified space of trajectories adds only broken trajectories.** Let `X` satisfy the
Morse–Smale condition, and record the trajectories from `p` to `r` on countably many levels `c i`
strictly between `f r` and `f p` that contain no critical point. Then every limit of records of
trajectories from `p` to `r` is the record of a broken trajectory from `p` to `r`. The Morse
indices along its chain of critical points decrease strictly
(`IsMorseSmale.strictAnti_manifoldMorseIndex_of_chain`), so a limit with `k` components has
`k + ind r ≤ ind p` (`IsMorseSmale.add_manifoldMorseIndex_le_of_chain`). Countability makes
`ι → M` metrizable, so that its closure is sequential. -/
theorem closure_morseTrajectoryRecords_subset [Countable ι] (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {p r : M} {c : ι → ℝ}
    (hreg : ∀ i y, f y = c i → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) :
    closure (hX.morseTrajectoryRecords p r c) ⊆ hX.morseBrokenTrajectoryRecords p r c := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  intro w hw
  obtain ⟨v, hv, hvw⟩ := mem_closure_iff_seq_limit.1 hw
  choose y hy hvy using hv
  -- A subsequence of the trajectories converges to a broken trajectory, along which the records
  -- converge.
  obtain ⟨k, x, z, s, n, hn, hx0, hxk, hxc, hxi, hz, -, hzlim⟩ :=
    h.exists_subseq_tendsto_broken hf y hy
  obtain ⟨w₀, hw₀, hlim⟩ :=
    hX.exists_tendsto_mem_morseBrokenTrajectoryRecords hreg hc hx0 hxk hxc
    (fun j he ↦ (hxi (Fin.castSucc_lt_succ (i := j))).ne (congrArg _ he.symm)) hz hzlim
    (w := v ∘ n) fun a ↦ hvy (n a)
  rwa [tendsto_nhds_unique (hvw.comp hn.tendsto_atTop) hlim]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
