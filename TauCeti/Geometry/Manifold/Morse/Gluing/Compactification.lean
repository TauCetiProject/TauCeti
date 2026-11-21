/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Broken
public import TauCeti.Geometry.Manifold.Morse.Stable.Compactification
import Mathlib.Geometry.Manifold.Metrizable

/-!
# Broken trajectories of any length are limits of unbroken ones

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. A broken trajectory from `p` to `r` is a chain
of critical points `p = x 0, …, x k = r`, consecutive ones distinct, with a point `z j` of a
trajectory from `x j` to `x (j + 1)` for each `j`. The compactified space of trajectories from `p`
to `r`, recorded on levels `c i` (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords`), adds
only broken trajectories (`IsMorseSmale.closure_morseTrajectoryRecords_subset`). This file proves
the converse, for any index difference and any number of breaks: every broken trajectory is a
limit of unbroken ones, so the compactified space is exactly the space of broken trajectories.

The proof glues one break at a time. The gluing theorem at a single break,
`IsMorseSmale.exists_mem_unstableSet_inter_stableSet_flow_mem`, holds with no condition on the
Morse indices: a trajectory from `p` to `q` and one from `q` to `r` are approximated, near any two
of their points, by one trajectory from `p` to `r`. By induction on the number of components, a
broken trajectory with components `z 0, …, z k` is approximated as follows: approximate the tail
`z 1, …, z k` by an unbroken trajectory `u` from `x 1` to `r`, which passes near each `z j` at some
time, and then glue `z 0` to `u` at `x 1`. A trajectory that passes near enough to `u` passes near
the same `z j` at shifted times, since the flow at a fixed time is continuous
(`IsMorseSmale.exists_mem_unstableSet_inter_stableSet_forall_flow_mem`). Along approximating
trajectories, the points on each level converge to the point where the component crossing that
level meets it
(`TauCeti.IsAdaptedPseudoGradient.tendsto_flow_of_tendsto_flow_of_mem_unstableSet_inter_stableSet`),
so the records converge to the record of the broken trajectory.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `exists_mem_unstableSet_inter_stableSet_forall_flow_mem`: a broken trajectory is a limit of
  unbroken ones in the sense of Morse theory: some trajectory from `p` to `r` passes, at suitable
  times, through any prescribed neighbourhoods of the points `z j`.
* `morseBrokenTrajectoryRecords_subset_closure`: the records of broken trajectories are limits of
  records of unbroken ones.
* `closure_morseTrajectoryRecords`: on countably many regular levels, the compactified space of
  trajectories from `p` to `r` is the space of broken trajectories.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories, and gluing).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the compactified moduli spaces of broken trajectories).
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

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Broken trajectories are limits of unbroken ones.** Let `x 0, …, x (k + 1)` be a chain of
critical points, consecutive ones distinct, and `z j` a point of a trajectory from `x j` to
`x (j + 1)` for each `j`. For any neighbourhoods `N j` of the points `z j` there is a trajectory
from `x 0` to `x (k + 1)` that passes through every `N j`: a point `u` of
`W^u(x 0) ∩ W^s(x (k + 1))` and times `s j` with `flow (s j) u ∈ N j`. -/
theorem exists_mem_unstableSet_inter_stableSet_forall_flow_mem {k : ℕ} {x : Fin (k + 2) → M}
    {z : Fin (k + 1) → M} (hxne : ∀ j : Fin (k + 1), x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin (k + 1),
      z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    {N : Fin (k + 1) → Set M} (hN : ∀ j, N j ∈ 𝓝 (z j)) :
    ∃ u ∈ hX.flow.unstableSet (x 0) ∩ hX.flow.stableSet (x (Fin.last (k + 1))),
      ∃ s : Fin (k + 1) → ℝ, ∀ j, hX.flow (s j) u ∈ N j := by
  induction k with
  | zero => exact ⟨z 0, by simpa using hz 0, fun _ ↦ 0, fun j ↦ by
      rw [Fin.fin_one_eq_zero j, Flow.map_zero_apply]; exact mem_of_mem_nhds (hN 0)⟩
  | succ k ih =>
    -- Approximate the tail `z 1, …, z (k + 1)`, from `x 1` to `x (k + 2)`, by an unbroken
    -- trajectory `u'` through the interiors of the neighbourhoods.
    obtain ⟨u', hu', s', hs'⟩ := ih (x := fun j ↦ x j.succ) (z := fun j ↦ z j.succ)
      (N := fun j ↦ interior (N j.succ)) (fun j ↦ by simpa using hxne j.succ)
      (fun j ↦ by simpa using hz j.succ) fun j ↦ interior_mem_nhds.2 (hN j.succ)
    simp only [Fin.succ_zero_eq_one, Fin.succ_last] at hu'
    -- The values of `f` decrease strictly along the chain, so `x 1 ≠ x (k + 2)`.
    have hanti : StrictAnti fun j ↦ f (x j) := Fin.strictAnti_iff_succ_lt.2 fun j ↦
      (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)).1.trans
        (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)).2
    have h1 : x 1 ≠ x (Fin.last (k + 2)) := fun he ↦ (hanti (show (1 : Fin (k + 3)) <
      Fin.last (k + 2) from Fin.one_lt_last)).ne' (congrArg f he)
    -- Trajectories through a small neighbourhood `O` of `u'` pass through the same neighbourhoods
    -- at the same times.
    set O := ⋂ j, (hX.flow (s' j)) ⁻¹' interior (N j.succ)
    have hO : O ∈ 𝓝 u' := (isOpen_iInter_of_finite fun j ↦ isOpen_interior.preimage
      (hX.flow.continuous_toFun (s' j))).mem_nhds (mem_iInter.2 hs')
    -- Glue the first component `z 0` to `u'` at `x 1`.
    obtain ⟨v, hv, σ₁, σ₂, hv₁, hv₂⟩ := h.exists_mem_unstableSet_inter_stableSet_flow_mem hf
      (by simpa using hxne 0) h1 (by simpa using hz 0) hu' (hN 0) hO
    refine ⟨v, hv, Fin.cases σ₁ fun j ↦ s' j + σ₂, fun j ↦ ?_⟩
    induction j using Fin.cases with
    | zero => simpa using hv₁
    | succ j =>
      simp only [Fin.cases_succ]
      rw [Flow.map_add]
      exact interior_subset (mem_iInter.1 hv₂ j)

include h hf in
/-- **Broken trajectories are limits of unbroken ones, on levels.** Record the trajectories from
`p` to `r`, with `p ≠ r`, on levels `c i` strictly between `f r` and `f p`. Then every record of a
broken trajectory from `p` to `r` is a limit of records of unbroken trajectories. -/
theorem morseBrokenTrajectoryRecords_subset_closure {p r : M} (hpr : p ≠ r) {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) :
    hX.morseBrokenTrajectoryRecords p r c ⊆ closure (hX.morseTrajectoryRecords p r c) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  intro w hw
  obtain ⟨k, x, z, hx0, hxk, -, hxne, hz, hwi⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  -- A broken trajectory from `p` to `r ≠ p` has at least one component.
  obtain _ | k := k
  · exact absurd (hx0.symm.trans hxk) hpr
  subst hx0 hxk
  -- Unbroken trajectories `u n` passing at times `s n j` through the `n`-th neighbourhoods of a
  -- countable basis at each `z j`.
  choose B hB using fun j ↦ (𝓝 (z j)).exists_antitone_basis
  choose u hu s hs using fun n ↦
    h.exists_mem_unstableSet_inter_stableSet_forall_flow_mem hf hxne hz (N := fun j ↦ B j n)
      fun j ↦ (hB j).mem n
  have hlim (j : Fin (k + 1)) : Tendsto (fun n ↦ hX.flow (s n j) (u n)) atTop (𝓝 (z j)) :=
    (hB j).tendsto fun n ↦ hs n j
  -- Their records.
  choose τ hτ using fun n i ↦
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr (hu n) (hc i).1 (hc i).2).exists
  refine mem_closure_of_tendsto (b := atTop) (f := fun n i ↦ hX.flow (τ n i) (u n))
    (tendsto_pi_nhds.2 fun i ↦ ?_)
    (.of_forall fun n ↦ hX.mem_morseTrajectoryRecords.2 ⟨u n, hu n, fun i ↦ ⟨hτ n i, τ n i, rfl⟩⟩)
  -- The point on the level `c i` converges to the point where the component through `w i` meets
  -- that level, which is `w i`.
  obtain ⟨hwc, j, t, ht⟩ := hwi i
  rw [← ht]
  exact hX.tendsto_flow_of_tendsto_flow_of_mem_unstableSet_inter_stableSet (hxne j) (hz j)
    (by rw [ht, hwc]) (hlim j) fun n ↦ hτ n i

include h hf in
/-- **The compactified space of trajectories is the space of broken trajectories.** Let `X` satisfy
the Morse–Smale condition, and record the trajectories from `p` to `r`, with `p ≠ r`, on countably
many levels `c i` strictly between `f r` and `f p` that contain no critical point. Then the closure
of the records of trajectories from `p` to `r` is exactly the set of records of broken
trajectories from `p` to `r`, whatever the difference of the Morse indices of `p` and `r`. -/
theorem closure_morseTrajectoryRecords [Countable ι] {p r : M} (hpr : p ≠ r) {c : ι → ℝ}
    (hreg : ∀ i y, f y = c i → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0)
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) :
    closure (hX.morseTrajectoryRecords p r c) = hX.morseBrokenTrajectoryRecords p r c :=
  (h.closure_morseTrajectoryRecords_subset hf hreg hc).antisymm
    (h.morseBrokenTrajectoryRecords_subset_closure hf hpr hc)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
