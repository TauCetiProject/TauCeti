/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory

/-!
# Level slices of the trajectory spaces of the Euclidean quartic

Let `p ≠ q` be critical points of the Euclidean quartic `TauCeti.quarticWellSum` on `ι → ℝ`, with
`q` obtained from `p` by replacing some zero coordinates by `±1`. The time-shift chart
`TauCeti.quarticTrajectoryPoint p q` parametrizes the points of the cube `[-1, 1]^ι` on
trajectories from `p` to `q`, and the flow translates the time shifts along the diagonal
(`TauCeti.Analysis.Calculus.Morse.Quartic.Trajectory`). This file shows that each trajectory from
`p` to `q` crosses each level strictly between the critical values exactly once. This is the fact
underlying the description of the unparametrized trajectories as the points of a level slice,
which is not formalized here.

* **Free action.** The flow fixes no point of a trajectory from `p` to `q` for a nonzero time
  (`TauCeti.quarticWellSumFlow_quarticTrajectoryPoint_eq_self_iff`).
* **Strict decrease.** On each moving coordinate the summand `(yᵢ² - 1)² / 4` along the reference
  trajectory is `σ(-2 u)² / 4` for the sigmoid `σ`, which decreases strictly in the time `u`. So
  the quartic decreases strictly along every trajectory from `p` to `q`
  (`TauCeti.strictAnti_quarticWellSum_quarticWellSumFlow_quarticTrajectoryPoint`).
* **Level slices.** Each trajectory from `p` to `q` crosses every level strictly between the
  values at `q` and at `p` exactly once
  (`TauCeti.existsUnique_quarticWellSum_quarticWellSumFlow_eq_iff`).

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.2 (unparametrized trajectories as points of a level set).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {ι : Type*} {p q : ι → ℝ}

/-- **The translation action is free**: for `p ≠ q`, the flow moves every point of a trajectory
from `p` to `q` for every nonzero time. -/
theorem quarticWellSumFlow_quarticTrajectoryPoint_eq_self_iff
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0)
    (hne : p ≠ q) {s : ℝ} {τ : {i // p i ≠ q i} → ℝ} :
    quarticWellSumFlow s (quarticTrajectoryPoint p q τ) = quarticTrajectoryPoint p q τ ↔
      s = 0 := by
  rw [quarticWellSumFlow_quarticTrajectoryPoint hq hpq,
    (quarticTrajectoryPoint_injective hq hpq).eq_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  simpa using congrFun h ⟨i, hi⟩

/-- On a moving coordinate the quartic summand of `quarticTrajectoryPoint p q τ` is
`σ(-2 τ j)² / 4`, for the sigmoid `σ`. -/
private theorem intervalBasePotential_quarticTrajectoryPoint_coe
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0)
    (τ : {i // p i ≠ q i} → ℝ) (j : {i // p i ≠ q i}) :
    intervalBasePotential 1 (quarticTrajectoryPoint p q τ j) =
      Real.sigmoid (-(2 * 1 * τ j)) ^ 2 / 4 := by
  have hqj := eq_neg_one_or_eq_one_of_ne hq hpq j.property
  have hsq : quarticTrajectoryPoint p q τ j ^ 2 = intervalBaseOrbit 1 (τ j) ^ 2 := by
    rw [quarticTrajectoryPoint_apply_coe]
    rcases hqj with h | h <;> rw [h] <;> ring
  rw [intervalBasePotential_apply, hsq, ← one_sub_intervalBaseOrbit_sq]
  ring

variable [Fintype ι]

/-- **The quartic decreases strictly along the trajectories** from `p` to `q`, for `p ≠ q`. -/
theorem strictAnti_quarticWellSum_quarticWellSumFlow_quarticTrajectoryPoint
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0)
    (hne : p ≠ q) (τ : {i // p i ≠ q i} → ℝ) :
    StrictAnti fun s ↦ quarticWellSum (quarticWellSumFlow s (quarticTrajectoryPoint p q τ)) := by
  intro s r hsr
  simp only [quarticWellSumFlow_quarticTrajectoryPoint hq hpq, quarticWellSum_def]
  -- On a moving coordinate the summand `σ(-2 (s + τ j))² / 4` decreases strictly.
  have hlt : ∀ j : {i // p i ≠ q i},
      intervalBasePotential 1 (quarticTrajectoryPoint p q (fun j ↦ r + τ j) j) <
        intervalBasePotential 1 (quarticTrajectoryPoint p q (fun j ↦ s + τ j) j) := fun j ↦ by
    rw [intervalBasePotential_quarticTrajectoryPoint_coe hq hpq,
      intervalBasePotential_quarticTrajectoryPoint_coe hq hpq]
    have h := Real.sigmoid_strictMono (show -(2 * 1 * (r + τ j)) < -(2 * 1 * (s + τ j)) by
      linarith)
    have h0 := Real.sigmoid_pos (-(2 * 1 * (r + τ j)))
    gcongr
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hne
  refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, hlt ⟨i₀, hi₀⟩⟩
  by_cases hi : p i = q i
  · rw [quarticTrajectoryPoint_apply_of_eq _ hi, quarticTrajectoryPoint_apply_of_eq _ hi]
  · exact (hlt ⟨i, hi⟩).le

/-- **Level slices of the trajectory spaces.** The levels of the quartic crossed exactly once
along each trajectory from `p` to `q` are exactly those strictly between its values at `q` and at
`p`. For `p = q` no level is crossed exactly once, since the trajectory is constant. -/
theorem existsUnique_quarticWellSum_quarticWellSumFlow_eq_iff
    (hq : ∀ i, q i = -1 ∨ q i = 0 ∨ q i = 1) (hpq : ∀ i, p i ≠ q i → p i = 0)
    (τ : {i // p i ≠ q i} → ℝ) {c : ℝ} :
    (∃! s, quarticWellSum (quarticWellSumFlow s (quarticTrajectoryPoint p q τ)) = c) ↔
      c ∈ Ioo (quarticWellSum q) (quarticWellSum p) := by
  set g := fun s ↦ quarticWellSum (quarticWellSumFlow s (quarticTrajectoryPoint p q τ))
  obtain rfl | hne := eq_or_ne p q
  · -- For `p = q` the trajectory is constant, so no level is crossed exactly once.
    have hconst : ∀ s, g s = g 0 := fun s ↦ by
      simp only [g, quarticWellSumFlow_quarticTrajectoryPoint hq hpq]
      congr 2
      funext j
      exact (j.property rfl).elim
    simp only [Ioo_self, mem_empty_iff_false, iff_false]
    rintro ⟨s, hs, huniq⟩
    have := huniq (s + 1) ((hconst _).trans ((hconst s).symm.trans hs))
    linarith
  have hanti : StrictAnti g :=
    strictAnti_quarticWellSum_quarticWellSumFlow_quarticTrajectoryPoint hq hpq hne τ
  obtain ⟨hmem, hlimbot, hlimtop⟩ :=
    mem_quarticConnectingSet.1 (quarticTrajectoryPoint_mem_quarticConnectingSet hq hpq τ)
  have hbot : Tendsto g atBot (𝓝 (quarticWellSum p)) :=
    (continuous_quarticWellSum.tendsto p).comp hlimbot
  have htop : Tendsto g atTop (𝓝 (quarticWellSum q)) :=
    (continuous_quarticWellSum.tendsto q).comp hlimtop
  have hflow : Continuous fun s ↦ quarticWellSumFlow s (quarticTrajectoryPoint p q τ) :=
    continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_quarticWellSumFlow hmem s).continuousAt
  have hcont : Continuous g := by fun_prop
  refine ⟨fun ⟨s, hs, _⟩ ↦ hs ▸ ⟨?_, ?_⟩, fun hc ↦ ?_⟩
  · exact (hanti.antitone.le_of_tendsto htop (s + 1)).trans_lt (hanti (lt_add_one s))
  · exact (hanti (sub_one_lt s)).trans_le (hanti.antitone.ge_of_tendsto hbot (s - 1))
  · obtain ⟨a, ha⟩ := (hbot.eventually (lt_mem_nhds hc.2)).exists
    obtain ⟨b, hb⟩ := (htop.eventually (gt_mem_nhds hc.1)).exists
    obtain ⟨s, hs⟩ := intermediate_value_univ b a hcont ⟨hb.le, ha.le⟩
    exact ⟨s, hs, fun r hr ↦ hanti.injective (hr.trans hs.symm)⟩

end TauCeti
