/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Perturbing a map near one point of an orbit

Let `φ` be a self-map, `p` a point and `k > 0`. A perturbation `ψ` which fixes `p` and is the
identity near the later orbit points `φ^[j] p`, `0 < j < k`, changes the `k`-th iterate near `p`
only by precomposition: near `p`,

`(φ ∘ ψ)^[k] = φ^[k] ∘ ψ`

(`Function.iterate_comp_eventuallyEq_of_eventuallyEq_id`). Indeed the orbit of a point near `p`
under `φ ∘ ψ` passes through the neighbourhoods of the points `φ^[j] p`, where `ψ` does nothing.
The same holds for a perturbation that moves `p`, such as a small translation, provided it is the
identity near the later points `φ^[j] (ψ p)` of the orbit of `ψ p`
(`Function.iterate_comp_eventuallyEq_iterate_comp`); pointwise, it suffices that `ψ` fixes these
points (`Function.iterate_comp_apply_eq_iterate_apply`). In particular, if `ψ` is the translation by
`c` near `p`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `w ↦ φ^[k] (w + c)`
(`Function.iterate_comp_eventuallyEq_comp_add`).

When `p` is a periodic point of period `k`, the derivative of `φ^[k]` at `p` is the linearized
return map of its orbit. The return map of the perturbed map `φ ∘ ψ` is then the return map of
`φ` composed with the derivative of `ψ` at `p`
(`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). This is how a perturbation supported in a small
neighbourhood of one point of a periodic orbit, for instance a Hamiltonian twist, changes the
linearized return map of that orbit.

Such localized perturbations need neighbourhoods of `p` that the orbits starting in them leave
before returning. Near a point of least period `k` of a continuous self-map of a metric space,
small closed balls are left by every orbit starting in them until time `k`
(`TauCeti.exists_pos_closedBall_subset_and_iterate_notMem`).

The hypotheses on the later orbit points hold for all points near `p` when `p` is not fixed by any
`φ^[j]`, `0 < j < k`: in a metric space, the orbits of the points of every small enough ball around
`p` leave that ball until time `k`, with a margin proportional to its radius
(`Continuous.eventually_forall_mul_le_dist_iterate`).
-/

public section

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X] {φ ψ : X → X} {p : X} {k : ℕ}

omit [TopologicalSpace X] in
/-- **Iterates of a map perturbed off an orbit, pointwise.** If `ψ` fixes the later points
`φ^[j] (ψ p)`, `0 < j < k`, of the orbit of `ψ p`, then the `k`-th iterate of `φ ∘ ψ` at `p` is
`φ^[k] (ψ p)`. -/
theorem iterate_comp_apply_eq_iterate_apply (hk : 0 < k)
    (hψ : ∀ j, 0 < j → j < k → ψ (φ^[j] (ψ p)) = φ^[j] (ψ p)) : (φ ∘ ψ)^[k] p = φ^[k] (ψ p) := by
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih (by omega) fun j hj hjk ↦ hψ j hj (by omega), comp_apply,
      hψ (k + 1) (by omega) (by omega), ← iterate_succ_apply' φ]

/-- **Iterates of a map perturbed near the later points of an orbit.** If `ψ` is continuous at
`p` and is the identity near `φ^[j] (ψ p)` for `0 < j < k`, and `φ` is continuous at the orbit
points `φ^[j] (ψ p)` for `j < k`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `φ^[k] ∘ ψ`. The
perturbation need not fix `p`: the orbit that matters is the `φ`-orbit of `ψ p`. -/
theorem iterate_comp_eventuallyEq_iterate_comp (hk : 0 < k) (hψ : ContinuousAt ψ p)
    (hφ : ∀ j < k, ContinuousAt φ (φ^[j] (ψ p)))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] (ψ p))] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] φ^[k] ∘ ψ := by
  have hcont : ∀ j ≤ k, ContinuousAt φ^[j] (ψ p) := by
    intro j hj
    induction j with
    | zero => exact continuousAt_id
    | succ j ih =>
      rw [iterate_succ']
      exact (hφ j (by omega)).comp (ih (by omega))
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  -- Induction on the number `j + 1 ≤ k + 1` of iterations.
  suffices h : ∀ j ≤ k, (φ ∘ ψ)^[j + 1] =ᶠ[𝓝 p] φ^[j + 1] ∘ ψ from h k le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have hc : ContinuousAt (φ^[j + 1] ∘ ψ) p := (hcont (j + 1) (by omega)).comp hψ
    have hψj : ψ ∘ (φ^[j + 1] ∘ ψ) =ᶠ[𝓝 p] φ^[j + 1] ∘ ψ :=
      hc.eventually (hid (j + 1) (by omega) (by omega))
    rw [iterate_succ', iterate_succ' φ]
    filter_upwards [ih (by omega), hψj] with x hx hx'
    simp only [comp_apply] at hx hx' ⊢
    rw [hx, hx']

/-- **Iterates of a map perturbed near one point of an orbit.** If `ψ` fixes `p`, is continuous at
`p` and is the identity near `φ^[j] p` for `0 < j < k`, and `φ` is continuous at the orbit points
`φ^[j] p` for `j < k`, then near `p` the `k`-th iterate of `φ ∘ ψ` is `φ^[k] ∘ ψ`. -/
theorem iterate_comp_eventuallyEq_of_eventuallyEq_id (hk : 0 < k) (hψp : ψ p = p)
    (hψ : ContinuousAt ψ p) (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] p)] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] φ^[k] ∘ ψ :=
  iterate_comp_eventuallyEq_iterate_comp hk hψ (by simpa only [hψp] using hφ)
    (by simpa only [hψp] using hid)

/-- **Iterates of a map perturbed by a local translation.** If `ψ` is the translation by `c` near
`p` and the identity near the later points `φ^[j] (p + c)`, `0 < j < k`, of the orbit of `p + c`,
and `φ` is continuous at the orbit points `φ^[j] (p + c)` for `j < k`, then near `p` the `k`-th
iterate of `φ ∘ ψ` is `w ↦ φ^[k] (w + c)`. -/
theorem iterate_comp_eventuallyEq_comp_add [Add X] [ContinuousAdd X] (hk : 0 < k) {c : X}
    (hadd : ψ =ᶠ[𝓝 p] fun w ↦ w + c) (hφ : ∀ j < k, ContinuousAt φ (φ^[j] (p + c)))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] (p + c))] id) :
    (φ ∘ ψ)^[k] =ᶠ[𝓝 p] fun w ↦ φ^[k] (w + c) := by
  rw [← hadd.eq_of_nhds] at hφ hid
  exact (iterate_comp_eventuallyEq_iterate_comp hk
    ((continuous_id.add continuous_const).continuousAt.congr_of_eventuallyEq hadd) hφ hid).trans
    (hadd.fun_comp φ^[k])

end Function

namespace Continuous

variable {X : Type*} [MetricSpace X] {φ : X → X} {p : X} {k : ℕ}

/-- **Orbits leave small balls with a margin.** If no iterate `φ^[j] p` with `0 < j < k` equals
`p`, then for every `c` and all small enough `ρ > 0`, the points `φ^[j] y` with
`y ∈ closedBall p ρ` and `0 < j < k` lie at distance at least `c * ρ` from `p`. -/
theorem eventually_forall_mul_le_dist_iterate (hφ : Continuous φ)
    (hp : ∀ j, 0 < j → j < k → φ^[j] p ≠ p) (c : ℝ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ j, 0 < j → j < k → ∀ y ∈ Metric.closedBall p ρ,
      c * ρ ≤ dist (φ^[j] y) p := by
  have hc : Tendsto (fun ρ : ℝ ↦ c * ρ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul c)
  refine ((eventually_all_finset (Finset.Ioo 0 k)).2 fun j hj ↦ ?_).mono fun ρ h j hj hjk ↦
    h j (Finset.mem_Ioo.2 ⟨hj, hjk⟩)
  obtain ⟨hj, hjk⟩ := Finset.mem_Ioo.1 hj
  -- The iterate `φ^[j] p` lies at distance `d > 0` from `p`; points near `p` stay within `d / 2`.
  have hd : 0 < dist (φ^[j] p) p := dist_pos.2 (hp j hj hjk)
  obtain ⟨θ, hθ, hcont⟩ := Metric.continuousAt_iff.1 ((hφ.iterate j).continuousAt (x := p))
    _ (half_pos hd)
  filter_upwards [hc.eventually (gt_mem_nhds (half_pos hd)),
    nhdsWithin_le_nhds (gt_mem_nhds hθ)] with ρ hcρ hρθ y hy
  have h := hcont ((Metric.mem_closedBall.1 hy).trans_lt hρθ)
  linarith [dist_triangle (φ^[j] p) (φ^[j] y) p, dist_comm (φ^[j] p) (φ^[j] y)]

end Continuous

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {φ ψ : E → E} {p : E} {k : ℕ} {A B : E →L[𝕜] E}

/-- **The linearized return map of a locally perturbed map.** If `ψ` fixes `p` and is the identity
near the orbit points `φ^[j] p`, `0 < j < k`, then the derivative at `p` of the `k`-th iterate
of `φ ∘ ψ` is the derivative of `φ^[k]` at `p` composed with that of `ψ`. -/
theorem HasFDerivAt.iterate_comp_of_eventuallyEq_id (hA : HasFDerivAt φ^[k] A p)
    (hB : HasFDerivAt ψ B p) (hk : 0 < k) (hψp : ψ p = p)
    (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p))
    (hid : ∀ j, 0 < j → j < k → ψ =ᶠ[𝓝 (φ^[j] p)] id) :
    HasFDerivAt (φ ∘ ψ)^[k] (A.comp B) p := by
  rw [← hψp] at hA
  exact (hA.comp p hB).congr_of_eventuallyEq
    (Function.iterate_comp_eventuallyEq_of_eventuallyEq_id hk hψp hB.continuousAt hφ hid)

namespace TauCeti

open Metric

/-! ### Small balls around points of least period `k` -/

/-- Around a point `x ∈ W` whose first `k - 1` iterates under a continuous self-map `φ` of a
metric space differ from it, the closed balls of small enough radius `r` lie in `W` and are left
by every orbit starting in them until time `k`. -/
theorem exists_pos_closedBall_subset_and_iterate_notMem {X : Type*} [MetricSpace X] {φ : X → X}
    (hφ : Continuous φ) {W : Set X} (hW : IsOpen W) {x : X} (hx : x ∈ W) {k : ℕ}
    (hmin : ∀ j, 0 < j → j < k → φ^[j] x ≠ x) :
    ∃ r > 0, closedBall x r ⊆ W ∧
      ∀ y ∈ closedBall x r, ∀ j, 0 < j → j < k → φ^[j] y ∉ closedBall x r := by
  suffices h : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ W ∧
      ∀ j ∈ Finset.range k, 0 < j → ∀ y ∈ closedBall x r, φ^[j] y ∉ closedBall x r by
    obtain ⟨r, ⟨hrW, hr⟩, hr0⟩ := (h.and self_mem_nhdsWithin).exists
    exact ⟨r, hr0, hrW, fun y hy j hj hjk ↦ hr j (Finset.mem_range.2 hjk) hj y hy⟩
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x hx
  refine Filter.Eventually.and ?_ ((Finset.eventually_all _).2 fun j hj ↦ ?_)
  · filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    exact (closedBall_subset_ball hr.2).trans hρW
  · -- With `d = dist (φ^[j] x) x > 0`, take `r < d / 2` and `r` below a radius on which
    -- `φ^[j]` moves points by less than `d / 2`.
    by_cases hj0 : 0 < j
    · have hd : 0 < dist (φ^[j] x) x :=
        dist_pos.2 (hmin j hj0 (Finset.mem_range.1 hj))
      obtain ⟨ρ', hρ', hcont⟩ := Metric.continuousAt_iff.1 (hφ.iterate j).continuousAt
        (dist (φ^[j] x) x / 2) (half_pos hd)
      filter_upwards [Ioo_mem_nhdsGT (lt_min hρ' (half_pos hd))] with r hr _ y hy
      rw [mem_closedBall] at hy ⊢
      have hr₁ := hr.2.trans_le (min_le_left _ _)
      have hr₂ := hr.2.trans_le (min_le_right _ _)
      have h := hcont (hy.trans_lt (by linarith))
      have := dist_triangle (φ^[j] x) (φ^[j] y) x
      rw [dist_comm] at h
      linarith
    · exact Eventually.of_forall fun r h ↦ absurd h hj0

end TauCeti
