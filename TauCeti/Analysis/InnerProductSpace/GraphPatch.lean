/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Topology.Order.OrderClosed
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The closure and frontier of a domain inside a graph patch

Let `ν ≠ 0` be a vector of a real inner product space and `γ` a function invariant under translation
along `ν`. The region `{z | γ z < ⟪z, ν⟫}` lies above the graph `{z | ⟪z, ν⟫ = γ z}` of a function
over the hyperplane `ν^⊥`. A domain `Ω` has a *graph patch* on an open set `U` when

`U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}`,

which is how a domain with `C^k` boundary is described near a boundary point. Inside such a patch:

* every point on or above the graph lies in the closure of `Ω`
  (`TauCeti.inter_setOf_le_inner_subset_closure`); no regularity of `γ` is needed, since such a
  point `y` is the limit of the points `y + t ν`, `t > 0`, which lie strictly above it;
* if `γ` is continuous on `U`, the closure of `Ω` is the closed region `{z | γ z ≤ ⟪z, ν⟫}`
  (`TauCeti.inter_closure_eq_inter_setOf_le_inner`), and the frontier of `Ω` is the graph
  `{z | ⟪z, ν⟫ = γ z}` (`TauCeti.inter_frontier_eq_inter_setOf_inner_eq`); `Ω` need not be open,
  since the patch makes `U ∩ Ω` open.

If `ν` is a unit vector and `γ` is `G`-Lipschitz on `U`, a point `z` of the closure of `Ω` is the
vertex of a cone in `Ω` with axis `ν`: the closed ball of radius `t / (2 (G + 1))` about `z + t ν`
lies in `Ω` as long as `closedBall z (2 t) ⊆ U`
(`TauCeti.closedBall_add_smul_subset_of_inter_eq`), because moving up by `t` along `ν` gains
height `t`, while within that ball the graph rises by at most `G t / (2 (G + 1))` and the height
drops by at most `t / (2 (G + 1))`. When `Ω` has compact closure and a patch of this kind at every
frontier point, finitely many patches and a Lebesgue number of the cover give one height and one
aperture for all points of the closure: `Ω` satisfies a uniform interior cone condition
(`TauCeti.exists_forall_closedBall_add_smul_subset`). This is the geometric input for
interpolation inequalities up to the boundary.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (domains with `C^{k,α}` boundary) and Section 6.8 (interpolation up to the boundary).
-/

public section

open Set Filter Topology Metric
open scoped InnerProductSpace NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {U Ω : Set E} {ν : E}
  {γ : E → ℝ}

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` invariant
along `ν ≠ 0`, every point on or above the graph of `γ` lies in the closure of `Ω`: such a point
`y` is the limit of the points `y + t ν`, `t > 0`, which lie strictly above it. -/
theorem inter_setOf_le_inner_subset_closure (hU : IsOpen U) (hν : ν ≠ 0)
    (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z) (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} ⊆ closure Ω := by
  rintro y ⟨hy, hle : γ y ≤ ⟪y, ν⟫_ℝ⟩
  -- Approach `y` along `ν` from above.
  have ht : Tendsto (fun t : ℝ => y + t • ν) (𝓝[>] 0) (𝓝 y) := by
    have h0 : Tendsto (fun t : ℝ => y + t • ν) (𝓝 0) (𝓝 (y + (0 : ℝ) • ν)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht (hU.mem_nhds hy), self_mem_nhdsWithin] with t htU htpos
  have hmem : y + t • ν ∈ U ∩ Ω := by
    rw [hΩ]
    refine ⟨htU, ?_⟩
    rw [mem_ofPred_eq, hγν, inner_add_left, real_inner_smul_left]
    have hνν : 0 < ⟪ν, ν⟫_ℝ := real_inner_self_pos.2 hν
    have ht0 : (0 : ℝ) < t := htpos
    linarith [mul_pos ht0 hνν]
  exact hmem.2

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` continuous
on `U` and invariant along `ν ≠ 0`, the closure of `Ω` is the closed region on or above the graph
of `γ`. -/
theorem inter_closure_eq_inter_setOf_le_inner (hU : IsOpen U) (hν : ν ≠ 0)
    (hγ : ContinuousOn γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ closure Ω = U ∩ {z | γ z ≤ ⟪z, ν⟫_ℝ} :=
  Subset.antisymm
    (fun _ hy => ⟨hy.1, inter_closure_subset_setOf_le hU hγ
      (continuous_id.inner continuous_const).continuousOn hΩ hy⟩)
    (fun _ hy => ⟨hy.1, inter_setOf_le_inner_subset_closure hU hν hγν hΩ hy⟩)

/-- Inside a graph patch `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}` on an open set `U`, with `γ` continuous
on `U` and invariant along `ν ≠ 0`, the frontier of `Ω` is the graph of `γ`. -/
theorem inter_frontier_eq_inter_setOf_inner_eq (hU : IsOpen U) (hν : ν ≠ 0)
    (hγ : ContinuousOn γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    U ∩ frontier Ω = U ∩ {z | ⟪z, ν⟫_ℝ = γ z} := by
  have hcl := Set.ext_iff.1 (inter_closure_eq_inter_setOf_le_inner hU hν hγ hγν hΩ)
  -- The patch makes `U ∩ Ω` open, so its points are interior points of `Ω`.
  have hUΩ : IsOpen (U ∩ Ω) := by
    have hf : ContinuousOn (fun z => ⟪z, ν⟫_ℝ - γ z) U :=
      (continuous_id.inner continuous_const).continuousOn.sub hγ
    have := hf.isOpen_inter_preimage hU (isOpen_Ioi (a := (0 : ℝ)))
    rwa [hΩ, show {z | γ z < ⟪z, ν⟫_ℝ} = (fun z => ⟪z, ν⟫_ℝ - γ z) ⁻¹' Ioi 0 by
      ext; simp [sub_pos]]
  ext y
  constructor
  · rintro ⟨hy, hycl, hynΩ⟩
    have hle : γ y ≤ ⟪y, ν⟫_ℝ := ((hcl y).1 ⟨hy, hycl⟩).2
    -- A point of `U` strictly above the graph lies in the interior of `Ω`.
    refine ⟨hy, le_antisymm (not_lt.1 fun hlt => hynΩ ?_) hle⟩
    have hyΩ : y ∈ U ∩ Ω := hΩ ▸ ⟨hy, hlt⟩
    exact interior_maximal inter_subset_right hUΩ hyΩ
  · rintro ⟨hy, heq⟩
    refine ⟨hy, ((hcl y).2 ⟨hy, heq.ge⟩).2, fun hyΩ => ?_⟩
    -- A point of `U ∩ Ω` lies strictly above the graph.
    exact (((Set.ext_iff.1 hΩ y).1 ⟨hy, interior_subset hyΩ⟩).2 : γ y < ⟪y, ν⟫_ℝ).ne heq.symm

/-- **An interior cone at a point of a graph patch.** Let `U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫}`, with
`ν` a unit vector and `γ` invariant along `ν` and `G`-Lipschitz on `U`. If `z` lies in the closure
of `Ω`, `t > 0` and `closedBall z (2 t) ⊆ U`, then the closed ball of radius `t / (2 (G + 1))`
about `z + t ν` lies in `Ω`. -/
theorem closedBall_add_smul_subset_of_inter_eq (hν : ‖ν‖ = 1) {G : ℝ≥0}
    (hγ : LipschitzOnWith G γ U) (hγν : ∀ z (t : ℝ), γ (z + t • ν) = γ z)
    (hΩ : U ∩ Ω = U ∩ {z | γ z < ⟪z, ν⟫_ℝ}) {z : E} (hz : z ∈ closure Ω) {t : ℝ} (ht : 0 < t)
    (hzU : closedBall z (2 * t) ⊆ U) :
    closedBall (z + t • ν) (t / (2 * (G + 1))) ⊆ Ω := by
  have hG : (0 : ℝ) < 2 * (G + 1) := by positivity
  -- `z` lies on or above the graph: the patch restricts to the open ball `ball z (2 t) ⊆ U`.
  have hBU : ball z (2 * t) ⊆ U := ball_subset_closedBall.trans hzU
  have hΩB : ball z (2 * t) ∩ Ω = ball z (2 * t) ∩ {z | γ z < ⟪z, ν⟫_ℝ} := by
    ext w
    have hw := Set.ext_iff.1 hΩ w
    simp only [mem_inter_iff] at hw ⊢
    exact ⟨fun h => ⟨h.1, (hw.1 ⟨hBU h.1, h.2⟩).2⟩, fun h => ⟨h.1, (hw.2 ⟨hBU h.1, h.2⟩).2⟩⟩
  have hzγ : γ z ≤ ⟪z, ν⟫_ℝ := inter_closure_subset_setOf_le isOpen_ball
    (hγ.continuousOn.mono hBU) (continuous_id.inner continuous_const).continuousOn hΩB
    ⟨mem_ball_self (by positivity), hz⟩
  intro w hw
  set y := z + t • ν
  have hwy : dist w y * (2 * (G + 1)) ≤ t := (le_div_iff₀ hG).1 (mem_closedBall.1 hw)
  have hyz : dist y z = t := by simp [y, dist_eq_norm, norm_smul, hν, abs_of_pos ht]
  have hwU : w ∈ U := hzU (mem_closedBall.2 (by nlinarith [dist_triangle w y z, G.coe_nonneg]))
  have hyU : y ∈ U := hzU (mem_closedBall.2 (by linarith))
  -- Within the ball the graph rises by at most `G ‖w - y‖`, and the height drops by at most
  -- `‖w - y‖`.
  have hγw : γ w ≤ γ z + G * dist w y := by
    have h := hγ.dist_le_mul w hwU y hyU
    rw [Real.dist_eq, hγν] at h
    linarith [le_abs_self (γ w - γ z)]
  have hinner : ⟪z, ν⟫_ℝ + t - dist w y ≤ ⟪w, ν⟫_ℝ := by
    have h1 : ⟪w, ν⟫_ℝ = ⟪z, ν⟫_ℝ + t + ⟪w - y, ν⟫_ℝ := by
      simp only [y, inner_sub_left, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hν]
      ring
    have h2 := abs_real_inner_le_norm (w - y) ν
    rw [hν, mul_one, ← dist_eq_norm] at h2
    linarith [neg_abs_le ⟪w - y, ν⟫_ℝ]
  have hlt : γ w < ⟪w, ν⟫_ℝ := by nlinarith [dist_nonneg (x := w) (y := y)]
  exact ((Set.ext_iff.1 hΩ w).2 ⟨hwU, hlt⟩).2

/-- **A uniform interior cone condition.** Let `Ω` have compact closure in a nontrivial real inner
product space, and near each point `x` of its frontier let `Ω` be the region above a Lipschitz
graph: `ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius `r > 0` and a
function `γ` invariant along `ν` and Lipschitz on `ball x r`. Then there are a height `h₀ > 0` and
an aperture `0 < c ≤ 1` such that every point `z` of the closure of `Ω` is the vertex of a cone in
`Ω`: for some unit vector `v`, the closed ball of radius `c t` about `z + t v` lies in `Ω` for every
`0 < t ≤ h₀`. -/
theorem exists_forall_closedBall_add_smul_subset [Nontrivial E] (hΩ : IsCompact (closure Ω))
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      LipschitzOnWith G γ (ball x r) ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    ∃ h₀ > 0, ∃ c > 0, c ≤ 1 ∧ ∀ z ∈ closure Ω, ∃ v : E, ‖v‖ = 1 ∧
      ∀ t, 0 < t → t ≤ h₀ → closedBall (z + t • v) (c * t) ⊆ Ω := by
  choose! ν γ G r hν hγ hγν hr hΩr using hbdry
  -- Finitely many patch balls cover the compact frontier.
  obtain ⟨T, hTfr, hcov⟩ :=
    (hΩ.of_isClosed_subset isClosed_frontier frontier_subset_closure).elim_nhds_subcover
      (fun x => ball x (r x)) fun x hx => ball_mem_nhds x (hr x hx)
  -- With the interior of `Ω` they cover `closure Ω`; take a Lebesgue number `δ` of this cover.
  set B : Option T → Set E := fun i => i.elim (interior Ω) fun x => ball (x : E) (r x)
  have hBopen : ∀ i, IsOpen (B i) := by
    rintro (_ | x)
    exacts [isOpen_interior, isOpen_ball]
  have hBcov : closure Ω ⊆ ⋃ i, B i := fun z hz => by
    by_cases hzΩ : z ∈ interior Ω
    · exact mem_iUnion.2 ⟨none, hzΩ⟩
    · obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.1 (hcov ⟨hz, hzΩ⟩)
      exact mem_iUnion.2 ⟨some ⟨x, hxT⟩, hzx⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hΩ hBopen hBcov
  -- The aperture is fixed by a bound `G'` on the Lipschitz constants of the finitely many patches.
  set G' : ℝ≥0 := ∑ x ∈ T, G x
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  have hG' : (0 : ℝ) < 2 * (G' + 1) := by positivity
  refine ⟨δ / 4, by positivity, 1 / (2 * (G' + 1)), by positivity,
    (div_le_one hG').2 (by linarith [G'.coe_nonneg]), fun z hz => ?_⟩
  obtain ⟨i, hi⟩ := hleb z hz
  have hsub : ∀ t, t ≤ δ / 4 → closedBall z (2 * t) ⊆ B i := fun t htδ =>
    (closedBall_subset_ball (by linarith)).trans hi
  rcases i with _ | ⟨x, hxT⟩
  · -- Near an interior point every direction works.
    refine ⟨e, he, fun t ht htδ => ((closedBall_subset_closedBall' ?_).trans
      (hsub t htδ)).trans interior_subset⟩
    have hez : dist (z + t • e) z = t := by simp [dist_eq_norm, norm_smul, he, abs_of_pos ht]
    rw [hez, one_div_mul_eq_div]
    linarith [div_le_self ht.le (by linarith [G'.coe_nonneg] : (1 : ℝ) ≤ 2 * (G' + 1))]
  · -- Near the frontier the axis of the patch works.
    have hx := hTfr x hxT
    refine ⟨ν x, hν x hx, fun t ht htδ => (closedBall_subset_closedBall ?_).trans
      (closedBall_add_smul_subset_of_inter_eq (hν x hx) (hγ x hx) (hγν x hx) (hΩr x hx) hz ht
        (hsub t htδ))⟩
    have hGx : (G x : ℝ) ≤ G' := by exact_mod_cast Finset.single_le_sum (fun _ _ => zero_le) hxT
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left ht.le (by positivity) (by linarith)

end TauCeti
