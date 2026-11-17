/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Perron.Barrier
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Regular boundary points

Let `Ω` be an open subset of a finite-dimensional real inner product space. A point `ξ` of
`frontier Ω` is *regular* when it admits a barrier relative to `Ω` (`TauCeti.IsBarrier`): a
superharmonic function on `Ω`, continuous on `closure Ω`, vanishing at `ξ` and positive on the
rest of `closure Ω`. Perron's method
(`TauCeti.exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier`) solves the Dirichlet problem
for continuous data on a bounded open set all of whose boundary points are regular. This file
proves two complements from Gilbarg–Trudinger, Section 2.8.

**Regularity is local.** A barrier needs only to be constructed near `ξ`: if `ξ` admits a
barrier relative to `Ω ∩ V` for a neighbourhood `V` of `ξ`, it admits one relative to `Ω`
(`TauCeti.IsBarrier.exists_isBarrier_of_inter`). With `B = ball ξ ρ ⊆ V` and `m > 0` the minimum
of the local barrier `w` over the points of `closure (Ω ∩ B)` at distance at least `ρ / 2` from
`ξ`, the function equal to `min m w` on `B` and to `m` outside `B` is a barrier relative to `Ω`.
It is superharmonic since it is the minimum of two superharmonic functions on `Ω ∩ B` and the
constant `m` near every point of `Ω` outside `ball ξ (ρ / 2)`, and superharmonicity is a local
property (`TauCeti.subharmonicOn_of_locally_subharmonicOn`). Consequently two open sets that
coincide near `ξ` have the same regularity at `ξ` (`TauCeti.exists_isBarrier_iff_of_inter_eq`).

**Regularity is necessary.** If the Dirichlet problem on the bounded open set `Ω` is solvable
for every continuous boundary datum, then every boundary point is regular: the solution `u`
with datum `x ↦ dist x ξ` is itself a barrier at `ξ`
(`InnerProductSpace.HarmonicOnNhd.isBarrier`). Indeed `x ↦ dist x ξ` is continuous and convex,
hence subharmonic (`ConvexOn.subharmonicOn`), so the comparison principle gives
`dist x ξ ≤ u x` on `closure Ω`. Together with Perron's method this characterizes the bounded
open sets on which the Dirichlet problem is solvable for all continuous data
(`TauCeti.forall_mem_frontier_exists_isBarrier_iff`).

## Main declarations

* `TauCeti.IsBarrier.exists_isBarrier_of_inter`: a local barrier yields a barrier.
* `TauCeti.exists_isBarrier_iff_of_inter_eq`: regularity depends only on `Ω` near the point.
* `InnerProductSpace.HarmonicOnNhd.isBarrier`: the harmonic function with boundary values
  `dist x ξ` is a barrier at `ξ`.
* `TauCeti.forall_mem_frontier_exists_isBarrier_iff`: **the Dirichlet problem on a bounded open
  set is solvable for all continuous boundary data exactly when every boundary point is
  regular.**

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8, the remarks following Lemma 2.13 and Theorem 2.14.
-/

public section

namespace TauCeti

open InnerProductSpace Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω Ω' V : Set E} {u w : E → ℝ} {ξ : E}

open scoped Classical in
/-- Gluing a barrier `w` relative to `Ω ∩ ball ξ ρ` with a constant: if `m > 0` lies below `w` at
the points of `closure (Ω ∩ ball ξ ρ)` at distance at least `ρ / 2` from `ξ`, the function equal
to `min m w` on `ball ξ ρ` and to `m` outside it is a barrier relative to `Ω`. -/
private lemma isBarrier_ite_min (hΩ : IsOpen Ω) {ρ m : ℝ} (hρ : 0 < ρ)
    (hw : IsBarrier (Ω ∩ ball ξ ρ) ξ w) (hm : 0 < m)
    (hmw : ∀ x ∈ closure (Ω ∩ ball ξ ρ) \ ball ξ (ρ / 2), m ≤ w x) :
    IsBarrier Ω ξ fun x ↦ if x ∈ ball ξ ρ then min m (w x) else m := by
  set W : E → ℝ := fun x ↦ if x ∈ ball ξ ρ then min m (w x) else m
  have hcl : closure Ω ∩ ball ξ ρ ⊆ closure (Ω ∩ ball ξ ρ) := fun x hx ↦ by
    simpa only [inter_comm] using isOpen_ball.inter_closure ⟨hx.2, hx.1⟩
  -- Near `ξ` the glued function is `min m w`; away from `ξ` it is the constant `m`.
  have hnear : EqOn W (fun x ↦ min m (w x)) (ball ξ ρ) := fun x hx ↦ ite_eq_left_iff.2 (absurd hx)
  have hfar : EqOn W (fun _ ↦ m) (closure Ω ∩ (closedBall ξ (ρ / 2))ᶜ) := fun x hx ↦ by
    by_cases hxρ : x ∈ ball ξ ρ
    · refine (hnear hxρ).trans (min_eq_left (hmw x ⟨hcl ⟨hx.1, hxρ⟩, fun h ↦ hx.2 ?_⟩))
      exact ball_subset_closedBall h
    · exact ite_eq_right_iff.2 (absurd · hxρ)
  -- The two open sets `ball ξ ρ` and `(closedBall ξ (ρ / 2))ᶜ` cover the space.
  have hcover : ∀ x, x ∈ ball ξ ρ ∨ x ∈ (closedBall ξ (ρ / 2))ᶜ := fun x ↦ by
    by_cases hx : x ∈ ball ξ ρ
    · exact .inl hx
    · refine .inr fun h ↦ hx ?_
      rw [mem_closedBall] at h
      rw [mem_ball]
      linarith
  have hc : ContinuousOn W (closure Ω) := by
    refine continuousOn_of_locally_continuousOn fun x _ ↦ ?_
    rcases hcover x with hx | hx
    · refine ⟨ball ξ ρ, isOpen_ball, hx, ?_⟩
      have hmin : ContinuousOn (fun y ↦ min m (w y)) (closure (Ω ∩ ball ξ ρ)) := by
        have := hw.continuousOn
        fun_prop
      exact (hmin.mono hcl).congr fun y hy ↦ hnear hy.2
    · exact ⟨_, isClosed_closedBall.isOpen_compl, hx, continuousOn_const.congr hfar⟩
  have hsub : SubharmonicOn (-W) Ω := by
    refine subharmonicOn_of_locally_subharmonicOn fun x _ ↦ ?_
    rcases hcover x with hx | hx
    · refine ⟨ball ξ ρ, isOpen_ball, hx, ?_⟩
      refine (((harmonicOnNhd_const (-m)).subharmonicOn.sup hw.subharmonicOn_neg
        (hΩ.inter isOpen_ball)).congr (hΩ.inter isOpen_ball)) fun y hy ↦ ?_
      simp [hnear hy.2, max_neg_neg]
    · refine ⟨_, isClosed_closedBall.isOpen_compl, hx,
        (harmonicOnNhd_const (-m)).subharmonicOn.congr (hΩ.inter isClosed_closedBall.isOpen_compl)
        fun y hy ↦ ?_⟩
      simp [hfar ⟨subset_closure hy.1, hy.2⟩]
  refine ⟨hsub, hc, ?_, fun x hx hxξ ↦ ?_⟩
  · simp [W, hρ, hw.apply_self, hm.le]
  · by_cases hxρ : x ∈ ball ξ ρ
    · rw [hnear hxρ]
      exact lt_min hm (hw.pos x (hcl ⟨hx, hxρ⟩) hxξ)
    · have hWx : W x = m := ite_eq_right_iff.2 (absurd · hxρ)
      exact hWx ▸ hm

/-- **A local barrier yields a barrier.** If `ξ` admits a barrier relative to `Ω ∩ V` for some
neighbourhood `V` of `ξ`, then `ξ` admits a barrier relative to the open set `Ω`. -/
theorem IsBarrier.exists_isBarrier_of_inter (hΩ : IsOpen Ω) (hV : V ∈ 𝓝 ξ)
    (hw : IsBarrier (Ω ∩ V) ξ w) : ∃ W, IsBarrier Ω ξ W := by
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.1 hV
  have hw' := hw.mono (inter_subset_inter_right Ω hρV)
  -- The points of `closure (Ω ∩ ball ξ ρ)` away from `ξ` form a compact set, on which the local
  -- barrier is bounded below by a positive constant.
  have hK : IsCompact (closure (Ω ∩ ball ξ ρ) \ ball ξ (ρ / 2)) :=
    (isCompact_closedBall ξ ρ).of_isClosed_subset (isClosed_closure.sdiff isOpen_ball)
      (sdiff_subset.trans (closure_minimal (inter_subset_right.trans ball_subset_closedBall)
        isClosed_closedBall))
  obtain ⟨m, hm, hmw⟩ := hK.exists_forall_le' (hw'.continuousOn.mono sdiff_subset)
    fun x hx ↦ hw'.pos x hx.1 fun h ↦ hx.2 (h ▸ mem_ball_self (half_pos hρ))
  exact ⟨_, isBarrier_ite_min hΩ hρ hw' hm hmw⟩

/-- **Regularity is a local property.** If the open sets `Ω` and `Ω'` coincide on a neighbourhood
`V` of `ξ`, then `ξ` admits a barrier relative to `Ω` exactly when it admits one relative to
`Ω'`. -/
theorem exists_isBarrier_iff_of_inter_eq (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hV : V ∈ 𝓝 ξ)
    (h : Ω ∩ V = Ω' ∩ V) : (∃ w, IsBarrier Ω ξ w) ↔ ∃ w, IsBarrier Ω' ξ w :=
  ⟨fun ⟨_, hw⟩ ↦ (h ▸ hw.mono inter_subset_left).exists_isBarrier_of_inter hΩ' hV,
    fun ⟨_, hw⟩ ↦ (h.symm ▸ hw.mono inter_subset_left).exists_isBarrier_of_inter hΩ hV⟩

/-- **The solution with boundary values `dist x ξ` is a barrier at `ξ`.** Let `Ω` be a bounded
open set and `ξ ∈ frontier Ω`. A function harmonic in `Ω`, continuous on `closure Ω` and equal to
`dist x ξ` at every `x ∈ frontier Ω` is a barrier at `ξ` relative to `Ω`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.isBarrier (hu : HarmonicOnNhd u Ω)
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (huc : ContinuousOn u (closure Ω))
    (hξ : ξ ∈ frontier Ω) (hug : ∀ x ∈ frontier Ω, u x = dist x ξ) : IsBarrier Ω ξ u := by
  refine ⟨hu.neg.subharmonicOn, huc, by rw [hug ξ hξ, dist_self], fun x hx hxξ ↦ ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact absurd (Subsingleton.elim x ξ) hxξ
  -- The convex function `dist · ξ` is subharmonic, so lies below `u` on `closure Ω`.
  have hd : Continuous fun y ↦ dist y ξ := continuous_id.dist continuous_const
  have hle := ((convexOn_dist ξ convex_univ).subharmonicOn isOpen_univ).mono
    (subset_univ Ω) |>.le_of_le_frontier hΩ hb hd.continuousOn hu huc
    (fun y hy ↦ (hug y hy).ge) x hx
  exact (dist_pos.2 hxξ).trans_le hle

/-- **Characterization of regularity** (Gilbarg–Trudinger, Theorem 2.14). On a bounded open set
`Ω`, the Dirichlet problem `Δu = 0` in `Ω`, `u = g` on `frontier Ω`, has a solution harmonic in
`Ω` and continuous on `closure Ω` for every boundary datum `g` continuous on `frontier Ω` if and
only if every boundary point of `Ω` admits a barrier. -/
theorem forall_mem_frontier_exists_isBarrier_iff (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (∀ ξ ∈ frontier Ω, ∃ w, IsBarrier Ω ξ w) ↔
      ∀ g : E → ℝ, ContinuousOn g (frontier Ω) →
        ∃ u, HarmonicOnNhd u Ω ∧ ContinuousOn u (closure Ω) ∧ EqOn u g (frontier Ω) := by
  refine ⟨fun h _ hg ↦ exists_harmonicOnNhd_continuousOn_closure_eqOn_frontier hΩ hb h hg,
    fun h ξ hξ ↦ ?_⟩
  obtain ⟨u, hu, huc, hug⟩ := h (dist · ξ) (continuous_id.dist continuous_const).continuousOn
  exact ⟨u, hu.isBarrier hΩ hb huc hξ hug⟩

end TauCeti
