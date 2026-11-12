/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.MeasureDensity

/-!
# The exterior of a Lipschitz domain

Let `Ω` be a Lipschitz domain. Inside the cylinder of a boundary chart, `Ω` is the region strictly
above a Lipschitz graph and its closure is the region on or above it, so the exterior
`(closure Ω)ᶜ` is the region strictly below the graph. Reflecting the normal coordinate turns this
into the region above the negated graph: the exterior of a Lipschitz domain is again a Lipschitz
domain, with the same Lipschitz constants and frontier contained in that of `Ω`. A Lipschitz domain
is also regular open, `interior (closure Ω) = Ω`, so the closure of its exterior is `Ωᶜ`.

Applied to the exterior, the interior corkscrew condition and the measure density property of
`TauCeti.Analysis.Sobolev.LipschitzDomain.MeasureDensity` become their exterior forms. For a
Lipschitz domain `Ω` with compact frontier, for instance a bounded one, and `R > 0`, every ball
`B(x, r)` with centre `x ∉ Ω` and radius `r ≤ R` contains a ball of radius `δ r` disjoint from the
closure of `Ω`, and so, for an additive Haar measure `μ`,

`c μ(B(x, r)) ≤ μ(B(x, r) \ closure Ω)`

with constants `δ, c > 0` depending only on `Ω` and `R`. This uniform exterior density at the
frontier is the geometric hypothesis of De Giorgi's oscillation estimates at the boundary, which
give Hölder continuity up to the boundary of weak solutions of divergence-form equations with
Hölder boundary values (Gilbarg–Trudinger, §8.10).

## Main declarations

* `Set.IsLipschitzChart.compl_closure`: a Lipschitz chart of `Ω`, with its normal coordinate
  reflected, is a Lipschitz chart of `(closure Ω)ᶜ`, with the negated graph.
* `Set.IsLipschitzDomain.compl_closure`: the exterior of a Lipschitz domain is a Lipschitz domain.
* `Set.IsLipschitzDomain.interior_closure`: a Lipschitz domain is regular open.
* `Set.IsLipschitzDomain.exists_ball_subset_compl_closure_inter_ball`: the exterior corkscrew
  condition of a Lipschitz domain with compact frontier.
* `Set.IsLipschitzDomain.exists_pos_mul_measure_closedBall_le_measure_closedBall_diff`: the
  exterior measure density property of a Lipschitz domain with compact frontier.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §8.10
  (boundary estimates under an exterior measure condition).
* D. S. Jerison, C. E. Kenig, *Boundary behavior of harmonic functions in non-tangentially
  accessible domains*, Adv. Math. 46 (1982), 80–147 (the exterior corkscrew condition).
-/

public section

noncomputable section

open Metric MeasureTheory TauCeti
open scoped NNReal ENNReal

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set F}

namespace IsLipschitzChart

variable {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}

/-- **The exterior chart.** If `e` is a Lipschitz chart of `Ω` with graph `γ`, then `e` followed by
the reflection `(t, y) ↦ (-t, y)` of the normal coordinate is a Lipschitz chart of the exterior
`(closure Ω)ᶜ` with graph `-γ`, the same Lipschitz constant and the same cylinder. -/
theorem compl_closure (hc : IsLipschitzChart Ω e γ K h r) :
    IsLipschitzChart (closure Ω)ᶜ
      (e.trans (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (LinearIsometryEquiv.refl ℝ E)).toAffineIsometryEquiv) (fun y ↦ -γ y) K h r := by
  refine isLipschitzChart_of_forall_mem_iff hc.height_pos hc.radius_pos hc.lipschitzWith.neg
    fun z hz ↦ ?_
  -- The reflected point `w = (-z.fst, z.snd)` lies in the cylinder, where the closure of `Ω` is
  -- the region on or above the graph.
  set w : WithLp 2 (ℝ × E) := WithLp.toLp 2 (-z.fst, z.snd) with hw_def
  have hwC : w ∈ normalCylinder h r := by
    rw [mem_normalCylinder] at hz ⊢
    simp only [hw_def, WithLp.toLp_fst, WithLp.toLp_snd]
    exact ⟨by linarith, by linarith, hz.2.2⟩
  have hsymm : (e.trans (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (LinearIsometryEquiv.refl ℝ E)).toAffineIsometryEquiv).symm z = e.symm w := by
    rw [AffineIsometryEquiv.symm_apply_eq]
    obtain ⟨⟨t, y⟩⟩ := z
    simp [hw_def]
  have hiff : e.symm w ∈ closure Ω ↔ γ w.snd ≤ w.fst := by
    rw [← e.injective.mem_set_image, AffineIsometryEquiv.apply_symm_apply]
    exact ⟨fun hw ↦ (hc.image_closure_inter_normalCylinder.subset ⟨hw, hwC⟩).1,
      fun hw ↦ (hc.image_closure_inter_normalCylinder.superset ⟨hw, hwC⟩).1⟩
  rw [hsymm, mem_compl_iff, hiff, not_le]
  simp only [hw_def, WithLp.toLp_fst, WithLp.toLp_snd]
  constructor <;> intro h <;> linarith

end IsLipschitzChart

namespace IsLipschitzDomain

/-- **The exterior of a Lipschitz domain is a Lipschitz domain.** Its frontier lies in the frontier
of `Ω`, and near a frontier point a chart of `Ω` with the normal coordinate reflected is a chart of
the exterior (`Set.IsLipschitzChart.compl_closure`). -/
theorem compl_closure (hΩ : Ω.IsLipschitzDomain E) : (closure Ω)ᶜ.IsLipschitzDomain E := by
  refine isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun x hx ↦ ?_
  rw [frontier_compl] at hx
  obtain ⟨e, γ, K, h, r, hc, hxC⟩ :=
    isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x (frontier_closure_subset hx)
  refine ⟨_, _, K, h, r, hc.compl_closure, ?_⟩
  rw [mem_normalCylinder] at hxC ⊢
  simp only [AffineIsometryEquiv.coe_trans, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
    Function.comp_apply, LinearIsometryEquiv.withLpProdCongr_apply, LinearIsometryEquiv.coe_neg,
    LinearIsometryEquiv.coe_refl, id_eq, WithLp.toLp_fst, WithLp.toLp_snd]
  exact ⟨by linarith, by linarith, hxC.2.2⟩

/-- **A Lipschitz domain is regular open**: it is the interior of its closure. A frontier point is
approached from below the graph of a chart, that is from outside the closure. -/
theorem interior_closure (hΩ : Ω.IsLipschitzDomain E) : interior (closure Ω) = Ω := by
  refine Subset.antisymm (fun x hx ↦ ?_) hΩ.isOpen.subset_interior_closure
  by_contra hxΩ
  have hxF : x ∈ frontier Ω := ⟨interior_subset hx, by rwa [hΩ.isOpen.interior_eq]⟩
  obtain ⟨e, γ, K, h, r, hc, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hxF
  have hγ := hc.fst_apply_eq_of_mem_frontier hxF hxC
  rw [mem_normalCylinder] at hxC
  obtain ⟨ε, hε, hεx⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  -- The point `w` at depth `s` below `e x` in the chart lies in the cylinder, below the graph.
  set s := min ε ((e x).fst + h) / 2 with hs_def
  have hs : 0 < s := by
    have : 0 < (e x).fst + h := by linarith
    positivity
  have hsε : s < ε := by rw [hs_def]; linarith [min_le_left ε ((e x).fst + h)]
  have hsh : s < (e x).fst + h := by rw [hs_def]; linarith [min_le_right ε ((e x).fst + h)]
  set w : WithLp 2 (ℝ × E) := WithLp.toLp 2 ((e x).fst - s, (e x).snd) with hw_def
  have hwC : w ∈ normalCylinder h r := by
    simp only [mem_normalCylinder, hw_def, WithLp.toLp_fst, WithLp.toLp_snd]
    exact ⟨by linarith, by linarith, hxC.2.2⟩
  have hdist : dist (e.symm w) x < ε := by
    rw [← e.dist_map, AffineIsometryEquiv.apply_symm_apply, WithLp.prod_dist_eq_of_L2]
    simp only [hw_def, WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq,
      sub_sub_cancel_left, abs_neg, abs_of_pos hs]
    simpa [Real.sqrt_sq hs.le] using hsε
  -- But `e.symm w` lies in the interior of the closure, hence on or above the graph.
  have hwcl : e.symm w ∈ closure Ω := interior_subset (hεx (mem_ball.2 hdist))
  have := (hc.image_closure_inter_normalCylinder.subset
    ⟨⟨e.symm w, hwcl, e.apply_symm_apply w⟩, hwC⟩).1
  simp only [mem_ofPred_eq, hw_def, WithLp.toLp_fst, WithLp.toLp_snd] at this
  linarith

/-- The closure of the exterior of a Lipschitz domain `Ω` is the complement of `Ω`. -/
theorem closure_compl_closure (hΩ : Ω.IsLipschitzDomain E) : closure (closure Ω)ᶜ = Ωᶜ := by
  rw [closure_compl, hΩ.interior_closure]

/-- **The exterior corkscrew condition.** For a Lipschitz domain `Ω` with compact frontier, for
instance a bounded Lipschitz domain, and `R > 0` there is `δ > 0` such that for every `x ∉ Ω` and
every `0 < r ≤ R`, the ball `B(x, r)` contains a ball of radius `δ r` disjoint from the closure of
`Ω`. -/
theorem exists_ball_subset_compl_closure_inter_ball (hΩ : Ω.IsLipschitzDomain E)
    (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ x ∉ Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ y, ball y (δ * r) ⊆ (closure Ω)ᶜ ∩ ball x r := by
  have hK' : IsCompact (frontier (closure Ω)ᶜ) := by
    rw [frontier_compl]
    exact hK.of_isClosed_subset isClosed_frontier frontier_closure_subset
  obtain ⟨δ, hδ, hball⟩ := hΩ.compl_closure.exists_ball_subset_inter_ball hK' hR
  exact ⟨δ, hδ, fun x hx ↦ hball x (hΩ.closure_compl_closure ▸ mem_compl hx)⟩

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {μ : Measure F}
  [μ.IsAddHaarMeasure]

/-- **The exterior measure density property of a Lipschitz domain.** For a Lipschitz domain `Ω`
with compact frontier, for instance a bounded Lipschitz domain, an additive Haar measure `μ` and
`R > 0`, there is `c > 0` such that `c μ(B(x, r)) ≤ μ(B(x, r) \ closure Ω)` for every `x ∉ Ω` and
every `0 < r ≤ R`, where `B(x, r)` is the closed ball. -/
theorem exists_pos_mul_measure_closedBall_le_measure_closedBall_diff
    (hΩ : Ω.IsLipschitzDomain E) (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∉ Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r \ closure Ω) := by
  have hK' : IsCompact (frontier (closure Ω)ᶜ) := by
    rw [frontier_compl]
    exact hK.of_isClosed_subset isClosed_frontier frontier_closure_subset
  obtain ⟨c, hc, hdens⟩ :=
    hΩ.compl_closure.exists_pos_mul_measure_closedBall_le_measure_closedBall_inter (μ := μ) hK' hR
  refine ⟨c, hc, fun x hx r hr hrR ↦ ?_⟩
  rw [sdiff_eq]
  exact hdens x (hΩ.closure_compl_closure ▸ mem_compl hx) r hr hrR

end IsLipschitzDomain

end Set
