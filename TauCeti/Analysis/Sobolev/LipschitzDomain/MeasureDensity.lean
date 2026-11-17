/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.MeasureTheory.Function.Campanato
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Topology.Frontier

/-!
# The measure density property of Lipschitz domains

A Lipschitz domain `Ω` with compact frontier, for instance a bounded one in a proper space,
satisfies the **interior corkscrew condition**: for every `R > 0` there is `δ > 0` such that every
ball `B(x, r)` centred in the closure of `Ω` with `r ≤ R` contains a ball of radius `δ r` lying in
`Ω`.
Consequently `Ω` has the **measure density property**: for an additive Haar measure `μ` there is
`c > 0` with

`c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)`

for every `x` in the closure of `Ω` and every `0 < r ≤ R`. This is the geometric input of the
estimates up to the boundary that average over the sets `B(x, r) ∩ Ω`. In particular Campanato's
characterization of Hölder continuity, proved in `TauCeti.MeasureTheory.Function.Campanato` on sets
with the measure density property, holds on every bounded Lipschitz domain: for `p ≥ 1` and
`α > 0`, a locally integrable function on `Ω` agrees almost everywhere with an `α`-Hölder function
on `Ω` exactly when it lies in the Campanato space `𝓛^{p, n + p α}(Ω)`, where `n` is the dimension.

The exterior `(closure Ω)ᶜ` of a Lipschitz domain is again a Lipschitz domain with the same
frontier, and its closure is `Ωᶜ` (see `TauCeti.Analysis.Sobolev.LipschitzDomain.Basic`). Applied
to the exterior, these results become their exterior forms: every ball `B(x, r)` with centre
`x ∉ Ω` and radius `r ≤ R` contains a ball of radius `δ r` disjoint from the closure of `Ω`, and

`c μ(B(x, r)) ≤ μ(B(x, r) \ closure Ω)`.

This uniform exterior density at the frontier is the geometric hypothesis of De Giorgi's
oscillation estimates at the boundary, which give Hölder continuity up to the boundary of weak
solutions of divergence-form equations with Hölder boundary values (Gilbarg–Trudinger, §8.10).

## The argument

Near a frontier point `z`, a chart presents `Ω` as the region above the graph of a `K`-Lipschitz
function `γ`. Moving up from `z` by `s` in the normal direction reaches a point `y` whose ball of
radius `s / (1 + K)` stays above the graph, since along that ball the normal coordinate drops by
less than `s / (1 + K)` while the graph rises by less than `K s / (1 + K)`. Finitely many charts
cover the compact frontier, and a Lebesgue number `ρ` of this cover places every ball of radius
`ρ` about a frontier point inside a single chart cylinder. A ball `B(x, r)` with `r ≤ ρ` either
has its concentric half lying in `Ω`, or meets the frontier in its concentric half, and in the
second case the chart construction at that frontier point gives the inner ball. Larger radii up
to `R` reduce to the radius `ρ` at the cost of the factor `ρ / R`.

## Main declarations

* `Set.IsLipschitzChart.exists_ball_subset_inter_ball`: the inner ball above a point of the closure
  inside a chart.
* `Set.IsLipschitzDomain.exists_ball_subset_inter_ball`: the interior corkscrew condition of a
  Lipschitz domain with compact frontier.
* `Set.IsLipschitzDomain.exists_pos_mul_measure_ball_le_measure_ball_inter`,
  `Set.IsLipschitzDomain.exists_pos_mul_measure_closedBall_le_measure_closedBall_inter`: the
  measure density property of a Lipschitz domain with compact frontier, for open and closed balls.
* `Set.IsLipschitzDomain.exists_ball_subset_compl_closure_inter_ball`: the exterior corkscrew
  condition of a Lipschitz domain with compact frontier.
* `Set.IsLipschitzDomain.exists_pos_mul_measure_ball_le_measure_ball_sdiff_closure`,
  `Set.IsLipschitzDomain.exists_pos_mul_measure_closedBall_le_measure_closedBall_sdiff_closure`:
  the exterior measure density property of a Lipschitz domain with compact frontier.
* `Set.IsLipschitzDomain.exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top`: Campanato's
  characterization `𝓛^{p, n + p α}(Ω) = C^{0,α}(Ω)` on a bounded Lipschitz domain.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, §5.1 and Theorem 5.5.
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1 and Theorem 1.2.2.2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §8.10
  (boundary estimates under an exterior measure condition).
* D. S. Jerison, C. E. Kenig, *Boundary behavior of harmonic functions in non-tangentially
  accessible domains*, Adv. Math. 46 (1982), 80–147 (the interior and exterior corkscrew
  conditions).
-/

public section

noncomputable section

open Bornology Metric MeasureTheory Module TauCeti
open scoped NNReal ENNReal

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set F}

namespace IsLipschitzChart

variable {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}

/-- **The inner ball above a point of the closure.** Let `z` be a point of the closure of `Ω`
such that, in the coordinates of a Lipschitz chart with graph constant `K`, the ball of radius
`2 s` about `z` lies in the chart cylinder. Then the ball of radius `2 s` about `z` contains a ball
of radius `s / (1 + K)` lying in `Ω`: the one centred at height `s` above `z`. -/
theorem exists_ball_subset_inter_ball (hc : Ω.IsLipschitzChart e γ K h r) {z : F}
    (hz : z ∈ closure Ω) {s : ℝ} (hs : 0 < s) (hball : ball (e z) (2 * s) ⊆ normalCylinder h r) :
    ∃ y, ball y (s / (1 + K)) ⊆ Ω ∩ ball z (2 * s) := by
  have hzC : e z ∈ normalCylinder h r := hball (mem_ball_self (by positivity))
  -- In the chart, `z` lies on or above the graph.
  have hzγ : γ (e z).snd ≤ (e z).fst := (hc.mem_closure_iff hzC).1 hz
  have hK : (0 : ℝ) ≤ K := K.2
  set t := s / (1 + K) with ht_def
  have _ : 0 < t := by positivity
  have hts : t ≤ s := div_le_self hs.le (by linarith)
  have hst : s - t = K * t := by
    rw [ht_def]
    field_simp
    ring
  -- The centre of the inner ball, at height `s` above `z` in the chart.
  set y : WithLp 2 (ℝ × E) := WithLp.toLp 2 ((e z).fst + s, (e z).snd) with hy_def
  have hyz : dist y (e z) = s := by
    rw [WithLp.prod_dist_eq_of_L2]
    simp [hy_def, abs_of_pos hs, Real.sqrt_sq hs.le]
  refine ⟨e.symm y, fun x hx ↦ ?_⟩
  have hxy : dist (e x) y < t := by
    rw [← e.apply_symm_apply y, e.dist_map]
    exact hx
  have hxz : dist (e x) (e z) < 2 * s := by
    linarith [dist_triangle (e x) y (e z)]
  refine ⟨(hc.mem_iff (hball (mem_ball.2 hxz))).2 ?_, by rwa [mem_ball, ← e.dist_map]⟩
  -- The graph rises by at most `K t` over the ball, while the normal coordinate drops by less
  -- than `t` from the height `s` above `z`.
  have hsnd : dist (e x).snd (e z).snd < t := by
    have := WithLp.dist_snd_le (e x) y
    simp only [hy_def, WithLp.toLp_snd] at this
    linarith
  have hfst : y.fst - (e x).fst < t := by
    have := WithLp.dist_fst_le (e x) y
    rw [Real.dist_eq, abs_sub_comm] at this
    linarith [le_abs_self (y.fst - (e x).fst)]
  have hγ : γ (e x).snd ≤ γ (e z).snd + K * t := by
    have := hc.lipschitzWith.dist_le_mul (e x).snd (e z).snd
    rw [Real.dist_eq] at this
    nlinarith [le_abs_self (γ (e x).snd - γ (e z).snd)]
  simp only [hy_def, WithLp.toLp_fst] at hfst
  linarith

end IsLipschitzChart

namespace IsLipschitzDomain

/-- **The interior corkscrew condition.** For a Lipschitz domain `Ω` with compact frontier, for
instance a bounded Lipschitz domain in a proper space, and `R > 0` there is `δ > 0` such that for
every `x` in the closure of `Ω` and every `0 < r ≤ R`, the ball `B(x, r)` contains a ball of radius
`δ r` lying in `Ω`. -/
theorem exists_ball_subset_inter_ball (hΩ : Ω.IsLipschitzDomain E)
    (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ x ∈ closure Ω, ∀ r : ℝ, 0 < r → r ≤ R → ∃ y, ball y (δ * r) ⊆ Ω ∩ ball x r := by
  obtain ⟨K, m, e, γ, h, ρ, hc, hcov⟩ := hΩ.exists_finite_cover hK
  obtain ⟨ρ₀, hρ₀, hleb⟩ := lebesgue_number_lemma_of_metric hK
    (fun i ↦ (isOpen_normalCylinder (h i) (ρ i)).preimage (e i).continuous) hcov
  have hK : (0 : ℝ) ≤ K := K.2
  -- The corkscrew condition at radii up to the Lebesgue number `ρ₀`, with `δ = 1 / (4 (1 + K))`.
  have hsmall : ∀ x ∈ closure Ω, ∀ r : ℝ, 0 < r → r ≤ ρ₀ →
      ∃ y, ball y (r / 4 / (1 + K)) ⊆ Ω ∩ ball x r := by
    intro x hx r hr hrρ
    by_cases hsub : ball x (r / 2) ⊆ Ω
    · have hle : r / 4 / (1 + K) ≤ r / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      exact ⟨x, fun w hw ↦ ⟨hsub (ball_subset_ball hle hw),
        ball_subset_ball (hle.trans (by linarith)) hw⟩⟩
    -- Otherwise the half ball meets the frontier, at a point `z` lying in a single chart.
    obtain ⟨w, hwΩ, hwx⟩ := Metric.mem_closure_iff.1 hx (r / 2) (by positivity)
    obtain ⟨z, hzB, hzF⟩ := (convex_ball x (r / 2)).isPreconnected.inter_frontier_nonempty
      ⟨w, by rwa [mem_ball, dist_comm], hwΩ⟩ (not_subset.1 hsub)
    obtain ⟨i, hi⟩ := hleb z hzF
    have hball : ball (e i z) (2 * (r / 4)) ⊆ normalCylinder (h i) (ρ i) := by
      intro v hv
      have hv' : (e i).symm v ∈ ball z ρ₀ := by
        rw [mem_ball, ← (e i).dist_map, (e i).apply_symm_apply]
        exact (mem_ball.1 hv).trans_le (by linarith)
      simpa using hi hv'
    obtain ⟨y, hy⟩ := (hc i).exists_ball_subset_inter_ball (frontier_subset_closure hzF)
      (by positivity) hball
    refine ⟨y, hy.trans (inter_subset_inter_right _ (ball_subset_ball' ?_))⟩
    rw [mem_ball] at hzB
    linarith
  -- Larger radii reduce to the radius `min r ρ₀`.
  refine ⟨1 / 4 / (1 + K) * min 1 (ρ₀ / R), by positivity, fun x hx r hr hrR ↦ ?_⟩
  obtain ⟨y, hy⟩ := hsmall x hx (min r ρ₀) (lt_min hr hρ₀) (min_le_right _ _)
  have hmin : min 1 (ρ₀ / R) * r ≤ min r ρ₀ := by
    refine le_min ((mul_le_of_le_one_left hr.le (min_le_left _ _))) ?_
    calc min 1 (ρ₀ / R) * r ≤ ρ₀ / R * R := by gcongr; exact min_le_right _ _
      _ = ρ₀ := div_mul_cancel₀ _ hR.ne'
  refine ⟨y, (ball_subset_ball ?_).trans (hy.trans
    (inter_subset_inter_right _ (ball_subset_ball (min_le_left _ _))))⟩
  calc 1 / 4 / (1 + K) * min 1 (ρ₀ / R) * r = 1 / 4 / (1 + K) * (min 1 (ρ₀ / R) * r) := by ring
    _ ≤ 1 / 4 / (1 + K) * min r ρ₀ := by gcongr
    _ = min r ρ₀ / 4 / (1 + K) := by ring

/-- **The exterior corkscrew condition.** For a Lipschitz domain `Ω` with compact frontier, for
instance a bounded Lipschitz domain in a proper space, and `R > 0` there is `δ > 0` such that for
every `x ∉ Ω` and every `0 < r ≤ R`, the ball `B(x, r)` contains a ball of radius `δ r` disjoint
from the closure of `Ω`. -/
theorem exists_ball_subset_compl_closure_inter_ball (hΩ : Ω.IsLipschitzDomain E)
    (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ x ∉ Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ y, ball y (δ * r) ⊆ (closure Ω)ᶜ ∩ ball x r := by
  obtain ⟨δ, hδ, hball⟩ := hΩ.compl_closure.exists_ball_subset_inter_ball
    (by rwa [frontier_compl, hΩ.frontier_closure]) hR
  exact ⟨δ, hδ, fun x hx ↦ hball x (hΩ.closure_compl_closure ▸ mem_compl hx)⟩

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {μ : Measure F}
  [μ.IsAddHaarMeasure]

/-- **The measure density property of a Lipschitz domain.** For a Lipschitz domain `Ω` with
compact frontier, an additive Haar measure `μ` and `R > 0`, there is `c > 0` such that
`c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)` for every `x` in the closure of `Ω` and every `0 < r ≤ R`, where
`B(x, r)` is the open ball. -/
theorem exists_pos_mul_measure_ball_le_measure_ball_inter
    (hΩ : Ω.IsLipschitzDomain E) (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ closure Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * μ (ball x r) ≤ μ (ball x r ∩ Ω) := by
  obtain ⟨δ, hδ, hball⟩ := hΩ.exists_ball_subset_inter_ball hK hR
  refine ⟨Real.toNNReal (δ ^ finrank ℝ F), by simp [hδ], fun x hx r hr hrR ↦ ?_⟩
  obtain ⟨y, hy⟩ := hball x hx r hr hrR
  calc ((Real.toNNReal (δ ^ finrank ℝ F) : ℝ≥0) : ℝ≥0∞) * μ (ball x r)
      = μ (ball y (δ * r)) := by
        rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity),
          Measure.addHaar_ball_of_pos μ x hr, Measure.addHaar_ball_of_pos μ y (by positivity),
          mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ μ (ball x r ∩ Ω) := measure_mono (hy.trans (inter_comm _ _).subset)

/-- **The measure density property of a Lipschitz domain.** For a Lipschitz domain `Ω` with
compact frontier, an additive Haar measure `μ` and `R > 0`, there is `c > 0` such that
`c μ(B(x, r)) ≤ μ(B(x, r) ∩ Ω)` for every `x` in the closure of `Ω` and every `0 < r ≤ R`, where
`B(x, r)` is the closed ball. -/
theorem exists_pos_mul_measure_closedBall_le_measure_closedBall_inter
    (hΩ : Ω.IsLipschitzDomain E) (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ closure Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r ∩ Ω) := by
  obtain ⟨c, hc, hdens⟩ := hΩ.exists_pos_mul_measure_ball_le_measure_ball_inter (μ := μ) hK hR
  refine ⟨c, hc, fun x hx r hr hrR ↦ ?_⟩
  rw [Measure.addHaar_closedBall μ x hr.le, ← Measure.addHaar_ball_of_pos μ x hr]
  exact (hdens x hx r hr hrR).trans
    (measure_mono (inter_subset_inter_left _ ball_subset_closedBall))

/-- **The exterior measure density property of a Lipschitz domain.** For a Lipschitz domain `Ω`
with compact frontier, an additive Haar measure `μ` and `R > 0`, there is `c > 0` such that
`c μ(B(x, r)) ≤ μ(B(x, r) \ closure Ω)` for every `x ∉ Ω` and every `0 < r ≤ R`, where `B(x, r)`
is the open ball. -/
theorem exists_pos_mul_measure_ball_le_measure_ball_sdiff_closure
    (hΩ : Ω.IsLipschitzDomain E) (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∉ Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * μ (ball x r) ≤ μ (ball x r \ closure Ω) := by
  obtain ⟨c, hc, hdens⟩ := hΩ.compl_closure.exists_pos_mul_measure_ball_le_measure_ball_inter
    (μ := μ) (by rwa [frontier_compl, hΩ.frontier_closure]) hR
  refine ⟨c, hc, fun x hx r hr hrR ↦ ?_⟩
  rw [sdiff_eq]
  exact hdens x (hΩ.closure_compl_closure ▸ mem_compl hx) r hr hrR

/-- **The exterior measure density property of a Lipschitz domain.** For a Lipschitz domain `Ω`
with compact frontier, an additive Haar measure `μ` and `R > 0`, there is `c > 0` such that
`c μ(B(x, r)) ≤ μ(B(x, r) \ closure Ω)` for every `x ∉ Ω` and every `0 < r ≤ R`, where `B(x, r)`
is the closed ball. -/
theorem exists_pos_mul_measure_closedBall_le_measure_closedBall_sdiff_closure
    (hΩ : Ω.IsLipschitzDomain E) (hK : IsCompact (frontier Ω)) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∉ Ω, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * μ (closedBall x r) ≤ μ (closedBall x r \ closure Ω) := by
  obtain ⟨c, hc, hdens⟩ :=
    hΩ.compl_closure.exists_pos_mul_measure_closedBall_le_measure_closedBall_inter
      (μ := μ) (by rwa [frontier_compl, hΩ.frontier_closure]) hR
  refine ⟨c, hc, fun x hx r hr hrR ↦ ?_⟩
  rw [sdiff_eq]
  exact hdens x (hΩ.closure_compl_closure ▸ mem_compl hx) r hr hrR

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {f : F → G}

/-- **Campanato's characterization on a bounded Lipschitz domain.** Let `Ω` be a bounded Lipschitz
domain in a space of dimension `n`, let `α > 0` and `p ≥ 1`. A function `f` locally integrable
for `μ.restrict Ω` agrees almost everywhere on `Ω` with a function that is `α`-Hölder continuous on
`Ω` if and only if it belongs to the Campanato space `𝓛^{p,λ}(Ω)` for `λ = n + p α`. -/
theorem exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top (hΩ : Ω.IsLipschitzDomain E)
    (hb : IsBounded Ω) {α : ℝ≥0} (hα : 0 < α) {p : ℝ} (hp : 1 ≤ p)
    (hf : LocallyIntegrable f (μ.restrict Ω)) :
    (∃ (K : ℝ≥0) (g : F → G), HolderOnWith K α g Ω ∧ f =ᵐ[μ.restrict Ω] g) ↔
      TauCeti.MeasureTheory.campanatoSeminormPow μ Ω p (finrank ℝ F + p * α) f ≠ ⊤ := by
  have hdiam : 2 * ediam Ω ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (isBounded_iff_ediam_ne_top.1 hb)
  obtain ⟨c, hc, hdens⟩ := hΩ.exists_pos_mul_measure_closedBall_le_measure_closedBall_inter
    (μ := μ) (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (R := (2 * ediam Ω).toReal + 1) (by positivity)
  refine TauCeti.MeasureTheory.exists_holderOnWith_ae_eq_iff_campanatoSeminormPow_ne_top hα hp hc
    hΩ.isOpen.nullMeasurableSet hf fun x hx r hr hr' ↦ hdens x (subset_closure hx) r hr ?_
  linarith [(ENNReal.ofReal_le_iff_le_toReal hdiam).1 hr']

end IsLipschitzDomain

end Set
