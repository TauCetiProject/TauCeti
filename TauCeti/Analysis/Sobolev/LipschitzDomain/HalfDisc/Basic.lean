/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.Rotation
public import TauCeti.Analysis.Sobolev.LipschitzDomain.BallGraph

/-!
# Half-discs are Lipschitz domains

The open half-disc `TauCeti.halfDisc r` is the set of points of `WithLp 2 (ℝ × ℝ)` of norm less
than `r` with positive first coordinate. The first coordinate is the normal coordinate of the model
space of Lipschitz boundary charts, so in the complex coordinate `z = s + it` it plays the role of
`t = Im z`, and `halfDisc r` is the interior of the half-disc `{z | 0 ≤ Im z ∧ |z| < r}`.

For `r ≤ 0` the half-disc and its frontier are empty. For `0 < r` its frontier consists of the
segment `{0} × [-r, r]`, the arc of the circle of radius `r` with positive first coordinate, and
the two corners `(0, ±r)`. Each frontier point has an explicit Lipschitz boundary chart:

* on the open segment the chart is a translation and the graph is zero;
* on the arc the normal direction points to the centre, and the graph is the lower boundary of the
  disc, truncated so that it is globally Lipschitz;
* at a corner the normal direction `(3/5, ∓4/5)` points strictly between the inner normals of the
  segment and the arc, and the graph is the maximum of the two boundary graphs.

The frontier is compact, so a single Lipschitz bound serves all frontier points
(`Set.IsLipschitzDomain.exists_isLipschitzDomainWith`).

## Main declarations

* `TauCeti.halfDisc`: the open half-disc of radius `r`.
* `TauCeti.isLipschitzDomain_halfDisc`: the half-disc is a Lipschitz domain.
* `TauCeti.exists_isLipschitzDomainWith_halfDisc`: the half-disc is a Lipschitz domain with a
  uniform Lipschitz bound.

## References

* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
-/

public section

noncomputable section

open Metric Set TopologicalSpace TauCeti
open scoped NNReal

namespace TauCeti

/-- The open half-disc of radius `r` in `WithLp 2 (ℝ × ℝ)`: the points of norm less than `r` whose
first coordinate, the normal coordinate of Lipschitz boundary charts, is positive. -/
def halfDisc (r : ℝ) : Opens (WithLp 2 (ℝ × ℝ)) :=
  ⟨ball 0 r ∩ {x | 0 < x.fst},
    isOpen_ball.inter (isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst)⟩

@[simp]
theorem coe_halfDisc (r : ℝ) :
    (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) = ball 0 r ∩ {x | 0 < x.fst} := by
  rw [halfDisc, Opens.coe_mk]

@[simp]
theorem mem_halfDisc {r : ℝ} {x : WithLp 2 (ℝ × ℝ)} : x ∈ halfDisc r ↔ ‖x‖ < r ∧ 0 < x.fst := by
  rw [← SetLike.mem_coe, coe_halfDisc, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq]

theorem isBounded_halfDisc (r : ℝ) : Bornology.IsBounded (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) :=
  isBounded_ball.subset inter_subset_left

/-- The closure of the half-disc lies in the closed half-disc. -/
private theorem closure_halfDisc_subset (r : ℝ) :
    closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) ⊆ closedBall 0 r ∩ {x | 0 ≤ x.fst} :=
  closure_minimal (inter_subset_inter ball_subset_closedBall fun _ (hx : 0 < _) => hx.le)
    (isClosed_closedBall.inter (isClosed_le continuous_const
      (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst))

/-- A Lipschitz chart of the half-disc centred at a point `p` of the arc `‖p‖ = r` with
`p.fst > 0`, whose normal direction points to the centre of the disc. -/
private theorem exists_isLipschitzChart_halfDisc_of_arc {r : ℝ} {p : WithLp 2 (ℝ × ℝ)}
    (hp : ‖p‖ = r) (hp₁ : 0 < p.fst) :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 := by
  have hsq : r ^ 2 = p.fst ^ 2 + p.snd ^ 2 := by
    simp only [← hp, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  have hr0 : 0 ≤ r := hp ▸ norm_nonneg p
  have hr : 0 < r := lt_of_le_of_ne hr0 fun h => by subst h; nlinarith
  have ht : p.fst ≤ r := by nlinarith
  have hs : |p.snd| ≤ r := abs_le_of_sq_le_sq (by nlinarith) hr0
  have hαβ : (-p.fst / r) ^ 2 + (-p.snd / r) ^ 2 = 1 := by
    field_simp
    linear_combination hsq.symm
  set e := prodRecentredRotation (-p.fst / r) (-p.snd / r) hαβ p
  have he₁ : (e 0).fst = r := by
    rw [prodRecentredRotation_apply_fst, WithLp.zero_fst, WithLp.zero_snd]
    field_simp
    linear_combination -hsq
  have he₂ : (e 0).snd = 0 := by
    rw [prodRecentredRotation_apply_snd, WithLp.zero_fst, WithLp.zero_snd]
    ring
  refine ⟨e, ballGraph r (r / 2) (e 0), _, p.fst / 4, p.fst / 4,
    isLipschitzChart_of_forall_mem_iff (by positivity) (by positivity)
      (lipschitzWith_ballGraph (by positivity) (by linarith)) fun z hz => ?_,
    prodRecentredRotation_apply_self _ _ _ _⟩
  have hz' := hz
  rw [mem_normalCylinder, Real.norm_eq_abs] at hz'
  obtain ⟨-, hu, hv⟩ := hz'
  have hfst : 0 < (e.symm z).fst := by
    rw [prodRecentredRotation_symm_apply_fst]
    have hsv : -(p.snd * z.snd) ≤ r * (p.fst / 4) :=
      calc -(p.snd * z.snd) ≤ |p.snd * z.snd| := neg_le_abs _
        _ = |p.snd| * |z.snd| := abs_mul _ _
        _ ≤ r * (p.fst / 4) := mul_le_mul hs hv.le (abs_nonneg _) hr0
    have key : 0 < r * p.fst - p.fst * z.fst + p.snd * z.snd := by nlinarith
    have heq : p.fst + (-p.fst / r * z.fst - -p.snd / r * z.snd) =
        (r * p.fst - p.fst * z.fst + p.snd * z.snd) / r := by
      field_simp
      ring
    rw [heq]
    exact div_pos key hr
  have hball := symm_mem_ball_iff_ballGraph_lt (e := e) hr0 (ρ := r / 2) (by linarith) (by
    rw [he₂, norm_zero]; linarith) hz
  simp only [coe_halfDisc, mem_inter_iff, mem_ofPred_eq, hball, hfst, and_true]

/-- A Lipschitz chart of the half-disc centred at a point `p` of the flat part of its boundary,
`p.fst = 0` and `|p.snd| < r`. -/
private theorem exists_isLipschitzChart_halfDisc_of_flat {r : ℝ} {p : WithLp 2 (ℝ × ℝ)}
    (hp₁ : p.fst = 0) (hp₂ : |p.snd| < r) :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 := by
  have hαβ : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  have ha : 0 < (r - |p.snd|) / 2 := by linarith
  refine ⟨prodRecentredRotation 1 0 hαβ p, fun _ => 0, 0, (r - |p.snd|) / 2, (r - |p.snd|) / 2,
    isLipschitzChart_of_forall_mem_iff ha ha (LipschitzWith.const 0) fun z hz => ?_,
    prodRecentredRotation_apply_self _ _ _ _⟩
  rw [mem_normalCylinder, Real.norm_eq_abs, ← and_assoc, ← abs_lt] at hz
  obtain ⟨hu, hv⟩ := hz
  have hfst : ((prodRecentredRotation 1 0 hαβ p).symm z).fst = z.fst := by
    rw [prodRecentredRotation_symm_apply_fst, hp₁]
    ring
  have hnorm : ‖(prodRecentredRotation 1 0 hαβ p).symm z‖ < r := by
    have hsnd : ((prodRecentredRotation 1 0 hαβ p).symm z).snd = p.snd + z.snd := by
      rw [prodRecentredRotation_symm_apply_snd]
      ring
    have hA := abs_nonneg z.fst
    have hB : |p.snd + z.snd| < (r + |p.snd|) / 2 := by
      linarith [abs_add_le p.snd z.snd]
    have hA2 : |z.fst| ^ 2 < ((r - |p.snd|) / 2) ^ 2 := by nlinarith
    have hB2 : |p.snd + z.snd| ^ 2 < ((r + |p.snd|) / 2) ^ 2 := by
      nlinarith [abs_nonneg (p.snd + z.snd)]
    have hS := abs_nonneg p.snd
    refine (sq_lt_sq₀ (norm_nonneg _) (by linarith)).1 ?_
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, Real.norm_eq_abs, hfst, hsnd]
    nlinarith
  simp only [coe_halfDisc, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq, hnorm, hfst, true_and]

/-- A Lipschitz chart of the half-disc centred at a corner `p`, `p.fst = 0` and `|p.snd| = r`. Its
normal direction `(3/5, -4/5 * σ)`, with `σ = p.snd / r`, points strictly into the quarter plane
spanned by the normals of the two boundary pieces, so both pieces are graphs over the tangential
direction. -/
private theorem exists_isLipschitzChart_halfDisc_of_corner {r : ℝ} {p : WithLp 2 (ℝ × ℝ)}
    (hr : 0 < r) (hp₁ : p.fst = 0) (hp₂ : |p.snd| = r) :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 := by
  set σ := p.snd / r
  have hs2 : p.snd ^ 2 = r ^ 2 := by rw [← sq_abs, hp₂]
  have hσ2 : σ ^ 2 = 1 := by
    rw [div_pow, hs2, div_self (by positivity)]
  have hσ : |σ| = 1 := by
    rw [abs_div, hp₂, abs_of_pos hr, div_self hr.ne']
  have hσs : σ * p.snd = r := by
    rw [div_mul_eq_mul_div, ← sq, hs2, sq, mul_div_assoc, div_self hr.ne', mul_one]
  have hαβ : (3 / 5 : ℝ) ^ 2 + (-(4 / 5) * σ) ^ 2 = 1 := by
    linear_combination (16 / 25 : ℝ) * hσ2
  set e := prodRecentredRotation (3 / 5) (-(4 / 5) * σ) hαβ p
  have he₁ : (e 0).fst = 4 * r / 5 := by
    rw [prodRecentredRotation_apply_fst, WithLp.zero_fst, WithLp.zero_snd, hp₁]
    linear_combination (4 / 5 : ℝ) * hσs
  have he₂ : ‖(e 0).snd‖ = 3 * r / 5 := by
    rw [prodRecentredRotation_apply_snd, WithLp.zero_fst, WithLp.zero_snd, hp₁, sub_zero, mul_zero,
      zero_add, zero_sub, mul_neg, Real.norm_eq_abs, abs_neg, abs_mul, hp₂]
    norm_num
    ring
  have hg : LipschitzWith 2 fun v : ℝ => -(4 / 3 * σ) * v := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_neg, abs_mul, hσ]
    norm_num
    nlinarith [abs_nonneg (v - w)]
  refine ⟨e, fun v => max (ballGraph r (4 * r / 5) (e 0) v) (-(4 / 3 * σ) * v), _, r / 5, r / 5,
    isLipschitzChart_of_forall_mem_iff (by positivity) (by positivity)
      ((lipschitzWith_ballGraph (by positivity) (by linarith)).max hg) fun z hz => ?_,
    prodRecentredRotation_apply_self _ _ _ _⟩
  have hfst : 0 < (e.symm z).fst ↔ -(4 / 3 * σ) * z.snd < z.fst := by
    rw [prodRecentredRotation_symm_apply_fst, hp₁]
    constructor <;> intro h <;> linarith
  have hball := symm_mem_ball_iff_ballGraph_lt (e := e) hr.le (ρ := 4 * r / 5) (by linarith)
    (by linarith) hz
  simp only [coe_halfDisc, mem_inter_iff, mem_ofPred_eq, hball, hfst, max_lt_iff]

/-- **The half-disc is a Lipschitz domain.** For `0 < r` its frontier consists of the flat part,
the arc and the two corners `(0, ±r)`, and each point has a Lipschitz boundary chart; for `r ≤ 0`
the half-disc is empty. -/
theorem isLipschitzDomain_halfDisc (r : ℝ) :
    (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomain ℝ := by
  refine Set.isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun p hp => ?_
  suffices H : ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 by
    obtain ⟨e, γ, K, a, b, hc, hex⟩ := H
    exact ⟨e, γ, K, a, b, hc, hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos⟩
  have hr : 0 < r := by
    by_contra h
    rw [coe_halfDisc, ball_eq_empty.2 (not_lt.1 h), empty_inter, frontier_empty] at hp
    exact hp
  have hcl := closure_halfDisc_subset r (frontier_subset_closure hp)
  have hnot : p ∉ halfDisc r := ((halfDisc r).isOpen.frontier_eq ▸ hp).2
  rw [mem_inter_iff, mem_closedBall_zero_iff, mem_ofPred_eq] at hcl
  obtain ⟨hpr, hp₁⟩ := hcl
  rw [mem_halfDisc, not_and_or, not_lt, not_lt] at hnot
  have hsq : ‖p‖ ^ 2 = p.fst ^ 2 + p.snd ^ 2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rcases hp₁.lt_or_eq with hp₁ | hp₁
  · exact exists_isLipschitzChart_halfDisc_of_arc (le_antisymm hpr (hnot.resolve_right
      hp₁.not_ge)) hp₁
  rcases lt_or_ge |p.snd| r with hs | hs
  · exact exists_isLipschitzChart_halfDisc_of_flat hp₁.symm hs
  · have hs' : |p.snd| ≤ r := by
      refine abs_le_of_sq_le_sq ?_ ((norm_nonneg p).trans hpr)
      nlinarith [norm_nonneg p]
    exact exists_isLipschitzChart_halfDisc_of_corner hr hp₁.symm (le_antisymm hs' hs)

/-- **The half-disc is a Lipschitz domain with a uniform constant**, since its frontier is
compact. -/
theorem exists_isLipschitzDomainWith_halfDisc (r : ℝ) :
    ∃ L, (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L :=
  (isLipschitzDomain_halfDisc r).exists_isLipschitzDomainWith
    ((isCompact_closedBall 0 r).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans ((closure_halfDisc_subset r).trans inter_subset_left)))

end TauCeti
