/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Order.Interval.Set.Infinite
import TauCeti.Analysis.Complex.Basic
import TauCeti.Topology.Codiscrete
import TauCeti.Topology.MetricSpace.NearestPoint

/-!
# Isolating singularities in Taylor expansion discs

For a discrete set of singularities in a left half-plane, one can isolate a singularity in a disc
centred on a vertical line to its right. Either a disc of the same radius centred at the real point
of the line is free of singularities, or the real-centred disc itself isolates a rightmost real
singularity. This is the geometric input to the two Taylor coefficient comparisons in the
windowed Landau theorem.

## References

* L. Alpöge, [Lean formalization of the Riemann hypothesis for Dirichlet L-functions](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005),
  `Deduction.landau_finite`, `Deduction.landau_dichotomy`, and `Deduction.landau_nearest` in
  `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`.
-/

public section

open Complex Filter Metric Set

namespace TauCeti

private theorem exists_shifted_isolating_disc {Z : Set ℂ} {σ R D : ℝ} {p : ℂ}
    (hp : p ∈ Z) (hleft : ∀ q ∈ Z, q.re ≤ σ) (hgap : σ - p.re < min D R)
    (hfin : (Z ∩ closedBall (⟨σ, p.im⟩ : ℂ) R).Finite) :
    ∃ t : ℝ, ∃ q ∈ Z, ∃ r, 0 < dist (⟨σ, t⟩ : ℂ) q ∧ dist (⟨σ, t⟩ : ℂ) q < r ∧
      r ≤ D ∧ Z ∩ ball ⟨σ, t⟩ r = {q} := by
  let L := min D R
  let ε := (L - (σ - p.re)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  let c₀ : ℂ := ⟨σ, p.im⟩
  let T := Z ∩ closedBall c₀ R
  -- Avoid ties and heights at which the centre could itself belong to `Z` in the search disc.
  have hbad := (hfin.finite_setOf_not_injOn_dist_complex_mk fun q hq ↦ hleft q hq.1).union
    (hfin.image Complex.im)
  obtain ⟨t, ht, htbad⟩ := ((Ioo_infinite (a := p.im - ε) (b := p.im + ε) (by linarith)).sdiff
    hbad).nonempty
  let c : ℂ := ⟨σ, t⟩
  have hinj : InjOn (fun q : ℂ ↦ dist c q) T := by
    by_contra hn
    exact htbad (Or.inl hn)
  have hshift : dist c c₀ < ε := by
    dsimp only [c, c₀]
    rw [Complex.dist_mk]
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_sq_eq_abs, abs_lt]
    exact ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have hpdist : dist p c₀ = σ - p.re := by
    have hm : (p - c₀).im = 0 := by simp [c₀]
    rw [Complex.dist_eq, ← Complex.abs_re_eq_norm.mpr hm]
    simp [c₀, abs_of_nonpos (sub_nonpos.mpr (hleft p hp))]
  have hpc : dist p c < L - ε := by
    have := dist_triangle_right p c c₀
    dsimp [ε] at hshift ⊢
    linarith
  have hsub : Z ∩ closedBall c (L - ε) ⊆ T := by
    intro q hq
    refine ⟨hq.1, mem_closedBall.mpr ?_⟩
    linarith [dist_triangle q c c₀, mem_closedBall.mp hq.2, min_le_right D R]
  have hpc' : p ∈ Z ∩ closedBall c (L - ε) := ⟨hp, hpc.le⟩
  have hF := hfin.subset hsub
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image _ (dist · c) hF ⟨p, hpc'⟩
  obtain ⟨r, hr, hrD, hEq⟩ := hF.exists_inter_ball_eq_singleton_of_forall_dist_lt hq.1
    ((hmin p hpc').trans_lt hpc) (fun w hw hne ↦ (hmin w hw).lt_of_ne fun heq ↦
      hne (hinj (hsub hw) (hsub hq) (by simpa only [dist_comm] using heq.symm)))
  have hne : c ≠ q := fun heq ↦ htbad (Or.inr ⟨q, hsub hq, congrArg Complex.im heq.symm⟩)
  exact ⟨t, q, hq.1, r, dist_pos.mpr hne, by simpa only [dist_comm] using hr,
    hrD.trans (by linarith [min_le_left D R]), hEq⟩

private theorem exists_real_isolating_disc {Z : Set ℂ} {σ R D : ℝ} {p : ℂ}
    (hp : p ∈ Z) (hD : dist (σ : ℂ) p = D) (hDR : D < R)
    (hfin : (Z ∩ closedBall (σ : ℂ) R).Finite) (hgap : ∀ q ∈ Z, D ≤ σ - q.re) :
    ∃ r, D < r ∧ r ≤ R ∧ Z ∩ ball (σ : ℂ) r = {((σ - D : ℝ) : ℂ)} := by
  have hre (q : ℂ) : σ - q.re ≤ dist (σ : ℂ) q := by
    simpa only [Complex.dist_eq, sub_re, ofReal_re] using Complex.re_le_norm ((σ : ℂ) - q)
  have heq (q : ℂ) (hq : q ∈ Z) (hd : dist (σ : ℂ) q = D) : q = ((σ - D : ℝ) : ℂ) := by
    have hcoord : σ - q.re = D := le_antisymm (hd ▸ hre q) (hgap q hq)
    have hD₀ : 0 ≤ D := hD ▸ dist_nonneg
    have habs : |((σ : ℂ) - q).re| = ‖(σ : ℂ) - q‖ := by
      rw [sub_re, ofReal_re, hcoord, abs_of_nonneg hD₀, ← Complex.dist_eq, hd]
    have him := Complex.abs_re_eq_norm.mp habs
    exact Complex.ext (by simp; linarith) (by simpa using him)
  have hpEq := heq p hp hD
  obtain ⟨r, hr, hrR, hEq⟩ := hfin.exists_inter_ball_eq_singleton_of_forall_dist_lt hp
    ((dist_comm p (σ : ℂ)).trans_lt (hD.trans_lt hDR)) (fun q hq hne ↦ by
      rw [dist_comm p, dist_comm q, hD]
      exact ((hgap q hq.1).trans (hre q)).lt_of_ne fun hd ↦
        hne ((heq q hq.1 hd.symm).trans hpEq.symm))
  rw [dist_comm p, hD] at hr
  exact ⟨r, hr, hrR, hpEq ▸ hEq⟩

/-- **Expansion disc dichotomy.** Let `Z` be relatively closed discrete to the right of `θ`, lie
at or to the left of `σ`, and contain a point strictly to the right of `θ`. Either a disc centred
on `re = σ` isolates one point of `Z` away from its centre and the real-centred disc of the same
radius misses `Z`, or a real-centred disc isolates a real point that is rightmost in `Z`. In both
cases the radius is at most `σ - θ`. -/
theorem exists_isolating_disc_or_rightmost_real {Z : Set ℂ} {σ θ : ℝ}
    (hZ : Zᶜ ∈ codiscreteWithin {z : ℂ | θ < z.re}) (hleft : ∀ p ∈ Z, p.re ≤ σ)
    (hpos : ∃ p ∈ Z, θ < p.re) :
    (∃ t : ℝ, ∃ p ∈ Z, ∃ r, 0 < dist (⟨σ, t⟩ : ℂ) p ∧ dist (⟨σ, t⟩ : ℂ) p < r ∧
      r ≤ σ - θ ∧ Z ∩ ball ⟨σ, t⟩ r = {p} ∧ Z ∩ ball (σ : ℂ) r = ∅) ∨
    ∃ β : ℝ, θ < β ∧ (β : ℂ) ∈ Z ∧ ∃ r, σ - β < r ∧ r ≤ σ - θ ∧
      Z ∩ ball (σ : ℂ) r = {(β : ℂ)} ∧ ∀ p ∈ Z, p.re ≤ β := by
  obtain ⟨p₀, hp₀, hθ⟩ := hpos
  -- Work with a slightly smaller radius to stay inside the domain of local finiteness.
  let R := σ - (θ + p₀.re) / 2
  have hR : R < σ - θ := by dsimp [R]; linarith
  have hpR : σ - p₀.re < R := by dsimp [R]; linarith
  have hfin (c : ℂ) (hc : c.re = σ) : (Z ∩ closedBall c R).Finite := by
    have hsub : closedBall c R ⊆ {z : ℂ | θ < z.re} := by
      intro z hz
      rw [mem_ofPred_eq]
      have hz' := mem_closedBall.mp hz
      rw [dist_comm, Complex.dist_eq] at hz'
      have hc' := Complex.re_le_norm (c - z)
      simp only [sub_re, hc] at hc'
      linarith only [hc'.trans hz', hR]
    simpa only [inter_comm] using
      (isCompact_closedBall c R).finite_inter_of_compl_mem_codiscreteWithin hsub hZ
  have hfin' := hfin (σ : ℂ) (ofReal_re σ)
  -- Cap the nearest distance at `R`, so only points in the compact search disc matter.
  have hmin : ∃ D ≤ R, (∀ p ∈ Z, D ≤ dist (σ : ℂ) p) ∧
      (D = R ∨ ∃ p ∈ Z, dist (σ : ℂ) p = D) := by
    obtain he | hn := (Z ∩ closedBall (σ : ℂ) R).eq_empty_or_nonempty
    · refine ⟨R, le_rfl, fun p hp ↦ le_of_not_ge fun hd ↦ ?_, Or.inl rfl⟩
      exact Set.notMem_empty p (he ▸ ⟨hp, mem_closedBall.mpr (by rwa [dist_comm])⟩)
    · obtain ⟨p, hp, hpmin⟩ := Set.exists_min_image _ (dist (σ : ℂ) ·) hfin' hn
      have hpR' := mem_closedBall.mp hp.2
      rw [dist_comm] at hpR'
      refine ⟨_, hpR', fun q hq ↦ ?_, Or.inr ⟨p, hp.1, rfl⟩⟩
      by_cases hqR : dist (σ : ℂ) q ≤ R
      · exact hpmin q ⟨hq, mem_closedBall.mpr (by rwa [dist_comm])⟩
      · exact hpR'.trans (le_of_not_ge hqR)
  obtain ⟨D, hDR, hlower, hatt⟩ := hmin
  by_cases hb : ∃ p ∈ Z, σ - p.re < D
  · obtain ⟨p, hp, hgap⟩ := hb
    obtain ⟨t, q, hq, r, hd, hdr, hrD, he⟩ := exists_shifted_isolating_disc hp hleft
      (lt_min hgap (hgap.trans_le hDR)) (hfin ⟨σ, p.im⟩ rfl)
    refine Or.inl ⟨t, q, hq, r, hd, hdr, hrD.trans (hDR.trans hR.le), he, ?_⟩
    exact eq_empty_iff_forall_notMem.mpr fun w hw ↦
      (hrD.trans (hlower w hw.1)).not_gt (by simpa only [dist_comm] using mem_ball.mp hw.2)
  · push Not at hb
    have hlt : D < R := (hb p₀ hp₀).trans_lt hpR
    obtain ⟨p, hp, hd⟩ := hatt.resolve_left hlt.ne
    obtain ⟨r, hr, hrR, he⟩ := exists_real_isolating_disc hp hd hlt hfin' hb
    refine Or.inr ⟨σ - D, by linarith, ?_, r, by linarith, hrR.trans hR.le, he,
      fun q hq ↦ by linarith [hb q hq]⟩
    have hm : ((σ - D : ℝ) : ℂ) ∈ Z ∩ ball (σ : ℂ) r := he.symm ▸ mem_singleton _
    exact hm.1

end TauCeti
