/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Short polygonal paths in Lipschitz domains

A bounded Lipschitz domain need not be convex, but nearby points of it can be joined inside it by
a short path: there are constants `C` and `δ > 0` such that any two points `x, y ∈ Ω` with
`‖x - y‖ < δ` are joined by three segments in `Ω` of total length at most `C ‖x - y‖`
(`Set.IsLipschitzDomain.exists_segment_chain`). Inside a boundary chart, where `Ω` is the region
above the graph of a `K`-Lipschitz function, the path goes up from `x` by `(K + 1) ‖x - y‖`
in the normal direction, across parallel to the segment `[x, y]`, and down to `y`; it stays above
the graph because the graph rises by at most `K ‖x - y‖` along the way, and its length is
`(2 K + 3) ‖x - y‖` (`Set.IsLipschitzChart.exists_segment_chain`). Away from the boundary the
segment `[x, y]` itself lies in `Ω`, and a Lebesgue number of a finite cover of the closure of
`Ω` by shrunken chart cylinders and `Ω` itself gives `δ`.

With the mean value inequality along the three segments
(`TauCeti.norm_image_sub_le_of_norm_fderiv_le_of_segment_subset`), a map whose derivative is
bounded by `L` on `Ω` is `C L`-Lipschitz between points of `Ω` at distance less than `δ`. This
replaces convexity in the Hölder bounds for lower derivatives of `C^{k,α}` functions on a bounded
Lipschitz domain
(`TauCeti.CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain`).
Some geometric condition is needed: on a slit disc the two sides of the slit are close in the
plane but far apart within the domain.
-/

public section

open Metric TauCeti
open scoped NNReal

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsLipschitzChart

variable {Ω : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}

/-- A segment of chart coordinates that stays in the cylinder and strictly above the graph
corresponds to a segment of `Ω`. -/
private theorem segment_symm_subset (hc : IsLipschitzChart Ω e γ K h r)
    {z w : WithLp 2 (ℝ × E)}
    (hzw : ∀ u ∈ segment ℝ z w, u ∈ normalCylinder h r ∧ γ u.snd < u.fst) :
    segment ℝ (e.symm z) (e.symm w) ⊆ Ω := by
  have himage : e.symm '' segment ℝ z w = segment ℝ (e.symm z) (e.symm w) :=
    image_segment ℝ (e.symm.toAffineEquiv : WithLp 2 (ℝ × E) →ᵃ[ℝ] F) z w
  rw [← himage]
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨huC, hug⟩ := hzw u hu
  rw [hc.mem_iff (by simpa using huC)]
  simpa using hug

omit [NormedSpace ℝ E] in
/-- Lifting a point of the half-height cylinder by `τ < h / 2` in the normal direction stays in
the full cylinder. -/
private theorem add_toLp_mem_normalCylinder {z : WithLp 2 (ℝ × E)} {τ : ℝ}
    (hz : z ∈ normalCylinder (h / 2) r) (hτ0 : 0 ≤ τ) (hτh : τ < h / 2) :
    z ∈ normalCylinder h r ∧ z + WithLp.toLp 2 (τ, 0) ∈ normalCylinder h r := by
  rw [mem_normalCylinder] at hz
  refine ⟨normalCylinder_mono (a := h) (b := r) (a' := h / 2) (b' := r)
    (by linarith) le_rfl (by rwa [mem_normalCylinder]), ?_⟩
  simp only [mem_normalCylinder, WithLp.add_fst, WithLp.add_snd, WithLp.toLp_fst,
    WithLp.toLp_snd, add_zero]
  exact ⟨by linarith, by linarith, hz.2.2⟩

/-- The vertical segment from a point strictly above the graph to its lift by `τ ≥ 0` stays
strictly above the graph. -/
private theorem lt_fst_of_mem_segment_add_toLp {z u : WithLp 2 (ℝ × E)} {τ : ℝ}
    (hz : γ z.snd < z.fst) (hτ0 : 0 ≤ τ) (hu : u ∈ segment ℝ z (z + WithLp.toLp 2 (τ, 0))) :
    γ u.snd < u.fst := by
  rw [segment_eq_image'] at hu
  obtain ⟨θ, ⟨hθ0, -⟩, rfl⟩ := hu
  simp only [add_sub_cancel_left, WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst,
    WithLp.smul_snd, WithLp.toLp_fst, WithLp.toLp_snd, smul_eq_mul, smul_zero, add_zero]
  nlinarith

/-- If `z` lies strictly above the graph of the `K`-Lipschitz function `γ` and
`(K + 1) ‖w - z‖ ≤ τ`, then the segment between the lifts of `z` and `w` by `τ` in the normal
direction lies strictly above the graph: along it the graph rises by at most `K ‖w - z‖` and the
height drops by at most `‖w - z‖`. -/
private theorem lt_fst_of_mem_segment_add_toLp_add_toLp (hγ : LipschitzWith K γ)
    {z w u : WithLp 2 (ℝ × E)} {τ : ℝ} (hz : γ z.snd < z.fst) (hτ : (K + 1) * ‖w - z‖ ≤ τ)
    (hu : u ∈ segment ℝ (z + WithLp.toLp 2 (τ, 0)) (w + WithLp.toLp 2 (τ, 0))) :
    γ u.snd < u.fst := by
  rw [segment_eq_image'] at hu
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hu
  have hlip := hγ.dist_le_mul (z.snd + θ • (w - z).snd) z.snd
  rw [dist_comm (z.snd + _), dist_self_add_right, norm_smul, Real.norm_of_nonneg hθ0,
    Real.dist_eq] at hlip
  simp only [add_sub_add_right_eq_sub, WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst,
    WithLp.smul_snd, WithLp.toLp_fst, WithLp.toLp_snd, smul_eq_mul, add_zero]
  have hs : ‖(w - z).snd‖ ≤ ‖w - z‖ := WithLp.norm_snd_le (x := w - z)
  have hf : |(w - z).fst| ≤ ‖w - z‖ := by
    simpa only [Real.norm_eq_abs] using WithLp.norm_fst_le (x := w - z)
  have h1 : (K : ℝ) * (θ * ‖(w - z).snd‖) ≤ K * ‖w - z‖ :=
    mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (w - z).snd]) K.coe_nonneg
  have h2 : -‖w - z‖ ≤ θ * (w - z).fst := by
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 hf).1 hθ0, norm_nonneg (w - z)]
  linarith [le_abs_self (γ (z.snd + θ • (w - z).snd) - γ z.snd)]

/-- **Short paths in a chart.** Let `x, y ∈ Ω` have chart coordinates in the half-height cylinder
`normalCylinder (h / 2) r`, with `(K + 1) ‖x - y‖ < h / 2`. Then `x` and `y` are joined in `Ω` by
three segments `[x, p]`, `[p, q]`, `[q, y]` of total length at most `(2 K + 3) ‖x - y‖`: the
points `p` and `q` lie above `x` and `y` at height `(K + 1) ‖x - y‖` in the normal direction. -/
theorem exists_segment_chain (hc : IsLipschitzChart Ω e γ K h r) {x y : F} (hx : x ∈ Ω)
    (hy : y ∈ Ω) (hxC : e x ∈ normalCylinder (h / 2) r) (hyC : e y ∈ normalCylinder (h / 2) r)
    (hxy : (K + 1) * dist x y < h / 2) :
    ∃ p q, segment ℝ x p ⊆ Ω ∧ segment ℝ p q ⊆ Ω ∧ segment ℝ q y ⊆ Ω ∧
      dist x p + dist p q + dist q y ≤ (2 * K + 3) * dist x y := by
  set τ := ((K : ℝ) + 1) * dist x y with hτ
  set v : WithLp 2 (ℝ × E) := WithLp.toLp 2 (τ, 0) with hv
  have hτ0 : 0 ≤ τ := by positivity
  have hcyl : ∀ {z}, z ∈ normalCylinder (h / 2) r →
      z ∈ normalCylinder h r ∧ z + v ∈ normalCylinder h r := fun hz ↦
    add_toLp_mem_normalCylinder hz hτ0 hxy
  have habove : ∀ {z}, z ∈ normalCylinder (h / 2) r → e.symm z ∈ Ω → γ z.snd < z.fst :=
    fun {z} hz hzΩ ↦ by simpa using (hc.mem_iff (by simpa using (hcyl hz).1)).1 hzΩ
  have hx' := habove hxC (by simpa using hx)
  have hy' := habove hyC (by simpa using hy)
  have hvert : ∀ {z}, z ∈ normalCylinder (h / 2) r → γ z.snd < z.fst →
      ∀ u ∈ segment ℝ z (z + v), u ∈ normalCylinder h r ∧ γ u.snd < u.fst :=
    fun hz hzγ u hu ↦ ⟨(convex_normalCylinder h r).segment_subset (hcyl hz).1 (hcyl hz).2 hu,
      lt_fst_of_mem_segment_add_toLp hzγ hτ0 hu⟩
  have hmid : ∀ u ∈ segment ℝ (e x + v) (e y + v),
      u ∈ normalCylinder h r ∧ γ u.snd < u.fst := fun u hu ↦
    ⟨(convex_normalCylinder h r).segment_subset (hcyl hxC).2 (hcyl hyC).2 hu,
      lt_fst_of_mem_segment_add_toLp_add_toLp hc.lipschitzWith hx'
        (by rw [← dist_eq_norm, e.dist_map, dist_comm]) hu⟩
  refine ⟨e.symm (e x + v), e.symm (e y + v), ?_, hc.segment_symm_subset hmid, ?_, ?_⟩
  · simpa using hc.segment_symm_subset (hvert hxC hx')
  · rw [segment_symm]
    simpa using hc.segment_symm_subset (hvert hyC hy')
  · have hvn : ‖v‖ = τ := by rw [hv, WithLp.norm_toLp_fst, Real.norm_of_nonneg hτ0]
    have h1 : dist x (e.symm (e x + v)) = τ := by
      rw [← e.dist_map, e.apply_symm_apply, dist_self_add_right, hvn]
    have h3 : dist (e.symm (e y + v)) y = τ := by
      rw [dist_comm, ← e.dist_map, e.apply_symm_apply, dist_self_add_right, hvn]
    rw [h1, h3, e.symm.dist_map, dist_add_right, e.dist_map, hτ]
    linarith

end IsLipschitzChart

namespace IsLipschitzDomain

omit [NormedSpace ℝ F] in
/-- Two points of a ball of radius `h / (4 (K + 1))` satisfy `(K + 1) ‖x - y‖ < h / 2`. -/
private theorem mul_dist_lt_of_mem_ball {K : ℝ≥0} {h : ℝ} {c x y : F}
    (hx : x ∈ ball c (h / (4 * (K + 1)))) (hy : y ∈ ball c (h / (4 * (K + 1)))) :
    ((K : ℝ) + 1) * dist x y < h / 2 := by
  rw [mem_ball] at hx hy
  have hxy : dist x y < h / (4 * (K + 1)) + h / (4 * (K + 1)) :=
    (dist_triangle_right x y c).trans_lt (add_lt_add hx hy)
  rw [← mul_two, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at hxy
  rw [lt_div_iff₀ two_pos]
  linarith

/-- The covering step behind `exists_segment_chain`: there are `K` and a scale `δ > 0` such that
for every `x ∈ Ω` the ball `ball x δ` lies in `Ω`, or in the half-height cylinder of a chart with
Lipschitz constant at most `K`, cut down to a ball of radius `h / (4 (K' + 1))`. -/
private theorem exists_ball_subset [ProperSpace F] {Ω : Set F} (hΩ : Ω.IsLipschitzDomain E)
    (hb : Bornology.IsBounded Ω) :
    ∃ (K : ℝ≥0) (δ : ℝ), 0 < δ ∧ ∀ x ∈ Ω, ball x δ ⊆ Ω ∨
      ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K' : ℝ≥0) (h r : ℝ) (c : F),
        IsLipschitzChart Ω e γ K' h r ∧ K' ≤ K ∧
          ball x δ ⊆ e ⁻¹' normalCylinder (h / 2) r ∩ ball c (h / (4 * (K' + 1))) := by
  have hcentred : ∀ x ∈ frontier Ω, ∃ (e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (K : ℝ≥0)
      (h r : ℝ), IsLipschitzChart Ω e γ K h r ∧ e x = 0 := fun x hx ↦ by
    obtain ⟨e, γ, K, h, r, hc, hxC⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
    obtain ⟨e', γ', h', r', hc', hex⟩ := hc.exists_isLipschitzChart_eq_zero hxC
    exact ⟨e', γ', K, h', r', hc', hex⟩
  choose e γ K h r hc hex using fun x : frontier Ω ↦ hcentred x x.property
  -- Around each frontier point, the half-height cylinder of its centred chart, cut down to a ball.
  set V : frontier Ω → Set F := fun x ↦
    e x ⁻¹' normalCylinder (h x / 2) (r x) ∩ ball x (h x / (4 * (K x + 1)))
  have hVopen : ∀ x, IsOpen (V x) := fun x ↦
    ((isOpen_normalCylinder _ _).preimage (e x).continuous).inter isOpen_ball
  have hVmem : ∀ x : frontier Ω, (x : F) ∈ V x := by
    intro x
    have hh := (hc x).height_pos
    refine ⟨?_, mem_ball_self (by positivity)⟩
    simpa [hex] using zero_mem_normalCylinder (E := E) (half_pos hh) (hc x).radius_pos
  have hcomp : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover V hVopen fun x hx ↦
    mem_iUnion.2 ⟨⟨x, hx⟩, hVmem _⟩
  -- A Lebesgue number for the cover of the closure of `Ω` by `Ω` and the sets `V i`, `i ∈ t`.
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun i : Option t ↦
      i.elim Ω fun j ↦ V j) hb.isCompact_closure
    (by rintro (_ | j); exacts [hΩ.isOpen, hVopen _]) (by
      intro x hx
      rw [closure_eq_self_union_frontier] at hx
      rcases hx with hx | hx
      · exact mem_iUnion.2 ⟨none, hx⟩
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (ht hx)
        exact mem_iUnion.2 ⟨some ⟨j, hj⟩, hxj⟩)
  refine ⟨t.sup K, δ, hδ, fun x hx ↦ ?_⟩
  obtain ⟨_ | ⟨j, hj⟩, hi⟩ := hleb x (subset_closure hx)
  · exact Or.inl hi
  · exact Or.inr ⟨e j, γ j, K j, h j, r j, j, hc j, Finset.le_sup hj, hi⟩

/-- **Short paths in a bounded Lipschitz domain.** There are constants `C` and `δ > 0` such that
any two points `x, y ∈ Ω` with `‖x - y‖ < δ` are joined in `Ω` by three segments `[x, p]`,
`[p, q]`, `[q, y]` of total length at most `C ‖x - y‖`. -/
theorem exists_segment_chain [ProperSpace F] {Ω : Set F} (hΩ : Ω.IsLipschitzDomain E)
    (hb : Bornology.IsBounded Ω) :
    ∃ C δ : ℝ≥0, 0 < δ ∧ ∀ x ∈ Ω, ∀ y ∈ Ω, dist x y < δ →
      ∃ p q, segment ℝ x p ⊆ Ω ∧ segment ℝ p q ⊆ Ω ∧ segment ℝ q y ⊆ Ω ∧
        dist x p + dist p q + dist q y ≤ C * dist x y := by
  obtain ⟨K, δ, hδ, hball⟩ := exists_ball_subset hΩ hb
  refine ⟨2 * K + 3, ⟨δ, hδ.le⟩, hδ, fun x hx y hy hxy ↦ ?_⟩
  have hyb : y ∈ ball x δ := by rwa [mem_ball, dist_comm]
  rcases hball x hx with hi | ⟨e, γ, K', h, r, c, hc, hK', hi⟩
  · -- The ball lies in `Ω`, so the segment `[x, y]` does.
    refine ⟨x, y, by simpa using hx,
      ((convex_ball x δ).segment_subset (mem_ball_self hδ) hyb).trans hi, by simpa using hy, ?_⟩
    simp only [dist_self, zero_add, add_zero]
    push_cast
    nlinarith [dist_nonneg (x := x) (y := y), K.coe_nonneg]
  · -- Both points lie in one shortened chart cylinder.
    obtain ⟨hxV, hyV⟩ := And.intro (hi (mem_ball_self hδ)) (hi hyb)
    obtain ⟨p, q, h1, h2, h3, hlen⟩ := hc.exists_segment_chain hx hy hxV.1 hyV.1
      (mul_dist_lt_of_mem_ball hxV.2 hyV.2)
    refine ⟨p, q, h1, h2, h3, hlen.trans ?_⟩
    have hK : (K' : ℝ) ≤ K := by exact_mod_cast hK'
    push_cast
    gcongr

end IsLipschitzDomain

end Set
