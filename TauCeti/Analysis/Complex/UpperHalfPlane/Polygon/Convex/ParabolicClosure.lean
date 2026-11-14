/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import Mathlib.Analysis.Convex.GaugeRescale
import TauCeti.Analysis.Complex.UpperHalfPlane.Parabola
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Height
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Disk
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Truncation

/-!
# Adjoining ideal vertices to a convex hyperbolic polygon gives a closed disk

A compact convex hyperbolic polygon is homeomorphic to the closed unit disk `closedBall (0 : ℂ) 1`,
with its interior mapped to the open unit disk and its sides mapped to the unit circle
(`CompactConvexPolygon.exists_homeomorph_closedBall`). When a convex polygon `P` has ideal vertices,
its carrier is noncompact, running off to `∂ℍ` at each ideal vertex.

This file proves the general, group-free counterpart for an arbitrary `P : ConvexPolygon n`:
adjoining one boundary point for each ideal vertex `{i : Fin n // (P.vertex i).isRight}` identifies
`P.carrier ⊕ {i : Fin n // (P.vertex i).isRight}` with `closedBall (0 : ℂ) 1`
(`ConvexPolygon.exists_equiv_closedBall`) so that:

* `P.carrier` embeds openly into `closedBall (0 : ℂ) 1`, carrying `interior P.carrier` onto
  `ball (0 : ℂ) 1` and `⋃ j, P.side j` onto the complement in `sphere (0 : ℂ) 1` of the adjoined
  ideal-vertex points;
* each ideal vertex `i` sits on `sphere (0 : ℂ) 1`, and its punctured neighborhoods in
  `closedBall (0 : ℂ) 1` come from points of `P.carrier` lying inside arbitrarily deep horodiscs
  `{z | B < Im (g • z)}` at `P.vertex i`.

## Proof

Choose `h₀ ∈ PSL(2, ℝ)` so that the reversed supporting geodesic `sideGeodesic 0 * pslS` of
`Q := h₀ • P` has `∞` strictly on its left. Then `sideGeodesic 0` is a semicircle containing `Q`
underneath it, so `Q.carrier` is bounded in `ℂ`, no vertex of `Q` is `∞`, and the Euclidean convex
set `s := parabolaMap '' Q.carrier` is bounded with nonempty interior. Gauge rescaling
(`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`) carries `closure s`
homeomorphically onto `closedBall (0 : ℂ) 1`. Because `Q` minus open horodiscs at its ideal
vertices is compact (`ConvexPolygon.isCompact_carrier_diff_iUnion`), the points of `closure s \ s`
are precisely the points `(x, x²)` on the boundary parabola at the real ideal vertices `x` of `Q`,
and approaching `(x, x²)` within `s` forces `z ∈ Q.carrier` into arbitrarily deep horodiscs at `x`.

## Main result

* `ConvexPolygon.exists_equiv_closedBall`: adjoining the ideal vertices of a convex hyperbolic
  polygon compactifies its carrier to the closed unit disk, with horodisc neighborhoods at each
  ideal vertex.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §9.2.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago Press,
  1992, §§4.2–4.3.
-/

public section

noncomputable section

open Filter Metric Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n]

/-! ### Normalizing a convex polygon underneath a semicircle -/

/-- Every convex polygon has a `PSL(2, ℝ)` translate whose reversed edge `0` has `∞` strictly on
its left, so its carrier lies underneath a semicircle and avoids `∞` on `∂ℍ`. -/
private theorem exists_smul_infty_mem_boundaryLeftHalfPlane_mul_pslS (P : ConvexPolygon n) :
    ∃ h₀ : PSL(2, ℝ),
      (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane ((h₀ • P).sideGeodesic 0 * pslS) := by
  obtain ⟨a₀, ha₀⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ((-1 : ℝ) : OnePoint ℝ) ∞
  refine ⟨a₀ * (P.sideGeodesic 0 * pslS)⁻¹, ?_⟩
  set h₀ := a₀ * (P.sideGeodesic 0 * pslS)⁻¹
  have hg₁ := isGeodesicFromTo_mul_pslS_iff.2 ((h₀ • P).isGeodesicFromTo_sideGeodesic 0)
  have hg₂ : IsGeodesicFromTo a₀ ((h₀ • P).vertex (0 + 1)) ((h₀ • P).vertex 0) := by
    have hmul : h₀ * P.sideGeodesic 0 * pslS = a₀ := by
      simp [h₀, mul_assoc]
    rw [← hmul]
    simpa only [vertex_smul] using
      isGeodesicFromTo_mul_pslS_iff.2 ((P.isGeodesicFromTo_sideGeodesic 0).smul h₀)
  rw [hg₂.boundaryLeftHalfPlane_eq hg₁, ← mul_one a₀, ← smul_boundaryLeftHalfPlane, ← ha₀]
  refine Set.smul_mem_smul_set ((coe_mem_boundaryLeftHalfPlane_iff 1 (-1)).2 ?_)
  rw [sideForm_one]
  norm_num

private theorem vertex_ne_infty_of_infty_mem {Q : ConvexPolygon n}
    (hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)) (i : Fin n) :
    Q.vertex i ≠ .inr ∞ := by
  intro hi
  have hmem := Q.vertex_mem_extClosedLeftHalfPlane_sideGeodesic 0 i
  rw [hi, inr_mem_extClosedLeftHalfPlane_iff] at hmem
  rcases hmem with h₀ | h₁ | hleft
  · exact smul_infty_notMem_boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)
      (by rwa [mul_smul, pslS_smul_infty, ← h₀])
  · exact smul_zero_notMem_boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)
      (by rwa [mul_smul, pslS_smul_zero, ← h₁])
  · obtain ⟨B, hB⟩ := (atImInfty_mem _).1
      ((eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane hleft).and
        (eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane hinf))
    have hpos : 0 < max B 0 + 1 := by positivity
    let z₀ : ℍ := ⟨⟨0, max B 0 + 1⟩, hpos⟩
    have hBz₀ : B ≤ z₀.im := by
      rw [← coe_im]
      dsimp only [z₀]
      linarith [le_max_left B 0]
    obtain ⟨hz₁, hz₂⟩ := hB z₀ hBz₀
    rw [leftHalfPlane_mul_pslS, mem_rightHalfPlane_iff] at hz₂
    exact ((mem_leftHalfPlane_iff _ _).1 hz₁).not_gt hz₂

/-- If `∞` lies strictly on the left of `Q.sideGeodesic 0 * pslS`, then `Q.carrier` lies inside a
Euclidean disk centred on `ℝ`, so its heights are bounded, `parabolaMap '' Q.carrier` is bounded,
and no vertex of `Q` is `∞`. -/
private theorem bounded_and_vertex_ne_infty_of_infty_mem {Q : ConvexPolygon n}
    (hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (Q.sideGeodesic 0 * pslS)) :
    (∃ ρ > 0, ∀ z ∈ Q.carrier, z.im ≤ ρ) ∧
      Bornology.IsBounded (parabolaMap '' Q.carrier) ∧
      ∀ i, Q.vertex i ≠ .inr ∞ := by
  obtain ⟨m, ρ, κ, hρ, hκ, hform⟩ := exists_sideForm_eq_of_infty_mem_boundaryLeftHalfPlane hinf
  have hnormSq {z : ℍ} (hz : z ∈ Q.carrier) : Complex.normSq ((z : ℂ) - m) ≤ ρ ^ 2 := by
    have hzcl := Q.carrier_subset_closure_leftHalfPlane 0 hz
    have hnot : z ∉ leftHalfPlane (Q.sideGeodesic 0 * pslS) := by
      rw [leftHalfPlane_mul_pslS, mem_rightHalfPlane_iff]
      exact not_lt.2 ((mem_closure_leftHalfPlane_iff _ _).1 hzcl)
    have hnonneg : 0 ≤ sideForm (Q.sideGeodesic 0 * pslS) z :=
      not_lt.1 fun hneg ↦ hnot ((mem_leftHalfPlane_iff_sideForm_neg _ _).2 hneg)
    rw [hform] at hnonneg
    linarith [nonneg_of_mul_nonneg_right hnonneg hκ]
  have him {z : ℍ} (hz : z ∈ Q.carrier) : z.im ≤ ρ := by
    have hsq : z.im ^ 2 ≤ Complex.normSq ((z : ℂ) - m) := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero, coe_re, coe_im]
      nlinarith [sq_nonneg (z.re - m)]
    nlinarith [hsq.trans (hnormSq hz)]
  refine ⟨⟨ρ, hρ, fun z hz ↦ him hz⟩, ?_, vertex_ne_infty_of_infty_mem hinf⟩
  set R := |m| + ρ
  refine (isCompact_Icc.reProdIm isCompact_Icc :
      IsCompact (Icc (-R) R ×ℂ Icc 0 (R ^ 2 + ρ ^ 2))).isBounded.subset ?_
  rintro _ ⟨z, hz, rfl⟩
  have hre : (z.re - m) ^ 2 ≤ ρ ^ 2 := by
    have hsq : (z.re - m) ^ 2 ≤ Complex.normSq ((z : ℂ) - m) := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero, coe_re, coe_im]
      nlinarith [sq_nonneg z.im]
    exact hsq.trans (hnormSq hz)
  have hsub : |z.re - m| ≤ ρ := by nlinarith [abs_nonneg (z.re - m), sq_abs (z.re - m)]
  have habs : |z.re| ≤ R := by
    have := abs_le.1 hsub
    have := le_abs_self m
    have := neg_abs_le m
    rw [abs_le]
    constructor <;> linarith
  have hzre2 : z.re ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs z.re, abs_nonneg z.re]
  have hzim2 : z.im ^ 2 ≤ ρ ^ 2 := by nlinarith [him hz, z.im_pos]
  rw [Complex.mem_reProdIm, parabolaMap_re, parabolaMap_im, Complex.normSq_apply, coe_re, coe_im]
  exact ⟨abs_le.1 habs, by nlinarith, by nlinarith⟩

/-! ### Closure and horodisc neighborhoods in parabolic coordinates -/

/-- Continuous retraction of `ℂ` onto the closed upper half-plane that inverts `parabolaMap` above
the parabola `v = u²` and sends `(x, x²)` to `x`. -/
private def parabolaLift (w : ℂ) : ℂ :=
  ⟨w.re, Real.sqrt (max 0 (w.im - w.re ^ 2))⟩

private theorem continuous_parabolaLift : Continuous parabolaLift := by
  unfold parabolaLift
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

private theorem parabolaLift_parabolaMap (z : ℍ) : parabolaLift (parabolaMap z) = (z : ℂ) := by
  apply Complex.ext
  · simp [parabolaLift]
  · simp only [parabolaLift, parabolaMap_re, parabolaMap_im, Complex.normSq_apply, coe_re, coe_im]
    have h : z.re * z.re + z.im * z.im - z.re ^ 2 = z.im ^ 2 := by ring
    rw [h, max_eq_right (sq_nonneg z.im), Real.sqrt_sq z.im_pos.le]

private theorem parabolaLift_of_sq_eq (x : ℝ) : parabolaLift ⟨x, x ^ 2⟩ = (x : ℂ) := by
  apply Complex.ext <;> simp [parabolaLift]

/-- Approaching `(x, x²)` in parabolic coordinates from within `Q.carrier` forces points into any
prescribed horodisc at `x` and hence requires `x` to be an ideal vertex of `Q`. -/
private theorem eventually_parabolaMap_horodisc {Q : ConvexPolygon n}
    (hne : ∀ i, Q.vertex i ≠ .inr ∞) {g : Fin n → PSL(2, ℝ)}
    (hg : ∀ i ξ, Q.vertex i = .inr ξ → g i • ξ = ∞) (x : ℝ) {A : Fin n → ℝ}
    (hA : ∀ j, Q.vertex j ≠ .inr (x : OnePoint ℝ) → 1 ≤ A j) :
    ∀ᶠ w in 𝓝 (⟨x, x ^ 2⟩ : ℂ), ∀ z ∈ Q.carrier, parabolaMap z = w →
      ∃ i, Q.vertex i = .inr (x : OnePoint ℝ) ∧ A i < (g i • z).im := by
  set K := Q.carrier \ ⋃ j, ⋃ (_ : (Q.vertex j).isRight), {z : ℍ | A j < (g j • z).im}
  have hKclosed : IsClosed (((↑) : ℍ → ℂ) '' K) :=
    ((Q.isCompact_carrier_diff_iUnion g hg A).image continuous_coe).isClosed
  have hxnotK : (x : ℂ) ∉ ((↑) : ℍ → ℂ) '' K := by
    rintro ⟨z, -, hz⟩
    exact z.im_pos.ne' (by simpa using congrArg Complex.im hz)
  have hU₀ : ∀ᶠ ζ in 𝓝 (x : ℂ), ζ ∉ ((↑) : ℍ → ℂ) '' K :=
    hKclosed.isOpen_compl.mem_nhds hxnotK
  have hother (j : Fin n) :
      ∀ᶠ ζ : ℂ in 𝓝 (x : ℂ), Q.vertex j ≠ .inr (x : OnePoint ℝ) →
        ∀ z : ℍ, (z : ℂ) = ζ → (Q.vertex j).isRight → (g j • z).im ≤ A j := by
    by_cases hj : (Q.vertex j).isRight
    · obtain ⟨ξ, hξ⟩ := Sum.isRight_iff.1 hj
      obtain ⟨xj, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hne j (hξ.trans (congrArg _ h))
      by_cases hxj : xj = x
      · subst hxj
        exact Eventually.of_forall fun _ hne' ↦ (hne' hξ).elim
      · obtain ⟨c, hc, hgc⟩ := exists_im_smul_eq_div_of_smul_coe_eq_infty (hg j xj hξ)
        have hcont : ContinuousAt (fun ζ : ℂ ↦ ζ.im / (c * Complex.normSq (ζ - xj))) (x : ℂ) := by
          refine ContinuousAt.div Complex.continuous_im.continuousAt
            (continuous_const.mul ((Complex.continuous_normSq.comp
              (continuous_id.sub continuous_const)))).continuousAt ?_
          refine mul_ne_zero hc.ne' (Complex.normSq_pos.2 (sub_ne_zero.2 ?_)).ne'
          exact Complex.ofReal_injective.ne (Ne.symm hxj)
        have hval : ((x : ℂ).im / (c * Complex.normSq ((x : ℂ) - xj))) < 1 := by simp
        filter_upwards [hcont.eventually (gt_mem_nhds hval)] with ζ hζ hne' z rfl _
        rw [hgc]
        exact hζ.le.trans (hA j hne')
    · exact Eventually.of_forall fun _ _ _ _ hj' ↦ (hj hj').elim
  have hall : ∀ᶠ ζ in 𝓝 (x : ℂ), ζ ∉ ((↑) : ℍ → ℂ) '' K ∧
      ∀ j, Q.vertex j ≠ .inr (x : OnePoint ℝ) →
        ∀ z : ℍ, (z : ℂ) = ζ → (Q.vertex j).isRight → (g j • z).im ≤ A j :=
    hU₀.and ( Filter.eventually_all.2 hother )
  have hpull : Tendsto parabolaLift (𝓝 (⟨x, x ^ 2⟩ : ℂ)) (𝓝 (x : ℂ)) :=
    parabolaLift_of_sq_eq x ▸ continuous_parabolaLift.continuousAt
  filter_upwards [hpull.eventually hall] with w ⟨hwK, hwj⟩ z hz rfl
  have hz_coe : parabolaLift (parabolaMap z) = (z : ℂ) := parabolaLift_parabolaMap z
  rw [hz_coe] at hwK hwj
  have hznotK : z ∉ K := fun hzK ↦ hwK ⟨z, hzK, rfl⟩
  have hmemU : z ∈ ⋃ j, ⋃ (_ : (Q.vertex j).isRight), {z : ℍ | A j < (g j • z).im} := by
    by_contra hnotU
    exact hznotK ⟨hz, hnotU⟩
  obtain ⟨i, hi, hAi⟩ := by simpa only [mem_iUnion, mem_ofPred_eq] using hmemU
  refine ⟨i, ?_, hAi⟩
  by_contra hne'
  exact hAi.not_ge (hwj i hne' z rfl hi)

private theorem eventually_geodesicLine_mem_carrier_atBot {Q : ConvexPolygon n} {i : Fin n}
    {ξ : OnePoint ℝ} (hξ : Q.vertex i = .inr ξ) :
    ∀ᶠ t in atBot, geodesicLine (Q.sideGeodesic i) t ∈ Q.carrier := by
  have hg := Q.isGeodesicFromTo_sideGeodesic i
  rw [hξ] at hg
  have hside : ∃ t₀ : ℝ, ∀ t ≤ t₀, geodesicLine (Q.sideGeodesic i) t ∈ Q.side i := by
    rw [Q.side_def, hξ]
    rcases hq : Q.vertex (i + 1) with w | η
    · rw [hq] at hg
      obtain ⟨hg₀, t₀, rfl⟩ := isGeodesicFromTo_inr_inl.1 hg
      exact ⟨t₀, fun t ht ↦ by rw [← hg₀, ← geodesicLine_image_Iic]; exact ⟨t, ht, rfl⟩⟩
    · rw [hq] at hg
      obtain ⟨hg₀, hg₁⟩ := isGeodesicFromTo_inr_inr.1 hg
      exact ⟨0, fun t _ ↦ by
        rw [← hg₀, ← hg₁, ← range_geodesicLine_eq_extGeodesicSegment]
        exact ⟨t, rfl⟩⟩
  obtain ⟨t₀, ht₀⟩ := hside
  filter_upwards [eventually_le_atBot t₀] with t ht
  exact Q.side_subset_carrier i (ht₀ t ht)

/-- Every real ideal vertex `(x : OnePoint ℝ)` of a bounded convex polygon `Q` contributes `(x, x²)`
to `closure (parabolaMap '' Q.carrier)`. -/
private theorem mk_sq_mem_closure_parabolaMap_image_carrier {Q : ConvexPolygon n}
    {ρ : ℝ} (him : ∀ z ∈ Q.carrier, z.im ≤ ρ) {i : Fin n} {x : ℝ}
    (hx : Q.vertex i = .inr (x : OnePoint ℝ)) :
    (⟨x, x ^ 2⟩ : ℂ) ∈ closure (parabolaMap '' Q.carrier) := by
  set g := Q.sideGeodesic i
  have hg := Q.isGeodesicFromTo_sideGeodesic i
  rw [hx] at hg
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (x : OnePoint ℝ) ∞
  obtain ⟨c, hc, hac⟩ := exists_im_smul_eq_div_of_smul_coe_eq_infty ha
  have hmem := eventually_geodesicLine_mem_carrier_atBot hx
  have hbot : Tendsto (fun t : ℝ ↦ (a • geodesicLine g t).im) atBot atTop := by
    have hag : (a * g) • ((0 : ℝ) : OnePoint ℝ) = ∞ := by
      rw [mul_smul, hg.smul_zero_eq, ha]
    have ht := Filter.tendsto_comap_iff.1 (tendsto_geodesicLine_atBot_atImInfty hag)
    exact ht.congr fun t ↦ by rw [Function.comp_apply, smul_geodesicLine]
  have hnormSq : Tendsto (fun t : ℝ ↦ Complex.normSq ((geodesicLine g t : ℂ) - x)) atBot (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ Complex.normSq_nonneg _) ?_
      ((tendsto_const_nhds.div_atTop (hbot.const_mul_atTop hc)) :
        Tendsto (fun t ↦ ρ / (c * (a • geodesicLine g t).im)) atBot (𝓝 0))
    filter_upwards [hmem, hbot.eventually (eventually_gt_atTop 0)] with t ht hpos
    have hN : 0 < c * Complex.normSq ((geodesicLine g t : ℂ) - x) := by
      refine mul_pos hc (Complex.normSq_pos.2 (sub_ne_zero.2 fun h ↦ ?_))
      exact (geodesicLine g t).im_pos.ne' (by simpa using congrArg Complex.im h)
    have heq := hac (geodesicLine g t)
    rw [eq_div_iff hN.ne'] at heq
    have hle : (a • geodesicLine g t).im * (c * Complex.normSq ((geodesicLine g t : ℂ) - x)) ≤ ρ :=
      heq.trans_le (him _ ht)
    rw [le_div_iff₀ (mul_pos hc hpos)]
    linarith
  have hcoe : Tendsto (fun t : ℝ ↦ (geodesicLine g t : ℂ)) atBot (𝓝 (x : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hnormSq.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with t ht
    rw [Complex.dist_eq]
    rw [Complex.normSq_eq_norm_sq] at ht
    nlinarith [norm_nonneg ((geodesicLine g t : ℂ) - x)]
  have hpar : Tendsto (fun t : ℝ ↦ parabolaMap (geodesicLine g t)) atBot (𝓝 ⟨x, x ^ 2⟩) := by
    have hcont : Continuous (fun ζ : ℂ ↦ (⟨ζ.re, Complex.normSq ζ⟩ : ℂ)) := by
      simp only [Complex.mk_eq_add_mul_I]
      fun_prop
    have hval : (⟨(x : ℂ).re, Complex.normSq (x : ℂ)⟩ : ℂ) = ⟨x, x ^ 2⟩ := by
      apply Complex.ext <;> simp [sq]
    refine (hval ▸ (hcont.tendsto (x : ℂ)).comp hcoe).congr fun t ↦ ?_
    apply Complex.ext <;> simp
  exact mem_closure_of_tendsto hpar (hmem.mono fun t ht ↦ ⟨_, ht, rfl⟩)

/-- `parabolaMap '' Q.carrier` is relatively closed in `range parabolaMap`. -/
private theorem mem_parabolaMap_image_carrier_of_mem_closure {Q : ConvexPolygon n} {w : ℂ}
    (hw : w ∈ closure (parabolaMap '' Q.carrier)) (hlt : w.re ^ 2 < w.im) :
    w ∈ parabolaMap '' Q.carrier := by
  have hf := isOpenEmbedding_parabolaMap
  obtain ⟨z, rfl⟩ : w ∈ range parabolaMap := by rwa [range_parabolaMap]
  refine ⟨z, ?_, rfl⟩
  rw [← Q.isClosed_carrier.closure_eq]
  rw [mem_closure_iff_nhds] at hw ⊢
  intro U hU
  obtain ⟨w', hw'V, z', hz', rfl⟩ := hw (parabolaMap '' U) (hf.isOpenMap.image_mem_nhds hU)
  obtain ⟨z'', hz''U, heq⟩ := hw'V
  exact ⟨z', hf.injective heq ▸ hz''U, hz'⟩

private theorem exists_smul_vertex_eq_infty (Q : ConvexPolygon n) :
    ∃ gQ : Fin n → PSL(2, ℝ), ∀ j η, Q.vertex j = .inr η → gQ j • η = ∞ := by
  have haux (j : Fin n) : ∃ g : PSL(2, ℝ), ∀ η, Q.vertex j = .inr η → g • η = ∞ := by
    rcases _ : Q.vertex j with _ | η
    · exact ⟨1, fun _ h ↦ by simp at h⟩
    · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) η ∞
      exact ⟨g, fun _ h ↦ by rwa [← Sum.inr.inj h]⟩
  exact ⟨fun j ↦ (haux j).choose, fun j ↦ (haux j).choose_spec⟩

/-- For a bounded convex polygon `Q` with no vertex at `∞`, the points of
`closure (parabolaMap '' Q.carrier)` outside `parabolaMap '' Q.carrier` are precisely `(x, x²)`
at the real ideal vertices `x` of `Q`. -/
private theorem mem_closure_parabolaMap_image_carrier_iff {Q : ConvexPolygon n}
    {ρ : ℝ} (him : ∀ z ∈ Q.carrier, z.im ≤ ρ) (hne : ∀ i, Q.vertex i ≠ .inr ∞) (w : ℂ) :
    w ∈ closure (parabolaMap '' Q.carrier) ↔
      w ∈ parabolaMap '' Q.carrier ∨
        ∃ i : Fin n, Q.vertex i = .inr (w.re : OnePoint ℝ) ∧ w = ⟨w.re, w.re ^ 2⟩ := by
  refine ⟨fun hw ↦ ?_, ?_⟩
  · have hle : w.re ^ 2 ≤ w.im := by
      refine (isClosed_le (Complex.continuous_re.pow 2)
        Complex.continuous_im).closure_subset_iff.2 ?_ hw
      rintro _ ⟨z, -, rfl⟩
      exact (sq_re_lt_im_parabolaMap z).le
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inl (mem_parabolaMap_image_carrier_of_mem_closure hw hlt)
    · have hw' : w = ⟨w.re, w.re ^ 2⟩ := Complex.ext rfl heq.symm
      obtain ⟨gQ, hgQ⟩ := exists_smul_vertex_eq_infty Q
      have hev : {w₁ : ℂ | ∀ z ∈ Q.carrier, parabolaMap z = w₁ →
          ∃ i, Q.vertex i = .inr (w.re : OnePoint ℝ) ∧ 1 < (gQ i • z).im} ∈ 𝓝 w := by
        rw [hw']
        exact eventually_parabolaMap_horodisc hne hgQ w.re (A := fun _ ↦ 1) (fun _ _ ↦ le_rfl)
      obtain ⟨w₁, hw₁U, z₁, hz₁, rfl⟩ := mem_closure_iff_nhds.1 hw _ hev
      obtain ⟨j, hj, -⟩ := hw₁U z₁ hz₁ rfl
      exact Or.inr ⟨j, hj, hw'⟩
  · rintro (hw | ⟨i, hi, hw'⟩)
    · exact subset_closure hw
    · rw [hw']
      exact mk_sq_mem_closure_parabolaMap_image_carrier him hi

/-- The inclusion of `parabolaMap '' Q.carrier` into its closure is an open embedding. -/
private theorem isOpenEmbedding_inclusion_closure (Q : ConvexPolygon n) :
    IsOpenEmbedding (fun w : parabolaMap '' Q.carrier ↦
      (⟨w.1, subset_closure w.2⟩ : closure (parabolaMap '' Q.carrier))) := by
  set s : Set ℂ := parabolaMap '' Q.carrier
  let inc : s → closure s := fun w ↦ ⟨w.1, subset_closure w.2⟩
  refine ⟨⟨?_, fun a b h ↦ Subtype.ext (congrArg (Subtype.val : closure s → ℂ) h)⟩, ?_⟩
  · rw [isInducing_iff_nhds]
    intro ⟨w, hw⟩
    rw [nhds_subtype_eq_comap, nhds_subtype_eq_comap, Filter.comap_comap]
    rfl
  · have hrange : range inc = (Subtype.val : closure s → ℂ) ⁻¹' range parabolaMap := by
      ext ⟨w, hw⟩
      simp only [inc, mem_range, Subtype.ext_iff, mem_preimage, range_parabolaMap, mem_ofPred_eq]
      exact ⟨fun ⟨⟨_, z, _, hz⟩, h⟩ ↦ h ▸ hz ▸ sq_re_lt_im_parabolaMap z,
        fun hlt ↦ ⟨⟨w, mem_parabolaMap_image_carrier_of_mem_closure hw hlt⟩, rfl⟩⟩
    rw [hrange]
    exact isOpenEmbedding_parabolaMap.isOpen_range.preimage continuous_subtype_val

/-- Choosing a translate `Q = h₀ • P` with `Q.carrier` bounded and avoiding `∞` identifies
`P.carrier ⊕ {i // (P.vertex i).isRight}` with `closure (parabolaMap '' Q.carrier)`. -/
private def equivClosureParabolaMapImage (P : ConvexPolygon n) (h₀ : PSL(2, ℝ))
    {ρ : ℝ} (him : ∀ z ∈ (h₀ • P).carrier, z.im ≤ ρ)
    (hne : ∀ i, (h₀ • P).vertex i ≠ .inr ∞)
    (x : {i : Fin n // (P.vertex i).isRight} → ℝ)
    (hx : ∀ i, (h₀ • P).vertex i.1 = .inr (x i : OnePoint ℝ)) :
    P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃
      closure (parabolaMap '' (h₀ • P).carrier) := by
  set Q := h₀ • P
  set s : Set ℂ := parabolaMap '' Q.carrier
  let toCls : P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} → closure s
    | .inl z => ⟨parabolaMap (h₀ • (z : ℍ)), subset_closure ⟨h₀ • z, by simp [Q, z.2], rfl⟩⟩
    | .inr i => ⟨⟨x i, (x i) ^ 2⟩, mk_sq_mem_closure_parabolaMap_image_carrier him (hx i)⟩
  refine Equiv.ofBijective toCls ⟨?_, ?_⟩
  · rintro (z₁ | i₁) (z₂ | i₂) h
    · have hz := isOpenEmbedding_parabolaMap.injective (congrArg Subtype.val h)
      exact congrArg Sum.inl (Subtype.ext (MulAction.injective h₀ hz))
    · have hlt := sq_re_lt_im_parabolaMap (h₀ • (z₁ : ℍ))
      have heq : parabolaMap (h₀ • (z₁ : ℍ)) = ⟨x i₂, (x i₂) ^ 2⟩ := congrArg Subtype.val h
      rw [heq] at hlt
      exact (lt_irrefl _ hlt).elim
    · have hlt := sq_re_lt_im_parabolaMap (h₀ • (z₂ : ℍ))
      have heq : (⟨x i₁, (x i₁) ^ 2⟩ : ℂ) = parabolaMap (h₀ • (z₂ : ℍ)) := congrArg Subtype.val h
      rw [← heq] at hlt
      exact (lt_irrefl _ hlt).elim
    · have hre : x i₁ = x i₂ := congrArg (Complex.re ∘ Subtype.val) h
      exact congrArg Sum.inr (Subtype.ext (Q.vertex_injective (by rw [hx i₁, hx i₂, hre])))
  · rintro ⟨w, hw⟩
    rcases (mem_closure_parabolaMap_image_carrier_iff him hne w).1 hw with
      ⟨z, hz, rfl⟩ | ⟨j, hj, hw'⟩
    · refine ⟨.inl ⟨h₀⁻¹ • z, ?_⟩, Subtype.ext (by simp [toCls])⟩
      have hz' : h₀ • (h₀⁻¹ • z) ∈ h₀ • P.carrier := by simpa [Q] using hz
      exact smul_mem_smul_set_iff.1 hz'
    · have hjP : (P.vertex j).isRight := by
        simp only [Q, vertex_smul] at hj
        cases hv : P.vertex j with
        | inl z => simp [hv] at hj
        | inr η => rfl
      refine ⟨.inr ⟨j, hjP⟩, Subtype.ext ?_⟩
      have hxj : x ⟨j, hjP⟩ = w.re :=
        OnePoint.coe_injective (Sum.inr.inj ((hx ⟨j, hjP⟩).symm.trans hj))
      simp [toCls, hxj, ← hw']

private theorem isOpenEmbedding_equivClosureParabolaMapImage_inl (P : ConvexPolygon n)
    (h₀ : PSL(2, ℝ)) {ρ : ℝ} (him : ∀ z ∈ (h₀ • P).carrier, z.im ≤ ρ)
    (hQne : ∀ j, (h₀ • P).vertex j ≠ .inr ∞)
    (x : {i : Fin n // (P.vertex i).isRight} → ℝ)
    (hx : ∀ i, (h₀ • P).vertex i.1 = .inr (x i : OnePoint ℝ)) :
    IsOpenEmbedding (fun z : P.carrier ↦
      equivClosureParabolaMapImage P h₀ him hQne x hx (.inl z)) := by
  set Q := h₀ • P
  set s : Set ℂ := parabolaMap '' Q.carrier
  have hf := isOpenEmbedding_parabolaMap
  let hPs : P.carrier ≃ₜ s :=
    (Equiv.ofBijective (fun z : P.carrier ↦ (⟨parabolaMap (h₀ • (z : ℍ)),
        mem_image_of_mem _ (by simp [Q, z.2])⟩ : s))
      ⟨fun z₁ z₂ h ↦ Subtype.ext (MulAction.injective h₀ (hf.injective (Subtype.ext_iff.1 h))),
        by rintro ⟨_, z, hz, rfl⟩
           exact ⟨⟨h₀⁻¹ • z, (smul_mem_smul_set_iff (a := h₀)).1 (by simpa [Q] using hz)⟩,
             Subtype.ext (by simp)⟩⟩).toHomeomorphOfIsInducing
      (Topology.IsInducing.subtypeVal.of_comp_iff.1
        ((hf.isInducing.comp (Homeomorph.smul h₀).isInducing).comp .subtypeVal))
  exact (isOpenEmbedding_inclusion_closure Q).comp hPs.isOpenEmbedding

/-- Punctured neighborhoods of an ideal-vertex point in `closure (parabolaMap '' (h₀ • P).carrier)`
correspond to arbitrarily deep horodiscs at that ideal vertex. -/
private theorem eventually_horodisc_of_equivClosureParabolaMapImage (P : ConvexPolygon n)
    (h₀ : PSL(2, ℝ)) {ρ : ℝ} (him : ∀ z ∈ (h₀ • P).carrier, z.im ≤ ρ)
    (hQne : ∀ j, (h₀ • P).vertex j ≠ .inr ∞)
    (x : {i : Fin n // (P.vertex i).isRight} → ℝ)
    (hx : ∀ i, (h₀ • P).vertex i.1 = .inr (x i : OnePoint ℝ))
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (φCls : closure (parabolaMap '' (h₀ • P).carrier) ≃ₜ Y)
    (i : {i : Fin n // (P.vertex i).isRight}) {ξ : OnePoint ℝ} {g : PSL(2, ℝ)}
    (hξ : P.vertex i = .inr ξ) (hgξ : g • ξ = ∞) (B : ℝ) :
    ∀ᶠ u in 𝓝 (((equivClosureParabolaMapImage P h₀ him hQne x hx).trans φCls.toEquiv) (.inr i)),
      u = ((equivClosureParabolaMapImage P h₀ him hQne x hx).trans φCls.toEquiv) (.inr i) ∨
        ∃ z : P.carrier,
          ((equivClosureParabolaMapImage P h₀ him hQne x hx).trans φCls.toEquiv) (.inl z) = u ∧
          B < (g • (z : ℍ)).im := by
  classical
  let Q := h₀ • P
  let eCls := equivClosureParabolaMapImage P h₀ him hQne x hx
  let e := eCls.trans φCls.toEquiv
  obtain ⟨gQ, hgQ⟩ := exists_smul_vertex_eq_infty Q
  let g' : Fin n → PSL(2, ℝ) := Function.update gQ i.1 (g * h₀⁻¹)
  have hg' (j : Fin n) (η : OnePoint ℝ) (hj : Q.vertex j = .inr η) : g' j • η = ∞ := by
    by_cases hji : j = i.1
    · subst hji
      have hη : η = h₀ • ξ := Sum.inr.inj (hj.symm.trans (by simp [Q, hξ]))
      simp [g', hη, mul_smul, hgξ]
    · simpa [g', hji] using hgQ j η hj
  let A : Fin n → ℝ := Function.update (fun _ ↦ (1 : ℝ)) i.1 (max B 1)
  have hA (j : Fin n) (hj : Q.vertex j ≠ .inr (x i : OnePoint ℝ)) : 1 ≤ A j := by
    by_cases hji : j = i.1
    · exact (hj (hji ▸ hx i)).elim
    · simp [A, hji]
  have hval_i : (φCls.symm (e (.inr i)) : ℂ) = ⟨x i, (x i) ^ 2⟩ :=
    congrArg Subtype.val (φCls.symm_apply_apply (eCls (.inr i)))
  have hpull : Tendsto (fun u : Y ↦ (φCls.symm u : ℂ)) (𝓝 (e (.inr i))) (𝓝 ⟨x i, (x i) ^ 2⟩) :=
    hval_i ▸ continuous_subtype_val.continuousAt.comp (φCls.symm.continuous.tendsto _)
  have hsep : ∀ᶠ u in 𝓝 (e (.inr i)),
      ∀ j : {k : Fin n // (P.vertex k).isRight}, j ≠ i → u ≠ e (.inr j) :=
    Filter.eventually_all.2 fun j ↦ by
      by_cases hji : j = i
      · exact Eventually.of_forall fun _ h ↦ (h hji).elim
      · exact (eventually_ne_nhds (e.injective.ne (Sum.inr_injective.ne (Ne.symm hji)))).mono
          fun _ h _ ↦ h
  filter_upwards [hpull.eventually (eventually_parabolaMap_horodisc hQne hg' (x i) hA), hsep]
    with u hu hne_j
  rcases eq_or_ne u (e (.inr i)) with rfl | hne_u
  · exact Or.inl rfl
  · rcases hsurj : e.symm u with z | j
    · have huz : e (.inl z) = u := by rw [← hsurj, e.apply_symm_apply]
      refine Or.inr ⟨z, huz, ?_⟩
      have hzQ : h₀ • (z : ℍ) ∈ Q.carrier := by simp [Q, z.2]
      have hval_z : (φCls.symm u : ℂ) = parabolaMap (h₀ • (z : ℍ)) := by
        rw [← huz]
        exact congrArg Subtype.val (φCls.symm_apply_apply (eCls (.inl z)))
      obtain ⟨k, hk, hAk⟩ := hu (h₀ • z) hzQ hval_z.symm
      obtain rfl : k = i.1 := Q.vertex_injective (hk.trans (hx i).symm)
      simp only [A, g', Function.update_self, mul_smul, inv_smul_smul] at hAk
      exact (le_max_left B 1).trans_lt hAk
    · have huj : u = e (.inr j) := by rw [← hsurj, e.apply_symm_apply]
      exact (hne_j j (fun h ↦ hne_u (h ▸ huj)) huj).elim

/-! ### The disk compactification of a convex polygon -/

/-- **Adjoining the ideal vertices of a convex hyperbolic polygon gives a closed disk.** For every
convex polygon `P`, there is a bijection `e` from `P.carrier ⊕ {i : Fin n // (P.vertex i).isRight}`
onto `closedBall (0 : ℂ) 1` such that:

* `z ↦ e (.inl z)` is an open embedding of `P.carrier` into `closedBall (0 : ℂ) 1`;
* `e (.inl z)` lies in `ball (0 : ℂ) 1` precisely when `z ∈ interior P.carrier`, and in
  `sphere (0 : ℂ) 1` precisely when `z` lies on some side of `P`;
* `e (.inr i)` lies on `sphere (0 : ℂ) 1` for every ideal vertex `i`;
* for every ideal vertex `P.vertex i = .inr ξ`, every `g ∈ PSL(2, ℝ)` with `g • ξ = ∞`, and every
  `B : ℝ`, every point of `closedBall (0 : ℂ) 1` sufficiently close to `e (.inr i)` is either
  `e (.inr i)` itself or `e (.inl z)` with `B < Im (g • z)`. -/
theorem exists_equiv_closedBall (P : ConvexPolygon n) :
    ∃ e : P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃ closedBall (0 : ℂ) 1,
      IsOpenEmbedding (fun z : P.carrier ↦ e (.inl z)) ∧
      (∀ z : P.carrier, (e (.inl z) : ℂ) ∈ ball (0 : ℂ) 1 ↔ (z : ℍ) ∈ interior P.carrier) ∧
      (∀ z : P.carrier, (e (.inl z) : ℂ) ∈ sphere (0 : ℂ) 1 ↔ ∃ j, (z : ℍ) ∈ P.side j) ∧
      (∀ i : {i : Fin n // (P.vertex i).isRight}, (e (.inr i) : ℂ) ∈ sphere (0 : ℂ) 1) ∧
      ∀ (i : {i : Fin n // (P.vertex i).isRight}) {ξ : OnePoint ℝ} {g : PSL(2, ℝ)},
        P.vertex i = .inr ξ → g • ξ = ∞ → ∀ B : ℝ,
          ∀ᶠ u in 𝓝 (e (.inr i)),
            u = e (.inr i) ∨ ∃ z : P.carrier, e (.inl z) = u ∧ B < (g • (z : ℍ)).im := by
  classical
  obtain ⟨h₀, hinf⟩ := P.exists_smul_infty_mem_boundaryLeftHalfPlane_mul_pslS
  set Q := h₀ • P
  obtain ⟨⟨ρ, -, him⟩, hbdd, hQne⟩ := bounded_and_vertex_ne_infty_of_infty_mem hinf
  set s : Set ℂ := parabolaMap '' Q.carrier
  have hf := isOpenEmbedding_parabolaMap
  have hne_int : (interior s).Nonempty :=
    (Q.nonempty_interior_carrier.image parabolaMap).mono (hf.isOpenMap.image_interior_subset _)
  obtain ⟨φ, hφint, hφcl, hφfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      Q.convex_parabolaMap_image_carrier hne_int hbdd
  have hideal (i : {i : Fin n // (P.vertex i).isRight}) :
      ∃ x : ℝ, Q.vertex i.1 = .inr (x : OnePoint ℝ) := by
    obtain ⟨ξ, hξ⟩ := Sum.isRight_iff.1 i.2
    have hQξ : Q.vertex i.1 = .inr (h₀ • ξ) := by simp [Q, hξ]
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hQne i.1 (hQξ.trans (congrArg _ h))
    exact ⟨x, hQξ.trans (congrArg _ hx.symm)⟩
  choose x hx using hideal
  let φCls : closure s ≃ₜ closedBall (0 : ℂ) 1 :=
    (φ.isEmbedding.homeomorphImage (closure s)).trans (Homeomorph.setCongr hφcl)
  let eCls := equivClosureParabolaMapImage P h₀ him hQne x hx
  let e : P.carrier ⊕ {i : Fin n // (P.vertex i).isRight} ≃ closedBall (0 : ℂ) 1 :=
    eCls.trans φCls.toEquiv
  have he_inl (z : P.carrier) : (e (.inl z) : ℂ) = φ (parabolaMap (h₀ • (z : ℍ))) := rfl
  have he_inr (i : {i : Fin n // (P.vertex i).isRight}) :
      (e (.inr i) : ℂ) = φ ⟨x i, (x i) ^ 2⟩ := rfl
  have hopen : IsOpenEmbedding (fun z : P.carrier ↦ e (.inl z)) :=
    φCls.isOpenEmbedding.comp (isOpenEmbedding_equivClosureParabolaMapImage_inl P h₀ him hQne x hx)
  have hpreint : parabolaMap ⁻¹' interior s = interior Q.carrier := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      hf.injective.preimage_image]
  have hprefr : parabolaMap ⁻¹' frontier s = frontier Q.carrier := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      hf.injective.preimage_image]
  refine ⟨e, hopen, fun z ↦ ?_, fun z ↦ ?_, fun i ↦ ?_,
    fun i {ξ g} hξ hgξ B ↦
      eventually_horodisc_of_equivClosureParabolaMapImage P h₀ him hQne x hx φCls i hξ hgξ B⟩
  · have hQcar : Q.carrier = ⇑(Homeomorph.smul h₀) '' P.carrier :=
      (P.carrier_smul h₀).trans Set.image_smul.symm
    rw [he_inl, ← hφint, φ.injective.mem_set_image, ← mem_preimage, hpreint, hQcar,
      ← (Homeomorph.smul h₀).image_interior]
    exact (Homeomorph.smul h₀).injective.mem_set_image
  · rw [he_inl, ← hφfr, φ.injective.mem_set_image, ← mem_preimage, hprefr, Q.frontier_carrier,
      mem_iUnion]
    simp_rw [Q, side_smul, smul_mem_smul_set_iff]
  · rw [he_inr, ← hφfr, φ.injective.mem_set_image]
    refine ⟨mk_sq_mem_closure_parabolaMap_image_carrier him (hx i), fun hint ↦ ?_⟩
    obtain ⟨z, -, hz⟩ := interior_subset hint
    exact lt_irrefl _ (hz ▸ sq_re_lt_im_parabolaMap z)

end TauCeti.UpperHalfPlane.ConvexPolygon

end
