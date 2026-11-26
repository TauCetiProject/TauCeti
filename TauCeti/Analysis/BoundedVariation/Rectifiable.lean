/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary.Basic
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Geometry.MeasureTheory.Rectifiable.ConeCriterion
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Countable rectifiability of the reduced boundary

For a set `s` in an open subset `Ω` of a finite-dimensional real inner product space `E` equipped
with an additive Haar measure `μ`, the reduced boundary `∂*s` (`TauCeti.reducedBoundary`) is
countably `(dim E - 1)`-rectifiable (`TauCeti.countablyRectifiable_reducedBoundary`). This is the
geometric half of De Giorgi's structure theorem for sets of locally finite perimeter.

The proof treats `dim E ≤ 1` and `dim E ≥ 2` by distinct mechanisms:

* **Low dimensions (`dim E ≤ 1`, `TauCeti.countable_reducedBoundary_of_finrank_le_one`).** When
  `dim E = 0`, `E` is a subsingleton. When `dim E = 1`, writing `μ = c • volume`, every small
  closed ball around a point of `∂*s` has perimeter measure at least `c > 0`
  (`TauCeti.eventually_addHaarScalarFactor_le_variationMeasure_closedBall_of_finrank_eq_one`), while
  punctured closed balls around `x ∈ ∂*s` have perimeter measure tending to `0`, so every point of
  `∂*s` is isolated (`TauCeti.exists_reducedBoundary_inter_ball_eq_singleton_of_finrank_eq_one`) and
  `∂*s` is countable.
* **Dimensions `dim E ≥ 2` (`TauCeti.exists_pos_forall_abs_inner_sub_outerNormal_le`).** By the
  lower volume density estimates (`TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball` and
  `TauCeti.eventually_ofReal_pow_le_mul_measure_ball_sdiff`), `∂*s` is a countable union of strata
  `T_m` on which both `s` and `sᶜ` satisfy uniform lower volume density bounds up to radius
  `1 / (m + 1)`. At any `x ∈ ∂*s`, the blow-ups `s_{x, r}` converge in `L¹_loc` to the half-space
  `{y | ⟪y, ν_s x⟫ < 0}`
  (`TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`).
  A point `z ∈ T_m` near `x` violating the cone bound `|⟪z - x, ν_s x⟫| ≤ η ‖z - x‖` puts a
  rescaled ball of radius `η / 2` completely on the wrong side of `{y | ⟪y, ν_s x⟫ < 0}` while
  carrying uniformly positive blow-up mass on both `s` and `sᶜ`, a contradiction for small
  `r = ‖z - x‖`. Applying the codimension-one cone criterion
  (`TauCeti.CountablyRectifiable.of_forall_exists_abs_inner_sub_le`) to each `T_m` concludes.

## Main statements

* `TauCeti.exists_reducedBoundary_inter_ball_eq_singleton_of_finrank_eq_one` and
  `TauCeti.countable_reducedBoundary_of_finrank_le_one`: when `dim E = 1` every point of
  `reducedBoundary μ Ω s` is isolated, and when `dim E ≤ 1` `reducedBoundary μ Ω s` is countable.
* `TauCeti.exists_pos_forall_abs_inner_sub_outerNormal_le`: when `dim E ≥ 2` and `μ` is an additive
  Haar measure, displacements `z - x` to points `z` of a uniform lower-density stratum near
  `x ∈ reducedBoundary μ Ω s` lie in an arbitrarily narrow cone around
  `(ℝ ∙ outerNormal μ Ω s x)ᗮ`.
* `TauCeti.countablyRectifiable_reducedBoundary`: for any additive Haar measure `μ` in any
  finite-dimensional real inner product space `E`, `reducedBoundary μ Ω s` is countably
  `(dim E - 1)`-rectifiable.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.9.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.3, Theorem 5.15.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.5, Theorem 3.59.
* H. Federer, *Geometric Measure Theory*, 4.5.6.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace symmDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E} {x : E}

/-! ### Dimension at most one -/

/-- **In dimension `1`, every point of the reduced boundary is isolated** for any additive Haar
measure `μ`: around any `x ∈ reducedBoundary μ Ω s` there is a radius `r₀ > 0` with
`closedBall x r₀ ⊆ Ω` and `reducedBoundary μ Ω s ∩ ball x r₀ = {x}`. -/
theorem exists_reducedBoundary_inter_ball_eq_singleton_of_finrank_eq_one [μ.IsAddHaarMeasure]
    (hn : finrank ℝ E = 1) (hx : x ∈ reducedBoundary μ Ω s) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ reducedBoundary μ Ω s ∩ ball x r₀ = {x} := by
  have := Ω.isOpen.locallyCompactSpace
  let x₀ : Ω := ⟨x, reducedBoundary_subset hx⟩
  obtain ⟨R, hR, hRΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds x₀.property)
  have hKR : IsCompact (closedBall x₀ R) := isCompact_closedBall_subtype hRΩ
  have hlim := tendsto_measure_closedBall_sdiff_singleton_nhds_zero
    (μ := variationMeasure μ Ω (s.indicator 1)) (z := x₀)
    ⟨R, hR, ((measure_mono sdiff_subset).trans_lt hKR.measure_lt_top).ne⟩
  have hc0 : (0 : ℝ≥0∞) < μ.addHaarScalarFactor volume :=
    ENNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume)
  obtain ⟨rk, hk, hrk, hrkR⟩ := (((hlim.mono_left nhdsWithin_le_nhds).eventually
    (gt_mem_nhds hc0)).and (Ioo_mem_nhdsGT hR)).exists
  have hrkΩ : closedBall x rk ⊆ Ω := (closedBall_subset_closedBall hrkR.le).trans hRΩ
  refine ⟨rk / 2, half_pos hrk, (closedBall_subset_closedBall (half_le_self hrk.le)).trans hrkΩ,
    Subset.antisymm (fun y ⟨hyB, hyx⟩ => ?_)
      (singleton_subset_iff.2 ⟨hx, mem_ball_self (half_pos hrk)⟩)⟩
  by_contra hyne
  have hδ : 0 < min (dist y x) (rk / 2) := lt_min (dist_pos.2 hyne) (half_pos hrk)
  obtain ⟨r, hge, _, hrδ⟩ :=
    ((eventually_addHaarScalarFactor_le_variationMeasure_closedBall_of_finrank_eq_one hn hyB).and
      (Ioo_mem_nhdsGT hδ)).exists
  have hx_notMem : x ∉ closedBall y r := fun hxy =>
    (lt_irrefl (dist y x)) <|
      calc dist y x = dist x y := dist_comm y x
        _ ≤ r := mem_closedBall.1 hxy
        _ < min (dist y x) (rk / 2) := hrδ
        _ ≤ dist y x := min_le_left _ _
  have hpre : ((↑) : Ω → E) ⁻¹' closedBall y r ⊆ closedBall x₀ rk \ {x₀} := fun z hz => by
    refine ⟨mem_closedBall.2 ?_, by rintro rfl; exact hx_notMem hz⟩
    calc dist (z : E) x ≤ dist (z : E) y + dist y x := dist_triangle _ _ _
      _ ≤ rk / 2 + rk / 2 :=
        add_le_add (((mem_closedBall.1 hz).trans_lt hrδ).le.trans (min_le_right _ _))
          (mem_ball.1 hyx).le
      _ = rk := add_halves rk
  exact hk.not_ge (hge.trans (measure_mono hpre))

/-- **In dimension at most `1`, the reduced boundary is countable** for any additive Haar measure
`μ`. -/
theorem countable_reducedBoundary_of_finrank_le_one [μ.IsAddHaarMeasure]
    (hn : finrank ℝ E ≤ 1) : (reducedBoundary μ Ω s).Countable := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with h0 | h1
  · have := finrank_zero_iff.1 h0
    exact Set.to_countable _
  · refine (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (isDiscrete_iff_forall_mem_exists_isOpen.2 fun x hx => ?_)
    obtain ⟨r₀, _, _, hiso⟩ :=
      exists_reducedBoundary_inter_ball_eq_singleton_of_finrank_eq_one h1 hx
    exact ⟨ball x r₀, isOpen_ball, inter_comm _ _ ▸ hiso⟩

/-! ### Normal cone estimate in dimension at least two -/

/-- **Normal cone estimate on uniform lower-density strata.** For an additive Haar measure `μ` in
dimension `dim E ≥ 2`, let `T` be a set of points at which both `s` and `sᶜ` satisfy uniform lower
`μ`-volume density bounds with finite constant `c` up to radius `ρ₀ > 0`. At any
`x ∈ reducedBoundary μ Ω s` and for any `η > 0`, every point `z ∈ T` sufficiently close to `x`
satisfies `|⟪z - x, outerNormal μ Ω s x⟫| ≤ η * ‖z - x‖`. -/
theorem exists_pos_forall_abs_inner_sub_outerNormal_le [μ.IsAddHaarMeasure]
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s)
    {T : Set E} {c : ℝ≥0∞} (hc : c ≠ ∞) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hs_low : ∀ z ∈ T, ∀ ρ ∈ Ioo 0 ρ₀,
      ENNReal.ofReal (ρ ^ finrank ℝ E) ≤ c * μ (s ∩ ball z ρ))
    (hs_compl_low : ∀ z ∈ T, ∀ ρ ∈ Ioo 0 ρ₀,
      ENNReal.ofReal (ρ ^ finrank ℝ E) ≤ c * μ (ball z ρ \ s))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ z ∈ T, dist z x < δ →
      |⟪z - x, outerNormal μ Ω s x⟫| ≤ η * ‖z - x‖ := by
  set η' : ℝ := min η 1
  have hη'0 : 0 < η' := lt_min hη zero_lt_one
  set τ : ℝ := η' / 2
  have hτ : 0 < τ := half_pos hη'0
  set ν : E := outerNormal μ Ω s x
  have hblow := tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx
    (isCompact_closedBall (0 : E) 2)
  have hmul : Tendsto (fun r : ℝ => c *
      μ ((((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hblow (Or.inr hc)
  have hev := hmul.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (pow_pos hτ (finrank ℝ E))))
  obtain ⟨δ₁, hδ₁, hδ₁_lt⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' zero_lt_one).1 hev
  refine ⟨min δ₁ (ρ₀ / τ), lt_min hδ₁ (div_pos hρ₀ hτ), fun z hz hzx_lt => ?_⟩
  rcases eq_or_ne z x with rfl | hzx
  · simp
  set r : ℝ := ‖z - x‖
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzx)
  have hr_δ₁ : r < δ₁ := by
    simpa only [r, ← dist_eq_norm] using hzx_lt.trans_le (min_le_left _ _)
  have hrτ : r * τ < ρ₀ := (lt_div_iff₀ hτ).1 <| by
    simpa only [r, ← dist_eq_norm] using hzx_lt.trans_le (min_le_right _ _)
  set w : E := r⁻¹ • (z - x)
  have hw : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']
  suffices hle : |⟪w, ν⟫| ≤ η' by
    have hzw : z - x = r • w := by simp [w, smul_smul, mul_inv_cancel₀ hr.ne']
    rw [hzw, inner_smul_left, RCLike.conj_to_real, abs_mul, abs_of_pos hr, mul_comm η]
    exact mul_le_mul_of_nonneg_left (hle.trans (min_le_left _ _)) hr.le
  by_contra! hgt
  have hxrw : x + r • w = z := by simp [w, smul_smul, mul_inv_cancel₀ hr.ne']
  have hpow : ENNReal.ofReal (|r| ^ finrank ℝ E) * ENNReal.ofReal (τ ^ finrank ℝ E) =
      ENNReal.ofReal ((r * τ) ^ finrank ℝ E) := by
    rw [abs_of_pos hr, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  have hlow1 : ENNReal.ofReal (τ ^ finrank ℝ E) ≤
      c * μ (((fun y => x + r • y) ⁻¹' s) ∩ ball w τ) := by
    rw [μ.le_mul_addHaar_preimage_add_smul_inter_ball_iff x w hr.ne', hpow, hxrw, abs_of_pos hr]
    exact hs_low z hz (r * τ) ⟨mul_pos hr hτ, hrτ⟩
  have hlow2 : ENNReal.ofReal (τ ^ finrank ℝ E) ≤
      c * μ (ball w τ \ (fun y => x + r • y) ⁻¹' s) := by
    rw [sdiff_eq_compl_inter, ← preimage_compl,
      μ.le_mul_addHaar_preimage_add_smul_inter_ball_iff x w hr.ne', hpow, hxrw, abs_of_pos hr,
      ← sdiff_eq_compl_inter]
    exact hs_compl_low z hz (r * τ) ⟨mul_pos hr hτ, hrτ⟩
  have hsmall : c *
      μ ((((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2) <
        ENNReal.ofReal (τ ^ finrank ℝ E) := hδ₁_lt ⟨hr, hr_δ₁⟩
  have hsubK : ball w τ ⊆ closedBall 0 2 :=
    ball_subset_closedBall.trans <| closedBall_subset_closedBall' <| by
      rw [dist_zero_right, hw]
      have hη'1 : η' ≤ 1 := min_le_right η 1
      dsimp only [τ]
      linarith
  rcases lt_abs.1 hgt with hpos | hneg
  · have hdisj : ball w τ ⊆ {y | 0 < ⟪y, ν⟫} :=
      ball_subset_closedBall.trans <| closedBall_subset_setOf_lt_inner <| by
        rw [norm_outerNormal hx, mul_one]; dsimp only [τ]; linarith
    have hsub : ((fun y => x + r • y) ⁻¹' s) ∩ ball w τ ⊆
        (((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2 :=
      fun y ⟨hyS, hyB⟩ =>
        ⟨Or.inl ⟨hyS, fun hyH => (mem_ofPred.1 (hdisj hyB)).asymm (mem_ofPred.1 hyH)⟩, hsubK hyB⟩
    exact (hlow1.trans (mul_le_mul_right (measure_mono hsub) _)).not_gt hsmall
  · have hmem : ball w τ ⊆ {y | ⟪y, ν⟫ < 0} :=
      ball_subset_closedBall.trans <| closedBall_subset_setOf_inner_lt <| by
        rw [norm_outerNormal hx, mul_one]; dsimp only [τ]; linarith
    have hsub : ball w τ \ ((fun y => x + r • y) ⁻¹' s) ⊆
        (((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2 :=
      fun y ⟨hyB, hyS⟩ => ⟨Or.inr ⟨hmem hyB, hyS⟩, hsubK hyB⟩
    exact (hlow2.trans (mul_le_mul_right (measure_mono hsub) _)).not_gt hsmall

/-- **De Giorgi's rectifiability theorem.** In any finite-dimensional real inner product space `E`
equipped with an additive Haar measure `μ`, the reduced boundary `reducedBoundary μ Ω s` of any set
`s` in any open set `Ω` is countably `(dim E - 1)`-rectifiable. -/
theorem countablyRectifiable_reducedBoundary [μ.IsAddHaarMeasure] :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  rcases le_or_gt (finrank ℝ E) 1 with hn | hn'
  · exact (countable_reducedBoundary_of_finrank_le_one hn).countablyRectifiable
  · have hn : 2 ≤ finrank ℝ E := hn'
    have hp : NNReal.HolderConjugate (finrank ℝ E) (NNReal.conjExponent (finrank ℝ E)) :=
      .conjExponent (by exact_mod_cast hn)
    let C : ℝ≥0 := (1 + 2) * finrank ℝ E *
      eLpNormLESNormFDerivOneConst μ (NNReal.conjExponent (finrank ℝ E))
    let r₀ (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
    let T (m : ℕ) : Set E := {z ∈ reducedBoundary μ Ω s |
      (∀ ρ ∈ Ioo 0 (r₀ m), ENNReal.ofReal (ρ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E * μ (s ∩ ball z ρ)) ∧
      (∀ ρ ∈ Ioo 0 (r₀ m), ENNReal.ofReal (ρ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E * μ (ball z ρ \ s))}
    have hcov : reducedBoundary μ Ω s = ⋃ m : ℕ, T m := by
      ext z
      simp only [T, mem_iUnion, mem_ofPred_eq]
      refine ⟨fun hz => ?_, fun ⟨_, hz, _⟩ => hz⟩
      have hev := (eventually_ofReal_pow_le_mul_measure_inter_ball hp hz (t := 2) one_lt_two).and
        (eventually_ofReal_pow_le_mul_measure_ball_sdiff hp hz (t := 2) one_lt_two)
      obtain ⟨u, hu, husub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' zero_lt_one).1 hev
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hu
      exact ⟨m, hz, fun ρ hρ => (husub ⟨hρ.1, hρ.2.trans hm⟩).1,
        fun ρ hρ => (husub ⟨hρ.1, hρ.2.trans hm⟩).2⟩
    rw [hcov]
    refine CountablyRectifiable.iUnion fun m =>
      CountablyRectifiable.of_forall_exists_abs_inner_sub_le fun x hx => ?_
    have hnorm : ‖outerNormal μ Ω s x‖ = 1 := norm_outerNormal hx.1
    have hne : outerNormal μ Ω s x ≠ 0 := fun h0 => by simp [h0] at hnorm
    obtain ⟨δ, hδ, hcone⟩ := exists_pos_forall_abs_inner_sub_outerNormal_le (μ := μ) hn hx.1
      (T := T m) (ENNReal.pow_ne_top ENNReal.coe_ne_top) Nat.one_div_pos_of_nat
      (fun z hz => hz.2.1) (fun z hz => hz.2.2) (η := 1 / 2) one_half_pos
    exact ⟨outerNormal μ Ω s x, hne, 1 / 2, by norm_num, δ, hδ,
      fun y hy hyx => by simpa only [hnorm, mul_one] using hcone y hy hyx⟩

end TauCeti
