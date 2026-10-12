/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.TwoPoint
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.Analysis.Normed.Group.WeightedVariance
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Wasserstein barycenters on the real line

On `ℝ`, the quadratic Wasserstein distance of two probability laws is the `L²(0, 1)` distance of
their quantile functions, and a monotone function on `(0, 1)` is, almost everywhere, the quantile
function of the law into which it pushes the uniform law. Averaging quantile functions therefore
averages laws: for weights `w i ≥ 0` summing to `1`, the
weighted quadratic Wasserstein cost `ν ↦ ∑ i, w i * W₂(ν, μ i) ^ 2` is minimized by the law
`TauCeti.quantileBarycenter w μ` whose quantile function is `∑ i, w i * (μ i).quantile`.

More precisely, the weighted variance decomposition applied pointwise to quantile functions gives,
for every probability law `ν` on `ℝ`,

`∑ i, w i * W₂(ν, μ i) ^ 2 = W₂(ν, β) ^ 2 + ∑ i, w i * W₂(β, μ i) ^ 2`

with `β = quantileBarycenter w μ`, as an identity in `[0, ∞]` with no moment hypotheses. Hence
`β` minimizes the weighted cost, and when that minimum is finite it is the only minimizer. In the
quadratic Wasserstein space `P₂ (ℝ)` this identifies the Fréchet barycenter of the finitely
supported law `∑ i, w i • δ_{μ i}`: it exists, is unique, and its quantile function is
`∑ i, w i * (μ i).quantile` almost everywhere.

At every exponent `1 ≤ p ≤ ∞`, the quantile barycenter of two laws with weights `1 - s` and `s`
moves at constant speed: interpolations at times `s` and `r` are at distance
`|s - r| W_p(μ₀, μ₁)`. So quantile interpolation is an explicit geodesic segment in `P_p(ℝ)`.
The barycenter theory of two weighted points in geodesic spaces,
`TauCeti.MeasureTheory.Measure.FrechetMean.TwoPoint`, then shows that for `1 < p < ∞` the
interpolation at the barycentric time `τ = TauCeti.twoPointBarycenterTime p t` is a `p`-Fréchet
barycenter of `(1 - t) δ_{μ₀} + t δ_{μ₁}`.

## Main definitions

* `TauCeti.quantileBarycenter w μ` — the law of `∑ i, w i * (μ i).quantile U` for `U` uniform on
  `(0, 1)`.

## Main statements

* `TauCeti.quantile_quantileBarycenter_ae` — the quantile function of the quantile barycenter is
  the weighted average of the quantile functions.
* `TauCeti.sum_mul_wassersteinEDist_sq_eq_add` — the barycentric decomposition of the weighted
  quadratic cost.
* `TauCeti.sum_mul_wassersteinEDist_sq_quantileBarycenter_le` and
  `TauCeti.sum_mul_wassersteinEDist_sq_le_iff_eq_quantileBarycenter` — the quantile barycenter is
  a minimizer, and the only one when the minimum is finite.
* `TauCeti.isFrechetBarycenter_two_iff_quantile_ae_eq` and
  `TauCeti.existsUnique_isFrechetBarycenter_two` — the Fréchet barycenter of finitely many laws in
  `P₂ (ℝ)` is unique and has the averaged quantile function.
* `TauCeti.wassersteinEDist_quantileBarycenter_pair` and
  `TauCeti.exists_isGeodesicSegment_quantileBarycenter` — quantile interpolation of two laws is a
  `W_p` geodesic.
* `TauCeti.isFrechetBarycenter_of_coe_eq_quantileBarycenter_twoPointBarycenterTime` — the
  quantile interpolation of two laws at the barycentric time is a `p`-Fréchet barycenter of the
  two weighted laws.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 2,
  for the quantile description of one-dimensional transport.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The **quantile barycenter** of the laws `μ i` with weights `w i`: the law of
`∑ i, w i * (μ i).quantile U` for `U` uniform on the open unit interval. When the weights sum to
`1` and the `μ i` are probability measures, it minimizes the weighted quadratic Wasserstein cost
to the `μ i`, and its quantile function is the weighted average of theirs. -/
def quantileBarycenter (w : ι → ℝ≥0) (μ : ι → Measure ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map fun t ↦ ∑ i, (w i : ℝ) * (μ i).quantile t

/-- The quantile barycenter is the law of the weighted average of the quantile functions under the
uniform law on `(0, 1)`. -/
theorem quantileBarycenter_def (w : ι → ℝ≥0) (μ : ι → Measure ℝ) :
    quantileBarycenter w μ =
      (volume.restrict (Ioo (0 : ℝ) 1)).map fun t ↦ ∑ i, (w i : ℝ) * (μ i).quantile t := by
  rw [quantileBarycenter]

/-- The quantile barycenter is a probability law, whatever the weights and the laws. -/
instance isProbabilityMeasure_quantileBarycenter (w : ι → ℝ≥0) (μ : ι → Measure ℝ) :
    IsProbabilityMeasure (quantileBarycenter w μ) := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  rw [quantileBarycenter_def]
  infer_instance

/-- The quantile function of the quantile barycenter is the weighted average of the quantile
functions, at almost every level. -/
theorem quantile_quantileBarycenter_ae (w : ι → ℝ≥0) (μ : ι → Measure ℝ) :
    (quantileBarycenter w μ).quantile =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun t ↦ ∑ i, (w i : ℝ) * (μ i).quantile t := by
  rw [quantileBarycenter_def]
  refine Measure.quantile_map_volume_Ioo_ae fun s hs t ht hst ↦ Finset.sum_le_sum fun i _ ↦ ?_
  exact mul_le_mul_of_nonneg_left ((μ i).monotoneOn_quantile hs ht hst) (w i).2

/-- A probability law on `ℝ` is the quantile barycenter exactly when its quantile function is the
weighted average of the quantile functions, at almost every level. -/
theorem eq_quantileBarycenter_iff {w : ι → ℝ≥0} {μ : ι → Measure ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] :
    ν = quantileBarycenter w μ ↔ ν.quantile =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun t ↦ ∑ i, (w i : ℝ) * (μ i).quantile t := by
  refine ⟨fun h ↦ h ▸ quantile_quantileBarycenter_ae w μ, fun h ↦ ?_⟩
  rw [← ν.map_quantile_volume_Ioo, quantileBarycenter_def]
  exact Measure.map_congr h

/-- The quadratic Wasserstein distance squared between real laws, as a squared quantile
distance. -/
private theorem wassersteinEDist_two_sq (α β : Measure ℝ) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] :
    wassersteinEDist 2 α β ^ 2 = ∫⁻ t in Ioo (0 : ℝ) 1, ‖α.quantile t - β.quantile t‖ₑ ^ 2 := by
  simpa using wassersteinEDist_rpow_eq_lintegral_rpow_enorm_quantile_sub one_le_two
    ENNReal.ofNat_ne_top α β

section Wasserstein

variable {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
include hw

/-- **The one-dimensional quadratic barycenter decomposition.** For weights summing to `1`, the
weighted quadratic Wasserstein cost of any probability law `ν` to the laws `μ i` splits as the
squared distance from `ν` to the quantile barycenter plus the weighted cost of the barycenter
itself. The identity holds in `[0, ∞]`, without moment hypotheses. -/
theorem sum_mul_wassersteinEDist_sq_eq_add (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 =
      wassersteinEDist 2 ν (quantileBarycenter w μ) ^ 2 +
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (quantileBarycenter w μ) (μ i) ^ 2 := by
  have hq := quantile_quantileBarycenter_ae w μ
  have hbar (f : ℝ → ℝ → ℝ) :
      ∫⁻ t in Ioo (0 : ℝ) 1, ‖f t ((quantileBarycenter w μ).quantile t)‖ₑ ^ 2
      = ∫⁻ t in Ioo (0 : ℝ) 1, ‖f t (∑ i, (w i : ℝ) * (μ i).quantile t)‖ₑ ^ 2 :=
    lintegral_congr_ae (hq.mono fun t ht ↦ by simp only [ht])
  have hbar' (i : ι) := hbar fun t x ↦ x - (μ i).quantile t
  simp only [wassersteinEDist_two_sq, hbar fun t x ↦ ν.quantile t - x, hbar']
  have hpt := lintegral_congr (μ := volume.restrict (Ioo (0 : ℝ) 1)) fun t ↦
    Finset.univ.sum_mul_enorm_sub_sq_eq hw (ν.quantile t) fun i ↦ (μ i).quantile t
  rw [lintegral_finsetSum' _ fun i _ ↦ by fun_prop, lintegral_add_left' (by fun_prop),
    lintegral_finsetSum' _ fun i _ ↦ by fun_prop] at hpt
  simpa only [lintegral_const_mul' _ _ ENNReal.coe_ne_top] using hpt

/-- **The quantile barycenter minimizes the weighted quadratic cost.** For weights summing to `1`,
no probability law on `ℝ` has a smaller weighted quadratic Wasserstein cost to the laws `μ i` than
their quantile barycenter. -/
theorem sum_mul_wassersteinEDist_sq_quantileBarycenter_le (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (quantileBarycenter w μ) (μ i) ^ 2 ≤
      ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 := by
  rw [sum_mul_wassersteinEDist_sq_eq_add hw μ ν]
  exact le_add_self

/-- **Uniqueness of the one-dimensional quadratic barycenter.** For weights summing to `1`, if the
weighted quadratic Wasserstein cost of the quantile barycenter is finite, then a probability law on
`ℝ` costs at most as much exactly when it is the quantile barycenter. -/
theorem sum_mul_wassersteinEDist_sq_le_iff_eq_quantileBarycenter
    (hfin : ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (quantileBarycenter w μ) (μ i) ^ 2 ≠ ∞)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 ≤
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (quantileBarycenter w μ) (μ i) ^ 2 ↔
      ν = quantileBarycenter w μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ le_rfl⟩
  rw [sum_mul_wassersteinEDist_sq_eq_add hw μ ν] at h
  have h0 := ENNReal.le_of_add_le_add_right hfin (h.trans_eq (zero_add _).symm)
  exact eq_of_wassersteinEDist_eq_zero two_ne_zero ν _
    (pow_eq_zero_iff two_ne_zero |>.1 (nonpos_iff_eq_zero.1 h0))

end Wasserstein

section FrechetBarycenter

/-! ### Barycenters in `P₂ (ℝ)` -/

variable {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) (μ : ι → WassersteinSpace 2 ℝ)
include hw

/-- The quantile barycenter of finitely many laws with finite second moment has finite second
moment. -/
theorem hasFiniteMoment_quantileBarycenter :
    HasFiniteMoment 2
      (quantileBarycenter w fun i ↦ ((μ i : ProbabilityMeasure ℝ) : Measure ℝ)) := by
  set ν := quantileBarycenter w fun i ↦ ((μ i : ProbabilityMeasure ℝ) : Measure ℝ)
  have hd : Measurable fun z : ℝ × ℝ ↦ edist z.1 z.2 := measurable_edist
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  have hfin : ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2 ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (sum_mul_wassersteinEDist_sq_quantileBarycenter_le hw _ (μ i₀))
    exact ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top (WassersteinSpace.wassersteinEDist_ne_top hd _ _))
  have hi : (w i₀ : ℝ≥0∞) * wassersteinEDist 2 ν (μ i₀) ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top hfin
      (Finset.single_le_sum (f := fun i ↦ (w i : ℝ≥0∞) * wassersteinEDist 2 ν (μ i) ^ 2)
      (fun _ _ ↦ bot_le) (Finset.mem_univ i₀))
  have hne : wassersteinEDist 2 ν (μ i₀) ≠ ∞ := by
    simpa [ENNReal.mul_eq_top, hi₀] using hi
  rw [hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment hd (μ i₀).hasFiniteMoment,
    wassersteinEDist_comm hd]
  exact hne

/-- The quantile barycenter of finitely many laws in `P₂ (ℝ)`, as an element of `P₂ (ℝ)`. -/
private theorem exists_coe_eq_quantileBarycenter : ∃ b : WassersteinSpace 2 ℝ,
    ((b : ProbabilityMeasure ℝ) : Measure ℝ) =
      quantileBarycenter w fun i ↦ ((μ i : ProbabilityMeasure ℝ) : Measure ℝ) :=
  ⟨WassersteinSpace.mk
    (⟨quantileBarycenter w fun i ↦ ((μ i : ProbabilityMeasure ℝ) : Measure ℝ), inferInstance⟩ :
      ProbabilityMeasure ℝ)
    (hasFiniteMoment_quantileBarycenter hw μ),
    congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)⟩

/-- **The one-dimensional quadratic Wasserstein barycenter.** For weights summing to `1`, a law
`ν` with finite second moment is a quadratic Fréchet barycenter in `P₂ (ℝ)` of the finitely
supported law `∑ i, w i • δ_{μ i}` exactly when it is the quantile barycenter of the `μ i`. -/
theorem isFrechetBarycenter_two_iff_eq_quantileBarycenter (ν : WassersteinSpace 2 ℝ) :
    IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν ↔
      ((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
        quantileBarycenter w fun i ↦ ((μ i : ProbabilityMeasure ℝ) : Measure ℝ) := by
  have := WassersteinSpace.borelSpace (X := ℝ) (p := 2) ENNReal.ofNat_ne_top
  set μ' := fun i ↦ ((μ i : ProbabilityMeasure ℝ) : Measure ℝ)
  set P := ∑ i, w i • Measure.dirac (μ i)
  have hd : Measurable fun z : ℝ × ℝ ↦ edist z.1 z.2 := measurable_edist
  have hm (z : WassersteinSpace 2 ℝ) : AEMeasurable (fun y ↦ edist z y) P :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  have hF (z : WassersteinSpace 2 ℝ) : frechetPower 2 P z =
      ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (z : ProbabilityMeasure ℝ) (μ' i) ^ 2 := by
    simp only [P, μ', frechetPower_sum_smul_dirac, WassersteinSpace.edist_def, ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  have hfinF (z : WassersteinSpace 2 ℝ) : frechetPower 2 P z ≠ ∞ := by
    rw [hF]
    exact ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top (WassersteinSpace.wassersteinEDist_ne_top hd _ _))
  have hR : frechetRadius 2 P ν ≠ ∞ := by
    intro h
    have := frechetRadius_rpow_eq_frechetPower two_ne_zero ENNReal.ofNat_ne_top (hm ν)
    rw [h, ENNReal.top_rpow_of_pos (by simp)] at this
    exact hfinF ν this.symm
  obtain ⟨b, hb⟩ := exists_coe_eq_quantileBarycenter hw μ
  rw [isFrechetBarycenter_iff_forall_frechetPower_le two_ne_zero ENNReal.ofNat_ne_top (hm ν) hm,
    and_iff_right hR]
  refine ⟨fun h ↦ ?_, fun h z ↦ ?_⟩
  · have hνb := h b
    rw [hF, hF, hb] at hνb
    exact (sum_mul_wassersteinEDist_sq_le_iff_eq_quantileBarycenter hw μ'
      (by simpa only [hF, hb] using hfinF b) _).1 hνb
  · rw [hF, hF, h]
    exact sum_mul_wassersteinEDist_sq_quantileBarycenter_le hw μ' _

/-- **The quantile formula for one-dimensional quadratic Wasserstein barycenters.** For weights
summing to `1`, a law `ν` with finite second moment is a quadratic Fréchet barycenter in `P₂ (ℝ)` of
the finitely supported law `∑ i, w i • δ_{μ i}` exactly when its quantile function is the weighted
average `∑ i, w i * (μ i).quantile` of the quantile functions, at almost every level. -/
theorem isFrechetBarycenter_two_iff_quantile_ae_eq (ν : WassersteinSpace 2 ℝ) :
    IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν ↔
      ((ν : ProbabilityMeasure ℝ) : Measure ℝ).quantile =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun t ↦ ∑ i, (w i : ℝ) * ((μ i : ProbabilityMeasure ℝ) : Measure ℝ).quantile t :=
  (isFrechetBarycenter_two_iff_eq_quantileBarycenter hw μ ν).trans eq_quantileBarycenter_iff

/-- **Existence and uniqueness of one-dimensional quadratic Wasserstein barycenters.** For weights
summing to `1`, the finitely supported law `∑ i, w i • δ_{μ i}` on `P₂ (ℝ)` has exactly one
quadratic Fréchet barycenter. -/
theorem existsUnique_isFrechetBarycenter_two :
    ∃! ν : WassersteinSpace 2 ℝ,
      IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν := by
  obtain ⟨b, hb⟩ := exists_coe_eq_quantileBarycenter hw μ
  refine ⟨b, (isFrechetBarycenter_two_iff_eq_quantileBarycenter hw μ b).2 hb, fun ν hν ↦ ?_⟩
  refine WassersteinSpace.ext (ProbabilityMeasure.toMeasure_injective ?_)
  rw [(isFrechetBarycenter_two_iff_eq_quantileBarycenter hw μ ν).1 hν, hb]

end FrechetBarycenter

/-! ### Two laws at every exponent -/

section TwoLaws

variable {p : ℝ≥0∞}

/-- The quantile function of the quantile barycenter of two laws with weights `1 - s` and `s` is
the interpolation `(1 - s) Q₀ + s Q₁` of their quantile functions. -/
private theorem quantile_quantileBarycenter_pair_ae {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (μ₀ μ₁ : Measure ℝ) :
    (quantileBarycenter ![(1 - s).toNNReal, s.toNNReal] ![μ₀, μ₁]).quantile
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun u ↦ (1 - s) * μ₀.quantile u + s * μ₁.quantile u := by
  filter_upwards [quantile_quantileBarycenter_ae ![(1 - s).toNNReal, s.toNNReal] ![μ₀, μ₁]]
    with u hu
  simp [hu, Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ (sub_nonneg.2 hs.2)]

/-- At time `0` the quantile interpolation of two laws is the first law. -/
private theorem quantileBarycenter_pair_zero (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] :
    quantileBarycenter ![(1 - 0 : ℝ).toNNReal, (0 : ℝ).toNNReal] ![μ₀, μ₁] = μ₀ :=
  (eq_quantileBarycenter_iff.2 (Filter.Eventually.of_forall fun u ↦ by simp)).symm

/-- At time `1` the quantile interpolation of two laws is the second law. -/
private theorem quantileBarycenter_pair_one (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₁] :
    quantileBarycenter ![(1 - 1 : ℝ).toNNReal, (1 : ℝ).toNNReal] ![μ₀, μ₁] = μ₁ :=
  (eq_quantileBarycenter_iff.2 (Filter.Eventually.of_forall fun u ↦ by simp)).symm

/-- **Quantile interpolation is a constant-speed curve for every Wasserstein distance.** For
`1 ≤ p ≤ ∞` and times `s, r ∈ [0, 1]`, the quantile interpolations of `μ₀` and `μ₁` at times `s`
and `r`, whose quantile functions are `(1 - s) Q₀ + s Q₁` and `(1 - r) Q₀ + r Q₁`, are at
`p`-Wasserstein distance `|s - r| W_p(μ₀, μ₁)`. -/
theorem wassersteinEDist_quantileBarycenter_pair (hp : 1 ≤ p) (μ₀ μ₁ : Measure ℝ)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    wassersteinEDist p (quantileBarycenter ![(1 - s).toNNReal, s.toNNReal] ![μ₀, μ₁])
        (quantileBarycenter ![(1 - r).toNNReal, r.toNNReal] ![μ₀, μ₁]) =
      ENNReal.ofReal |s - r| * wassersteinEDist p μ₀ μ₁ := by
  rw [wassersteinEDist_eq_eLpNorm_quantile_sub hp, wassersteinEDist_eq_eLpNorm_quantile_sub hp]
  have hdiff : (fun u ↦
      (quantileBarycenter ![(1 - s).toNNReal, s.toNNReal] ![μ₀, μ₁]).quantile u -
        (quantileBarycenter ![(1 - r).toNNReal, r.toNNReal] ![μ₀, μ₁]).quantile u)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (r - s) • fun u ↦ μ₀.quantile u - μ₁.quantile u := by
    filter_upwards [quantile_quantileBarycenter_pair_ae hs μ₀ μ₁,
      quantile_quantileBarycenter_pair_ae hr μ₀ μ₁] with u hus hur
    simp only [hus, hur, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eLpNorm_congr_ae hdiff, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_sub_comm]

variable [Fact (1 ≤ p)]

/-- **Quantile interpolation is a Wasserstein geodesic.** For `1 ≤ p ≤ ∞`, any two laws in
`P_p(ℝ)` are joined by a geodesic segment whose point at each time `s ∈ [0, 1]` is the quantile
interpolation, the law with quantile function `(1 - s) Q₀ + s Q₁`. -/
theorem exists_isGeodesicSegment_quantileBarycenter (μ₀ μ₁ : WassersteinSpace p ℝ) :
    ∃ γ : ℝ → WassersteinSpace p ℝ, IsGeodesicSegment γ μ₀ μ₁ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ((γ s : ProbabilityMeasure ℝ) : Measure ℝ) =
        quantileBarycenter ![(1 - s).toNNReal, s.toNNReal]
          ![((μ₀ : ProbabilityMeasure ℝ) : Measure ℝ),
            ((μ₁ : ProbabilityMeasure ℝ) : Measure ℝ)] := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  set m₀ := ((μ₀ : ProbabilityMeasure ℝ) : Measure ℝ)
  set m₁ := ((μ₁ : ProbabilityMeasure ℝ) : Measure ℝ)
  set β : ℝ → Measure ℝ := fun s ↦ quantileBarycenter ![(1 - s).toNNReal, s.toNNReal] ![m₀, m₁]
  have hW : wassersteinEDist p m₀ m₁ ≠ ∞ :=
    WassersteinSpace.wassersteinEDist_ne_top measurable_edist μ₀ μ₁
  -- Each interpolation has finite `p`-th moment, being at finite distance from `μ₀`.
  have hβ (s : Icc (0 : ℝ) 1) : HasFiniteMoment p (β s) := by
    rw [hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist
      μ₀.hasFiniteMoment]
    have h := wassersteinEDist_quantileBarycenter_pair hp m₀ m₁ (left_mem_Icc.2 zero_le_one) s.2
    rw [quantileBarycenter_pair_zero] at h
    rw [h]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW
  let γ : ℝ → WassersteinSpace p ℝ := fun s ↦
    WassersteinSpace.mk ⟨β (projIcc 0 1 zero_le_one s), inferInstance⟩
      (hβ (projIcc 0 1 zero_le_one s))
  have hγ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ((γ s : ProbabilityMeasure ℝ) : Measure ℝ) = β s := by
    have h : β (projIcc 0 1 zero_le_one s) = β s := by rw [projIcc_of_mem _ hs]
    exact (congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)).trans h
  refine ⟨γ, ⟨?_, ?_, fun s hs r hr ↦ ?_⟩, hγ⟩
  · refine WassersteinSpace.ext (ProbabilityMeasure.toMeasure_injective ?_)
    rw [hγ 0 (left_mem_Icc.2 zero_le_one)]
    exact quantileBarycenter_pair_zero m₀ m₁
  · refine WassersteinSpace.ext (ProbabilityMeasure.toMeasure_injective ?_)
    rw [hγ 1 (right_mem_Icc.2 zero_le_one)]
    exact quantileBarycenter_pair_one m₀ m₁
  · rw [WassersteinSpace.dist_def, WassersteinSpace.dist_def, hγ s hs, hγ r hr,
      wassersteinEDist_quantileBarycenter_pair hp m₀ m₁ hs hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)]

/-- **The barycenter of two laws on the line at every finite exponent.** For `1 < p < ∞` and
`t ∈ [0, 1]`, the law whose quantile function is `(1 - τ) Q₀ + τ Q₁`, where
`τ = TauCeti.twoPointBarycenterTime p t`, is a `p`-Fréchet barycenter in `P_p(ℝ)` of
`(1 - t) δ_{μ₀} + t δ_{μ₁}`. For `p = 2` the time `τ` is `t` itself. -/
theorem isFrechetBarycenter_of_coe_eq_quantileBarycenter_twoPointBarycenterTime
    (hp : 1 < p) (hp_top : p ≠ ∞) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (μ₀ μ₁ ν : WassersteinSpace p ℝ)
    (hν : ((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
      quantileBarycenter
        ![(1 - twoPointBarycenterTime p.toReal t).toNNReal,
          (twoPointBarycenterTime p.toReal t).toNNReal]
        ![((μ₀ : ProbabilityMeasure ℝ) : Measure ℝ), ((μ₁ : ProbabilityMeasure ℝ) : Measure ℝ)]) :
    IsFrechetBarycenter p
      (ENNReal.ofReal (1 - t) • Measure.dirac μ₀ + ENNReal.ofReal t • Measure.dirac μ₁) ν := by
  have := WassersteinSpace.borelSpace (X := ℝ) hp_top
  obtain ⟨γ, hγ, hγβ⟩ := exists_isGeodesicSegment_quantileBarycenter μ₀ μ₁
  have hτ := twoPointBarycenterTime_mem_Icc p.toReal ht
  have hν' : γ (twoPointBarycenterTime p.toReal t) = ν :=
    WassersteinSpace.ext (ProbabilityMeasure.toMeasure_injective ((hγβ _ hτ).trans hν.symm))
  exact hν' ▸ hγ.isFrechetBarycenter_twoPointBarycenterTime hp hp_top ht

end TwoLaws

end TauCeti
