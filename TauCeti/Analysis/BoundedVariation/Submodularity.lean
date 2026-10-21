/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Convolution
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Submodularity of the perimeter

For null-measurable sets `s` and `t` and an open set `Ω`, the perimeter is submodular:

`P(s ∪ t; Ω) + P(s ∩ t; Ω) ≤ P(s; Ω) + P(t; Ω)`.

No finiteness of perimeter or volume is assumed. In particular unions, intersections and
differences of two null-measurable sets of finite perimeter in `Ω` have finite perimeter in `Ω`.

The inequality is the indicator case of a statement about functions with values in `[0, 1]`:
since `1_{s ∩ t} = 1_s 1_t` and `1_{s ∪ t} = 1_s + 1_t - 1_s 1_t`, it follows from

`|D(u v)|(Ω) + |D(u + v - u v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)`

for `u` and `v` with values in `[0, 1]` almost everywhere on `Ω`. For `C¹` functions this is the
pointwise inequality `‖v ∇u + u ∇v‖ + ‖(1 - v) ∇u + (1 - u) ∇v‖ ≤ ‖∇u‖ + ‖∇v‖`. In general,
mollifications of `u` and `v` keep their values in `[0, 1]`, converge in `L¹_loc`, and do not
increase variation on open sets compactly inside `Ω`, so lower semicontinuity of the total
variation passes the smooth inequality to the limit.

## Main results

* `TauCeti.totalVariationOn_mul_add_totalVariationOn_add_sub_mul_le`: the inequality
  `|D(u v)|(Ω) + |D(u + v - u v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)` for functions with values in `[0, 1]`.
* `TauCeti.perimeter_union_add_perimeter_inter_le`: submodularity of the perimeter.
* `TauCeti.perimeter_union_le`, `TauCeti.perimeter_inter_le` and `TauCeti.perimeter_diff_le`:
  the perimeters of `s ∪ t`, `s ∩ t` and `s \ t` are at most `P(s; Ω) + P(t; Ω)`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Lemma 12.22.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Proposition 3.38.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Metric Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped ENNReal Convolution Topology Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u v : E → ℝ} {s t : Set E}

/-- For `x, y ∈ [0, 1]`, the derivatives `y a + x b` of a product and
`(1 - y) a + (1 - x) b` of `x + y - x y` have total norm at most `‖a‖ + ‖b‖`. -/
private theorem norm_smul_add_add_norm_smul_add_le {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (a b : F) :
    ‖x • b + y • a‖ + ‖(1 - y) • a + (1 - x) • b‖ ≤ ‖a‖ + ‖b‖ := by
  have h₁ := norm_add_le (x • b) (y • a)
  have h₂ := norm_add_le ((1 - y) • a) ((1 - x) • b)
  rw [norm_smul_of_nonneg hx.1, norm_smul_of_nonneg hy.1] at h₁
  rw [norm_smul_of_nonneg (sub_nonneg.2 hy.2), norm_smul_of_nonneg (sub_nonneg.2 hx.2)] at h₂
  linarith

/-- For `b, c ∈ [0, 1]`, `|a c - b d| ≤ |a - b| + |c - d|`. -/
private theorem abs_mul_sub_mul_le {a b c d : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) : |a * c - b * d| ≤ |a - b| + |c - d| := by
  have hc' : |c| ≤ 1 := abs_le.2 ⟨by linarith [hc.1], hc.2⟩
  have hb' : |b| ≤ 1 := abs_le.2 ⟨by linarith [hb.1], hb.2⟩
  calc |a * c - b * d| = |(a - b) * c + b * (c - d)| := by ring_nf
    _ ≤ |a - b| * |c| + |b| * |c - d| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ |a - b| * 1 + 1 * |c - d| := by gcongr
    _ = |a - b| + |c - d| := by ring

/-- The smooth case: for `C¹` functions `u` and `v` with values in `[0, 1]`,
`|D(u v)|(Ω) + |D(u + v - u v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)`. -/
private theorem totalVariationOn_mul_add_le_of_contDiff (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hu01 : ∀ x, u x ∈ Icc (0 : ℝ) 1) (hv01 : ∀ x, v x ∈ Icc (0 : ℝ) 1) :
    totalVariationOn μ Ω (u * v) + totalVariationOn μ Ω (u + v - u * v) ≤
      totalVariationOn μ Ω u + totalVariationOn μ Ω v := by
  have hL {w : E → ℝ} (hw : ContDiff ℝ 1 w) :
      totalVariationOn μ Ω w = ∫⁻ x in Ω, ‖fderiv ℝ w x‖ₑ ∂μ :=
    hw.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv
  rw [hL (w := u * v) (hu.mul hv), hL (w := u + v - u * v) ((hu.add hv).sub (hu.mul hv)), hL hu,
    hL hv,
    ← lintegral_add_left ((hu.continuous_fderiv one_ne_zero).measurable.enorm)]
  refine (le_lintegral_add _ _).trans (lintegral_mono fun x => ?_)
  have hdu := hu.differentiable one_ne_zero x
  have hdv := hv.differentiable one_ne_zero x
  have hmul : fderiv ℝ (u * v) x = u x • fderiv ℝ v x + v x • fderiv ℝ u x :=
    fderiv_mul hdu hdv
  have hsub : fderiv ℝ (u + v - u * v) x =
      (1 - v x) • fderiv ℝ u x + (1 - u x) • fderiv ℝ v x := by
    rw [fderiv_sub (hdu.add hdv) (hdu.mul hdv), fderiv_add hdu hdv, hmul]
    module
  rw [hmul, hsub, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_smul_add_add_norm_smul_add_le (hu01 x) (hv01 x) _ _)

/-- Two sequences whose sums are eventually at most `c` have liminfs summing to at most `c`. -/
private theorem liminf_add_liminf_le_of_eventually_add_le {a b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ᶠ n in atTop, a n + b n ≤ c) : liminf a atTop + liminf b atTop ≤ c := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat]
  refine ENNReal.iSup_add_iSup_le fun m k => ?_
  calc (⨅ i ≥ m, a i) + (⨅ i ≥ k, b i) ≤ a (max N (max m k)) + b (max N (max m k)) :=
        add_le_add (iInf₂_le _ (by omega)) (iInf₂_le _ (by omega))
    _ ≤ c := hN _ (le_max_left _ _)

/-- The inequality with the variations of `u v` and `u + v - u v` taken on an open set `Ω'` whose
points have closed `r`-balls inside `Ω`, for locally integrable `u` and `v` with values everywhere
in `[0, 1]`. -/
private theorem totalVariationOn_mul_add_le_of_closedBall_subset {Ω' : Opens E} {r : ℝ}
    (hr : 0 < r) (hΩ : ∀ x ∈ Ω', closedBall x r ⊆ Ω) (hu : LocallyIntegrable u μ)
    (hv : LocallyIntegrable v μ) (hu01 : ∀ x, u x ∈ Icc (0 : ℝ) 1)
    (hv01 : ∀ x, v x ∈ Icc (0 : ℝ) 1) :
    totalVariationOn μ Ω' (u * v) + totalVariationOn μ Ω' (u + v - u * v) ≤
      totalVariationOn μ Ω u + totalVariationOn μ Ω v := by
  -- Normalized bumps of outer radius `1 / (n + 1)`.
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let mol : (E → ℝ) → ℕ → E → ℝ := fun w n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] w
  -- Mollifications are smooth, keep their values in `[0, 1]`, and converge in `L¹_loc`.
  have hsmooth {w : E → ℝ} (hw : LocallyIntegrable w μ) (n : ℕ) : ContDiff ℝ 1 (mol w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed hw
  have hmem {w : E → ℝ} (hw : LocallyIntegrable w μ) (hw01 : ∀ x, w x ∈ Icc (0 : ℝ) 1)
      (n : ℕ) (x : E) : mol w n x ∈ Icc (0 : ℝ) 1 := by
    have hexists := ((φ n).hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (lsmul ℝ ℝ) (φ n).continuous_normed hw x
    exact ⟨le_convolution_lsmul_of_forall_le (μ := μ) (φ n).support_normed_eq.subset
      (φ n).nonneg_normed (φ n).integral_normed hexists fun y _ => (hw01 y).1,
      convolution_lsmul_le_of_forall_le (μ := μ) (φ n).support_normed_eq.subset
      (φ n).nonneg_normed (φ n).integral_normed hexists fun y _ => (hw01 y).2⟩
  have hlim {w : E → ℝ} (hw : LocallyIntegrable w μ) {K : Set E} (hK : IsCompact K) :
      Tendsto (fun n => ∫⁻ x in K, ‖mol w n x - w x‖ₑ ∂μ) atTop (𝓝 0) :=
    tendsto_setLIntegral_enorm_normed_convolution_sub hφ hw hK
  -- Products and `x + y - x y` of the mollifications converge in `L¹_loc` as well.
  have hlim₂ {F : ℕ → E → ℝ} {f : E → ℝ}
      (hF : ∀ n x, ‖F n x - f x‖ₑ ≤ ‖mol u n x - u x‖ₑ + ‖mol v n x - v x‖ₑ)
      {K : Set E} (hK : IsCompact K) :
      Tendsto (fun n => ∫⁻ x in K, ‖F n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hsum := (hlim hu hK).add (hlim hv hK)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun n => ?_
    rw [← lintegral_add_left' (f := fun x => ‖mol u n x - u x‖ₑ)
      (((hsmooth hu n).continuous.aestronglyMeasurable.sub hu.aestronglyMeasurable).restrict.enorm)]
    exact lintegral_mono (hF n)
  have hmul (n : ℕ) (x : E) : ‖(mol u n * mol v n) x - (u * v) x‖ₑ ≤
      ‖mol u n x - u x‖ₑ + ‖mol v n x - v x‖ₑ := by
    simp only [Pi.mul_apply, ← ofReal_norm, Real.norm_eq_abs,
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_mul_sub_mul_le (hu01 x) (hmem hv hv01 n x))
  have hunion (n : ℕ) (x : E) :
      ‖(mol u n + mol v n - mol u n * mol v n) x - (u + v - u * v) x‖ₑ ≤
        ‖mol u n x - u x‖ₑ + ‖mol v n x - v x‖ₑ := by
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, ← ofReal_norm, Real.norm_eq_abs,
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hU := hmem hu hu01 n x
    calc _ = |(1 - u x) * (1 - v x) - (1 - mol u n x) * (1 - mol v n x)| := by
          congr 1
          ring
      _ ≤ |(1 - u x) - (1 - mol u n x)| + |(1 - v x) - (1 - mol v n x)| :=
          abs_mul_sub_mul_le ⟨by linarith [hU.2], by linarith [hU.1]⟩
            ⟨by linarith [(hv01 x).2], by linarith [(hv01 x).1]⟩
      _ = |mol u n x - u x| + |mol v n x - v x| := by ring_nf
  -- Lower semicontinuity on `Ω'`.
  have hli {w : E → ℝ} (hw : ContDiff ℝ 1 w) : LocallyIntegrableOn w Ω' μ :=
    hw.continuous.locallyIntegrable.locallyIntegrableOn _
  have huv : LocallyIntegrable (u * v) μ :=
    (locallyIntegrable_const (1 : ℝ)).mono (hu.aestronglyMeasurable.mul hv.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [Pi.mul_apply, norm_mul, norm_one]
        exact (mul_le_mul (abs_le.2 ⟨by linarith [(hu01 x).1], (hu01 x).2⟩)
          (abs_le.2 ⟨by linarith [(hv01 x).1], (hv01 x).2⟩) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul 1))
  have hlsc₁ := totalVariationOn_le_liminf (Ω := Ω') (l := atTop)
    (.of_forall fun n => hli ((hsmooth hu n).mul (hsmooth hv n))) (huv.locallyIntegrableOn _)
    fun K hK _ => hlim₂ hmul hK
  have hlsc₂ := totalVariationOn_le_liminf (Ω := Ω') (l := atTop)
    (.of_forall fun n => hli (((hsmooth hu n).add (hsmooth hv n)).sub
      ((hsmooth hu n).mul (hsmooth hv n))))
    (((hu.add hv).sub huv).locallyIntegrableOn _) fun K hK _ => hlim₂ hunion hK
  -- Once the radii are at most `r`, mollification does not increase variation from `Ω` to `Ω'`.
  have hsmall : ∀ᶠ n in atTop, (φ n).rOut ≤ r := hφ.eventually (ge_mem_nhds hr)
  refine (add_le_add hlsc₁ hlsc₂).trans
    (liminf_add_liminf_le_of_eventually_add_le (hsmall.mono fun n hn => ?_))
  have hball (x : E) (hx : x ∈ Ω') : closedBall x (φ n).rOut ⊆ Ω :=
    (closedBall_subset_closedBall hn).trans (hΩ x hx)
  exact (totalVariationOn_mul_add_le_of_contDiff (hsmooth hu n) (hsmooth hv n) (hmem hu hu01 n)
    (hmem hv hv01 n)).trans (add_le_add
      ((φ n).totalVariationOn_normed_convolution_le (hu.locallyIntegrableOn _) hball)
      ((φ n).totalVariationOn_normed_convolution_le (hv.locallyIntegrableOn _) hball))

/-- A function with values in `[0, 1]` almost everywhere on `Ω` agrees almost everywhere on `Ω`
with a function that is locally integrable on the whole space and everywhere `[0, 1]`-valued. -/
private theorem exists_locallyIntegrable_mem_Icc_ae_eq
    (hu : AEStronglyMeasurable u (μ.restrict Ω)) (hu01 : ∀ᵐ x ∂μ.restrict Ω, u x ∈ Icc (0 : ℝ) 1) :
    ∃ w : E → ℝ, LocallyIntegrable w μ ∧ (∀ x, w x ∈ Icc (0 : ℝ) 1) ∧ w =ᵐ[μ.restrict Ω] u := by
  -- Clamp `u` to `[0, 1]` and extend by zero outside `Ω`.
  let g : E → ℝ := fun x => max 0 (min (u x) 1)
  have hg : g =ᵐ[μ.restrict Ω] u := hu01.mono fun x hx => by simp [g, hx.1, hx.2]
  have hΩ : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hmem (x : E) : (Ω : Set E).indicator g x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ (Ω : Set E)
    · rw [indicator_of_mem hx]
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    · rw [indicator_of_notMem hx]
      exact ⟨le_rfl, zero_le_one⟩
  refine ⟨(Ω : Set E).indicator g, (locallyIntegrable_const (1 : ℝ)).mono
    ((aestronglyMeasurable_indicator_iff hΩ).2 (hu.congr hg.symm)) (ae_of_all _ fun x => ?_),
    hmem, (indicator_ae_eq_restrict hΩ.nullMeasurableSet).trans hg⟩
  rw [Real.norm_eq_abs, norm_one, abs_le]
  exact ⟨by linarith [(hmem x).1], (hmem x).2⟩

/-- **The submodularity inequality for total variation.** If `u` and `v` take values in `[0, 1]`
almost everywhere on `Ω`, then `|D(u v)|(Ω) + |D(u + v - u v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)`, against an
additive Haar measure. For indicators of sets `s` and `t` the two functions on the left are the
indicators of `s ∩ t` and `s ∪ t`. -/
theorem totalVariationOn_mul_add_totalVariationOn_add_sub_mul_le
    (hu : AEStronglyMeasurable u (μ.restrict Ω)) (hv : AEStronglyMeasurable v (μ.restrict Ω))
    (hu01 : ∀ᵐ x ∂μ.restrict Ω, u x ∈ Icc (0 : ℝ) 1)
    (hv01 : ∀ᵐ x ∂μ.restrict Ω, v x ∈ Icc (0 : ℝ) 1) :
    totalVariationOn μ Ω (u * v) + totalVariationOn μ Ω (u + v - u * v) ≤
      totalVariationOn μ Ω u + totalVariationOn μ Ω v := by
  -- Pass to representatives that are locally integrable and everywhere `[0, 1]`-valued.
  obtain ⟨u', hu', hu'01, hu'u⟩ := exists_locallyIntegrable_mem_Icc_ae_eq hu hu01
  obtain ⟨v', hv', hv'01, hv'v⟩ := exists_locallyIntegrable_mem_Icc_ae_eq hv hv01
  rw [← totalVariationOn_congr_ae (hu'u.mul hv'v),
    ← totalVariationOn_congr_ae ((hu'u.add hv'v).sub (hu'u.mul hv'v)),
    ← totalVariationOn_congr_ae hu'u, ← totalVariationOn_congr_ae hv'v,
    totalVariationOn_def (u := u' * v'), totalVariationOn_def (u := u' + v' - u' * v'),
    iSup_subtype', iSup_subtype']
  have : Nonempty {φ : 𝓓(Ω, E) // ∀ x, ‖φ x‖ ≤ 1} := ⟨⟨0, fun x => by simp⟩⟩
  refine ENNReal.iSup_add_iSup_le fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ?_
  -- The supports of `φ` and `ψ` lie in an open set `Ω'` whose closed `δ / 2`-balls lie in `Ω`.
  have hK : IsCompact (tsupport φ ∪ tsupport ψ) :=
    φ.hasCompactSupport.isCompact.union ψ.hasCompactSupport.isCompact
  obtain ⟨δ, hδ, hKΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen
    (union_subset φ.tsupport_subset ψ.tsupport_subset)
  let Ω' : Opens E := ⟨thickening (δ / 2) (tsupport φ ∪ tsupport ψ), isOpen_thickening⟩
  have hsub : tsupport φ ∪ tsupport ψ ⊆ Ω' := self_subset_thickening (half_pos hδ) _
  have hball (x : E) (hx : x ∈ Ω') : closedBall x (δ / 2) ⊆ Ω :=
    (closedBall_subset_cthickening hx _).trans <|
      (cthickening_thickening_subset (half_pos hδ).le _ _).trans (by rwa [add_halves])
  let φ' : 𝓓(Ω', E) := ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_union_left.trans hsub⟩
  let ψ' : 𝓓(Ω', E) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_union_right.trans hsub⟩
  have hφ' (x : E) : divergenceCLM φ' x = divergenceCLM φ x := by simp [φ']
  have hψ' (x : E) : divergenceCLM ψ' x = divergenceCLM ψ x := by simp [ψ']
  refine le_trans ?_ (totalVariationOn_mul_add_le_of_closedBall_subset (half_pos hδ) hball hu' hv'
    hu'01 hv'01)
  have h₁ := ofReal_integral_le_totalVariationOn (μ := μ) (u := u' * v') φ' hφ
  have h₂ := ofReal_integral_le_totalVariationOn (μ := μ) (u := u' + v' - u' * v') ψ' hψ
  simp only [hφ', hψ'] at h₁ h₂
  exact add_le_add h₁ h₂

/-- **Submodularity of the perimeter.** For sets `s` and `t` that are null-measurable on `Ω`,
`P(s ∪ t; Ω) + P(s ∩ t; Ω) ≤ P(s; Ω) + P(t; Ω)`, against an additive Haar measure. -/
theorem perimeter_union_add_perimeter_inter_le (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) :
    perimeter μ Ω (s ∪ t) + perimeter μ Ω (s ∩ t) ≤ perimeter μ Ω s + perimeter μ Ω t := by
  have hmem (r : Set E) (x : E) : r.indicator (1 : E → ℝ) x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ r <;> simp [hx]
  have hunion : s.indicator 1 + t.indicator 1 - s.indicator 1 * t.indicator 1 =
      (s ∪ t).indicator (1 : E → ℝ) := by
    ext x
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]
  have h := totalVariationOn_mul_add_totalVariationOn_add_sub_mul_le
    (aestronglyMeasurable_one.indicator₀ hs) (aestronglyMeasurable_one.indicator₀ ht)
    (ae_of_all _ (hmem s)) (ae_of_all _ (hmem t))
  rw [hunion, ← inter_indicator_one, add_comm] at h
  simpa only [perimeter_def] using h

/-- The perimeter of a union is at most the sum of the perimeters. -/
theorem perimeter_union_le (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) :
    perimeter μ Ω (s ∪ t) ≤ perimeter μ Ω s + perimeter μ Ω t :=
  le_self_add.trans (perimeter_union_add_perimeter_inter_le hs ht)

/-- The perimeter of an intersection is at most the sum of the perimeters. -/
theorem perimeter_inter_le (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) :
    perimeter μ Ω (s ∩ t) ≤ perimeter μ Ω s + perimeter μ Ω t :=
  le_add_self.trans (perimeter_union_add_perimeter_inter_le hs ht)

/-- The perimeter of a difference is at most the sum of the perimeters. -/
theorem perimeter_diff_le (hs : NullMeasurableSet s (μ.restrict Ω))
    (ht : NullMeasurableSet t (μ.restrict Ω)) :
    perimeter μ Ω (s \ t) ≤ perimeter μ Ω s + perimeter μ Ω t := by
  rw [sdiff_eq, ← perimeter_compl (s := t)]
  exact perimeter_inter_le hs ht.compl

end TauCeti
