/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Abs
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine
import TauCeti.MeasureTheory.Measure.Continuity
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Perimeter of smooth symmetric subgraphs

Let `E` be a finite-dimensional real inner product space, `e` a unit vector with orthogonal
hyperplane `H = (ℝ ∙ e)ᗮ`, and `w : H → ℝ` a function. The open symmetric subgraph of `w` along `e`
is

`S = {x : E | |⟪e, x⟫| < w y / 2}`,

where `y` is the orthogonal projection of `x` onto `H`. Each parallel line section of `S` along `e`
is the centered open interval `Metric.eball 0 (ENNReal.ofReal (w y) / 2)`.

When `w` is `C¹`, the whole-space distributional perimeter of `S` satisfies the area-formula upper
bound

`P(S) ≤ ∫⁻ y in {y ∈ H | 0 < w y}, ENNReal.ofReal √(4 + ‖Dw y‖²)`

(`TauCeti.perimeter_setOf_abs_inner_lt_div_two_le`), with no nonnegativity or integrability
hypothesis on `w`.

## Strategy

Writing `h x = w (q x) / 2 - |⟪e, x⟫|`, the subgraph is `{0 < h}`. For any `δ > 0`, clamping `h` to
`u = min (max h 0) δ` yields a locally Lipschitz function whose gradient has norm
`(1 / 2) √(4 + ‖Dw (q x)‖²)` a.e. on `{0 < h < δ}` and vanishes a.e. outside. Integrating the
coarea formula (`LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv`) along lines
parallel to `e` bounds `∫⁻ r in Ioo 0 δ, P({r < h})` by `δ · ∫⁻_{0 < w} √(4 + ‖Dw‖²)`, so for
every `k` there is `r_k ∈ (0, 1 / (k + 1))` with `P({r_k < h}) ≤ B + 1 / (k + 1)`. Since
`{r_k < h} → {0 < h}` locally in measure via
`AEMeasurable.tendsto_measure_setOf_pos_lt_le_inter`, lower semicontinuity of the perimeter
concludes.

## References

* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
-/

public section

noncomputable section

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace Topology symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection `E →L[ℝ] (ℝ ∙ e)ᗮ` induced by `TauCeti.orthogonalLineEquiv`. -/
private def subgraphProj (e : E) (he : ‖e‖ = 1) : E →L[ℝ] (ℝ ∙ e)ᗮ :=
  (ContinuousLinearMap.fst ℝ (ℝ ∙ e)ᗮ ℝ).comp
    (orthogonalLineEquiv e he).symm.toContinuousLinearMap

/-- Height function `x ↦ w (subgraphProj e he x) / 2 - |⟪e, x⟫|` of a symmetric subgraph. -/
private def subgraphHeight (e : E) (he : ‖e‖ = 1) (w : (ℝ ∙ e)ᗮ → ℝ) (x : E) : ℝ :=
  w (subgraphProj e he x) / 2 - |⟪e, x⟫_ℝ|

private theorem subgraphProj_add_smul (e : E) (he : ‖e‖ = 1) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    subgraphProj e he ((y : E) + t • e) = y :=
  orthogonalLineEquiv_symm_fst_add_smul e he y t

private theorem subgraphHeight_add_smul (e : E) (he : ‖e‖ = 1) (w : (ℝ ∙ e)ᗮ → ℝ)
    (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    subgraphHeight e he w ((y : E) + t • e) = w y / 2 - |t| := by
  simp [subgraphHeight, subgraphProj_add_smul e he, inner_add_smul e he]

private theorem continuous_subgraphHeight (e : E) (he : ‖e‖ = 1) {w : (ℝ ∙ e)ᗮ → ℝ}
    (hw : Continuous w) :
    Continuous (subgraphHeight e he w) :=
  ((hw.comp (subgraphProj e he).continuous).div_const 2).sub
    (continuous_const.inner continuous_id).abs

variable [FiniteDimensional ℝ E]

/-- Away from `{⟪e, x⟫ = 0}`, the Fréchet derivative of `subgraphHeight e he w` at `x` is the
dual of `v + (-(sign ⟪e, x⟫)) • e`, where `v` is the dual of `(1 / 2) • fderiv ℝ w (q x)`. -/
private theorem fderiv_subgraphHeight_eq_toDual (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) {x : E} (hxt : ⟪e, x⟫_ℝ ≠ 0) :
    let q := subgraphProj e he
    let v : (ℝ ∙ e)ᗮ := (InnerProductSpace.toDual ℝ (ℝ ∙ e)ᗮ).symm ((1 / 2 : ℝ) • fderiv ℝ w (q x))
    fderiv ℝ (subgraphHeight e he w) x =
      InnerProductSpace.toDual ℝ E ((v : E) + (-(SignType.sign ⟪e, x⟫_ℝ : ℝ)) • e) := by
  intro q v
  have hd1 : HasFDerivAt (fun z : E ↦ w (q z) / 2)
      (((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) x := by
    simpa [div_eq_inv_mul, smul_eq_mul, ContinuousLinearMap.smul_comp] using
      (((hw.differentiable one_ne_zero (q x)).hasFDerivAt).comp x
        q.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hd2 : HasFDerivAt (fun z : E ↦ -|⟪e, z⟫_ℝ|)
      ((-(SignType.sign ⟪e, x⟫_ℝ : ℝ)) • innerSL ℝ e) x := by
    rw [neg_smul]
    exact ((innerSL ℝ e).hasFDerivAt.abs hxt).neg
  have hdh : HasFDerivAt (subgraphHeight e he w)
      ((((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) +
        (-(SignType.sign ⟪e, x⟫_ℝ : ℝ)) • innerSL ℝ e) x :=
    (hd1.add hd2).congr_of_eventuallyEq (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)
  rw [hdh.fderiv]
  ext z
  obtain ⟨⟨y_z, t_z⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective z
  have hv_apply : ⟪(v : E), (y_z : E)⟫_ℝ = ((1 / 2 : ℝ) • fderiv ℝ w (q x)) y_z := by
    simpa [v] using InnerProductSpace.toDual_symm_apply
      (y := (1 / 2 : ℝ) • fderiv ℝ w (q x)) (x := y_z)
  have hv_ort : ⟪(v : E), e⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  have hy_ort : ⟪e, (y_z : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp y_z.property
  simp [q, orthogonalLineEquiv_apply, subgraphProj_add_smul e he, inner_add_right, inner_smul_right,
    hv_ort, hy_ort, he, hv_apply]

/-- Away from `{⟪e, x⟫ = 0}`, the extended norm of `fderiv ℝ (subgraphHeight e he w) x` is
`(1 / 2) √(4 + ‖fderiv ℝ w (q x)‖²)`. -/
private theorem enorm_fderiv_subgraphHeight (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) {x : E} (hxt : ⟪e, x⟫_ℝ ≠ 0) :
    ‖fderiv ℝ (subgraphHeight e he w) x‖ₑ =
      ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (subgraphProj e he x)‖ ^ 2)) := by
  let q := subgraphProj e he
  let v : (ℝ ∙ e)ᗮ := (InnerProductSpace.toDual ℝ (ℝ ∙ e)ᗮ).symm ((1 / 2 : ℝ) • fderiv ℝ w (q x))
  let σ : ℝ := -(SignType.sign ⟪e, x⟫_ℝ : ℝ)
  have hv_norm : ‖v‖ = (1 / 2) * ‖fderiv ℝ w (q x)‖ := by
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hσsq : σ ^ 2 = 1 := by
    dsimp [σ]
    rcases lt_or_gt_of_ne hxt with ht | ht <;> simp [ht]
  rw [← ofReal_norm, fderiv_subgraphHeight_eq_toDual e he hw hxt, LinearIsometryEquiv.norm_map]
  congr 1
  have hsq : ‖(v : E) + σ • e‖ ^ 2 = ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)) ^ 2 := by
    rw [norm_add_smul_sq e he, hv_norm, hσsq, mul_pow, mul_pow,
      Real.sq_sqrt (add_nonneg (by norm_num) (sq_nonneg _))]
    ring
  nlinarith [norm_nonneg ((v : E) + σ • e), Real.sqrt_nonneg (4 + ‖fderiv ℝ w (q x)‖ ^ 2)]

variable [MeasurableSpace E] [BorelSpace E]

/-- Clamped-gradient formula for a `C¹` symmetric subgraph: clamping `h x = w (q x) / 2 - |⟪e, x⟫|`
to `[0, δ]` has a.e. gradient norm `(1 / 2) √(4 + ‖Dw (q x)‖²)` on `{0 < h < δ}` and `0` outside. -/
private theorem enorm_fderiv_clamp_subgraph_ae (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) {δ : ℝ} (hδ : 0 < δ) :
    let q := subgraphProj e he
    let h := subgraphHeight e he w
    let u : E → ℝ := fun x ↦ min (max (h x) 0) δ
    ∀ᵐ x : E ∂volume,
      ‖fderiv ℝ u x‖ₑ =
        {x : E | 0 < h x ∧ h x < δ}.indicator
          (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2))) x := by
  intro q h u
  have hcont_h : Continuous h := continuous_subgraphHeight e he hw.continuous
  -- The singular set `Z = {h = 0} ∪ {h = δ} ∪ {⟪e, x⟫ = 0}` meets every line in ≤ 5 points.
  let Z : Set E := {x : E | h x = 0 ∨ h x = δ ∨ ⟪e, x⟫_ℝ = 0}
  have hZ_closed : IsClosed Z :=
    (isClosed_eq hcont_h continuous_const).union
      ((isClosed_eq hcont_h continuous_const).union
        (isClosed_eq (continuous_const.inner continuous_id) continuous_const))
  have hZ_null : volume Z = 0 := by
    rw [volume_eq_lintegral_volume_lineSection e he hZ_closed.measurableSet.nullMeasurableSet]
    refine (lintegral_eq_zero_iff'
      (aemeasurable_volume_lineSection e he hZ_closed.measurableSet.nullMeasurableSet)).2
      (.of_forall fun y ↦ ?_)
    set R : ℝ := w y / 2
    have hsub : {t : ℝ | (y : E) + t • e ∈ Z} ⊆ {0, R, -R, R - δ, -(R - δ)} := fun t ht ↦ by
      simp only [Z, mem_ofPred_eq, h, subgraphHeight_add_smul e he, inner_add_smul e he] at ht
      rcases ht with h1 | h2 | h3
      · have habs : |t| = R := by dsimp only [R]; linarith
        rcases (abs_eq (habs ▸ abs_nonneg t)).1 habs with rfl | rfl <;> simp
      · have habs : |t| = R - δ := by dsimp only [R]; linarith
        rcases (abs_eq (habs ▸ abs_nonneg t)).1 habs with rfl | rfl <;> simp
      · exact Or.inl h3
    exact measure_mono_null hsub (Set.Finite.measure_zero (by simp) volume)
  have hZ_ae : ∀ᵐ x : E ∂volume, x ∉ Z :=
    ae_iff.2 (by simpa only [not_not, ofPred_mem_eq] using hZ_null)
  filter_upwards [hZ_ae] with x hxZ
  simp only [Z, mem_ofPred_eq, not_or] at hxZ
  obtain ⟨hx0, hxδ, hxt⟩ := hxZ
  -- Outside `Z`, `u` is locally constant on `{h < 0}` and `{δ < h}`, and `h` on `{0 < h < δ}`.
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hev : u =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(isOpen_lt hcont_h continuous_const).mem_nhds hneg] with z hz
      simp [u, max_eq_right (le_of_lt hz), min_eq_left hδ.le]
    have hx_not : x ∉ {x : E | 0 < h x ∧ h x < δ} := fun hx ↦ hneg.not_gt hx.1
    rw [hev.fderiv_eq, fderiv_const_apply, indicator_of_notMem hx_not]
    exact (eNorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
  · rcases lt_or_gt_of_ne hxδ with hlt | hgt
    · have hev_u : u =ᶠ[𝓝 x] h := by
        filter_upwards [((isOpen_lt continuous_const hcont_h).inter
            (isOpen_lt hcont_h continuous_const)).mem_nhds ⟨hpos, hlt⟩] with z hz
        simp [u, max_eq_left hz.1.le, min_eq_left hz.2.le]
      have hx_mem : x ∈ {x : E | 0 < h x ∧ h x < δ} := ⟨hpos, hlt⟩
      rw [indicator_of_mem hx_mem, hev_u.fderiv_eq]
      exact enorm_fderiv_subgraphHeight e he hw hxt
    · have hev : u =ᶠ[𝓝 x] fun _ ↦ δ := by
        filter_upwards [(isOpen_lt continuous_const hcont_h).mem_nhds hgt] with z hz
        simp [u, max_eq_left (hδ.trans hz).le, min_eq_right hz.le]
      have hx_not : x ∉ {x : E | 0 < h x ∧ h x < δ} := fun hx ↦ hgt.not_gt hx.2
      rw [hev.fderiv_eq, fderiv_const_apply, indicator_of_notMem hx_not]
      exact (eNorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl

/-- Coarea upper bound for superlevel perimeters of `subgraphHeight e he w` on `(0, δ)`. -/
private theorem lintegral_perimeter_superlevel_subgraphHeight_le (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < subgraphHeight e he w x} ≤
      ENNReal.ofReal δ *
        ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
  let H := (ℝ ∙ e)ᗮ
  let q := subgraphProj e he
  let h := subgraphHeight e he w
  let u : E → ℝ := fun x ↦ min (max (h x) 0) δ
  -- Step 1: Truncate `h` to `[0, δ]` so the coarea formula applies to `u`.
  have hcont_h : Continuous h := continuous_subgraphHeight e he hw.continuous
  have hlip_h : LocallyLipschitz h := by
    refine ((hw.comp q.contDiff).div_const 2).locallyLipschitz.sub
      (LipschitzWith.of_dist_le_mul (K := 1) fun x₁ x₂ ↦ ?_).locallyLipschitz
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    calc |(|⟪e, x₁⟫_ℝ| - |⟪e, x₂⟫_ℝ|)| ≤ |⟪e, x₁ - x₂⟫_ℝ| := by
          rw [inner_sub_right]; exact abs_abs_sub_abs_le _ _
      _ ≤ ‖e‖ * ‖x₁ - x₂‖ := abs_real_inner_le_norm e (x₁ - x₂)
      _ = ‖x₁ - x₂‖ := by rw [he, one_mul]
  have hulip : LocallyLipschitzOn (⊤ : Opens E) u :=
    ((hlip_h.max_const 0).min_const δ).locallyLipschitzOn
  have hsuper : ∀ r ∈ Ioo 0 δ, {x : E | r < u x} = {x : E | r < h x} := fun r hr ↦ by
    ext x; simp only [u, mem_ofPred_eq, lt_min_iff, lt_max_iff]
    exact ⟨fun ⟨h1, _⟩ ↦ h1.resolve_right (not_lt.2 hr.1.le), fun hx ↦ ⟨Or.inl hx, hr.2⟩⟩
  have hgrad_meas : AEMeasurable
      ({x : E | 0 < h x ∧ h x < δ}.indicator
        (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))) volume :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.add (((hw.continuous_fderiv one_ne_zero).comp q.continuous).norm.pow
        2))))).measurable.indicator ((measurableSet_lt measurable_const hcont_h.measurable).inter
          (measurableSet_lt hcont_h.measurable measurable_const))).aemeasurable
  -- Step 2: Apply coarea, slice along `e`, and bound each line integral by `δ √(4 + ‖Dw‖²)`.
  calc ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < h x}
      = ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < u x} :=
        setLIntegral_congr_fun measurableSet_Ioo fun r hr ↦ by rw [hsuper r hr]
    _ ≤ ∫⁻ r, perimeter volume ⊤ {x : E | r < u x} := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, ‖fderiv ℝ u x‖ₑ := by
        rw [hulip.lintegral_perimeter_eq_setLIntegral_enorm_fderiv, Opens.coe_top,
          Measure.restrict_univ]
    _ = ∫⁻ x, {x : E | 0 < h x ∧ h x < δ}.indicator
          (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2))) x :=
        lintegral_congr_ae (enorm_fderiv_clamp_subgraph_ae e he hw hδ)
    _ = ∫⁻ y : H, ∫⁻ t : ℝ, {x : E | 0 < h x ∧ h x < δ}.indicator
          (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))
          ((y : E) + t • e) :=
        lintegral_eq_lintegral_lintegral_line e he hgrad_meas
    _ ≤ ∫⁻ y : H, {y : H | 0 < w y}.indicator
          (fun y ↦ ENNReal.ofReal δ * ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2)) y := by
        refine lintegral_mono fun y ↦ ?_
        set c : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w y‖ ^ 2))
        set T : Set ℝ := {t : ℝ | 0 < w y / 2 - |t| ∧ w y / 2 - |t| < δ}
        have hTm : MeasurableSet T :=
          (measurableSet_lt measurable_const
            (measurable_const.sub continuous_abs.measurable)).inter
            (measurableSet_lt (measurable_const.sub continuous_abs.measurable) measurable_const)
        have hind_eq : (fun t : ℝ ↦ {x : E | 0 < h x ∧ h x < δ}.indicator
            (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))
            ((y : E) + t • e)) = T.indicator (fun _ ↦ c) := funext fun t ↦ by
          by_cases ht : t ∈ T
          · rw [indicator_of_mem ht,
              indicator_of_mem (by simpa [T, h, subgraphHeight_add_smul e he] using ht),
              subgraphProj_add_smul e he]
          · rw [indicator_of_notMem ht,
              indicator_of_notMem (by simpa [T, h, subgraphHeight_add_smul e he] using ht)]
        rw [hind_eq, lintegral_indicator_const hTm]
        by_cases hy : 0 < w y
        · rw [indicator_of_mem hy]
          refine (mul_le_mul_right (volume_setOf_pos_sub_abs_lt_le (w y / 2) hδ) c).trans_eq ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hδ.le]
          congr 1; ring
        · rw [indicator_of_notMem hy,
            eq_empty_of_forall_notMem (s := T) fun t ⟨h1, _⟩ ↦ by linarith [abs_nonneg t]]
          simp
    _ = ENNReal.ofReal δ *
          ∫⁻ y in {y : H | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
        rw [lintegral_indicator (measurableSet_lt measurable_const hw.continuous.measurable),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Perimeter upper bound for a `C¹` symmetric subgraph.** Let `w : (ℝ ∙ e)ᗮ → ℝ` be `C¹`. The
open symmetric subgraph `S = {x : E | |⟪e, x⟫| < w y / 2}` (where `y` is the orthogonal projection
of `x` onto `(ℝ ∙ e)ᗮ`) has whole-space perimeter at most `∫⁻_{0 < w} √(4 + ‖Dw‖²)`. No
nonnegativity or integrability assumption on `w` is needed. -/
theorem perimeter_setOf_abs_inner_lt_div_two_le (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) :
    perimeter volume ⊤
        {x : E | |⟪e, x⟫_ℝ| < w ((orthogonalLineEquiv e he).symm x).1 / 2} ≤
      ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
  let H := (ℝ ∙ e)ᗮ
  let h := subgraphHeight e he w
  have hS_eq : {x : E | |⟪e, x⟫_ℝ| < w ((orthogonalLineEquiv e he).symm x).1 / 2} =
      {x : E | 0 < h x} := by ext x; simp [h, subgraphHeight, subgraphProj, sub_pos]
  rw [hS_eq]
  have hcont_h : Continuous h := continuous_subgraphHeight e he hw.continuous
  set B : ℝ≥0∞ := ∫⁻ y in {y : H | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2)
  rcases eq_or_ne B ∞ with hBtop | hBfin
  · simp [hBtop]
  have hexists (k : ℕ) : ∃ r ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)),
      perimeter volume ⊤ {x : E | r < h x} ≤ B + ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    exists_mem_Ioo_le_add_of_setLIntegral_le hBfin (by positivity)
      (lintegral_perimeter_superlevel_subgraphHeight_le e he hw (by positivity))
  choose r hr_mem hr_per using hexists
  have hlsc : perimeter volume ⊤ {x : E | 0 < h x} ≤
      liminf (fun k : ℕ ↦ perimeter volume ⊤ {x : E | r k < h x}) atTop := by
    refine perimeter_le_liminf
      (.of_forall fun _ ↦ (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet)
      (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet fun K hK _ ↦ ?_
    have hGlim : Tendsto
        (fun k : ℕ ↦ volume ({x : E | 0 < h x ∧ h x ≤ 1 / ((k : ℝ) + 1)} ∩ K)) atTop (𝓝 0) :=
      hcont_h.measurable.aemeasurable.tendsto_measure_setOf_pos_lt_le_inter
        hK.measurableSet.nullMeasurableSet hK.measure_lt_top.ne
        (fun _ _ hmn ↦ one_div_le_one_div_of_le (by positivity) (by gcongr))
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim
      (fun _ ↦ zero_le) fun k ↦ measure_mono fun x ⟨hx, hxK⟩ ↦ ⟨?_, hxK⟩
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd ((hr_mem k).1.trans h1) h2
    · exact ⟨h1, (not_lt.1 h2).trans (hr_mem k).2.le⟩
  calc perimeter volume ⊤ {x : E | 0 < h x}
      ≤ liminf (fun k : ℕ ↦ perimeter volume ⊤ {x : E | r k < h x}) atTop := hlsc
    _ ≤ liminf (fun k : ℕ ↦ B + ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop :=
        liminf_le_liminf (.of_forall hr_per)
    _ = B := Tendsto.liminf_eq <| by
        simpa only [ENNReal.ofReal_zero, add_zero] using
          (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat).const_add B

end TauCeti

end
