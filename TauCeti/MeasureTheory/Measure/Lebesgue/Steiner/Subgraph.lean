/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.BoundedVariation.Coarea

/-!
# Perimeter of smooth symmetric subgraphs

Let `E` be a finite-dimensional real inner product space, `e` a unit vector with orthogonal
hyperplane `H = (ℝ ∙ e)ᗮ`, and `w : H → ℝ` a function. The open symmetric subgraph of `w` along `e`
is

`S = {x : E | |⟪e, x⟫| < w y / 2}`,

where `y` is the orthogonal projection of `x` onto `H`. Each parallel line section of `S` along `e`
is the centered open interval `Metric.eball 0 (ENNReal.ofReal (w y) / 2)`
(`TauCeti.lineSection_setOf_abs_inner_lt_div_two`).

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
`{r_k < h} → {0 < h}` locally in measure, lower semicontinuity of the perimeter concludes.

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

/-- Line sections of an open symmetric subgraph `{x | |⟪e, x⟫| < f y / 2}` along the unit
direction `e` are the centered open intervals `Metric.eball 0 (ENNReal.ofReal (f y) / 2)`. -/
theorem lineSection_setOf_abs_inner_lt_div_two (e : E) (he : ‖e‖ = 1)
    (f : (ℝ ∙ e)ᗮ → ℝ) (y : (ℝ ∙ e)ᗮ) :
    {t : ℝ | (y : E) + t • e ∈
        {x : E | |⟪e, x⟫_ℝ| < f ((orthogonalLineEquiv e he).symm x).1 / 2}} =
      Metric.eball (0 : ℝ) (ENNReal.ofReal (f y) / 2) := by
  ext t
  have hqyt : ((orthogonalLineEquiv e he).symm ((y : E) + t • e)).1 = y := by
    rw [← orthogonalLineEquiv_apply e he y t, (orthogonalLineEquiv e he).symm_apply_apply]
  simp only [mem_ofPred_eq, inner_add_smul e he, hqyt, Metric.mem_eball, edist_zero_right,
    Real.eNorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos zero_lt_two]
  rcases le_or_gt (f y) 0 with hle | hgt
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hle zero_le_two)]
    exact ⟨fun h ↦ by linarith [abs_nonneg t], fun h ↦ absurd h (not_lt_of_ge zero_le)⟩
  · rw [ENNReal.ofReal_lt_ofReal_iff (div_pos hgt zero_lt_two)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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
  let q : E →L[ℝ] H :=
    (ContinuousLinearMap.fst ℝ H ℝ).comp (orthogonalLineEquiv e he).symm.toContinuousLinearMap
  have hqyt (y : H) (t : ℝ) : q ((y : E) + t • e) = y := by
    rw [← orthogonalLineEquiv_apply e he y t]
    exact congrArg Prod.fst ((orthogonalLineEquiv e he).symm_apply_apply (y, t))
  let h : E → ℝ := fun x ↦ w (q x) / 2 - |⟪e, x⟫_ℝ|
  have hhyt (y : H) (t : ℝ) : h ((y : E) + t • e) = w y / 2 - |t| := by
    simp [h, hqyt, inner_add_smul e he]
  have hS_eq : {x : E | |⟪e, x⟫_ℝ| < w ((orthogonalLineEquiv e he).symm x).1 / 2} =
      {x : E | 0 < h x} := by ext x; simp [h, q, sub_pos]
  rw [hS_eq]
  have hcont_h : Continuous h :=
    ((hw.continuous.comp q.continuous).div_const 2).sub
      (continuous_const.inner continuous_id).abs
  have hlip_h : LocallyLipschitz h := by
    refine ((hw.comp q.contDiff).div_const 2).locallyLipschitz.sub
      (LipschitzWith.of_dist_le_mul (K := 1) fun x₁ x₂ ↦ ?_).locallyLipschitz
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    calc |(|⟪e, x₁⟫_ℝ| - |⟪e, x₂⟫_ℝ|)| ≤ |⟪e, x₁ - x₂⟫_ℝ| := by
          rw [inner_sub_right]; exact abs_abs_sub_abs_le _ _
      _ ≤ ‖e‖ * ‖x₁ - x₂‖ := abs_real_inner_le_norm e (x₁ - x₂)
      _ = ‖x₁ - x₂‖ := by rw [he, one_mul]
  -- Key coarea estimate on `{0 < h < δ}` for every `δ > 0`.
  have hcoarea {δ : ℝ} (hδ : 0 < δ) :
      ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < h x} ≤
        ENNReal.ofReal δ *
          ∫⁻ y in {y : H | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
    let u : E → ℝ := fun x ↦ min (max (h x) 0) δ
    have hulip : LocallyLipschitzOn (⊤ : Opens E) u :=
      ((hlip_h.max_const 0).min_const δ).locallyLipschitzOn
    have hsuper : ∀ r ∈ Ioo 0 δ, {x : E | r < u x} = {x : E | r < h x} := fun r hr ↦ by
      ext x; simp only [u, mem_ofPred_eq, lt_min_iff, lt_max_iff]
      exact ⟨fun ⟨h1, _⟩ ↦ h1.resolve_right (not_lt.2 hr.1.le), fun hx ↦ ⟨Or.inl hx, hr.2⟩⟩
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
        simp only [Z, mem_ofPred_eq, hhyt, inner_add_smul e he] at ht
        rcases ht with h1 | h2 | h3
        · have habs : |t| = R := by dsimp only [R]; linarith
          rcases (abs_eq (habs ▸ abs_nonneg t)).1 habs with rfl | rfl <;> simp
        · have habs : |t| = R - δ := by dsimp only [R]; linarith
          rcases (abs_eq (habs ▸ abs_nonneg t)).1 habs with rfl | rfl <;> simp
        · exact Or.inl h3
      exact measure_mono_null hsub (Set.Finite.measure_zero (by simp) volume)
    have hgrad_ae : ∀ᵐ x : E ∂volume,
        ‖fderiv ℝ u x‖ₑ =
          {x : E | 0 < h x ∧ h x < δ}.indicator
            (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2))) x := by
      filter_upwards [ae_iff.2 (by simpa using hZ_null : volume {x : E | ¬x ∉ Z} = 0)] with x hxZ
      simp only [Z, mem_ofPred_eq, not_or] at hxZ
      obtain ⟨hx0, hxδ, hxt⟩ := hxZ
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have hev : u =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
          filter_upwards [(isOpen_lt hcont_h continuous_const).mem_nhds hneg] with z hz
          simp [u, max_eq_right (le_of_lt hz), min_eq_left hδ.le]
        rw [hev.fderiv_eq, fderiv_const_apply,
          indicator_of_notMem (fun (hx : 0 < h x ∧ h x < δ) ↦ hneg.not_gt hx.1)]
        exact (eNorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
      · rcases lt_or_gt_of_ne hxδ with hlt | hgt
        · rw [indicator_of_mem (show x ∈ {x : E | 0 < h x ∧ h x < δ} from ⟨hpos, hlt⟩)]
          have hev_u : u =ᶠ[𝓝 x] h := by
            filter_upwards [((isOpen_lt continuous_const hcont_h).inter
                (isOpen_lt hcont_h continuous_const)).mem_nhds ⟨hpos, hlt⟩] with z hz
            simp [u, max_eq_left hz.1.le, min_eq_left hz.2.le]
          rw [hev_u.fderiv_eq]
          have hd1 : HasFDerivAt (fun z : E ↦ w (q z) / 2)
              (((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) x := by
            simpa [div_eq_inv_mul, smul_eq_mul, ContinuousLinearMap.smul_comp] using
              (((hw.differentiable one_ne_zero (q x)).hasFDerivAt).comp x
                q.hasFDerivAt).const_mul (1 / 2 : ℝ)
          let σ : ℝ := if 0 < ⟪e, x⟫_ℝ then -1 else 1
          have hσsq : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
          have hd2 : HasFDerivAt (fun z : E ↦ -|⟪e, z⟫_ℝ|) (σ • innerSL ℝ e) x := by
            rcases lt_or_gt_of_ne hxt with ht_neg | ht_pos
            · have hev : (fun z : E ↦ -|⟪e, z⟫_ℝ|) =ᶠ[𝓝 x] fun z ↦ ⟪e, z⟫_ℝ := by
                filter_upwards [(isOpen_lt (continuous_const.inner continuous_id)
                  continuous_const).mem_nhds ht_neg] with z hz
                dsimp only [id_eq] at hz; rw [abs_of_neg hz, neg_neg]
              rw [show σ = 1 from ite_eq_right (not_lt.2 ht_neg.le), one_smul]
              exact (innerSL ℝ e).hasFDerivAt.congr_of_eventuallyEq hev
            · have hev : (fun z : E ↦ -|⟪e, z⟫_ℝ|) =ᶠ[𝓝 x] fun z ↦ -⟪e, z⟫_ℝ := by
                filter_upwards [(isOpen_lt continuous_const
                  (continuous_const.inner continuous_id)).mem_nhds ht_pos] with z hz
                dsimp only [id_eq] at hz; rw [abs_of_pos hz]
              rw [show σ = -1 from ite_eq_left ht_pos, neg_one_smul]
              exact (innerSL ℝ e).hasFDerivAt.neg.congr_of_eventuallyEq hev
          have hdh : HasFDerivAt h
              ((((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) + σ • innerSL ℝ e) x :=
            (hd1.add hd2).congr_of_eventuallyEq (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)
          let v : H := (InnerProductSpace.toDual ℝ H).symm ((1 / 2 : ℝ) • fderiv ℝ w (q x))
          have hv_norm : ‖v‖ = (1 / 2) * ‖fderiv ℝ w (q x)‖ := by
            rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_of_nonneg (by positivity)]
          have hdual : (((1 / 2 : ℝ) • fderiv ℝ w (q x)).comp q) + σ • innerSL ℝ e =
              InnerProductSpace.toDual ℝ E ((v : E) + σ • e) := by
            ext z
            obtain ⟨⟨y_z, t_z⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective z
            have hv_apply : ⟪(v : E), (y_z : E)⟫_ℝ = ((1 / 2 : ℝ) • fderiv ℝ w (q x)) y_z := by
              simpa [v] using InnerProductSpace.toDual_symm_apply
                (y := (1 / 2 : ℝ) • fderiv ℝ w (q x)) (x := y_z)
            simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
              orthogonalLineEquiv_apply, hqyt, InnerProductSpace.toDual_apply_apply, inner_add_left,
              inner_add_right, inner_smul_left, inner_smul_right,
              Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property,
              Submodule.mem_orthogonal_singleton_iff_inner_right.mp y_z.property,
              real_inner_self_eq_norm_sq, he, smul_eq_mul, starRingEnd_apply, star_trivial,
              mul_zero, add_zero, zero_add, one_pow, mul_one, hv_apply]
            ring
          rw [← ofReal_norm, hdh.fderiv, hdual, LinearIsometryEquiv.norm_map]
          congr 1
          have hsq : ‖(v : E) + σ • e‖ ^ 2 = ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)) ^ 2 := by
            rw [norm_add_smul_sq e he, hv_norm, hσsq, mul_pow, mul_pow,
              Real.sq_sqrt (add_nonneg (by norm_num) (sq_nonneg _))]
            ring
          nlinarith [norm_nonneg ((v : E) + σ • e), Real.sqrt_nonneg (4 + ‖fderiv ℝ w (q x)‖ ^ 2)]
        · have hev : u =ᶠ[𝓝 x] fun _ ↦ δ := by
            filter_upwards [(isOpen_lt continuous_const hcont_h).mem_nhds hgt] with z hz
            simp [u, max_eq_left (hδ.trans hz).le, min_eq_right hz.le]
          rw [hev.fderiv_eq, fderiv_const_apply,
            indicator_of_notMem (fun (hx : 0 < h x ∧ h x < δ) ↦ hgt.not_gt hx.2)]
          exact (eNorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
    have hgrad_meas : AEMeasurable
        ({x : E | 0 < h x ∧ h x < δ}.indicator
          (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))) volume :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.add (((hw.continuous_fderiv one_ne_zero).comp q.continuous).norm.pow
          2))))).measurable.indicator ((measurableSet_lt measurable_const hcont_h.measurable).inter
            (measurableSet_lt hcont_h.measurable measurable_const))).aemeasurable
    calc ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < h x}
        = ∫⁻ r in Ioo 0 δ, perimeter volume ⊤ {x : E | r < u x} :=
          setLIntegral_congr_fun measurableSet_Ioo fun r hr ↦ by rw [hsuper r hr]
      _ ≤ ∫⁻ r, perimeter volume ⊤ {x : E | r < u x} := setLIntegral_le_lintegral _ _
      _ = ∫⁻ x, ‖fderiv ℝ u x‖ₑ := by
          rw [hulip.lintegral_perimeter_eq_setLIntegral_enorm_fderiv, Opens.coe_top,
            Measure.restrict_univ]
      _ = ∫⁻ x, {x : E | 0 < h x ∧ h x < δ}.indicator
            (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2))) x :=
          lintegral_congr_ae hgrad_ae
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
          rw [show (fun t : ℝ ↦ {x : E | 0 < h x ∧ h x < δ}.indicator
              (fun x ↦ ENNReal.ofReal ((1 / 2) * √(4 + ‖fderiv ℝ w (q x)‖ ^ 2)))
              ((y : E) + t • e)) = T.indicator (fun _ ↦ c) from funext fun t ↦ by
                by_cases ht : t ∈ T
                · rw [indicator_of_mem ht, indicator_of_mem (by simpa [T, hhyt] using ht), hqyt]
                · rw [indicator_of_notMem ht, indicator_of_notMem (by simpa [T, hhyt] using ht)],
            lintegral_indicator_const hTm]
          by_cases hy : 0 < w y
          · rw [indicator_of_mem hy]
            set R : ℝ := w y / 2
            have hTvol : volume T ≤ ENNReal.ofReal (2 * δ) := by
              have hTsub : T ⊆ Ioo (R - δ) R ∪ Ioo (-R) (-(R - δ)) := fun t ⟨h1, h2⟩ ↦ by
                change 0 < R - |t| at h1; change R - |t| < δ at h2
                rcases le_or_gt 0 t with ht | ht
                · rw [abs_of_nonneg ht] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
                · rw [abs_of_neg ht] at h1 h2; exact Or.inr ⟨by linarith, by linarith⟩
              refine ((measure_mono hTsub).trans (measure_union_le _ _)).trans_eq ?_
              rw [Real.volume_Ioo, Real.volume_Ioo, show R - (R - δ) = δ by ring,
                show -(R - δ) - -R = δ by ring, ← ENNReal.ofReal_add hδ.le hδ.le, two_mul]
            refine (mul_le_mul_right hTvol c).trans_eq ?_
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hδ.le]
            congr 1; ring
          · rw [indicator_of_notMem hy,
              eq_empty_of_forall_notMem (s := T) fun t ⟨h1, _⟩ ↦ by linarith [abs_nonneg t]]
            simp
      _ = ENNReal.ofReal δ *
            ∫⁻ y in {y : H | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2) := by
          rw [lintegral_indicator (measurableSet_lt measurable_const hw.continuous.measurable),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  set B : ℝ≥0∞ := ∫⁻ y in {y : H | 0 < w y}, ENNReal.ofReal √(4 + ‖fderiv ℝ w y‖ ^ 2)
  rcases eq_or_ne B ∞ with hBtop | hBfin
  · simp [hBtop]
  have hexists (k : ℕ) : ∃ r ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)),
      perimeter volume ⊤ {x : E | r < h x} ≤ B + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    by_contra! hgt
    have hle : ENNReal.ofReal δ * B + ENNReal.ofReal δ * ENNReal.ofReal δ ≤
        ENNReal.ofReal δ * B := by
      have h1 : ENNReal.ofReal δ * (B + ENNReal.ofReal δ) =
          ∫⁻ _ in Ioo 0 δ, (B + ENNReal.ofReal δ) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
      rw [← mul_add, h1]
      exact (setLIntegral_mono' measurableSet_Ioo fun r hr ↦ (hgt r hr).le).trans (hcoarea hδ)
    have h0 : ENNReal.ofReal δ * ENNReal.ofReal δ = 0 := nonpos_iff_eq_zero.1 <|
      WithTop.le_of_add_le_add_left (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin)
        (hle.trans_eq (add_zero _).symm)
    exact mul_ne_zero (by positivity) (by positivity) h0
  choose r hr_mem hr_per using hexists
  have hlsc : perimeter volume ⊤ {x : E | 0 < h x} ≤
      liminf (fun k : ℕ ↦ perimeter volume ⊤ {x : E | r k < h x}) atTop := by
    refine perimeter_le_liminf
      (.of_forall fun _ ↦ (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet)
      (measurableSet_lt measurable_const hcont_h.measurable).nullMeasurableSet fun K hK _ ↦ ?_
    let G : ℕ → Set E := fun k ↦ {x : E | 0 < h x ∧ h x ≤ 1 / ((k : ℝ) + 1)} ∩ K
    have hGm (k : ℕ) : NullMeasurableSet (G k) volume :=
      (((measurableSet_lt measurable_const hcont_h.measurable).inter
        (measurableSet_le hcont_h.measurable measurable_const)).inter
        hK.measurableSet).nullMeasurableSet
    have hGanti : Antitone G := fun m n hmn _ ⟨⟨h1, h2⟩, hxK⟩ ↦
      ⟨⟨h1, h2.trans (one_div_le_one_div_of_le (by positivity) (by gcongr))⟩, hxK⟩
    have hGfin : volume (G 0) ≠ ∞ :=
      ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono inter_subset_right)
    have hGinter : (⋂ k, G k) = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
      simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq, G] at hx
      exact (hx 0).1.1.not_ge
        (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun k ↦ (hx k).1.2)
    have hGlim : Tendsto (fun k : ℕ ↦ volume (G k)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hGinter, measure_empty] using
        tendsto_measure_iInter_atTop hGm hGanti ⟨0, hGfin⟩
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
