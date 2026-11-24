/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Integral.Lebesgue.ApproximateBound
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import TauCeti.Topology.UniformSpace.UniformConvergence.Translate

/-!
# Limits of translates along a strip with vanishing derivatives on windows

Let `w i : ℝ × ℝ → F` be `C¹` maps into a Banach space, and translate them along the first
coordinate by parameters `s_i`, so that the translated windows `[a + s_i, b + s_i] × [0, 1]`
eventually lie in the domain where the `w i` are `C¹`. Suppose that the translates
`z ↦ w i (z + (s_i, 0))` converge locally uniformly on the strip `ℝ × [0, 1]` to a map `v`.

* If the `L¹` norm of `∂_s w i` over every translated window tends to zero, then `v` does not
  depend on the first coordinate
  (`TauCeti.eq_of_tendstoLocallyUniformlyOn_comp_add`): along each
  horizontal segment the variation of `w i` is the integral of `∂_s w i`.
* If moreover the `L¹` norm of the defect `∂_t w i - Φ(t, w i)` over the windows of width one
  tends to zero, for a continuous time-dependent vector field `Φ`, then `x(t) = v(0, t)` solves
  the integral equation `x(t₂) - x(t₁) = ∫_{t₁}^{t₂} Φ(t, x(t)) dt` and hence the differential
  equation `x' = Φ(t, x)` on `[0, 1]`
  (`TauCeti.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`):
  along each vertical segment the defect from the integral equation is the integral of
  `∂_t w i - Φ(t, w i)`.

On windows of bounded measure, convergence to zero in `L²` implies convergence to zero in `L¹`
(`TauCeti.MeasureTheory.tendsto_setLIntegral_enorm_of_tendsto_setLIntegral_ofReal_norm_sq`,
specialized to the translated windows in
`TauCeti.tendsto_setLIntegral_enorm_Icc_prod_of_tendsto_setLIntegral_ofReal_norm_sq`), which is the
form in which energy bounds supply the hypotheses.

These are the analytic steps of the breaking of Floer cylinders along necks, where `Φ` is a
Hamiltonian vector field and the derivative bounds come from the vanishing of the energy over the
windows. Stated for maps into a Banach space, they apply both to Floer cylinders in a symplectic
vector space and to Floer cylinders in a manifold read through an embedding into a vector space.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-- **`L²` control gives `L¹` control on translated windows.** On the windows
`[a + s_i, b + s_i] × [c, d]`, which all have measure `(b - a) (d - c)`, if the `L²` norms of `g i`
tend to zero then so do their `L¹` norms. -/
theorem tendsto_setLIntegral_enorm_Icc_prod_of_tendsto_setLIntegral_ofReal_norm_sq {ι F : Type*}
    [NormedAddCommGroup F] {l : Filter ι} {s : ι → ℝ} {a b c d : ℝ} {g : ι → ℝ × ℝ → F}
    (hg : ∀ᶠ i in l,
      AEStronglyMeasurable (g i) (volume.restrict (Icc (a + s i) (b + s i) ×ˢ Icc c d)))
    (h : Tendsto (fun i ↦ ∫⁻ z in Icc (a + s i) (b + s i) ×ˢ Icc c d,
      ENNReal.ofReal (‖g i z‖ ^ 2)) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ z in Icc (a + s i) (b + s i) ×ˢ Icc c d, ‖g i z‖ₑ) l (𝓝 0) := by
  refine MeasureTheory.tendsto_setLIntegral_enorm_of_tendsto_setLIntegral_ofReal_norm_sq
    (C := ENNReal.ofReal (b - a) * ENNReal.ofReal (d - c))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (Eventually.of_forall fun i ↦ ?_) hg h
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  simp

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {U : Set (ℝ × ℝ)} {w : ℝ × ℝ → F}

/-- Along a horizontal segment the variation of a `C¹` map `w` is the integral of `∂_s w`.
Integrating over `t ∈ [0, 1]`, the variation between the two vertical sides of `[α, β] × [0, 1]` is
controlled by the `L¹` norm of `∂_s w` over the rectangle. -/
theorem setLIntegral_edist_le_setLIntegral_enorm_fderiv (hU : IsOpen U) (hw : ContDiffOn ℝ 1 w U)
    {α β : ℝ} (hαβ : α ≤ β) (hR : Icc α β ×ˢ Icc 0 1 ⊆ U) :
    ∫⁻ t in Icc (0 : ℝ) 1, edist (w (β, t)) (w (α, t)) ≤
      ∫⁻ z in Icc α β ×ˢ Icc 0 1, ‖fderiv ℝ w z (1, 0)‖ₑ := by
  have hcont : ContinuousOn (fun z ↦ fderiv ℝ w z (1, 0)) U :=
    (hw.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  rw [Measure.volume_eq_prod, setLIntegral_prod_symm (fun z ↦ ‖fderiv ℝ w z (1, 0)‖ₑ)
    ((hcont.mono hR).eNorm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc))]
  refine setLIntegral_mono' measurableSet_Icc fun t ht ↦ ?_
  have hmem {r : ℝ} (hr : r ∈ uIcc α β) : (r, t) ∈ U := hR ⟨by rwa [uIcc_of_le hαβ] at hr, ht⟩
  -- The fundamental theorem of calculus along the segment `[α, β] × {t}`.
  have hderiv : ∀ r ∈ uIcc α β, HasDerivAt (fun r ↦ w (r, t)) (fderiv ℝ w (r, t) (1, 0)) r :=
    fun r hr ↦ hasDerivAt_slice_left
      ((hw.differentiableOn one_ne_zero _ (hmem hr)).differentiableAt (hU.mem_nhds (hmem hr)))
  have hint : IntervalIntegrable (fun r ↦ fderiv ℝ w (r, t) (1, 0)) volume α β :=
    (hcont.comp (by fun_prop) fun r hr ↦ hmem hr).intervalIntegrable
  rw [eDist_eq_eNorm_sub, ← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    intervalIntegral.integral_of_le hαβ]
  exact (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono_set Ioc_subset_Icc_self)

/-- Along a vertical segment `{r} × [t₁, t₂]` the defect of a `C¹` map `w` from the integral
equation of the time-dependent vector field `Φ` is the integral of `∂_t w - Φ(t, w)`. Integrating
over `r ∈ [α, β]`, the defect is controlled by the `L¹` norm of `∂_t w - Φ(t, w)` over the rectangle
`[α, β] × [0, 1]`. -/
theorem setLIntegral_enorm_sub_sub_integral_le {Φ : ℝ × F → F} (hΦ : Continuous Φ)
    (hU : IsOpen U) (hw : ContDiffOn ℝ 1 w U) {α β t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂)
    (ht₂ : t₂ ≤ 1) (hR : Icc α β ×ˢ Icc 0 1 ⊆ U) :
    ∫⁻ r in Icc α β, ‖w (r, t₂) - w (r, t₁) - ∫ t in t₁..t₂, Φ (t, w (r, t))‖ₑ ≤
      ∫⁻ z in Icc α β ×ˢ Icc 0 1, ‖fderiv ℝ w z (0, 1) - Φ (z.2, w z)‖ₑ := by
  have hcont : ContinuousOn (fun z ↦ fderiv ℝ w z (0, 1)) U :=
    (hw.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hcontΦ : ContinuousOn (fun z : ℝ × ℝ ↦ Φ (z.2, w z)) U :=
    hΦ.comp_continuousOn (continuousOn_snd.prodMk hw.continuousOn)
  rw [Measure.volume_eq_prod, setLIntegral_prod
    (fun z ↦ ‖fderiv ℝ w z (0, 1) - Φ (z.2, w z)‖ₑ)
    (((hcont.sub hcontΦ).mono hR).eNorm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc))]
  refine setLIntegral_mono' measurableSet_Icc fun r hr ↦ ?_
  have hsub : uIcc t₁ t₂ ⊆ Icc 0 1 := uIcc_subset_Icc ⟨ht₁, ht.trans ht₂⟩ ⟨ht₁.trans ht, ht₂⟩
  have hmem {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : (r, t) ∈ U := hR ⟨hr, hsub htm⟩
  -- The fundamental theorem of calculus along the segment `{r} × [t₁, t₂]`.
  have hderiv : ∀ t ∈ uIcc t₁ t₂, HasDerivAt (fun t ↦ w (r, t)) (fderiv ℝ w (r, t) (0, 1)) t :=
    fun t htm ↦ hasDerivAt_slice_right
      ((hw.differentiableOn one_ne_zero _ (hmem htm)).differentiableAt (hU.mem_nhds (hmem htm)))
  have hint : IntervalIntegrable (fun t ↦ fderiv ℝ w (r, t) (0, 1)) volume t₁ t₂ :=
    (hcont.comp (by fun_prop) fun t htm ↦ hmem htm).intervalIntegrable
  have hintΦ : IntervalIntegrable (fun t ↦ Φ (t, w (r, t))) volume t₁ t₂ :=
    (hcontΦ.comp (by fun_prop) fun t htm ↦ hmem htm).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    ← intervalIntegral.integral_sub hint hintΦ, intervalIntegral.integral_of_le ht]
  exact (eNorm_integral_le_lintegral_eNorm _).trans
    (lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht₁ ht₂)))

variable {ι : Type*} {l : Filter ι} [l.NeBot] {w : ι → ℝ × ℝ → F} {s : ι → ℝ} {v : ℝ × ℝ → F}

/-- **Translates with vanishing `∂_s` on windows have a limit independent of `s`.** Let each
`w i` be `C¹` on an open set `U`, let the translated windows `[a + s_i, b + s_i] × [0, 1]`
eventually lie in `U`, and let the `L¹` norm of `∂_s w i` over them tend to zero. If the
translates `z ↦ w i (z + (s_i, 0))` converge locally uniformly on the strip `ℝ × [0, 1]` to `v`,
then `v (r, t) = v (0, t)`. -/
theorem eq_of_tendstoLocallyUniformlyOn_comp_add (hU : IsOpen U)
    (hw : ∀ i, ContDiffOn ℝ 1 (w i) U)
    (hW : ∀ a b : ℝ, ∀ᶠ i in l, Icc (a + s i) (b + s i) ×ˢ Icc 0 1 ⊆ U)
    (hd : ∀ a b : ℝ, Tendsto (fun i ↦ ∫⁻ z in Icc (a + s i) (b + s i) ×ˢ Icc 0 1,
      ‖fderiv ℝ (w i) z (1, 0)‖ₑ) l (𝓝 0))
    (hv : TendstoLocallyUniformlyOn (fun i z ↦ w i (z + (s i, 0))) v l
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t) := by
  -- It suffices to compare the two vertical sides of a rectangle `[α, β] × [0, 1]`.
  have key {α β : ℝ} (hαβ : α ≤ β) : ∀ t ∈ Icc (0 : ℝ) 1, v (β, t) = v (α, t) := by
    obtain ⟨hUC, -, hvK⟩ := tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn isCompact_Icc
      (Eventually.of_forall fun i ↦ (hw i).continuousOn) (hW α β) hv
    have hsides {γ : ℝ} (hγ : γ ∈ Icc α β) : ContinuousOn (fun t ↦ v (γ, t)) (Icc 0 1) :=
      hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦ ⟨hγ, ht⟩
    have hβ : β ∈ Icc α β := ⟨hαβ, le_rfl⟩
    have hα : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
    -- The mean distance between the two sides vanishes.
    have hzero : ∫⁻ t in Icc (0 : ℝ) 1, edist (v (β, t)) (v (α, t)) = 0 := by
      refine lintegral_eq_zero_of_eventually_le_add
        (f := fun i t ↦ edist (w i (β + s i, t)) (w i (α + s i, t)))
        (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hd α β)
          (Eventually.of_forall fun _ ↦ zero_le) ?_) fun ε hε ↦ ?_
      · filter_upwards [hW α β] with i hi
        exact setLIntegral_edist_le_setLIntegral_enorm_fderiv hU (hw i) (by linarith) hi
      · filter_upwards [EMetric.tendstoUniformlyOn_iff.1 hUC (ε / 2)
          (ENNReal.half_pos (by exact_mod_cast hε.ne'))] with i hi
        refine ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ ?_
        have h₁ := hi (β, t) ⟨hβ, ht⟩
        have h₂ := hi (α, t) ⟨hα, ht⟩
        simp only [Prod.mk_add_mk, add_zero] at h₁ h₂
        calc edist (v (β, t)) (v (α, t))
            ≤ edist (v (β, t)) (w i (β + s i, t)) + edist (w i (β + s i, t)) (w i (α + s i, t)) +
                edist (w i (α + s i, t)) (v (α, t)) := edist_triangle4 _ _ _ _
          _ ≤ ε / 2 + edist (w i (β + s i, t)) (w i (α + s i, t)) + ε / 2 := by
              rw [edist_comm (w i (α + s i, t))]
              gcongr
          _ = edist (w i (β + s i, t)) (w i (α + s i, t)) + ε := by
              rw [add_comm (_ / 2), add_assoc, ENNReal.add_halves]
    have hae := (lintegral_eq_zero_iff' ((continuous_edist.comp_continuousOn
      ((hsides hβ).prodMk (hsides hα))).aemeasurable measurableSet_Icc)).1 hzero
    exact Measure.eqOn_Icc_of_ae_eq volume zero_ne_one (hae.mono fun t ht ↦ edist_eq_zero.1 ht)
      (hsides hβ) (hsides hα)
  intro r t ht
  rcases le_total r 0 with hr | hr
  · exact (key hr t ht).symm
  · exact key hr t ht

omit [CompleteSpace F] [l.NeBot] in
/-- The defect of the integral equation of `Φ` along the limit path `v (0, ·)` is eventually, for
almost every `r ∈ [0, 1]`, at most `ε` more than the defect of `w i` along the segment
`{r + s i} × [t₁, t₂]`, by the uniform convergence of the translates and of the vector field along
them. -/
private theorem eventually_ae_enorm_sub_sub_integral_le_add {Φ : ℝ × F → F} (hΦ : Continuous Φ)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1)
    (hUC : TendstoUniformlyOn (fun i z ↦ w i (z + (s i, 0))) v l (Icc 0 1 ×ˢ Icc 0 1))
    (hΦUC : TendstoUniformlyOn (fun i z ↦ Φ (z.2, w i (z + (s i, 0)))) (fun z ↦ Φ (z.2, v z))
      l (Icc 0 1 ×ˢ Icc 0 1))
    (hFc : ∀ᶠ i in l, ContinuousOn (fun z ↦ w i (z + (s i, 0))) (Icc 0 1 ×ˢ Icc 0 1))
    (hvK : ContinuousOn v (Icc 0 1 ×ˢ Icc 0 1))
    (hstat : ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t)) (ε : ℝ≥0) (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖v (0, t₂) - v (0, t₁) - ∫ t in t₁..t₂, Φ (t, v (0, t))‖ₑ ≤
        ‖w i (r + s i, t₂) - w i (r + s i, t₁) - ∫ t in t₁..t₂, Φ (t, w i (r + s i, t))‖ₑ + ε := by
  have hsub : uIcc t₁ t₂ ⊆ Icc 0 1 := uIcc_subset_Icc ⟨ht₁, ht.trans ht₂⟩ ⟨ht₁.trans ht, ht₂⟩
  set δ : ℝ := ε / 3 with hδε
  have hδ : 0 < δ := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hUC δ hδ,
    Metric.tendstoUniformlyOn_iff.1 hΦUC δ hδ, hFc] with i hi hiΦ hic
  refine ae_restrict_of_forall_mem measurableSet_Icc fun r hr ↦ ?_
  have hmem {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : (r, t) ∈ Icc (0 : ℝ) 1 ×ˢ Icc 0 1 :=
    ⟨hr, hsub htm⟩
  have hF (t : ℝ) : w i ((r, t) + (s i, 0)) = w i (r + s i, t) := by simp
  -- Along the segment the limit is `v(0, ·)`, and the translates are uniformly close to it.
  have hxv : ∫ t in t₁..t₂, Φ (t, v (0, t)) = ∫ t in t₁..t₂, Φ (t, v (r, t)) :=
    intervalIntegral.integral_congr fun t htm ↦ by
      simp only [hstat r t (hsub htm)]
  have hcv : ContinuousOn (fun t ↦ Φ (t, v (r, t))) (uIcc t₁ t₂) :=
    hΦ.comp_continuousOn (continuousOn_id.prodMk
      (hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t htm ↦ hmem htm))
  have hcw : ContinuousOn (fun t ↦ Φ (t, w i (r + s i, t))) (uIcc t₁ t₂) := by
    refine hΦ.comp_continuousOn (continuousOn_id.prodMk ?_)
    simp_rw [← hF]
    exact hic.comp (continuousOn_const.prodMk continuousOn_id) fun t htm ↦ hmem htm
  have hend {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : ‖v (0, t) - w i (r + s i, t)‖ ≤ δ := by
    have h := hi (r, t) (hmem htm)
    rw [dist_eq_norm, hF, hstat r t (hsub htm)] at h
    exact h.le
  have hA := intervalIntegral.norm_sub_sub_integral_le (a₁ := v (0, t₁)) (a₂ := v (0, t₂))
    (b₁ := w i (r + s i, t₁)) (b₂ := w i (r + s i, t₂)) hcv.intervalIntegrable
    hcw.intervalIntegrable fun t htm ↦ by
      have h := hiΦ (r, t) (hmem (uIoc_subset_uIcc htm))
      rw [dist_eq_norm, hF] at h
      exact h.le
  rw [← hxv] at hA
  have hlen : δ * |t₂ - t₁| ≤ δ :=
    mul_le_of_le_one_right hδ.le (by rw [abs_of_nonneg (sub_nonneg.2 ht)]; linarith)
  replace hA := hA.trans (by linarith [hend left_mem_uIcc, hend right_mem_uIcc] :
    _ ≤ ‖w i (r + s i, t₂) - w i (r + s i, t₁) - ∫ t in t₁..t₂, Φ (t, w i (r + s i, t))‖ + ε)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hA

/-- **Translates with vanishing defect on windows solve the integral equation in the limit.**
Under the hypotheses of
`TauCeti.eq_of_tendstoLocallyUniformlyOn_comp_add`, let `Φ` be a
continuous time-dependent vector field such that the `L¹` norm of the defect `∂_t w i - Φ(t, w i)`
over the windows `[s_i, 1 + s_i] × [0, 1]` tends to zero. Then the path `x(t) = v(0, t)` satisfies
the integral equation `x(t₂) - x(t₁) = ∫_{t₁}^{t₂} Φ(t, x(t)) dt` for `0 ≤ t₁ ≤ t₂ ≤ 1`. -/
theorem sub_sub_integral_eq_zero_of_tendstoLocallyUniformlyOn_comp_add
    {Φ : ℝ × F → F} (hΦ : Continuous Φ) (hU : IsOpen U) (hw : ∀ i, ContDiffOn ℝ 1 (w i) U)
    (hW : ∀ a b : ℝ, ∀ᶠ i in l, Icc (a + s i) (b + s i) ×ˢ Icc 0 1 ⊆ U)
    (hd : ∀ a b : ℝ, Tendsto (fun i ↦ ∫⁻ z in Icc (a + s i) (b + s i) ×ˢ Icc 0 1,
      ‖fderiv ℝ (w i) z (1, 0)‖ₑ) l (𝓝 0))
    (hdΦ : Tendsto (fun i ↦ ∫⁻ z in Icc (s i) (1 + s i) ×ˢ Icc 0 1,
      ‖fderiv ℝ (w i) z (0, 1) - Φ (z.2, w i z)‖ₑ) l (𝓝 0))
    (hv : TendstoLocallyUniformlyOn (fun i z ↦ w i (z + (s i, 0))) v l
      ((univ : Set ℝ) ×ˢ Icc 0 1)) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1) :
    v (0, t₂) - v (0, t₁) - ∫ t in t₁..t₂, Φ (t, v (0, t)) = 0 := by
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add hU hw hW
    hd hv
  obtain ⟨hUC, hFc, hvK⟩ := tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn isCompact_Icc
    (Eventually.of_forall fun i ↦ (hw i).continuousOn) (hW 0 1) hv
  -- The vector field along the translates converges uniformly on `[0, 1] × [0, 1]`, since the
  -- graphs of the translates converge uniformly to the compact graph of the limit.
  have hΦUC : TendstoUniformlyOn (fun i z ↦ Φ (z.2, w i (z + (s i, 0)))) (fun z ↦ Φ (z.2, v z))
      l (Icc 0 1 ×ˢ Icc 0 1) :=
    ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (continuousOn_id.prodMk hvK)).comp_tendstoUniformlyOn
      (g := fun p : (ℝ × ℝ) × F ↦ Φ (p.1.2, p.2)) (fun _ _ ↦
        (hΦ.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).continuousAt)
      hUC.graph
  set A := v (0, t₂) - v (0, t₁) - ∫ t in t₁..t₂, Φ (t, v (0, t))
  -- The defects of the `w i` along the segments `{r} × [t₁, t₂]` tend to zero in `L¹`, and
  -- they converge uniformly in `r ∈ [0, 1]` to the defect `A` of the limit.
  have hzero : ∫⁻ _ in Icc (0 : ℝ) 1, ‖A‖ₑ = 0 := by
    refine lintegral_eq_zero_of_eventually_le_add
      (f := fun i r ↦ ‖w i (r + s i, t₂) - w i (r + s i, t₁) -
        ∫ t in t₁..t₂, Φ (t, w i (r + s i, t))‖ₑ)
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdΦ
        (Eventually.of_forall fun _ ↦ zero_le) ?_) fun ε hε ↦ ?_
    · filter_upwards [hW 0 1] with i hi
      rw [zero_add] at hi
      refine le_of_eq_of_le ?_ (setLIntegral_enorm_sub_sub_integral_le hΦ hU (hw i) ht₁ ht ht₂ hi)
      -- Translate the segments `{r} × [t₁, t₂]` back to `r ∈ [0, 1]`.
      have hT := (measurePreserving_add_right volume (s i)).setLIntegral_comp_preimage_emb
        (measurableEmbedding_addRight _)
        (fun r ↦ ‖w i (r, t₂) - w i (r, t₁) - ∫ t in t₁..t₂, Φ (t, w i (r, t))‖ₑ)
        (Icc (s i) (1 + s i))
      rwa [preimage_add_const_Icc, sub_self, add_sub_cancel_right] at hT
    · exact eventually_ae_enorm_sub_sub_integral_le_add hΦ ht₁ ht ht₂ hUC hΦUC hFc hvK hstat ε hε
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hzero
  exact eNorm_eq_zero.1 hzero

/-- **Translates with vanishing defect on windows converge to a solution.** Under the hypotheses
of
`TauCeti.sub_sub_integral_eq_zero_of_tendstoLocallyUniformlyOn_comp_add`,
the path `x(t) = v(0, t)` solves `x'(t) = Φ(t, x(t))` on `[0, 1]`. -/
theorem hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add
    {Φ : ℝ × F → F} (hΦ : Continuous Φ) (hU : IsOpen U) (hw : ∀ i, ContDiffOn ℝ 1 (w i) U)
    (hW : ∀ a b : ℝ, ∀ᶠ i in l, Icc (a + s i) (b + s i) ×ˢ Icc 0 1 ⊆ U)
    (hd : ∀ a b : ℝ, Tendsto (fun i ↦ ∫⁻ z in Icc (a + s i) (b + s i) ×ˢ Icc 0 1,
      ‖fderiv ℝ (w i) z (1, 0)‖ₑ) l (𝓝 0))
    (hdΦ : Tendsto (fun i ↦ ∫⁻ z in Icc (s i) (1 + s i) ×ˢ Icc 0 1,
      ‖fderiv ℝ (w i) z (0, 1) - Φ (z.2, w i z)‖ₑ) l (𝓝 0))
    (hv : TendstoLocallyUniformlyOn (fun i z ↦ w i (z + (s i, 0))) v l
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t ↦ v (0, t)) (Φ (t, v (0, t))) (Icc 0 1) t := by
  obtain ⟨-, -, hvK⟩ := tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn isCompact_Icc
    (Eventually.of_forall fun i ↦ (hw i).continuousOn) (hW 0 1) hv
  have hx : ContinuousOn (fun t ↦ v (0, t)) (Icc 0 1) :=
    hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦
      ⟨left_mem_Icc.2 zero_le_one, ht⟩
  have hf : ContinuousOn (fun t ↦ Φ (t, v (0, t))) (Icc 0 1) :=
    hΦ.comp_continuousOn (continuousOn_id.prodMk hx)
  -- By the integral equation, `x(t) = v(0, t)` is a primitive of the vector field along it.
  intro t ht
  have : Fact (t ∈ Icc (0 : ℝ) 1) := ⟨ht⟩
  have hd' := intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (s := Icc 0 1)
    (t := Icc 0 1) (hf.mono (uIcc_subset_Icc (left_mem_Icc.2 zero_le_one) ht)).intervalIntegrable
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)
  refine (hd'.const_add (v (0, 0))).congr_of_mem (fun τ hτ ↦ ?_) ht
  have h := sub_sub_integral_eq_zero_of_tendstoLocallyUniformlyOn_comp_add
    hΦ hU hw hW hd hdΦ hv le_rfl hτ.1 hτ.2
  rw [← sub_eq_zero, ← h]
  abel

end TauCeti
