/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Variations with a prescribed moving endpoint

Let `F : ℝ → ℝ → M` be a two-parameter family of curves, `σ : ℝ → M` a curve with
`σ 0 = F 0 a`, `ψ = extChartAt I x₀` an extended chart and `β : ℝ → ℝ` a profile. The **chart
endpoint correction** `TauCeti.Manifold.chartEndpointCorrection I F σ a x₀ β` is the family
equal to `F s t` where `β t = 0` and to `ψ⁻¹ (ψ (F s t) + β t • (ψ (σ s) - ψ (F s a)))`
elsewhere; the two agree where `F s t` lies in the chart. Its central curve is `F 0` when the
central curve lies in the chart on the support of `β`, and when `β a = 1` its curve at `s` starts
at `σ s` whenever `σ s` lies in the chart. On a manifold without
boundary it is as regular as `F`, `σ` and `β` along the central curve. If the velocity of `σ` at
`0` is the variation field of `F` at `a`, the correction has the same variation field as `F`.

Applied to the constant family at a curve `γ`, with a bump profile around `a`, this realizes
every curve `σ` through `γ a` as the moving left endpoint of a variation of `γ` with fixed right
endpoint. Only the regularity of `σ` at `0` is used, and no smooth extension of `σ` is needed.

## Main definitions and results

* `TauCeti.Manifold.chartEndpointCorrection`: the chart endpoint correction of a family.
* `TauCeti.Manifold.contMDiffAt_chartEndpointCorrection`: it is `C^n` along the central curve.
* `TauCeti.Manifold.variationField_chartEndpointCorrection`: it preserves the variation field
  when the velocity of `σ` at `0` is the variation field of `F` at `a`.
* `TauCeti.Manifold.exists_contMDiffAt_endpointVariation`: a `C^n` variation of a `C^n` curve
  whose left endpoint follows a prescribed `C^n` curve and whose right endpoint is fixed.
* `TauCeti.Manifold.exists_contMDiffAt_endpointCorrection`: a `C^n` family can be corrected to
  have a prescribed moving left endpoint, with the same central curve, the same right endpoints
  and the same variation field.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 6 (variations of curves and the first variation formula).
-/

public section

open Filter Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : ℝ → ℝ → M} {σ : ℝ → M} {a : ℝ} {x₀ : M} {β : ℝ → ℝ}

variable (I) in
/-- The correction of the family `F` which, in the extended chart `ψ` at `x₀`, moves `F s t` by
`β t` times the displacement `ψ (σ s) - ψ (F s a)` of the left endpoint `F s a` to `σ s`. It is
defined piecewise: where `β t = 0` it is `F s t`, and elsewhere it is
`ψ⁻¹ (ψ (F s t) + β t • (ψ (σ s) - ψ (F s a)))`. The two descriptions agree where `F s t` lies
in the chart (`chartEndpointCorrection_eq_chart`). -/
def chartEndpointCorrection (F : ℝ → ℝ → M) (σ : ℝ → M) (a : ℝ) (x₀ : M) (β : ℝ → ℝ)
    (s t : ℝ) : M :=
  if β t = 0 then F s t else (extChartAt I x₀).symm
    (extChartAt I x₀ (F s t) + β t • (extChartAt I x₀ (σ s) - extChartAt I x₀ (F s a)))

/-- Where the profile vanishes, the correction is the original family. -/
@[simp]
theorem chartEndpointCorrection_of_profile_eq_zero {t : ℝ} (ht : β t = 0) (s : ℝ) :
    chartEndpointCorrection I F σ a x₀ β s t = F s t := by
  rw [chartEndpointCorrection, ite_eq_left ht]

/-- Where the original family lies in the chart, the correction is given by the chart formula. -/
theorem chartEndpointCorrection_eq_chart {s t : ℝ} (ht : F s t ∈ (extChartAt I x₀).source) :
    chartEndpointCorrection I F σ a x₀ β s t = (extChartAt I x₀).symm
      (extChartAt I x₀ (F s t) + β t •
        (extChartAt I x₀ (σ s) - extChartAt I x₀ (F s a))) := by
  rw [chartEndpointCorrection]
  split_ifs with hβ
  · rw [hβ, zero_smul, add_zero, (extChartAt I x₀).left_inv ht]
  · rfl

/-- If `σ 0 = F 0 a` and the central curve `F 0` lies in the chart wherever the profile is
nonzero, the central curve of the correction is the central curve of the original family. -/
theorem chartEndpointCorrection_zero (hbase : F 0 a = σ 0)
    (hsource : ∀ t ∈ support β, F 0 t ∈ (extChartAt I x₀).source) :
    chartEndpointCorrection I F σ a x₀ β 0 = F 0 := by
  funext t
  by_cases ht : β t = 0
  · exact chartEndpointCorrection_of_profile_eq_zero ht 0
  · rw [chartEndpointCorrection_eq_chart (hsource t ht), hbase, sub_self, smul_zero, add_zero]
    exact (extChartAt I x₀).left_inv (hsource t ht)

/-- If the profile is one at `a` and `σ s` lies in the chart, the curve of the correction at `s`
starts at `σ s`. -/
theorem chartEndpointCorrection_endpoint {s : ℝ} (hβ : β a = 1)
    (hσ : σ s ∈ (extChartAt I x₀).source) :
    chartEndpointCorrection I F σ a x₀ β s a = σ s := by
  rw [chartEndpointCorrection, ite_eq_right (by rw [hβ]; exact one_ne_zero), hβ, one_smul,
    add_sub_cancel, (extChartAt I x₀).left_inv hσ]

variable [I.Boundaryless]

/-- On a `C^n` manifold without boundary, the correction of a family which is `C^n` at `(0, a)`
and `(0, t)`, by a `C^n` curve `σ` and a `C^n` profile supported where the central curve stays in
the chart, is `C^n` at `(0, t)`. -/
theorem contMDiffAt_chartEndpointCorrection {n : ℕ∞ω} [IsManifold I n M]
    (hsource : ∀ t ∈ tsupport β, F 0 t ∈ (extChartAt I x₀).source) (hβ : ContDiff ℝ n β)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : F 0 a = σ 0)
    (ha : F 0 a ∈ (extChartAt I x₀).source)
    (hFa : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, a))
    {t : ℝ} (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ chartEndpointCorrection I F σ a x₀ β z.1 z.2) (0, t) := by
  by_cases htβ : t ∈ tsupport β
  · have hcF : ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ extChartAt I x₀ (F z.1 z.2)) (0, t) :=
      contMDiffAt_iff_contDiffAt.mp
        ((contMDiffAt_extChartAt' (by simpa using hsource t htβ)).comp (0, t) hF)
    have hcσ : ContDiffAt ℝ n (extChartAt I x₀ ∘ σ) 0 :=
      contMDiffAt_iff_contDiffAt.mp
        ((contMDiffAt_extChartAt' (by simpa [← hbase] using ha)).comp 0 hσ)
    have hcFa : ContDiffAt ℝ n (fun s ↦ extChartAt I x₀ (F s a)) 0 :=
      contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' (by simpa using ha)).comp 0
        (hFa.comp 0 (contDiff_prodMk_left a).contMDiff.contMDiffAt))
    have hg : ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ extChartAt I x₀ (F z.1 z.2) +
        β z.2 • (extChartAt I x₀ (σ z.1) - extChartAt I x₀ (F z.1 a))) (0, t) :=
      hcF.add ((hβ.contDiffAt.comp (0, t) contDiffAt_snd).smul
        ((hcσ.comp (0, t) contDiffAt_fst).sub (hcFa.comp (0, t) contDiffAt_fst)))
    have hmem : extChartAt I x₀ (F 0 t) +
        β t • (extChartAt I x₀ (σ 0) - extChartAt I x₀ (F 0 a)) ∈ (extChartAt I x₀).target := by
      simpa only [hbase, sub_self, smul_zero, add_zero] using
        (extChartAt I x₀).map_source (hsource t htβ)
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm
        (extChartAt I x₀ (F 0 t) + β t • (extChartAt I x₀ (σ 0) - extChartAt I x₀ (F 0 a))) :=
      (contMDiffOn_extChartAt_symm x₀ _ hmem).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds hmem)
    refine (hsymm.comp (0, t) (contMDiffAt_iff_contDiffAt.mpr hg)).congr_of_eventuallyEq ?_
    filter_upwards [hF.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source x₀).mem_nhds (hsource t htβ))] with z hz
    exact chartEndpointCorrection_eq_chart hz
  · have hev : β =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp htβ
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds hev] with z hz
    exact chartEndpointCorrection_of_profile_eq_zero hz z.1

/-- If the velocity of `σ` at `0` is the variation field of `F` at `a`, then at every parameter
where the central curve lies in the chart, the correction has the same variation field as `F`. -/
theorem variationField_chartEndpointCorrection [IsManifold I 1 M] {t : ℝ}
    (hF : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ F s t) 0)
    (hFa : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ F s a) 0)
    (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I σ 0) (ht : F 0 t ∈ (extChartAt I x₀).source)
    (ha : F 0 a ∈ (extChartAt I x₀).source) (hbase : F 0 a = σ 0)
    (hvel : curveVelocity I σ 0 = variationField I F a) :
    variationField I (chartEndpointCorrection I F σ a x₀ β) t = variationField I F t := by
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (F 0 a) :=
    (contMDiffAt_extChartAt' (n := 1) (by simpa using ha)).mdifferentiableAt one_ne_zero
  have hσv := hasDerivAt_comp_curve (γ := σ) (t := 0) (hbase ▸ hchart)
    (hasMFDerivAt_curveVelocity hσ)
  have hFv := hasDerivAt_comp_curve (γ := fun s ↦ F s a) (t := 0) hchart
    (hasMFDerivAt_curveVelocity hFa)
  have hcoeff : (mvfderiv I (extChartAt I x₀) (σ 0) (curveVelocity I σ 0) : E) =
      mvfderiv I (extChartAt I x₀) (F 0 a) (curveVelocity I (fun s ↦ F s a) 0) := by
    rw [hvel, variationField_apply, hbase]
  have hδ : HasDerivAt (fun s ↦ extChartAt I x₀ (σ s) - extChartAt I x₀ (F s a)) 0 0 := by
    simpa only [comp_def, hcoeff, sub_self] using hσv.fun_sub hFv
  let c : ℝ → E := fun s ↦ extChartAt I x₀ (F s t)
  let d : ℝ → E := fun s ↦ c s + β t • (extChartAt I x₀ (σ s) - extChartAt I x₀ (F s a))
  have hc := hasDerivAt_comp_curve
    ((contMDiffAt_extChartAt' (n := 1) (by simpa using ht)).mdifferentiableAt one_ne_zero)
    (hasMFDerivAt_curveVelocity hF)
  have hd : HasDerivAt d (mvfderiv I (extChartAt I x₀) (F 0 t)
      (curveVelocity I (fun s ↦ F s t) 0)) 0 := by
    simpa only [d, c, comp_def, Pi.smul_apply, smul_zero, add_zero] using
      hc.fun_add (hδ.const_smul (β t))
  have hd0 : d 0 = c 0 := by simp [d, hbase]
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (c 0) :=
    ((contMDiffOn_extChartAt_symm x₀ _ ((extChartAt I x₀).map_source ht)).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds
        ((extChartAt I x₀).map_source ht))).mdifferentiableAt one_ne_zero
  have hdc : curveVelocity I ((extChartAt I x₀).symm ∘ d) 0 =
      curveVelocity I ((extChartAt I x₀).symm ∘ c) 0 := by
    have hmap : (fun z : E ↦ (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (d 0) z : E)) =
        fun z : E ↦ (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (c 0) z : E) := by
      rw [hd0]
    exact ((hd0 ▸ hsymm).curveVelocity_comp_mfderiv hd).trans
      ((congrFun hmap _).trans (hsymm.curveVelocity_comp_mfderiv hc).symm)
  have hsource : ∀ᶠ s in 𝓝 0, F s t ∈ (extChartAt I x₀).source :=
    hF.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source x₀).mem_nhds ht)
  have hleft : (fun s ↦ chartEndpointCorrection I F σ a x₀ β s t) =ᶠ[𝓝 0]
      (extChartAt I x₀).symm ∘ d := by
    filter_upwards [hsource] with s hs
    exact chartEndpointCorrection_eq_chart hs
  have hright : (extChartAt I x₀).symm ∘ c =ᶠ[𝓝 0] fun s ↦ F s t := by
    filter_upwards [hsource] with s hs
    exact (extChartAt I x₀).left_inv hs
  rw [variationField_apply, variationField_apply]
  exact hleft.curveVelocity_eq.trans (hdc.trans hright.curveVelocity_eq)

/-- **Variations with a prescribed moving endpoint.** On a `C^n` manifold without boundary, let
`γ` be `C^n` on `[a, b]` with `a < b`, and let `σ` be a curve which is `C^n` at `0` with
`σ 0 = γ a`. Then there is a `C^n` variation of `γ` whose curves start at `σ s` for `s` near
`0` and all end at `γ b`. -/
theorem exists_contMDiffAt_endpointVariation {n : ℕ∞} [IsManifold I n M] {γ : ℝ → M} {b : ℝ}
    (hab : a < b) (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : γ a = σ 0) :
    ∃ F : ℝ → ℝ → M, F 0 = γ ∧
      (∀ t ∈ uIcc a b,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, F s a = σ s) ∧ ∀ s, F s b = γ b := by
  obtain ⟨φ, hφs, -, hφ, -, hφa⟩ := exists_contDiff_tsupport_subset (n := n) (x := a)
    (s := γ ⁻¹' (extChartAt I (γ a)).source ∩ Iio b) (inter_mem
      ((hγ a left_mem_uIcc).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (γ a)).mem_nhds (mem_extChartAt_source (γ a))))
      (isOpen_Iio.mem_nhds hab))
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport fun hb ↦ lt_irrefl b (hφs hb).2
  have ha : γ a ∈ (extChartAt I (γ a)).source := mem_extChartAt_source (γ a)
  have hγ₂ (t : ℝ) (ht : t ∈ uIcc a b) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ γ z.2) (0, t) :=
    (hγ t ht).comp (0, t) contDiff_snd.contMDiff.contMDiffAt
  refine ⟨chartEndpointCorrection I (fun _ ↦ γ) σ a (γ a) φ,
    chartEndpointCorrection_zero hbase fun t ht ↦ (hφs (subset_tsupport φ ht)).1,
    fun t ht ↦ contMDiffAt_chartEndpointCorrection (fun t ht ↦ (hφs ht).1) hφ hσ hbase ha
      (hγ₂ a left_mem_uIcc) (hγ₂ t ht), ?_,
    fun s ↦ chartEndpointCorrection_of_profile_eq_zero hφb s⟩
  filter_upwards [hσ.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (γ a)).mem_nhds (by rwa [← hbase]))] with s hs
  exact chartEndpointCorrection_endpoint hφa hs

/-- **Correcting the moving endpoint of a variation.** On a `C^n` manifold without boundary, with
`1 ≤ n`, let `F` be a family which is `C^n` along its central curve on `[a, b]`, with `a < b`,
and let `σ` be a curve which is `C^n` at `0`, with `σ 0 = F 0 a` and with velocity at `0` the
variation field of `F` at `a`. Then there is a `C^n` family with the same central curve, whose
curves start at `σ s` for `s` near `0` and end at `F s b`, and with the same variation field
as `F` on `[a, b]`. -/
theorem exists_contMDiffAt_endpointCorrection {n : ℕ∞} [IsManifold I n M] (hn : 1 ≤ n) {b : ℝ}
    (hab : a < b)
    (hF : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : F 0 a = σ 0)
    (hvel : curveVelocity I σ 0 = variationField I F a) :
    ∃ G : ℝ → ℝ → M, G 0 = F 0 ∧
      (∀ t ∈ uIcc a b,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, G s a = σ s) ∧ (∀ s, G s b = F s b) ∧
      ∀ t ∈ uIcc a b, variationField I G t = variationField I F t := by
  have hn₁ : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  have : IsManifold I 1 M := .of_le hn₁
  have hn₀ : (n : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hn₁).ne'
  have hslice (t : ℝ) (ht : t ∈ uIcc a b) : ContMDiffAt 𝓘(ℝ, ℝ) I n (fun s ↦ F s t) 0 :=
    (hF t ht).comp 0 (contDiff_prodMk_left t).contMDiff.contMDiffAt
  have hFa := hF a left_mem_uIcc
  obtain ⟨φ, hφs, -, hφ, -, hφa⟩ := exists_contDiff_tsupport_subset (n := n) (x := a)
    (s := F 0 ⁻¹' (extChartAt I (F 0 a)).source ∩ Iio b) (inter_mem
      ((hFa.comp a (contDiff_prodMk_right 0).contMDiff.contMDiffAt).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (F 0 a)).mem_nhds (mem_extChartAt_source (F 0 a))))
      (isOpen_Iio.mem_nhds hab))
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport fun hb ↦ lt_irrefl b (hφs hb).2
  have ha : F 0 a ∈ (extChartAt I (F 0 a)).source := mem_extChartAt_source (F 0 a)
  refine ⟨chartEndpointCorrection I F σ a (F 0 a) φ,
    chartEndpointCorrection_zero hbase fun t ht ↦ (hφs (subset_tsupport φ ht)).1,
    fun t ht ↦ contMDiffAt_chartEndpointCorrection (fun t ht ↦ (hφs ht).1) hφ hσ hbase ha hFa
      (hF t ht),
    ?_, fun s ↦ chartEndpointCorrection_of_profile_eq_zero hφb s, fun t ht ↦ ?_⟩
  · filter_upwards [hσ.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (F 0 a)).mem_nhds (by rwa [← hbase]))] with s hs
    exact chartEndpointCorrection_endpoint hφa hs
  · by_cases htφ : t ∈ tsupport φ
    · exact variationField_chartEndpointCorrection ((hslice t ht).mdifferentiableAt hn₀)
        ((hslice a left_mem_uIcc).mdifferentiableAt hn₀) (hσ.mdifferentiableAt hn₀)
        (hφs htφ).1 ha hbase hvel
    · have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport htφ
      rw [variationField_apply, variationField_apply]
      exact EventuallyEq.curveVelocity_eq
        (Eventually.of_forall fun s ↦ chartEndpointCorrection_of_profile_eq_zero hφt s)

end TauCeti.Manifold
