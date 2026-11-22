/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Analysis.Convex.Cone.EndpointVariation
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Variations with a prescribed moving endpoint

Let `F : ℝ → ℝ → M` be a two-parameter family of curves, `σ : ℝ → M` a curve with
`σ 0 = F 0 a`, `ψ = extChartAt I x₀` an extended chart and `β : ℝ → ℝ` a profile. The **chart
endpoint correction** `TauCeti.Manifold.chartEndpointCorrection I F σ a x₀ β` is the family
equal to `F s t` where `β t = 0` and to `ψ⁻¹ (ψ (F s t) + β t • (ψ (σ s) - ψ (F s a)))`
elsewhere; the two agree where `F s t` lies in the chart. Its central curve is `F 0` when the
central curve lies in the chart on the support of `β`, and when `β a = 1` its curve at `s` passes
through `σ s` at `a` whenever `σ s` lies in the chart. On a manifold without boundary it is as
regular as `F`, `σ` and `β` along the central curve. If the velocity of `σ` at
`0` is the variation field of `F` at `a`, the correction has the same variation field as `F`.

Applied to the constant family at a curve `γ`, with a bump profile around `a` vanishing at
`b ≠ a`, this realizes every curve `σ` through `γ a` as the moving endpoint at `a` of a variation
of `γ` with fixed endpoint at `b`. Since only `a ≠ b` is assumed, `a` may be either endpoint of
the segment `uIcc a b`. To prescribe both endpoints of an existing family, apply
`exists_contMDiffAt_endpointCorrection` successively at `a` and `b`; velocity matching is needed
only to preserve its variation field. Only the regularity of `σ` at `0` is used, and no smooth
extension of `σ` is needed.

The curves of these variations may leave a prescribed domain `D ⊆ M`. When a partial
diffeomorphism `e` onto an open subset of a real normed space identifies `D` with a set stable
under translation by a convex cone, for instance a translated convex cone or a half-space near a
corner or a smooth boundary point of `D`, the endpoint variations of
`TauCeti.exists_contDiffAt_endpointVariation_of_add_mem` read through `e` give variations of a
curve `γ` in `D ∩ e.source` with prescribed moving endpoint `σ` at `a` and fixed endpoint at
`b ≠ a`. Given a filter `l ≤ 𝓝 0`, such as `𝓝[≥] 0`, along which the displacement
`e (σ s) - e (σ 0)` of
the endpoint lies in the cone, the curves of the variation lie in `D` for all `s` eventually
along `l`. These are the competitors of a curve constrained to `D`.

## Main definitions and results

* `TauCeti.Manifold.chartEndpointCorrection`: the chart endpoint correction of a family.
* `TauCeti.Manifold.contMDiffAt_chartEndpointCorrection`: it is `C^n` along the central curve.
* `TauCeti.Manifold.variationField_chartEndpointCorrection`: it preserves the variation field
  when the velocity of `σ` at `0` is the variation field of `F` at `a`.
* `TauCeti.Manifold.exists_contMDiffAt_endpointVariation`: a `C^n` variation of a `C^n` curve
  whose endpoint at `a` follows a prescribed `C^n` curve and whose endpoint at `b ≠ a` is fixed.
* `TauCeti.Manifold.exists_contMDiffAt_endpointCorrection`: a `C^n` family can be corrected to
  have a prescribed moving endpoint at `a`, with the same central curve, the same endpoints at
  `b ≠ a`, preserving the variation field when `1 ≤ n` and endpoint velocities match.
* `TauCeti.Manifold.exists_contMDiffAt_endpointVariation_of_add_mem`: variations with a
  prescribed moving endpoint at `a` and fixed endpoint at `b ≠ a` inside a domain that reads, in a
  partial diffeomorphism, as a set stable under translation by a convex cone.
* `TauCeti.Manifold.exists_contMDiffAt_coneEndpointVariation`: the case of a domain that reads as
  a translated convex cone.

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
`β t` times the displacement `ψ (σ s) - ψ (F s a)` of the value `F s a` at `a` to `σ s`. It is
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
passes through `σ s` at `a`. -/
theorem chartEndpointCorrection_endpoint {s : ℝ} (hβ : β a = 1)
    (hσ : σ s ∈ (extChartAt I x₀).source) :
    chartEndpointCorrection I F σ a x₀ β s a = σ s := by
  rw [chartEndpointCorrection, ite_eq_right (by rw [hβ]; exact one_ne_zero), hβ, one_smul,
    add_sub_cancel, (extChartAt I x₀).left_inv hσ]

variable [I.Boundaryless]

/-- On a `C^n` manifold without boundary, the correction is `C^n` at `(0, t)` if the family is
`C^n` there, its slice at `a` and `σ` are `C^n` at `0`, and the profile is `C^n` at `t`. When
`t` lies in the topological support of the profile, the central curve must lie in the chart at `t`.
-/
theorem contMDiffAt_chartEndpointCorrection {n : ℕ∞ω} [IsManifold I n M]
    {t : ℝ} (hsource : t ∈ tsupport β → F 0 t ∈ (extChartAt I x₀).source)
    (hβ : ContDiffAt ℝ n β t)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : F 0 a = σ 0)
    (ha : F 0 a ∈ (extChartAt I x₀).source)
    (hFa : ContMDiffAt 𝓘(ℝ, ℝ) I n (fun s ↦ F s a) 0)
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ chartEndpointCorrection I F σ a x₀ β z.1 z.2) (0, t) := by
  by_cases htβ : t ∈ tsupport β
  · have hcF : ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ extChartAt I x₀ (F z.1 z.2)) (0, t) :=
      contMDiffAt_iff_contDiffAt.mp
        ((contMDiffAt_extChartAt' (by simpa using hsource htβ)).comp (0, t) hF)
    have hcσ : ContDiffAt ℝ n (extChartAt I x₀ ∘ σ) 0 :=
      contMDiffAt_iff_contDiffAt.mp
        ((contMDiffAt_extChartAt' (by simpa [← hbase] using ha)).comp 0 hσ)
    have hcFa : ContDiffAt ℝ n (fun s ↦ extChartAt I x₀ (F s a)) 0 :=
      contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' (by simpa using ha)).comp 0
        hFa)
    have hg : ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ extChartAt I x₀ (F z.1 z.2) +
        β z.2 • (extChartAt I x₀ (σ z.1) - extChartAt I x₀ (F z.1 a))) (0, t) :=
      hcF.add ((hβ.comp (0, t) contDiffAt_snd).smul
        ((hcσ.comp (0, t) contDiffAt_fst).sub (hcFa.comp (0, t) contDiffAt_fst)))
    have hmem : extChartAt I x₀ (F 0 t) +
        β t • (extChartAt I x₀ (σ 0) - extChartAt I x₀ (F 0 a)) ∈ (extChartAt I x₀).target := by
      simpa only [hbase, sub_self, smul_zero, add_zero] using
        (extChartAt I x₀).map_source (hsource htβ)
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm
        (extChartAt I x₀ (F 0 t) + β t • (extChartAt I x₀ (σ 0) - extChartAt I x₀ (F 0 a))) :=
      (contMDiffOn_extChartAt_symm x₀ _ hmem).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds hmem)
    refine (hsymm.comp (0, t) (contMDiffAt_iff_contDiffAt.mpr hg)).congr_of_eventuallyEq ?_
    filter_upwards [hF.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source x₀).mem_nhds (hsource htβ))] with z hz
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

/-- **Correcting the moving endpoint of a variation.** On a `C^n` manifold without boundary,
let `F 0` be continuous at `a`, let the slice `s ↦ F s a` and `σ` be `C^n` at `0`, and assume
`σ 0 = F 0 a` and `a ≠ b`. There is a family with the same central curve, whose curves pass
through `σ s` at `a` for `s` near `0` and through `F s b` at `b`. It preserves joint `C^n`
regularity at each `(0, t)`. If `1 ≤ n` and the endpoint velocities match, it also preserves
the variation field at every parameter where the original transverse curve is differentiable. -/
theorem exists_contMDiffAt_endpointCorrection {n : ℕ∞} [IsManifold I n M] {b : ℝ}
    (hab : a ≠ b) (hF₀ : ContinuousAt (F 0) a)
    (hFa : ContMDiffAt 𝓘(ℝ, ℝ) I n (fun s ↦ F s a) 0)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : F 0 a = σ 0) :
    ∃ G : ℝ → ℝ → M, G 0 = F 0 ∧
      (∀ t, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) →
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, G s a = σ s) ∧ (∀ s, G s b = F s b) ∧
      (1 ≤ n → curveVelocity I σ 0 = variationField I F a →
        ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ F s t) 0 →
          variationField I G t = variationField I F t) := by
  obtain ⟨φ, hφs, -, hφ, -, hφa⟩ := exists_contDiff_tsupport_subset (n := n) (x := a)
    (s := F 0 ⁻¹' (extChartAt I (F 0 a)).source ∩ {b}ᶜ) (inter_mem
      (hF₀.preimage_mem_nhds
        ((isOpen_extChartAt_source (F 0 a)).mem_nhds (mem_extChartAt_source (F 0 a))))
      (isOpen_compl_singleton.mem_nhds hab))
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport fun hb ↦ (hφs hb).2 rfl
  have ha : F 0 a ∈ (extChartAt I (F 0 a)).source := mem_extChartAt_source (F 0 a)
  refine ⟨chartEndpointCorrection I F σ a (F 0 a) φ,
    chartEndpointCorrection_zero hbase fun t ht ↦ (hφs (subset_tsupport φ ht)).1,
    fun t ht ↦ contMDiffAt_chartEndpointCorrection (fun ht ↦ (hφs ht).1) hφ.contDiffAt hσ
      hbase ha hFa ht,
    ?_, fun s ↦ chartEndpointCorrection_of_profile_eq_zero hφb s, fun hn hvel t ht ↦ ?_⟩
  · filter_upwards [hσ.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (F 0 a)).mem_nhds (by rwa [← hbase]))] with s hs
    exact chartEndpointCorrection_endpoint hφa hs
  · have hn₁ : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
    have : IsManifold I 1 M := .of_le hn₁
    have hn₀ : (n : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hn₁).ne'
    by_cases htφ : t ∈ tsupport φ
    · exact variationField_chartEndpointCorrection ht (hFa.mdifferentiableAt hn₀)
        (hσ.mdifferentiableAt hn₀) (hφs htφ).1 ha hbase hvel
    · have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport htφ
      rw [variationField_apply, variationField_apply]
      exact EventuallyEq.curveVelocity_eq
        (Eventually.of_forall fun s ↦ chartEndpointCorrection_of_profile_eq_zero hφt s)

/-- **Variations with a prescribed moving endpoint.** On a `C^n` manifold without boundary, let
`γ` be continuous at `a`, and let `σ` be `C^n` at `0` with `σ 0 = γ a`. For `a ≠ b` there is a
variation of `γ` whose curves pass through `σ s` at `a` for `s` near `0` and through `γ b` at
`b`. It is jointly `C^n` at `(0, t)` wherever `γ` is `C^n` at `t`. Either ordering of `a` and
`b` is allowed, so the moving endpoint may be the left or the right one. -/
theorem exists_contMDiffAt_endpointVariation {n : ℕ∞} [IsManifold I n M] {γ : ℝ → M} {b : ℝ}
    (hab : a ≠ b) (hγ : ContinuousAt γ a)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0) (hbase : γ a = σ 0) :
    ∃ F : ℝ → ℝ → M, F 0 = γ ∧
      (∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t →
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, F s a = σ s) ∧ ∀ s, F s b = γ b := by
  obtain ⟨F, hF₀, hF, hFa, hFb, -⟩ :=
    exists_contMDiffAt_endpointCorrection (F := fun _ ↦ γ) hab hγ contMDiffAt_const hσ hbase
  exact ⟨F, hF₀, fun t ht ↦ hF t (ht.comp (0, t) contDiff_snd.contMDiff.contMDiffAt), hFa, hFb⟩

section Domain

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ∞ω} {l : Filter ℝ}
  {γ : ℝ → M} {b : ℝ} {D : Set M} {C : ConvexCone ℝ V}

omit [I.Boundaryless] in
/-- **Variations with a moving endpoint inside a domain.** Let `e` be a `C^n` partial
diffeomorphism from `M` to a real normed space `V`, reading a set `D ⊆ M` on its target as a set
`S ⊆ V` stable under translation by a convex cone `C`. Let `γ` be `C^n` on `uIcc a b`, with `a ≠ b`
and values in `D ∩ e.source`, and let `σ` be `C^n` at `0` with `σ 0 = γ a`. If
`e (σ s) - e (σ 0) ∈ C` for `s` along a filter `l ≤ 𝓝 0`, there is a variation `G` of `γ`, `C^n`
along `{0} × uIcc a b`, whose curves pass through `σ s` at `a` for `s` near `0` and through `γ b`
at `b`, and map `uIcc a b` into `D` for `s` along `l`. -/
theorem exists_contMDiffAt_endpointVariation_of_add_mem (hl : l ≤ 𝓝 0) (hab : a ≠ b)
    (e : PartialDiffeomorph I 𝓘(ℝ, V) M V n) {S : Set V} (hS : ∀ x ∈ S, ∀ v ∈ C, x + v ∈ S)
    (hD : ∀ z ∈ e.target, e.symm z ∈ D ↔ z ∈ S)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t) (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0)
    (hγσ : γ a = σ 0) (hγD : MapsTo γ (uIcc a b) (D ∩ e.source))
    (hσC : ∀ᶠ s in l, e (σ s) - e (σ 0) ∈ C) :
    ∃ G : ℝ → ℝ → M, G 0 = γ ∧
      (∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, G s a = σ s) ∧ (∀ s, G s b = γ b) ∧
      ∀ᶠ s in l, MapsTo (G s) (uIcc a b) D := by
  have hσe : σ 0 ∈ e.source := hγσ ▸ (hγD left_mem_uIcc).2
  have hinv {x : M} (hx : x ∈ e.source) : e.symm (e x) = x := e.left_inv hx
  have hγS : MapsTo (fun t ↦ e (γ t)) (uIcc a b) (S ∩ e.target) := fun t ht ↦
    ⟨(hD _ (e.map_source (hγD ht).2)).1 (by rw [hinv (hγD ht).2]; exact (hγD ht).1),
      e.map_source (hγD ht).2⟩
  have hcomp {f : ℝ → M} {t : ℝ} (hf : ContMDiffAt 𝓘(ℝ, ℝ) I n f t) (hft : f t ∈ e.source) :
      ContDiffAt ℝ n (fun t ↦ e (f t)) t :=
    contMDiffAt_iff_contDiffAt.1
      ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hft)).comp t hf)
  obtain ⟨A, hA0, hA, hAa, hAb, hAS⟩ := exists_contDiffAt_endpointVariation_of_add_mem hl hab hS
    e.open_target (fun t ht ↦ hcomp (hγ t ht) (hγD ht).2) (hcomp hσ hσe) (congrArg e hγσ) hγS
    hσC
  have hG {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
      update (fun s t ↦ e.symm (A s t)) 0 γ s t = e.symm (A s t) := by
    rw [update_of_ne hs]
  refine ⟨update (fun s t ↦ e.symm (A s t)) 0 γ, update_self .., fun t ht ↦ ?_, ?_, fun s ↦ ?_, ?_⟩
  · have hnear : ∀ᶠ z : ℝ × ℝ in 𝓝 ((0 : ℝ), t), γ z.2 ∈ e.source :=
      ((hγ t ht).continuousAt.comp (x := ((0 : ℝ), t)) continuousAt_snd).eventually_mem
        (e.open_source.mem_nhds (hγD ht).2)
    have htarget : A 0 t ∈ e.target := by
      rw [hA0]
      exact e.map_source (hγD ht).2
    refine ContMDiffAt.congr_of_eventuallyEq (f := fun z : ℝ × ℝ ↦ e.symm (A z.1 z.2)) ?_
      (hnear.mono fun z hz ↦ ?_)
    · exact (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds htarget)).comp (0, t)
        (contMDiffAt_iff_contDiffAt.2 (hA t ht))
    · rcases eq_or_ne z.1 0 with hz0 | hz0
      · simp only [hz0, update_self, hA0, hinv hz]
      · exact hG hz0 z.2
  · filter_upwards [hσ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hσe)] with s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [update_self, hγσ]
    · rw [hG hs0, hAa, hinv hs]
  · rcases eq_or_ne s 0 with rfl | hs0
    · rw [update_self]
    · rw [hG hs0, hAb, hinv (hγD right_mem_uIcc).2]
  · filter_upwards [hAS] with s hs t ht
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [update_self]
      exact (hγD ht).1
    · rw [hG hs0]
      exact (hD _ (hs ht).2).2 (hs ht).1

omit [I.Boundaryless] in
/-- **Variations with a moving endpoint inside a cone.** Let `e` be a `C^n` partial
diffeomorphism from `M` to a real normed space `V`, reading a set `D ⊆ M` on its target as the
translated convex cone `{z | z - e (σ 0) ∈ C}`. Let `γ` be `C^n` on `uIcc a b`, with `a ≠ b` and
values in `D ∩ e.source`, and let `σ` be `C^n` at `0` with `σ 0 = γ a`. If `σ s ∈ D` for `s`
along a filter `l ≤ 𝓝 0`, there is a variation `G` of `γ`, `C^n` along `{0} × uIcc a b`, whose
curves pass through `σ s` at `a` for `s` near `0` and through `γ b` at `b`, and map `uIcc a b`
into `D` for `s` along `l`. -/
theorem exists_contMDiffAt_coneEndpointVariation (hl : l ≤ 𝓝 0) (hab : a ≠ b)
    (e : PartialDiffeomorph I 𝓘(ℝ, V) M V n) (hD : ∀ z ∈ e.target, e.symm z ∈ D ↔ z - e (σ 0) ∈ C)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t) (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I n σ 0)
    (hγσ : γ a = σ 0) (hγD : MapsTo γ (uIcc a b) (D ∩ e.source)) (hσD : ∀ᶠ s in l, σ s ∈ D) :
    ∃ G : ℝ → ℝ → M, G 0 = γ ∧
      (∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, G s a = σ s) ∧ (∀ s, G s b = γ b) ∧
      ∀ᶠ s in l, MapsTo (G s) (uIcc a b) D := by
  have hσe : σ 0 ∈ e.source := hγσ ▸ (hγD left_mem_uIcc).2
  have hinv {x : M} (hx : x ∈ e.source) : e.symm (e x) = x := e.left_inv hx
  refine exists_contMDiffAt_endpointVariation_of_add_mem (S := {z | z - e (σ 0) ∈ C}) hl hab e
    (fun x hx v hv ↦ by simpa only [mem_ofPred_eq, add_sub_right_comm] using C.add_mem hx hv) hD
    hγ hσ hγσ hγD ?_
  filter_upwards [hσD, hl (hσ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hσe))]
    with s hs hse
  exact (hD _ (e.map_source hse)).1 (by rwa [hinv hse])

end Domain

end TauCeti.Manifold
