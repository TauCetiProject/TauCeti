/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.MovingMetric
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Family.Coordinates
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Coordinates
public import TauCeti.Analysis.Calculus.Variational.QuadraticAction.Minimizer
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Weak action minimizers in a Riemannian chart

The quadratic coordinate action equals the native moving-metric action for integral paths
with interval-integrable velocity. A weak minimizer among inverse-chart H¹ competitors with
fixed endpoints is smooth within the closed interval.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open Bundle Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

namespace Manifold

variable [I.Boundaryless] [CompleteSpace E]

/-- The weak quadratic coordinate integral of an integral path with interval-integrable coordinate
velocity equals its native moving-metric
action. The specified velocity agrees with the classical coordinate derivative almost
everywhere, as proved from the integral primitive. -/
theorem quadraticAction_chartMetric_eq_movingMetricAction
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (x₀ : M) (U : ℝ → M → ℝ)
    (hsrc : MapsTo γ (Icc a b) (extChartAt I x₀).source)
    (w : ℝ → E) (hw : IntervalIntegrable w volume a b)
    (hprimitive : ∀ s ∈ Icc a b, extChartAt I x₀ (γ s) =
      extChartAt I x₀ (γ a) + ∫ r in a..s, w r) :
    quadraticAction
      (fun z : ℝ × E ↦ (g z.1).toNondegenerateMetric.chartMetric x₀ z.2)
      (fun z : ℝ × E ↦ U z.1 ((extChartAt I x₀).symm z.2))
      (extChartAt I x₀ ∘ γ) w a b =
      movingMetricAction I (fun t ↦ (g t).ofLE (by norm_num)) U γ a b := by
  let e := extChartAt I x₀
  let u := e ∘ γ
  have hdu := intervalIntegral.ae_hasDerivAt_of_forall_eq_add_integral hab u hw hprimitive
  have hmem : ∀ᵐ s ∂volume.restrict (Icc a b), s ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  rw [quadraticAction_def, movingMetricAction_def]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hdu,
    ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hmem] with s hs hsI
  have hs' : γ s ∈ e.source := hsrc (Ioo_subset_Icc_self hsI)
  have htarget : u s ∈ e.target := e.map_source hs'
  have heq : γ =ᶠ[𝓝 s] e.symm ∘ u := by
    filter_upwards [Ioo_mem_nhds hsI.1 hsI.2] with r hr
    exact (e.left_inv (hsrc (Ioo_subset_Icc_self hr))).symm
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I e.symm (u s) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) x₀ _ htarget).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds htarget)).mdifferentiableAt (by simp)
  have hvel := hmd.curveVelocity_comp_mfderiv hs
  rw [← heq.curveVelocity_eq] at hvel
  have hbase : γ s ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    exact TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hs'
  have hcoord : curveVelocity I γ s =
      (trivializationAt E (TangentSpace I) x₀).symm (γ s) (w s) := by
    rw [← Trivialization.symmL_apply (R := ℝ) _ hbase, TangentBundle.symmL_trivializationAt
      (by simpa only [e, extChartAt_source] using hs'), I.range_eq_univ, mfderivWithin_univ]
    exact hvel
  simp only [Function.comp_def]
  rw [ContMDiffNondegenerateMetric.chartMetric_extChartAt_apply (g s).toNondegenerateMetric
      hs', ContMDiffRiemannianMetric.toNondegenerateMetric_apply,
    e.left_inv hs', ContMDiffRiemannianMetric.ofLE_inner, hcoord]

end Manifold

end TauCeti

namespace TauCeti.Manifold

open Bundle Set Filter MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- Native action minimality transports to the quadratic integral for exactly the same
weak chart competitors. -/
private theorem isQuadraticActionMinimizerOn_chartMetric
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (x₀ : M) (U : ℝ → M → ℝ)
    (hsrc : MapsTo γ (Icc a b) (extChartAt I x₀).source)
    (w : ℝ → E) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hprimitive : ∀ s ∈ Icc a b, extChartAt I x₀ (γ s) =
      extChartAt I x₀ (γ a) + ∫ r in a..s, w r)
    (hmin : ∀ v z : ℝ → E, MemLp z 2 (volume.restrict (Icc a b)) →
      MapsTo v (Icc a b) (extChartAt I x₀).target →
      v a = extChartAt I x₀ (γ a) → v b = extChartAt I x₀ (γ b) →
      (∀ s ∈ Icc a b, v s = v a + ∫ r in a..s, z r) →
      movingMetricAction I (fun t ↦ (g t).ofLE (by norm_num)) U γ a b ≤
        movingMetricAction I (fun t ↦ (g t).ofLE (by norm_num)) U
          ((extChartAt I x₀).symm ∘ v) a b) :
    IsQuadraticActionMinimizerOn
      (fun z : ℝ × E ↦ (g z.1).toNondegenerateMetric.chartMetric x₀ z.2)
      (fun z : ℝ × E ↦ U z.1 ((extChartAt I x₀).symm z.2))
      (extChartAt I x₀).target (extChartAt I x₀ ∘ γ) w a b := by
  let e := extChartAt I x₀
  let G := fun z : ℝ × E ↦ (g z.1).toNondegenerateMetric.chartMetric x₀ z.2
  let V := fun z : ℝ × E ↦ U z.1 (e.symm z.2)
  apply (isQuadraticActionMinimizerOn_iff _ _ _ _ _ _ _).mpr
  refine ⟨hab, (fun s hs ↦ e.map_source (hsrc hs)), hw, hprimitive, ?_⟩
  intro v z hz hvtarget hva hvb hprimv
  have hξsrc : MapsTo (e.symm ∘ v) (Icc a b) e.source :=
    fun s hs ↦ e.map_target (hvtarget hs)
  have hprimξ : ∀ s ∈ Icc a b, e ((e.symm ∘ v) s) =
      e ((e.symm ∘ v) a) + ∫ r in a..s, z r := by
    intro s hs
    simp only [Function.comp_def, e.right_inv (hvtarget hs),
      e.right_inv (hvtarget (left_mem_Icc.mpr hab))]
    exact hprimv s hs
  have hcentral := quadraticAction_chartMetric_eq_movingMetricAction (g := g)
    hab x₀ U hsrc w
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hw.integrable (by norm_num)))
      hprimitive
  have hcompetitor := quadraticAction_chartMetric_eq_movingMetricAction (g := g)
    hab x₀ U hξsrc z
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hz.integrable (by norm_num)))
      hprimξ
  have hcoords : EqOn (e ∘ (e.symm ∘ v)) v (Icc a b) :=
    fun s hs ↦ e.right_inv (hvtarget hs)
  have haction : quadraticAction G V v z a b =
      quadraticAction G V (e ∘ (e.symm ∘ v)) z a b := by
    exact quadraticAction_congr fun s hs ↦
      (hcoords (by rwa [uIcc_of_le hab] at hs)).symm
  rw [hcentral, haction, hcompetitor]
  exact hmin v z hz hvtarget hva hvb hprimv

/-- A weak chart path minimizing the actual native moving-metric action is smooth on the
closed segment. Its competitors are actual inverse-chart paths with square-integrable
velocities; no Euler or momentum identity is assumed. -/
theorem contMDiffOn_of_minimizing_movingMetricAction_in_chart
    {γ : ℝ → M} {a b : ℝ} (x₀ : M) (U : ℝ → M → ℝ)
    {J : Set ℝ} (hJ : IsOpen J) (htime : Icc a b ⊆ J)
    (hg : IsSmoothMetricFamilyOn g J)
    (hU : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun z : ℝ × M ↦ U z.1 z.2)
      (J ×ˢ (extChartAt I x₀).source))
    (hsrc : MapsTo γ (Icc a b) (extChartAt I x₀).source)
    (w : ℝ → E) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hprimitive : ∀ s ∈ Icc a b, extChartAt I x₀ (γ s) =
      extChartAt I x₀ (γ a) + ∫ r in a..s, w r)
    (hmin : ∀ v z : ℝ → E, MemLp z 2 (volume.restrict (Icc a b)) →
      MapsTo v (Icc a b) (extChartAt I x₀).target →
      v a = extChartAt I x₀ (γ a) → v b = extChartAt I x₀ (γ b) →
      (∀ s ∈ Icc a b, v s = v a + ∫ r in a..s, z r) →
      movingMetricAction I (fun t ↦ (g t).ofLE (by norm_num)) U γ a b ≤
        movingMetricAction I (fun t ↦ (g t).ofLE (by norm_num)) U
          ((extChartAt I x₀).symm ∘ v) a b) :
    ContMDiffOn 𝓘(ℝ) I ∞ γ (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    exact contMDiffOn_empty
  let e := extChartAt I x₀
  let G := fun z : ℝ × E ↦ (g z.1).toNondegenerateMetric.chartMetric x₀ z.2
  let V := fun z : ℝ × E ↦ U z.1 (e.symm z.2)
  let u := e ∘ γ
  have htarget : MapsTo u (Icc a b) e.target := fun s hs ↦ e.map_source (hsrc hs)
  have hpoint : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
      (fun z : ℝ × E ↦ e.symm z.2) (J ×ˢ e.target) :=
    (contMDiffOn_extChartAt_symm x₀).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz ↦ hz.2)
  have hV : ContDiffOn ℝ ∞ V (J ×ˢ e.target) :=
    (hU.comp (contDiff_fst.contMDiff.contMDiffOn.prodMk hpoint)
      (fun z hz ↦ ⟨hz.1, e.map_target hz.2⟩)).contDiffOn
  have hsym : ∀ z ∈ J ×ˢ e.target, ∀ v v' : E, G z v v' = G z v' v := by
    intro z hz v v'
    exact (g z.1).toNondegenerateMetric.isSymm_chartMetric hz.2 |>.eq v v'
  have hpos : ∀ z ∈ J ×ˢ e.target, ∀ v : E, v ≠ 0 → 0 < G z v v :=
    fun z hz v hv ↦ (g z.1).chartMetric_pos hz.2 hv
  have hmin' : IsQuadraticActionMinimizerOn G V e.target u w a b :=
    isQuadraticActionMinimizerOn_chartMetric hab x₀ U hsrc w hw hprimitive hmin
  have hregular := hmin'.contDiffOn hJ (isOpen_extChartAt_target x₀) htime
    (hg.contDiffOn_chartMetric x₀) hV hsym hpos
  exact ((contMDiffOn_extChartAt_symm x₀).comp hregular.contMDiffOn htarget).congr
    (fun s hs ↦ (e.left_inv (hsrc hs)).symm)

end TauCeti.Manifold
