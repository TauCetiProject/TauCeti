/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ReducedAction
public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.WeakMinimizer

/-!
# Smoothness of weak reduced-action minimizers in a chart

A square-integrable coordinate velocity and its integral primitive describe a weak path.
If that path minimizes the actual square-time reduced action among endpoint-fixed weak
chart paths, it is smooth within the closed segment. The metric and scalar potential are
the native quantities at backward time `T - s²`; the interval may start at square time zero.

This is a regularity theorem for a supplied minimizer. It does not prove existence of a
minimizer, nor assume an Euler equation or a momentum identity.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open Bundle Set MeasureTheory
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- Actual reduced-action minimality of an H¹ chart path forces smoothness of that same path
within the closed square-time segment, including its one-sided endpoint jets. -/
theorem contMDiffOn_of_minimizing_regularizedReducedAction_in_chart
    {γ : ℝ → M} {a b T : ℝ} (x₀ : M)
    {J : Set ℝ} (hJ : IsOpen J) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (hg : IsSmoothMetricFamilyOn g J)
    (hR : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun z : ℝ × M ↦ (g z.1).scalarCurvature z.2)
      (J ×ˢ (extChartAt I x₀).source))
    (hsrc : MapsTo γ (Icc a b) (extChartAt I x₀).source)
    (w : ℝ → E) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hprimitive : ∀ s ∈ Icc a b, extChartAt I x₀ (γ s) =
      extChartAt I x₀ (γ a) + ∫ r in a..s, w r)
    (hmin : ∀ v z : ℝ → E, MemLp z 2 (volume.restrict (Icc a b)) →
      MapsTo v (Icc a b) (extChartAt I x₀).target →
      v a = extChartAt I x₀ (γ a) → v b = extChartAt I x₀ (γ b) →
      (∀ s ∈ Icc a b, v s = v a + ∫ r in a..s, z r) →
      regularizedReducedAction I g T γ a b ≤
        regularizedReducedAction I g T ((extChartAt I x₀).symm ∘ v) a b) :
    ContMDiffOn 𝓘(ℝ) I ∞ γ (Icc a b) := by
  let c := fun s : ℝ ↦ T - s ^ 2
  let K := c ⁻¹' J
  have hK : IsOpen K := hJ.preimage (continuous_const.sub (continuous_id.pow 2))
  have hgc : IsSmoothMetricFamilyOn (g ∘ c) K :=
    hg.comp_preimage (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn
  have htime' : Icc a b ⊆ K := fun s hs ↦ htime s hs
  let U := fun (s : ℝ) (x : M) ↦ 2 * s ^ 2 * (g (c s)).scalarCurvature x
  have hc : ContMDiffOn (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞
      (fun z : ℝ × M ↦ (c z.1, z.2)) (K ×ˢ (extChartAt I x₀).source) :=
    (contMDiff_const.sub (contMDiff_fst.pow 2)).prodMk contMDiff_snd |>.contMDiffOn
  have hUc : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun z : ℝ × M ↦ U z.1 z.2)
      (K ×ˢ (extChartAt I x₀).source) :=
    ((contMDiffOn_const.mul (contMDiffOn_fst.pow 2)).mul
      (hR.comp hc (fun z hz ↦ ⟨hz.1, hz.2⟩)))
  apply contMDiffOn_of_minimizing_movingMetricAction_in_chart
    (g := g ∘ c) x₀ U hK htime' hgc hUc hsrc w hw hprimitive
  intro v z hz hv hva hvb hprimv
  simpa only [regularizedReducedAction_eq_movingMetricAction, Function.comp_def, U, c] using
    hmin v z hz hv hva hvb hprimv

end TauCeti.Manifold
