/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Convex.Function.Topology
import TauCeti.Analysis.Convex.StrictTangent
import TauCeti.Analysis.Convex.SubgradientImage

/-!
# Supporting contacts under uniform perturbations

For a strictly convex reference `v`, a sufficiently close perturbation `w` gives interior
supporting contacts for `w - (1 - δ) v` at slopes `δ • Dv(z)` for every `z` in a compact
subset of the domain. The gradient image of the contact set consequently has Haar measure at
least `δ^n` times the measure of the reference gradient image on that compact subset.

The argument follows the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
-/

public section

open Set MeasureTheory
open scoped Gradient Pointwise Topology

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `w` is uniformly close to a strictly convex C¹ reference `v` on the compact closure
of an open set, then `w - (1 - δ) v` has an interior supporting point with derivative
`δ • Dv(z)` for each `z` in a fixed compact subset of the domain. -/
theorem exists_mem_fderiv_sub_eq_smul_fderiv_and_supporting {S K : Set E} {v : E → ℝ}
    (hSo : IsOpen S) (hcl : IsCompact (closure S))
    (hvs : StrictConvexOn ℝ S v)
    (hvc : ContinuousOn v (closure S)) (hvC1 : ContDiffOn ℝ 1 v S)
    (hK : IsCompact K) (hKS : K ⊆ S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ > 0, ∀ w : E → ℝ, ContinuousOn w (closure S) → DifferentiableOn ℝ w S →
      (∀ y ∈ closure S, |w y - v y| ≤ τ) → ∀ z ∈ K,
      ∃ x ∈ S,
        fderiv ℝ (fun y => w y - (1 - δ) * v y) x = δ • fderiv ℝ v z ∧
        ∀ y ∈ closure S, w x - (1 - δ) * v x + δ * fderiv ℝ v z (y - x) ≤ w y - (1 - δ) * v y := by
  have hv : ConvexOn ℝ (closure S) v := hvs.convexOn.closure_of_continuousOn hvc
  -- The tangent gap has a positive minimum over the compact pairs of points.
  let T := K ×ˢ frontier S
  let gap : E × E → ℝ := fun p => v p.2 - v p.1 - fderiv ℝ v p.1 (p.2 - p.1)
  have hT : IsCompact T :=
    hK.prod (hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  have hvD : DifferentiableOn ℝ v S := hvC1.differentiableOn (by norm_num)
  have hgrad : ContinuousOn (fderiv ℝ v) S := hvC1.continuousOn_fderiv_of_isOpen hSo le_rfl
  have hgap : ContinuousOn gap T := by
    have hf : ContinuousOn (fun p : E × E => v p.1) T :=
      hvc.comp continuous_fst.continuousOn fun _ hp => subset_closure (hKS hp.1)
    have hs : ContinuousOn (fun p : E × E => v p.2) T :=
      hvc.comp continuous_snd.continuousOn fun _ hp => frontier_subset_closure hp.2
    have hg : ContinuousOn (fun p : E × E => fderiv ℝ v p.1) T :=
      hgrad.comp continuous_fst.continuousOn fun _ hp => hKS hp.1
    exact (hs.sub hf).sub (hg.clm_apply (continuous_snd.sub continuous_fst).continuousOn)
  have hgap_pos : ∀ p ∈ T, 0 < gap p := by
    rintro ⟨z, y⟩ ⟨hz, hy⟩
    have hyS : y ∉ S := (hSo.frontier_eq ▸ hy).2
    have hzy : z ≠ y := fun h => hyS (h ▸ hKS hz)
    exact sub_pos.mpr (hvs.fderiv_lt_sub_of_mem_closure hSo hv (hKS hz)
      (frontier_subset_closure hy) hzy
      ((hvD z (hKS hz)).differentiableAt (hSo.mem_nhds (hKS hz))))
  obtain ⟨a, ha, hminGap⟩ := hT.exists_forall_le' hgap hgap_pos
  refine ⟨δ * a / 4, by positivity, ?_⟩
  intro w hwc hwD hclose z hz
  let p := fderiv ℝ v z
  let r : E → ℝ := fun y => w y - (1 - δ) * v y
  have hrc : ContinuousOn r (closure S) := hwc.sub (continuousOn_const.mul hvc)
  -- The affine function with slope δ • Dv(z) stays below the residual on the frontier.
  have hfront (y : E) (hy : y ∈ frontier S) : r z + (δ • p) (y - z) ≤ r y := by
    have h := mul_le_mul_of_nonneg_left (hminGap (z, y) ⟨hz, hy⟩) hδ.le
    simp only [gap] at h
    have hyerr := abs_le.mp (hclose y (frontier_subset_closure hy))
    have hzerr := abs_le.mp (hclose z (subset_closure (hKS hz)))
    simp only [r, smul_apply, smul_eq_mul, p]
    nlinarith [mul_pos hδ ha]
  obtain ⟨x, hx, hsupp⟩ := exists_forall_add_apply_le_of_forall_frontier hcl hrc (hKS hz) hfront
  -- At an interior supporting point the tilted function has zero derivative.
  have hloc : IsLocalMin (fun y => r y - (δ • p) y) x := by
    filter_upwards [hSo.mem_nhds hx] with y hy
    have h := hsupp y (subset_closure hy)
    rw [map_sub] at h
    linarith
  have hxn := hSo.mem_nhds hx
  have hrD : DifferentiableAt ℝ r x :=
    ((hwD x hx).differentiableAt hxn).sub (((hvD x hx).differentiableAt hxn).const_mul (1 - δ))
  have hzero := hloc.hasFDerivAt_eq_zero (hrD.hasFDerivAt.sub (δ • p).hasFDerivAt)
  refine ⟨x, hx, sub_eq_zero.mp hzero, fun y hy => ?_⟩
  simpa only [r, p, smul_apply, smul_eq_mul] using hsupp y hy

/-- Points of `S` where the affine function of slope `fderiv ℝ u x` through `(x, u x)`
supports the graph of `u` on the closure. This is a tangent support at differentiable points.
At a nondifferentiable point, `fderiv ℝ u x = 0`, so membership means that `x ∈ S` and
`x` minimizes `u` on `closure S`. In the supporting-gradient-image theorem below, the residual
is differentiable on `S`, so every member has the tangent interpretation. -/
def supportingTangentSet (S : Set E) (u : E → ℝ) : Set E :=
  {x ∈ S | ∀ y ∈ closure S, u x + fderiv ℝ u x (y - x) ≤ u y}

/-- Membership means that the point lies in `S` and its affine support of slope `fderiv ℝ u x`
lies below `u` on the closure. This is its tangent where `u` is differentiable; otherwise
`fderiv ℝ u x = 0`, and the condition says that `x` minimizes `u` on `closure S`. -/
@[simp] theorem mem_supportingTangentSet {S : Set E} {u : E → ℝ} {x : E} :
    x ∈ supportingTangentSet S u ↔
      x ∈ S ∧ ∀ y ∈ closure S, u x + fderiv ℝ u x (y - x) ≤ u y := by
  rw [supportingTangentSet]
  exact Iff.rfl

end NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For `w` uniformly close to `v`, the Haar measure of the supporting gradient image of
`w - (1 - δ) v` is at least `δ ^ finrank ℝ E` times the reference gradient image measure on `K`. -/
theorem exists_ofReal_pow_mul_measure_image_gradient_le_measure_image_gradient_supportingTangentSet
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {S K : Set E} {v : E → ℝ}
    (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (hvs : StrictConvexOn ℝ S v)
    (hvc : ContinuousOn v (closure S)) (hvC1 : ContDiffOn ℝ 1 v S)
    (hK : IsCompact K) (hKS : K ⊆ S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ > 0, ∀ w : E → ℝ, ContinuousOn w (closure S) → DifferentiableOn ℝ w S →
      (∀ y ∈ closure S, |w y - v y| ≤ τ) →
        ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ ((∇ v) '' K) ≤
          μ ((∇ fun y => w y - (1 - δ) * v y) ''
            supportingTangentSet S (fun y => w y - (1 - δ) * v y)) := by
  obtain ⟨τ, hτ, hcontact⟩ := exists_mem_fderiv_sub_eq_smul_fderiv_and_supporting
    hSo hSb.isCompact_closure hvs hvc hvC1 hK hKS hδ
  refine ⟨τ, hτ, ?_⟩
  intro w hwc hwD hclose
  let r := fun y => w y - (1 - δ) * v y
  rw [← Measure.addHaar_smul_of_nonneg μ hδ.le]
  apply measure_mono
  rintro p ⟨q, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨x, hx, hderiv, hsupp⟩ := hcontact w hwc hwD hclose z hz
  have hgrad : ∇ r x = δ • ∇ v z := by
    apply (InnerProductSpace.toDual ℝ E).injective
    simpa only [toDual_gradient, map_smul] using hderiv
  refine ⟨x, mem_supportingTangentSet.mpr ⟨hx, ?_⟩, hgrad⟩
  intro y hy
  rw [hderiv]
  simpa only [smul_apply, smul_eq_mul] using hsupp y hy

end TauCeti
