/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Interior support contacts under uniform perturbations

A positive tangent gap on the frontier forces a contact in the interior. This is the
contact construction used in the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
-/

public section

open Set MeasureTheory
open scoped Gradient Pointwise Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Strict convexity on the open set gives a strict tangent inequality at its boundary.
omit [FiniteDimensional ℝ E] in
private theorem tangent_gap_on_closure {S : Set E} {v : E → ℝ}
    (hSo : IsOpen S) (hv : ConvexOn ℝ (closure S) v) (hvs : StrictConvexOn ℝ S v)
    {z y : E} (hz : z ∈ S) (hy : y ∈ closure S) (hzy : z ≠ y)
    (hd : DifferentiableAt ℝ v z) : 0 < v y - v z - fderiv ℝ v z (y - z) := by
  let A : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z y
  have hA : Function.Injective A := AffineMap.lineMap_injective ℝ hzy
  have hs : StrictConvexOn ℝ (A ⁻¹' S) (v ∘ A) := by
    refine ⟨hvs.1.affine_preimage A, fun a ha b hb hab p q hp hq hpq => ?_⟩
    change v (A (p • a + q • b)) < p • v (A a) + q • v (A b)
    rw [Convex.combo_affine_apply hpq]
    exact hvs.2 ha hb (fun h => hab (hA h)) hp hq hpq
  have h0 : (0 : ℝ) ∈ A ⁻¹' S := by simpa [A] using hz
  have hAhalf : A (1 / 2) = (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • y := by
    change AffineMap.lineMap z y (1 / 2 : ℝ) = _
    rw [AffineMap.lineMap_apply_module, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have hmidseg : A (1 / 2) ∈ openSegment ℝ z y := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    exact hAhalf.symm
  have hmid : (1 / 2 : ℝ) ∈ A ⁻¹' S := by
    change A (1 / 2) ∈ S
    have hz' : z ∈ interior S := by simpa only [hSo.interior_eq] using hz
    simpa only [hSo.interior_eq] using
      hvs.1.openSegment_interior_closure_subset_interior hz' hy hmidseg
  have hD : HasDerivAt (v ∘ A) (fderiv ℝ v z (y - z)) 0 := by
    have hL : HasDerivAt A (y - z) 0 := AffineMap.hasDerivAt_lineMap
    have hA0 : A 0 = z := AffineMap.lineMap_apply_zero _ _
    have hvA : HasFDerivAt v (fderiv ℝ v z) (A 0) := by simpa only [hA0] using hd.hasFDerivAt
    exact hvA.comp_hasDerivAt 0 hL
  have hstrict := hs.lt_slope_of_hasDerivAt h0 hmid (by norm_num) hD
  have hchord : v (A (1 / 2)) ≤ (1 / 2 : ℝ) * v z + (1 / 2 : ℝ) * v y := by
    have h := hv.2 (subset_closure hz) hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simpa only [hAhalf, smul_eq_mul] using h
  simp only [slope_def_field, Function.comp_apply, sub_zero, A,
    AffineMap.lineMap_apply_zero] at hstrict
  change v (AffineMap.lineMap z y (1 / 2)) ≤ _ at hchord
  linarith

/-- Uniformly small perturbations realize interior contacts with the slopes of the
scaled reference. -/
theorem exists_residual_contact_of_uniform_close {S K : Set E} {v : E → ℝ}
    (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (hv : ConvexOn ℝ (closure S) v) (hvs : StrictConvexOn ℝ S v)
    (hvc : ContinuousOn v (closure S)) (hvC1 : ContDiffOn ℝ 1 v S)
    (hK : IsCompact K) (hKS : K ⊆ S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ > 0, ∀ w : E → ℝ, ContinuousOn w (closure S) → DifferentiableOn ℝ w S →
      (∀ y ∈ closure S, |w y - v y| ≤ τ) → ∀ z ∈ K,
      ∃ x ∈ S,
        fderiv ℝ (fun y => w y - (1 - δ) * v y) x = δ • fderiv ℝ v z ∧
        ∀ y ∈ closure S, w x - (1 - δ) * v x + δ * fderiv ℝ v z (y - x) ≤ w y - (1 - δ) * v y := by
  let T := K ×ˢ frontier S
  let gap : E × E → ℝ := fun p => v p.2 - v p.1 - fderiv ℝ v p.1 (p.2 - p.1)
  have hcl := hSb.isCompact_closure
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
    have hzy : z ≠ y := fun h => (show y ∉ S from (hSo.frontier_eq ▸ hy).2) (h ▸ hKS hz)
    exact tangent_gap_on_closure hSo hv hvs (hKS hz) (frontier_subset_closure hy) hzy
      ((hvD z (hKS hz)).differentiableAt (hSo.mem_nhds (hKS hz)))
  obtain ⟨a, ha, hminGap⟩ := hT.exists_forall_le' hgap hgap_pos
  refine ⟨δ * a / 4, by positivity, ?_⟩
  intro w hwc hwD hclose z hz
  let p := fderiv ℝ v z
  let r : E → ℝ := fun y => w y - (1 - δ) * v y
  let φ : E → ℝ := fun y => r y - δ * p y
  have hrc : ContinuousOn r (closure S) := hwc.sub (continuousOn_const.mul hvc)
  have hφc : ContinuousOn φ (closure S) := hrc.sub (continuous_const.mul p.continuous).continuousOn
  have hzcl : z ∈ closure S := subset_closure (hKS hz)
  have hstrict : ∀ y ∈ closure S \ S, φ z < φ y := by
    intro y hy
    have hyf : y ∈ frontier S := hSo.frontier_eq.symm ▸ hy
    have h := mul_le_mul_of_nonneg_left (hminGap (z, y) ⟨hz, hyf⟩) hδ.le
    change δ * a ≤ δ * (v y - v z - p (y - z)) at h
    rw [map_sub] at h
    have hyerr := abs_le.mp (hclose y hy.1)
    have hzerr := abs_le.mp (hclose z hzcl)
    dsimp only [φ, r]
    linarith [mul_pos hδ ha]
  obtain ⟨x, hx, hmin⟩ := hcl.exists_isMinOn_mem_subset hφc hzcl hstrict
  have hloc := hmin.isLocalMin (Filter.mem_of_superset (hSo.mem_nhds hx) subset_closure)
  have hxn := hSo.mem_nhds hx
  have hrD : DifferentiableAt ℝ r x :=
    ((hwD x hx).differentiableAt hxn).sub (((hvD x hx).differentiableAt hxn).const_mul (1 - δ))
  have hzero := hloc.hasFDerivAt_eq_zero (hrD.hasFDerivAt.sub (p.hasFDerivAt.const_mul δ))
  refine ⟨x, hx, sub_eq_zero.mp hzero, fun y hy => ?_⟩
  have h := hmin hy
  change r x - δ * p x ≤ r y - δ * p y at h
  change r x + δ * p (y - x) ≤ r y
  rw [map_sub]
  linarith

/-- Small perturbations retain at least the rescaled reference gradient-image volume among
the gradients of interior points with a supporting affine function on the closure. -/
theorem exists_contact_volume_lower_bound_of_uniform_close
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {S K : Set E} {v : E → ℝ}
    (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (hv : ConvexOn ℝ (closure S) v) (hvs : StrictConvexOn ℝ S v)
    (hvc : ContinuousOn v (closure S)) (hvC1 : ContDiffOn ℝ 1 v S)
    (hK : IsCompact K) (hKS : K ⊆ S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ > 0, ∀ w : E → ℝ, ContinuousOn w (closure S) → DifferentiableOn ℝ w S →
      (∀ y ∈ closure S, |w y - v y| ≤ τ) →
        let r := fun y => w y - (1 - δ) * v y
        ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ ((∇ v) '' K) ≤
          μ ((∇ r) '' {x ∈ S | ∀ y ∈ closure S, r x + fderiv ℝ r x (y - x) ≤ r y}) := by
  obtain ⟨τ, hτ, hcontact⟩ := exists_residual_contact_of_uniform_close
    hSo hSb hv hvs hvc hvC1 hK hKS hδ
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
  refine ⟨x, ⟨hx, ?_⟩, hgrad⟩
  intro y hy
  rw [hderiv]
  exact hsupp y hy

end TauCeti
