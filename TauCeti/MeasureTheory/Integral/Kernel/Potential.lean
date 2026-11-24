/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `L¹` continuity of kernel potentials

An integrable kernel translated by a measurable family of shifts can be integrated against
integrable weights. Almost everywhere convergence of the shifts and `L¹` convergence of the
weights imply `L¹` convergence of these potentials. A quantitative estimate
separates the weight error from the kernel translation error. The convergence results hold along
any filter with a countable basis; the quantitative estimates need no topology on the shift group.

A kernel `G x y` on a bounded set `s` that is dominated by a translation kernel, `|G x y| ≤
|K (x - y)| + C` with `K` only locally integrable, still integrates against integrable weights:
`(x, y) ↦ G x y * g y` is integrable on `s × s`
(`MeasureTheory.LocallyIntegrable.integrable_uncurry_mul_of_abs_le`). Green kernels of bounded
domains are dominated in this way by the fundamental solution, which is locally integrable but not
integrable. For a symmetric kernel `G`, Fubini's theorem moves `G` from a bounded weight `ψ`
supported in `s` onto `f`: `∫_s f(x) ∫ G(x, y) ψ(y) dy dx = ∫_s ψ(y) ∫_s G(y, x) f(x) dx dy`
(`MeasureTheory.Integrable.setIntegral_mul_integral_mul_comm`).
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory
namespace Integrable

variable {G : Type*} [AddGroup G] [MeasurableSpace G] {ν : Measure G} [ν.IsAddRightInvariant]

section Measurable
variable [MeasurableAdd G]

section Translation
variable {K : Type*}

/-- The `L¹` distance between two translates is at most twice the kernel's `L¹` norm. -/
theorem integral_norm_kernel_translation_sub_le [NormedAddCommGroup K] {k : G → K}
    (hk : Integrable k ν) (a b : G) :
    (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) ≤ 2 * ∫ z : G, ‖k z‖ ∂ν := by
  have hi (c : G) : Integrable (fun z ↦ k (z - c)) ν := hk.comp_sub_right c
  calc
    (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) ≤ ∫ z : G, ‖k (z - a)‖ + ‖k (z - b)‖ ∂ν :=
      integral_mono ((hi a).sub (hi b)).norm ((hi a).norm.add (hi b).norm)
        (fun z ↦ norm_sub_le _ _)
    _ = 2 * ∫ z : G, ‖k z‖ ∂ν := by
      rw [integral_add (hi a).norm (hi b).norm]
      rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖),
        integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]
      ring

private theorem norm_weighted_kernel_translation_sub_le [NormedAddCommGroup K] {V : Type*}
    [SeminormedAddGroup V] {k : G → K} (hk : Integrable k ν) (a b : G) (v : V) :
    ‖(∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) * ‖v‖‖ ≤
      (2 * ∫ z : G, ‖k z‖ ∂ν) * ‖v‖ := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hk.integral_norm_kernel_translation_sub_le a b)
    (norm_nonneg _)

/-- For fixed shifts and weights, split the product difference into a weight error and a
translation error, retaining the exact `L¹` constants. -/
theorem integral_norm_translated_kernel_mul_sub_le [NormedRing K] {k : G → K}
    (hk : Integrable k ν) (a b : G) (u v : K) :
    (∫ z : G, ‖k (z - a) * u - k (z - b) * v‖ ∂ν) ≤
      (∫ z : G, ‖k z‖ ∂ν) * ‖u - v‖ +
        (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) * ‖v‖ := by
  have hi (c : G) : Integrable (fun z ↦ k (z - c)) ν := hk.comp_sub_right c
  have hu : Integrable (fun z ↦ ‖k (z - a)‖ * ‖u - v‖) ν :=
    (hi a).norm.mul_const ‖u - v‖
  have hv : Integrable (fun z ↦ ‖k (z - a) - k (z - b)‖ * ‖v‖) ν := by
    simpa only [Pi.sub_apply] using ((hi a).sub (hi b)).norm.mul_const ‖v‖
  calc
    _ ≤ ∫ z : G, ‖k (z - a)‖ * ‖u - v‖ + ‖k (z - a) - k (z - b)‖ * ‖v‖ ∂ν := by
      apply integral_mono (((hi a).mul_const u).sub ((hi b).mul_const v)).norm (hu.add hv)
      intro z
      have he : k (z - a) * u - k (z - b) * v =
          k (z - a) * (u - v) + (k (z - a) - k (z - b)) * v := by
        rw [mul_sub, sub_mul]
        abel
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = _ := by
      rw [integral_add hu hv]
      simp_rw [integral_mul_const]
      rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]

end Translation

section Product
omit [MeasurableAdd G]
variable [MeasurableSub₂ G] [SFinite ν]
variable {K : Type*} {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An integrable kernel with integrable weights and a.e.-measurable shifts gives a jointly
integrable function `(t, z) ↦ k (z - c t) * v t` for the product measure. -/
theorem integrable_prod_comp_sub_mul [NormedRing K] {k : G → K}
    (hk : Integrable k ν)
    {c : α → G} {v : α → K} (hc : AEMeasurable c μ)
    (hv : Integrable v μ) :
    Integrable (fun p : α × G ↦ k (p.2 - c p.1) * v p.1) (μ.prod ν) := by
  have := TauCeti.measurableAdd_of_measurableSub (G := G)
  have hm : AEStronglyMeasurable (fun p : α × G ↦ k (p.2 - c p.1) * v p.1)
      (μ.prod ν) :=
    (hk.aestronglyMeasurable.comp_prod_sub hc).mul hv.aestronglyMeasurable.comp_fst
  have hi (t : α) : Integrable (fun z ↦ k (z - c t)) ν := hk.comp_sub_right (c t)
  apply (integrable_prod_iff hm).2
  constructor
  · exact Filter.Eventually.of_forall fun t ↦ (hi t).mul_const (v t)
  · apply (hv.norm.const_mul (∫ z : G, ‖k z‖ ∂ν)).mono' hm.norm.integral_prod_right'
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    calc
      _ ≤ ∫ z : G, ‖k (z - c t)‖ * ‖v t‖ ∂ν :=
        integral_mono ((hi t).mul_const (v t)).norm ((hi t).norm.mul_const ‖v t‖)
          (fun z ↦ norm_mul_le _ _)
      _ = (∫ z : G, ‖k z‖ ∂ν) * ‖v t‖ := by
        rw [integral_mul_const, integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]

/-- An integrable kernel with integrable weights and measurable shifts has an integrable
weighted potential after integrating over the shifts. -/
theorem integral_comp_sub_mul [NormedRing K] [NormedSpace ℝ K] [SFinite μ] {k : G → K}
    (hk : Integrable k ν)
    {c : α → G} {v : α → K} (hc : AEMeasurable c μ) (hv : Integrable v μ) :
    Integrable (fun z ↦ ∫ t, k (z - c t) * v t ∂μ) ν :=
  (hk.integrable_prod_comp_sub_mul hc hv).integral_prod_right

/-- The translation error weighted by an integrable function is integrable. -/
theorem integrable_integral_norm_comp_sub_sub_mul_norm [NormedAddCommGroup K] {V : Type*}
    [NormedAddCommGroup V] {k : G → K} (hk : Integrable k ν)
    {a b : α → G} {v : α → V} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hv : Integrable v μ) :
    Integrable (fun t ↦ (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖) μ := by
  have := TauCeti.measurableAdd_of_measurableSub (G := G)
  have hm : AEStronglyMeasurable
      (fun t ↦ (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖) μ := by
    have hprod : AEStronglyMeasurable
        (fun p : α × G ↦ ‖k (p.2 - a p.1) - k (p.2 - b p.1)‖) (μ.prod ν) :=
      ((hk.aestronglyMeasurable.comp_prod_sub ha).sub
        (hk.aestronglyMeasurable.comp_prod_sub hb)).norm
    exact hprod.integral_prod_right'.mul hv.aestronglyMeasurable.norm
  apply (hv.norm.const_mul (2 * ∫ z : G, ‖k z‖ ∂ν)).mono' hm
  filter_upwards with t
  exact norm_weighted_kernel_translation_sub_le hk (a t) (b t) (v t)

/-- A kernel potential difference is bounded by the weight discrepancy and a translation error. -/
theorem integral_norm_kernel_potential_sub_le [NormedRing K] [NormedSpace ℝ K]
    [SFinite μ] {k : G → K}
    (hk : Integrable k ν)
    {a b : α → G} {u v : α → K} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hu : Integrable u μ) (hv : Integrable v μ) :
    (∫ z : G, ‖(∫ t, k (z - a t) * u t ∂μ) - (∫ t, k (z - b t) * v t ∂μ)‖ ∂ν) ≤
      (∫ z : G, ‖k z‖ ∂ν) * (∫ t, ‖u t - v t‖ ∂μ) +
      ∫ t, (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ ∂μ := by
  have := TauCeti.measurableAdd_of_measurableSub (G := G)
  have hA := integrable_prod_comp_sub_mul hk ha hu
  have hB := integrable_prod_comp_sub_mul hk hb hv
  have hD := hA.sub hB
  have hweighted := integrable_integral_norm_comp_sub_sub_mul_norm hk ha hb hv
  have hweight : Integrable (fun t ↦ (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖) μ := by
    simpa only [Pi.sub_apply] using (hu.sub hv).norm.const_mul (∫ z : G, ‖k z‖ ∂ν)
  calc
    -- Minkowski moves the norm inside the parameter integral.
    _ ≤ ∫ z : G, ∫ t, ‖k (z - a t) * u t - k (z - b t) * v t‖ ∂μ ∂ν := by
      apply integral_mono_ae
      · exact (hA.swap.integral_prod_left.sub hB.swap.integral_prod_left).norm
      · exact hD.integral_norm_prod_right
      · filter_upwards [hA.prod_left_ae, hB.prod_left_ae] with z hzA hzB
        rw [← integral_sub hzA hzB]
        exact norm_integral_le_integral_norm _
    -- Fubini makes the fixed-shift estimate available pointwise in the parameter.
    _ = ∫ t, (∫ z : G, ‖k (z - a t) * u t - k (z - b t) * v t‖ ∂ν) ∂μ :=
      integral_integral_swap hD.swap.norm
    -- Separate the weight discrepancy from the kernel translation error.
    _ ≤ ∫ t, (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖ +
        (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ ∂μ :=
      integral_mono hD.integral_norm_prod_left (hweight.add hweighted)
        (fun t ↦ integral_norm_translated_kernel_mul_sub_le hk (a t) (b t) (u t) (v t))
    _ = _ := by rw [integral_add hweight hweighted, integral_const_mul]

end Product

end Measurable

section Convergence
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G] [MeasurableSub₂ G]
  [SFinite ν] [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop]
variable {K : Type*} {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

/-- Almost everywhere convergence of shifts gives weighted `L¹` translation convergence. -/
theorem tendsto_integral_weighted_kernel_translation_sub [NormedAddCommGroup K] {V : Type*}
    [NormedAddCommGroup V] {k : G → K} (hk : Integrable k ν)
    {cn : ι → α → G} {c : α → G} {v : α → V} (hcn : ∀ n, AEMeasurable (cn n) μ)
    (hc : AEMeasurable c μ) (hv : Integrable v μ)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n ↦ cn n t) l (𝓝 (c t))) :
    Tendsto (fun n ↦ ∫ t, (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖ ∂μ)
      l (𝓝 0) := by
  have hm (n : ι) :=
    (integrable_integral_norm_comp_sub_sub_mul_norm hk (hcn n) hc hv).aestronglyMeasurable
  have hpointwise : ∀ᵐ t ∂μ, Tendsto
      (fun n ↦ (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖)
      l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with t ht
    simpa using (hk.tendsto_integral_norm_translate_sub ht).mul_const ‖v t‖
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun t ↦ (2 * ∫ z : G, ‖k z‖ ∂ν) * ‖v t‖) (Eventually.of_forall hm)
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun t ↦
      norm_weighted_kernel_translation_sub_le hk (cn n t) (c t) (v t))
    (hv.norm.const_mul _) hpointwise
  simpa using h

/-- Almost everywhere convergence of shifts and `L¹` convergence of weights give `L¹`
convergence of the corresponding kernel potentials. -/
theorem tendsto_integral_norm_kernel_potential_sub [NormedRing K] [NormedSpace ℝ K]
    [SFinite μ] {k : G → K}
    (hk : Integrable k ν)
    {cn : ι → α → G} {vn : ι → α → K} {c : α → G} {v : α → K}
    (hcn : ∀ n, AEMeasurable (cn n) μ) (hc : AEMeasurable c μ)
    (hvn : ∀ n, Integrable (vn n) μ) (hv : Integrable v μ)
    (hclim : ∀ᵐ t ∂μ, Tendsto (fun n ↦ cn n t) l (𝓝 (c t)))
    (hvlim : Tendsto (fun n ↦ ∫ t, ‖vn n t - v t‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z : G,
      ‖(∫ t, k (z - cn n t) * vn n t ∂μ) - (∫ t, k (z - c t) * v t ∂μ)‖ ∂ν)
      l (𝓝 0) := by
  have hbound := (hvlim.const_mul (∫ z : G, ‖k z‖ ∂ν)).add
    (tendsto_integral_weighted_kernel_translation_sub hk hcn hc hv hclim)
  apply squeeze_zero (fun n ↦ integral_nonneg (fun _ ↦ norm_nonneg _))
    (fun n ↦ integral_norm_kernel_potential_sub_le hk (hcn n) hc (hvn n) hv)
  simpa using hbound

end Convergence

end Integrable

/-! ### Kernels dominated by a locally integrable translation kernel -/

namespace LocallyIntegrable

open Metric

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ]

omit [ProperSpace E] [IsFiniteMeasureOnCompacts μ] in
/-- The row integrals over a bounded set `s` of a kernel dominated by `|K (x - y)| + C` off the
diagonal are bounded uniformly in `y ∈ s`. -/
private theorem setLIntegral_enorm_le_of_abs_le {K : E → ℝ} {s : Set E} (hs : MeasurableSet s)
    {R C : ℝ} (hsR : s ⊆ closedBall 0 R) {G : E → E → ℝ}
    (hG : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → |G x y| ≤ |K (x - y)| + C) {y : E} (hy : y ∈ s) :
    ∫⁻ x in s, ‖G x y‖ₑ ∂μ ≤ (∫⁻ w in closedBall 0 (2 * R), ‖K w‖ₑ ∂μ) + ‖C‖ₑ * μ s := by
  have hsing : ∀ᵐ x ∂μ, x ≠ y := ae_iff.2 (by simp)
  calc ∫⁻ x in s, ‖G x y‖ₑ ∂μ
      ≤ ∫⁻ x in s, ((closedBall 0 (2 * R)).indicator (fun w ↦ ‖K w‖ₑ) (x - y) + ‖C‖ₑ) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hsing] with x hx hxy
        have hxR := mem_closedBall_zero_iff.1 (hsR hx)
        have hyR := mem_closedBall_zero_iff.1 (hsR hy)
        have hxy' : x - y ∈ closedBall (0 : E) (2 * R) :=
          mem_closedBall_zero_iff.2 ((norm_sub_le x y).trans (by linarith))
        rw [Set.indicator_of_mem hxy', ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [Real.norm_eq_abs]
        linarith [hG x hx y hy hxy, le_abs_self C]
      _ = (∫⁻ x in s, (closedBall 0 (2 * R)).indicator (fun w ↦ ‖K w‖ₑ) (x - y) ∂μ) +
          ‖C‖ₑ * μ s := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ _ := by
        refine add_le_add_left ?_ _
        calc _ ≤ ∫⁻ x, (closedBall 0 (2 * R)).indicator (fun w ↦ ‖K w‖ₑ) (x - y) ∂μ :=
              setLIntegral_le_lintegral _ _
          _ = _ := by
            rw [lintegral_sub_right_eq_self _ y, lintegral_indicator measurableSet_closedBall]

/-- **Integral operators with a locally integrable singularity on a bounded set.** Let `s` be a
bounded measurable set and let the kernel `G` satisfy `|G x y| ≤ |K (x - y)| + C` at distinct
points `x, y` of `s`, where `K` is locally integrable. Then `(x, y) ↦ G x y * g y` is integrable
on `s × s` for every `g` integrable on `s`. -/
theorem integrable_uncurry_mul_of_abs_le {K : E → ℝ} (hK : LocallyIntegrable K μ) {s : Set E}
    (hs : MeasurableSet s) (hsb : Bornology.IsBounded s) {C : ℝ} {G : E → E → ℝ}
    (hGm : AEStronglyMeasurable (Function.uncurry G) ((μ.restrict s).prod (μ.restrict s)))
    (hG : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → |G x y| ≤ |K (x - y)| + C) {g : E → ℝ}
    (hg : IntegrableOn g s μ) :
    Integrable (Function.uncurry fun x y ↦ G x y * g y) ((μ.restrict s).prod (μ.restrict s)) := by
  obtain ⟨R, hR⟩ := hsb.subset_closedBall 0
  set M := (∫⁻ w in closedBall 0 (2 * R), ‖K w‖ₑ ∂μ) + ‖C‖ₑ * μ s
  have hM : M < ⊤ :=
    ENNReal.add_lt_top.2 ⟨(hK.integrableOn_isCompact (isCompact_closedBall _ _)).2,
      ENNReal.mul_lt_top eNorm_lt_top hsb.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y ↦ G x y * g y)
      ((μ.restrict s).prod (μ.restrict s)) :=
    hGm.mul hg.aestronglyMeasurable.comp_snd
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.eNorm]
  calc ∫⁻ y in s, ∫⁻ x in s, ‖G x y * g y‖ₑ ∂μ ∂μ
      = ∫⁻ y in s, (∫⁻ x in s, ‖G x y‖ₑ ∂μ) * ‖g y‖ₑ ∂μ := by
        refine lintegral_congr fun y ↦ ?_
        simp_rw [eNorm_mul]
        exact lintegral_mul_const' _ _ eNorm_ne_top
    _ ≤ ∫⁻ y in s, M * ‖g y‖ₑ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hs] with y hy
        gcongr
        exact setLIntegral_enorm_le_of_abs_le hs hR hG hy
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ hM.ne]
        exact ENNReal.mul_lt_top hM hg.2

end LocallyIntegrable

/-! ### Symmetric kernels -/

namespace Integrable

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- **Fubini's theorem for a symmetric kernel.** Let `G` be symmetric and let
`(x, y) ↦ G x y * f y` be integrable on `s × s`. For a bounded measurable `ψ` supported in `s`,
`∫_s f(x) ∫ G(x, y) ψ(y) dy dx = ∫_s ψ(y) ∫_s G(y, x) f(x) dx dy`. -/
theorem setIntegral_mul_integral_mul_comm {s : Set α} {G : α → α → ℝ} {f ψ : α → ℝ}
    (hGf : Integrable (Function.uncurry fun x y ↦ G x y * f y)
      ((μ.restrict s).prod (μ.restrict s)))
    (hs : MeasurableSet s) (hG : ∀ x y, G x y = G y x) (hψ : AEStronglyMeasurable ψ (μ.restrict s))
    {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) (hψs : Function.support ψ ⊆ s) :
    ∫ x in s, f x * ∫ y, G x y * ψ y ∂μ ∂μ = ∫ y in s, ψ y * ∫ x in s, G y x * f x ∂μ ∂μ := by
  have hψ0 := Function.support_subset_iff'.1 hψs
  have hprod : Integrable (Function.uncurry fun x y ↦ f x * (G x y * ψ y))
      ((μ.restrict s).prod (μ.restrict s)) := by
    refine (hGf.swap.mul_bdd (c := C) hψ.comp_snd (Eventually.of_forall fun p ↦ hC p.2)).congr
      (Eventually.of_forall fun ⟨x, y⟩ ↦ ?_)
    simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair, hG x y]
    ring
  calc ∫ x in s, f x * ∫ y, G x y * ψ y ∂μ ∂μ
      = ∫ x in s, ∫ y in s, f x * (G x y * ψ y) ∂μ ∂μ := by
        refine setIntegral_congr_fun hs fun x _ ↦ ?_
        rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
          rw [hψ0 y hy, mul_zero]]
    _ = ∫ y in s, ∫ x in s, f x * (G x y * ψ y) ∂μ ∂μ := integral_integral_swap hprod
    _ = _ := by
        refine setIntegral_congr_fun hs fun y _ ↦ ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [hG x y]
        ring

end Integrable

end MeasureTheory
