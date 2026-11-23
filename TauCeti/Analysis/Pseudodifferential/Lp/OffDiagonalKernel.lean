/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Function.Lp.Integral.BoundedSmul

/-!
# Kernel representation of `Lᵖ` extensions of quantizations

Let `a` be a symbol of any order on `ℝⁿ`, with off-diagonal kernel `K`
(`TauCeti.Symbol.offDiagonalKernel`), and let `T` be a bounded operator on `Lᵖ`, `1 ≤ p < ∞`,
which agrees with the Kohn–Nirenberg quantization `Op(a)` on Schwartz functions. This file shows
that `T` is still given by the kernel away from the support of its argument: if `f ∈ Lᵖ` vanishes
off a compact set `s`, then `T f (x) = ∫ K(x, y) f(y) dy` for almost every `x ∉ s`. This is the
form in which the Calderón–Zygmund theorem asks for a kernel representation.

## The argument

The representation holds for Schwartz functions with compact support
(`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`). A general `f ∈ Lᵖ`,
vanishing off a compact set `s`, is the `Lᵖ` limit of smooth functions supported in the closed
`δ / 2`-thickening `L` of `s` (`MeasureTheory.MemLp.exist_contDiff_tsupport_subset_eLpNorm_sub_le`).
Their images under `T` converge to `T f` almost everywhere along a subsequence. At a point `x`
outside the closed `δ`-thickening of `s`, the kernel `y ↦ K(x, y)` is bounded on `L`, so by
Hölder's inequality on `L` the integrals against it converge too.

## Main results

* `TauCeti.Symbol.ae_apply_eq_integral_offDiagonalKernel`: an `Lᵖ` extension `T` of `Op(a)`, for a
  symbol of any order, satisfies `T f (x) = ∫ K(x, y) f(y) dy` for almost every `x` off a compact
  set outside which `f` vanishes.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Representation

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {p : ℝ≥0∞}

/-- The kernel representation of an `Lᵖ` extension of `Op(a)` at the points outside the closed
`δ`-thickening of a compact set off which the argument vanishes. -/
private theorem ae_notMem_cthickening_apply_eq_integral_offDiagonalKernel [Fact (1 ≤ p)]
    (a : Symbol n V W m) (hp : p ≠ ∞)
    {T : Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W p volume}
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp p) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    (f : Lp V p (volume : Measure (CoordinateSpace n))) {s : Set (CoordinateSpace n)}
    (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x, x ∉ cthickening δ s → T f x = ∫ y, offDiagonalKernel a x y (f y) := by
  -- Smooth approximations `w k → f` in `Lᵖ`, supported in the compact `L = cthickening (δ / 2) s`.
  set L := cthickening (δ / 2) s
  have hfL : ∀ᵐ y, y ∉ L → f y = 0 :=
    hf.mono fun y hy hyL ↦ hy fun h ↦ hyL (self_subset_cthickening s h)
  choose g hgc hg hgL hfg using fun k : ℕ ↦
    (Lp.memLp f).exist_contDiff_tsupport_subset_eLpNorm_sub_le hp Fact.out hs.isClosed
      (cthickening_mem_nhdsSet s (half_pos hδ)) hf (Nat.one_div_pos_of_nat (n := k))
  set w : ℕ → 𝓢(CoordinateSpace n, V) := fun k ↦ (hgc k).toSchwartzMap (hg k)
  have hw (k : ℕ) : ⇑(w k) = g k := funext fun _ ↦ HasCompactSupport.toSchwartzMap_toFun _ _ _
  have hw0 (k : ℕ) : ∀ᵐ y, y ∉ L → w k y = 0 :=
    .of_forall fun y hy ↦ hw k ▸ image_eq_zero_of_notMem_tsupport fun h ↦ hy (hgL k h)
  have hw_lim : Tendsto (fun k ↦ eLpNorm (⇑(w k) - ⇑f) p volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (fun _ ↦ zero_le) fun k ↦ hw k ▸ (eLpNorm_sub_comm _ _ _ _).trans_le (hfg k)
  have hwLp : Tendsto (fun k ↦ (w k).toLp p volume) atTop (𝓝 f) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).2 (hw_lim.congr fun k ↦ eLpNorm_congr_ae ?_)
    filter_upwards [(w k).coeFn_toLp p volume] with z hz
    simp [hz]
  -- So `T (w k) → T f` almost everywhere along a subsequence.
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((T.continuous.tendsto f).comp hwLp)).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.2 fun k ↦ hT (w k)] with x hx hTx hxδ
  have hxL : x ∉ L := fun h ↦ hxδ (cthickening_mono (half_le_self hδ.le) s h)
  -- The kernel `y ↦ K(x, y)` is bounded on the compact set `L`, which does not contain `x`.
  have hL : IsCompact L := hs.cthickening
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn
    ((continuousOn_offDiagonalKernel_compl_singleton a x).mono fun y hy (hyx : y = x) ↦
      hxL (hyx ▸ hy))
  have hC := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := M)) (ENNReal.rpow_ne_top_of_nonneg
    (ENNReal.one_sub_one_div_toReal_nonneg (Fact.out : 1 ≤ p)) (hL.measure_ne_top (μ := volume)))
  have hint (g : CoordinateSpace n → V) (hg : MemLp g p volume) (hgL : ∀ᵐ y, y ∉ L → g y = 0) :
      Integrable (fun y ↦ offDiagonalKernel a x y (g y)) :=
    (hg.integrable_of_ae_notMem_eq_zero Fact.out hL.measure_lt_top.ne hgL).apply_of_norm_le
      ((stronglyMeasurable_uncurry_offDiagonalKernel a).comp_measurable
        measurable_prodMk_left).aestronglyMeasurable hM hgL
  -- On the other hand `T (w k) x = ∫ K(x, y) (w k y) dy`, which tends to `∫ K(x, y) (f y) dy`.
  have hrep (k : ℕ) : T ((w k).toLp p volume) x = ∫ y, offDiagonalKernel a x y (w k y) :=
    (hTx k).trans (quantizeSchwartzValue_eq_integral_offDiagonalKernel a
      (hw k ▸ hgc k) fun h ↦ hxL (hgL k (hw k ▸ h)))
  refine tendsto_nhds_unique hx ?_
  simp_rw [Function.comp_apply, hrep]
  refine (tendsto_integral_of_L1 _ (hint f (Lp.memLp f) hfL).aestronglyMeasurable
    (.of_forall fun k ↦ hint _ ((w k).memLp p) (hw0 k)) ?_).comp hns.tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.const_mul hw_lim (Or.inr hC)) (fun _ ↦ zero_le) fun k ↦ ?_
  simpa only [Pi.sub_apply, map_sub, one_div] using
    lintegral_enorm_apply_le_mul_eLpNorm (.of_forall hM) (Fact.out : 1 ≤ p)
      ((w k).continuous.aestronglyMeasurable.sub (Lp.aestronglyMeasurable f))
      ((hfL.and (hw0 k)).mono fun y hy hyL ↦ by simp [hy.1 hyL, hy.2 hyL])

/-- **Kernel representation of `Lᵖ` extensions.** Let `T` be a bounded operator on `Lᵖ`,
`1 ≤ p < ∞`, which agrees with `Op(a)` on Schwartz functions, for a symbol `a` of any order. If
`f ∈ Lᵖ` vanishes off a compact set `s`, then `T f (x) = ∫ K(x, y) f(y) dy` for almost every
`x ∉ s`, where `K` is the off-diagonal kernel of `a`. -/
theorem ae_apply_eq_integral_offDiagonalKernel [Fact (1 ≤ p)] (a : Symbol n V W m) (hp : p ≠ ∞)
    {T : Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W p volume}
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp p) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    (f : Lp V p (volume : Measure (CoordinateSpace n))) {s : Set (CoordinateSpace n)}
    (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → T f x = ∫ y, offDiagonalKernel a x y (f y) := by
  -- Every point off the closed set `s` lies off one of its closed thickenings.
  filter_upwards [ae_all_iff.2 fun k : ℕ ↦ ae_notMem_cthickening_apply_eq_integral_offDiagonalKernel
    a hp hT f hs hf (Nat.one_div_pos_of_nat (n := k))] with x hx hxs
  have hx' : x ∉ ⋂ δ, ⋂ (_ : 0 < δ), cthickening δ s := by
    rwa [← closure_eq_iInter_cthickening, hs.isClosed.closure_eq]
  simp only [mem_iInter, not_forall] at hx'
  obtain ⟨δ, hδ, hxδ⟩ := hx'
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  exact hx k fun h ↦ hxδ (cthickening_mono hk.le s h)

end Representation

end Symbol

end TauCeti
