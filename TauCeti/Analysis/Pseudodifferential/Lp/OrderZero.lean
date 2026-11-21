/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Uniform
public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.StandardKernel
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.MeasureTheory.Function.L2Space

/-!
# `Lᵖ` boundedness of uniform symbols of order zero

Let `a` be a symbol of order `0` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold with constants independent of the position `x`
(`TauCeti.Symbol.IsUniform`), with values in operators between complex Hilbert spaces. This file
proves that for every `1 < p < ∞` its Kohn–Nirenberg quantization `Op(a)` is bounded in the `Lᵖ`
norm, `‖Op(a) u‖_p ≤ C ‖u‖_p`, and so extends to a bounded operator on `Lᵖ`. For `p = 2` this is
the Calderón–Vaillancourt theorem (`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`); for
`p ≠ 2` the operator is a Calderón–Zygmund operator.

## The argument

The Calderón–Zygmund theorem on an inner product space
(`ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`) bounds an operator `T` on `L²` in
every `Lᵖ` norm, `1 < p < ∞`, once `T` and its adjoint are represented, off the support of their
argument, by kernels satisfying the size estimate `‖K(x, y)‖ ≤ C ‖x - y‖^(-n)` and a Hölder
smoothness estimate in the second variable. The ingredients are:

* the bounded extension `T` of `Op(a)` to `L²`, given by the Calderón–Vaillancourt theorem;
* the adjoint of `T`, which extends `Op(b)` for a uniform symbol `b` of order `0`
  (`TauCeti.Symbol.IsUniform.exists_integral_inner_quantizeUniformCLM_eq`);
* the size and smoothness estimates of the off-diagonal kernels of `a` and of `b`
  (`TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_le`,
  `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_sub_right_le`);
* the representation of `T f` by the off-diagonal kernel away from the support of an `L²`
  function `f` with compact support (`TauCeti.Symbol.ae_apply_eq_integral_offDiagonalKernel`).

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
* `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`: **`Lᵖ`
  boundedness**, `‖Op(a) u‖_p ≤ C ‖u‖_p` for every Schwartz function `u`, for `1 < p < ∞`.
* `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp_of_one_lt`: the bounded extension of `Op(a)` to
  `Lᵖ`, for `1 < p < ∞`.

## References

* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §2 and §5
  (`Lᵖ` boundedness of pseudodifferential operators of order zero via Calderón–Zygmund theory).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal SchwartzMap ComplexConjugate InnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Representation

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {p : ℝ≥0∞}

omit [CompleteSpace V] [CompleteSpace W] in
/-- Integration against the kernel `y ↦ K(x, y)` is bounded on functions vanishing off a compact
set `L` not containing `x`: `∫ ‖K(x, y) g(y)‖ dy ≤ C ‖g‖_p`. -/
private theorem exists_lintegral_enorm_offDiagonalKernel_apply_le [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (a : Symbol n V W m) {x : CoordinateSpace n} {L : Set (CoordinateSpace n)} (hL : IsCompact L)
    (hxL : x ∉ L) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : CoordinateSpace n → V, AEStronglyMeasurable g volume →
      (∀ᵐ y, y ∉ L → g y = 0) →
      ∫⁻ y, ‖offDiagonalKernel a x y (g y)‖ₑ ≤ C * eLpNorm g p volume := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn
    ((continuousOn_offDiagonalKernel_compl_singleton a x).mono fun y hy (hyx : y = x) ↦
      hxL (hyx ▸ hy))
  have hp1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  refine ⟨‖M‖ₑ * volume L ^ (1 - 1 / p.toReal), ENNReal.mul_ne_top eNorm_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 (div_le_one_of_le₀ hp1 ENNReal.toReal_nonneg))
      hL.measure_lt_top.ne), fun g hg hgL ↦ ?_⟩
  calc (∫⁻ y, ‖offDiagonalKernel a x y (g y)‖ₑ)
      ≤ ∫⁻ y, L.indicator (fun y ↦ ‖M‖ₑ * ‖g y‖ₑ) y := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgL] with y hy
        by_cases hyL : y ∈ L
        · rw [indicator_of_mem hyL]
          refine ((offDiagonalKernel a x y).le_opENorm (g y)).trans ?_
          gcongr
          exact eNorm_le_iff_norm_le.2 ((hM y hyL).trans (le_abs_self M))
        · rw [hy hyL, map_zero, eNorm_zero]
          exact zero_le
    _ = ‖M‖ₑ * eLpNorm g 1 (volume.restrict L) := by
        rw [lintegral_indicator hL.measurableSet, lintegral_const_mul' _ _ eNorm_ne_top,
          eLpNorm_one_eq_lintegral_eNorm hg.restrict]
    _ ≤ ‖M‖ₑ * (eLpNorm g p (volume.restrict L) *
          volume.restrict L univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)) := by
        gcongr
        exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ Fact.out hg.restrict
    _ ≤ ‖M‖ₑ * volume L ^ (1 - 1 / p.toReal) * eLpNorm g p volume := by
        rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one, mul_comm (eLpNorm g p _),
          ← mul_assoc]
        gcongr
        exact Measure.restrict_le_self

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
  obtain ⟨C, hC, hCle⟩ :=
    exists_lintegral_enorm_offDiagonalKernel_apply_le hp a (hs.cthickening (r := δ / 2)) hxL
  have hKm : AEStronglyMeasurable (offDiagonalKernel a x) volume :=
    ((stronglyMeasurable_uncurry_offDiagonalKernel a).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hint (g : CoordinateSpace n → V) (hg : MemLp g p volume) (hgL : ∀ᵐ y, y ∉ L → g y = 0) :
      Integrable (fun y ↦ offDiagonalKernel a x y (g y)) :=
    ⟨(ContinuousLinearMap.id ℂ _).aestronglyMeasurable_comp₂ hKm hg.aestronglyMeasurable,
      (hCle g hg.aestronglyMeasurable hgL).trans_lt
        (ENNReal.mul_lt_top hC.lt_top hg.eLpNorm_lt_top)⟩
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
  have hsub : ∀ᵐ y, y ∉ L → (⇑(w k) - ⇑f) y = 0 := by
    filter_upwards [hfL, hw0 k] with y hy hy' hyL
    simp [hy hyL, hy' hyL]
  simpa only [Pi.sub_apply, map_sub] using
    hCle _ ((w k).continuous.aestronglyMeasurable.sub (Lp.aestronglyMeasurable f)) hsub

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

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- If `T` extends `Op(a)` to `L²` and `Op(b)` is the formal adjoint of `Op(a)`, then the adjoint
of `T` extends `Op(b)`. -/
private theorem adjoint_toLp_eq_toLp_quantizeUniformCLM {a : Symbol n V W m} (ha : a.IsUniform)
    {b : Symbol n W V m} (hb : b.IsUniform)
    (hab : ∀ (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)),
      ∫ x, ⟪quantizeUniformCLM a ha u x, v x⟫_ℂ = ∫ x, ⟪u x, quantizeUniformCLM b hb v x⟫_ℂ)
    {T : Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W 2 volume}
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    (v : 𝓢(CoordinateSpace n, W)) :
    ContinuousLinearMap.adjoint T (v.toLp 2) = (quantizeUniformCLM b hb v).toLp 2 := by
  -- Both sides have the same inner products with the dense set of Schwartz functions.
  suffices key : ∀ u : 𝓢(CoordinateSpace n, V),
      ⟪ContinuousLinearMap.adjoint T (v.toLp 2), u.toLp 2⟫_ℂ =
        ⟪(quantizeUniformCLM b hb v).toLp 2, u.toLp 2⟫_ℂ by
    have hfun : (fun g : Lp V 2 (volume : Measure (CoordinateSpace n)) ↦
        ⟪ContinuousLinearMap.adjoint T (v.toLp 2), g⟫_ℂ) =
        fun g ↦ ⟪(quantizeUniformCLM b hb v).toLp 2, g⟫_ℂ :=
      (SchwartzMap.denseRange_toLpCLM (E := CoordinateSpace n) (F := V) (μ := volume) (p := 2)
        ENNReal.ofNat_ne_top).equalizer (continuous_const.inner continuous_id)
        (continuous_const.inner continuous_id)
        (funext fun u ↦ by simpa only [Function.comp_apply, SchwartzMap.toLpCLM_apply] using key u)
    exact ext_inner_right ℂ (congrFun hfun)
  intro u
  have h₁ : (fun x ↦ ⟪(v.toLp 2 : CoordinateSpace n → W) x,
      (T (u.toLp 2) : CoordinateSpace n → W) x⟫_ℂ) =ᵐ[volume]
      fun x ↦ conj ⟪quantizeUniformCLM a ha u x, v x⟫_ℂ := by
    filter_upwards [v.coeFn_toLp 2 volume, hT u] with x h₁ h₂
    rw [h₁, h₂, coe_quantizeUniformCLM, inner_conj_symm]
  have h₂ : (fun x ↦ ⟪((quantizeUniformCLM b hb v).toLp 2 : CoordinateSpace n → V) x,
      (u.toLp 2 : CoordinateSpace n → V) x⟫_ℂ) =ᵐ[volume]
      fun x ↦ conj ⟪u x, quantizeUniformCLM b hb v x⟫_ℂ := by
    filter_upwards [(quantizeUniformCLM b hb v).coeFn_toLp 2 volume,
      u.coeFn_toLp 2 volume] with x h₁ h₂
    rw [h₁, h₂, inner_conj_symm]
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def, integral_congr_ae h₁,
    integral_congr_ae h₂, integral_conj, integral_conj, hab]

/-- The off-diagonal kernel of a uniform symbol of order `0`, as a real-linear kernel, satisfies
the hypotheses of the Calderón–Zygmund theorem: it is strongly measurable, and it satisfies the size
estimate and the smoothness estimate in the second variable with exponent `1 / 2`. -/
private theorem IsUniform.exists_calderonZygmund_offDiagonalKernel {a : Symbol n V W 0}
    (ha : a.IsUniform) :
    letI : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
    letI : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
    StronglyMeasurable (Function.uncurry fun x y ↦
      (offDiagonalKernel a x y).restrictScalars ℝ) ∧
    ∃ C₀ C : ℝ≥0, (∀ x y : CoordinateSpace n, x ≠ y →
      ‖(offDiagonalKernel a x y).restrictScalars ℝ‖ ≤
        C₀ * dist x y ^ (-(Module.finrank ℝ (CoordinateSpace n) : ℝ))) ∧
      ∀ x y y' : CoordinateSpace n, 2 * dist y y' < dist x y' →
        ‖(offDiagonalKernel a x y).restrictScalars ℝ -
            (offDiagonalKernel a x y').restrictScalars ℝ‖ ≤
          C * (dist y y' ^ (1 / 2 : ℝ) *
            dist x y' ^ (-(Module.finrank ℝ (CoordinateSpace n) + 1 / 2 : ℝ))) := by
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
  refine ⟨(ContinuousLinearMap.restrictScalarsIsometry ℂ V W ℝ ℝ).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_uncurry_offDiagonalKernel a), ?_⟩
  simp only [finrank_euclideanSpace_fin, dist_eq_norm, ← ContinuousLinearMap.restrictScalars_sub,
    ContinuousLinearMap.norm_restrictScalars]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- On `ℝ⁰` there are no pairs of distinct points.
    refine ⟨0, 0, fun x y hxy ↦ absurd (Subsingleton.elim x y) hxy, fun x y y' h ↦ ?_⟩
    rw [Subsingleton.elim x y', sub_self, norm_zero] at h
    exact absurd h (not_lt.2 (by positivity))
  have hn' : (0 : ℝ) < 0 + n := by simpa using hn
  obtain ⟨C₀, hC₀, hsize⟩ := ha.exists_norm_offDiagonalKernel_le hn'
  obtain ⟨C, hC, hsmooth⟩ := ha.exists_norm_offDiagonalKernel_sub_right_le (δ := 1 / 2)
    (by norm_num) (by norm_num) (by positivity)
  refine ⟨C₀.toNNReal, C.toNNReal, fun x y hxy ↦ ?_, fun x y y' h ↦ ?_⟩
  · simpa [Real.coe_toNNReal _ hC₀] using hsize x y hxy
  · simpa [Real.coe_toNNReal _ hC, mul_assoc] using hsmooth x y y' h

/-- **`Lᵖ` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` between
complex Hilbert spaces whose estimates are uniform in the position, and for every `1 < p < ∞`,
there is a constant `C` with `‖Op(a) u‖_p ≤ C ‖u‖_p` for every Schwartz function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt {a : Symbol n V W 0}
    (ha : a.IsUniform) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) p volume ≤
        ENNReal.ofReal C * eLpNorm u p volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZeroLp ha
  obtain ⟨b, hb, hab⟩ := ha.exists_integral_inner_quantizeUniformCLM_eq
  have hT' (v : 𝓢(CoordinateSpace n, W)) :
      ContinuousLinearMap.adjoint T (v.toLp 2) =ᵐ[volume]
        quantizeSchwartzValue b.coefficient v := by
    rw [adjoint_toLp_eq_toLp_quantizeUniformCLM ha hb hab hT v, ← coe_quantizeUniformCLM b hb]
    exact (quantizeUniformCLM b hb v).coeFn_toLp 2 volume
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
  obtain ⟨hkm, C₀, C, hsize, hk⟩ := ha.exists_calderonZygmund_offDiagonalKernel
  obtain ⟨hkm', C₀', C', hsize', hk'⟩ := hb.exists_calderonZygmund_offDiagonalKernel
  obtain ⟨D, hD⟩ := ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow
    (T.restrictScalars ℝ) hkm hkm' (by norm_num) (by norm_num) hsize hsize' hk hk'
    (fun f s hs hf ↦ ae_apply_eq_integral_offDiagonalKernel a ENNReal.ofNat_ne_top hT f hs hf)
    (fun f s hs hf ↦ by
      rw [L2.adjoint_restrictScalars]
      exact ae_apply_eq_integral_offDiagonalKernel b ENNReal.ofNat_ne_top hT' f hs hf)
    hp hp_top
  refine ⟨D, D.coe_nonneg, fun u ↦ ?_⟩
  have h := hD (u.toLp 2)
  rw [ENNReal.ofReal_coe_nnreal]
  rwa [ContinuousLinearMap.coe_restrictScalars', eLpNorm_congr_ae (hT u),
    eLpNorm_congr_ae (u.coeFn_toLp 2 volume)] at h

/-- **The bounded extension of `Op(a)` to `Lᵖ`.** For a symbol `a` of order `0` between complex
Hilbert spaces whose estimates are uniform in the position, and for every `1 < p < ∞`, there is a
bounded operator on `Lᵖ` which agrees with `Op(a)` on Schwartz functions. -/
theorem exists_quantizeUniformOrderZeroLp_of_one_lt (a : Symbol n V W 0) (ha : a.IsUniform)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ T : Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W p volume,
      ∀ u : 𝓢(CoordinateSpace n, V),
        T (u.toLp p) =ᵐ[volume] quantizeSchwartzValue a.coefficient u := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt hp hp_top
  set e := SchwartzMap.toLpCLM ℂ V p (volume : Measure (CoordinateSpace n))
  have hdense : DenseRange e := by
    have he : ⇑e = ⇑(SchwartzMap.toLpCLM ℝ V p (volume : Measure (CoordinateSpace n))) := by
      ext1 u
      simp [e]
    rw [he]
    exact SchwartzMap.denseRange_toLpCLM hp_top
  have hbound : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖(SchwartzMap.toLpCLM ℂ W p volume).comp (quantizeUniformCLM a ha) u‖ ≤ C * ‖e u‖ := by
    refine ⟨C, fun u ↦ ?_⟩
    simp only [ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, Lp.norm_def, e]
    rw [eLpNorm_congr_ae ((quantizeUniformCLM a ha u).coeFn_toLp p volume),
      eLpNorm_congr_ae (u.coeFn_toLp p volume), coe_quantizeUniformCLM,
      ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (u.memLp p).eLpNorm_ne_top) (hC u)
  refine ⟨((SchwartzMap.toLpCLM ℂ W p volume).comp
    (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm e.toLinearMap, fun u ↦ ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense hbound u
  simp only [e, SchwartzMap.toLpCLM_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply] at h
  rw [h, ← coe_quantizeUniformCLM a ha]
  exact (quantizeUniformCLM a ha u).coeFn_toLp p volume

end InnerProductSpace

end Symbol

end TauCeti
