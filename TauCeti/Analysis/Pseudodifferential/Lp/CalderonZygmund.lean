/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.StandardKernel
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import TauCeti.Analysis.Normed.Lp.SmoothApprox
import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint
import TauCeti.MeasureTheory.Measure.LocallyNull
import TauCeti.Topology.MetricSpace.Thickening

/-!
# `Lᵖ` boundedness of uniform symbols of order zero

Let `a` be a symbol of order `0` on `ℝⁿ`, with values in operators `V →L[ℂ] W` between complex
Hilbert spaces, whose estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold uniformly in the
position (`TauCeti.Symbol.IsUniform`). This file proves that for every `1 < p < ∞` its
Kohn–Nirenberg quantization `Op(a)` is bounded in the `Lᵖ` norm:

`‖Op(a) u‖_p ≤ C ‖u‖_p` for every Schwartz function `u`

(`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`), so that it extends
to a bounded operator `Lᵖ(ℝⁿ; V) → Lᵖ(ℝⁿ; W)`
(`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp_of_one_lt`). These are the `Lᵖ` mapping
properties of pseudodifferential operators of order zero from which the order shifts on the
Bessel-potential spaces `H^{s,p}` follow.

## The argument

`Op(a)` is a Calderón–Zygmund operator, so the Calderón–Zygmund theorem
(`ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`) applies to the bounded extension
`T` of `Op(a)` to `L²` given by the Calderón–Vaillancourt theorem
(`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`). Its hypotheses are:

* the size and smoothness estimates of the off-diagonal kernel `K = offDiagonalKernel a` and of
  the kernel `(x, y) ↦ K(y, x)†`, which are
  `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_le` and the two smoothness estimates of
  `TauCeti.Analysis.Pseudodifferential.StandardKernel`;
* the representation of `T` and of its adjoint `T†` by these kernels away from the support of
  their argument.

The representation of `T` (`TauCeti.Symbol.IsUniform.ae_eq_integral_offDiagonalKernel`) is the
kernel representation of `Op(a)` on Schwartz functions,
`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`, extended to `L²` functions `f`
vanishing outside a compact set `s`. On a compact set `A` disjoint from `s`, the kernel cut off to
`A × B`, for a closed thickening `B` of `s` at positive distance from `A`, is bounded and defines a
bounded integral operator `R` on `L²`. The smooth approximations of `f` supported in `B`
(`MeasureTheory.MemLp.exist_contDiff_tsupport_subset_eLpNorm_sub_le`) satisfy `T = R` on `A`, and
this passes to the limit.

The representation of `T†` (`TauCeti.Symbol.IsUniform.adjoint_ae_eq_integral_offDiagonalKernel`)
follows by duality: on `A`, `T† g` and `R† g` have the same pairing with every `φ ∈ L²` vanishing
outside `A`, since `T φ = R φ` on `s` and `g` vanishes outside `s`; pairing with `1_A (T† g - R† g)`
gives `T† g = R† g` on `A`. The adjoint `R†` is the integral operator with the adjoint kernel
(`TauCeti.adjoint_integralOperatorLp`).

## Main results

* `TauCeti.Symbol.IsUniform.exists_eLpNorm_le_of_ae_eq_quantizeSchwartzValue`: the `L²` extension
  of `Op(a)` satisfies `‖T f‖_p ≤ C ‖f‖_p`.
* `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`: the `Lᵖ` bound on
  Schwartz functions.
* `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp_of_one_lt`: the bounded extension to `Lᵖ`.

## References

* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §5
  (pseudodifferential operators of order zero as singular integrals, and their `Lᵖ` bounds).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture II, §1.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Function ContinuousLinearMap
open scoped ENNReal NNReal SchwartzMap Topology InnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W 0}

/-! ### Bounds for the kernel away from the diagonal -/

/-- The size estimate `‖K(x, y)‖ ≤ C ‖x - y‖⁻ⁿ` of the kernel of a uniform symbol of order `0`, in
every dimension: in dimension `0` there are no pairs of distinct points. -/
private theorem IsUniform.exists_norm_offDiagonalKernel_le_rpow (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ x y : CoordinateSpace n, x ≠ y →
      ‖offDiagonalKernel a x y‖ ≤ C * dist x y ^ (-(n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, le_rfl, fun x y hxy ↦ (hxy (Subsingleton.elim x y)).elim⟩
  · obtain ⟨C, hC0, hC⟩ := ha.exists_norm_offDiagonalKernel_le (by rw [zero_add]; exact_mod_cast hn)
    exact ⟨C, hC0, fun x y hxy ↦ by simpa [dist_eq_norm] using hC x y hxy⟩

/-- The kernel of `a` cut off to `A × B`: it is `K(x, y)` for `x ∈ A` and `y ∈ B`, and `0`
otherwise. -/
private def truncKernel (a : Symbol n V W 0) (A B : Set (CoordinateSpace n))
    (x y : CoordinateSpace n) : V →L[ℂ] W :=
  A.indicator (fun x ↦ B.indicator (offDiagonalKernel a x) y) x

omit [CompleteSpace V] [CompleteSpace W] in
private theorem truncKernel_of_mem {A B : Set (CoordinateSpace n)} {x y : CoordinateSpace n}
    (hx : x ∈ A) (hy : y ∈ B) : truncKernel a A B x y = offDiagonalKernel a x y := by
  simp [truncKernel, hx, hy]

omit [CompleteSpace V] [CompleteSpace W] in
/-- Against a function vanishing outside `B`, the cut-off kernel acts like the kernel at points
of `A`. -/
private theorem truncKernel_apply_eq_of_mem {A B : Set (CoordinateSpace n)}
    {x y : CoordinateSpace n} (hx : x ∈ A) {v : V} (hv : y ∉ B → v = 0) :
    truncKernel a A B x y v = offDiagonalKernel a x y v := by
  by_cases hy : y ∈ B
  · rw [truncKernel_of_mem hx hy]
  · rw [hv hy, map_zero, map_zero]

omit [CompleteSpace V] [CompleteSpace W] in
/-- Against a function vanishing outside `B`, integrating the cut-off kernel at a point of `A` is
integrating the kernel. -/
private theorem integral_truncKernel_apply_eq {A B : Set (CoordinateSpace n)}
    {x : CoordinateSpace n} (hx : x ∈ A) {g : CoordinateSpace n → V}
    (hg : ∀ᵐ y, y ∉ B → g y = 0) :
    ∫ y, truncKernel a A B x y (g y) = ∫ y, offDiagonalKernel a x y (g y) :=
  integral_congr_ae (hg.mono fun _ hy ↦ truncKernel_apply_eq_of_mem hx hy)

/-- On bounded measurable sets `A` and `B` at distance at least `r > 0`, the cut-off kernel defines
a bounded integral operator `R` on `L²`, with the cut-off adjoint kernel defining `R†`. -/
private theorem IsUniform.exists_integralOperator_truncKernel (ha : a.IsUniform)
    {A B : Set (CoordinateSpace n)} (hA : MeasurableSet A) (hA' : Bornology.IsBounded A)
    (hB : MeasurableSet B) (hB' : Bornology.IsBounded B) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) :
    ∃ R : Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W 2 volume,
      (∀ f, R f =ᵐ[volume] fun x ↦ ∫ y, truncKernel a A B x y (f y)) ∧
      ∀ g, adjoint R g =ᵐ[volume] fun y ↦ ∫ x, adjoint (truncKernel a A B x y) (g x) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_offDiagonalKernel_le_rpow
  set c := ENNReal.ofReal (C * r ^ (-(n : ℝ)))
  have hle (x y : CoordinateSpace n) :
      ‖truncKernel a A B x y‖ₑ ≤ A.indicator (fun _ ↦ B.indicator (fun _ ↦ c) y) x := by
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy := hsep x hx y hy
        rw [truncKernel_of_mem hx hy, indicator_of_mem hx, indicator_of_mem hy, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ((hC x y (dist_pos.1 (hr.trans_le hxy))).trans ?_)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hr hxy (neg_nonpos.2 n.cast_nonneg)) hC0
      · simp only [truncKernel, indicator_of_mem hx, indicator_of_notMem hy, ← ofReal_norm,
          norm_zero, ENNReal.ofReal_zero, le_refl]
    · simp only [truncKernel, indicator_of_notMem hx, ← ofReal_norm, norm_zero,
        ENNReal.ofReal_zero, le_refl]
  have hK : AEStronglyMeasurable (uncurry (truncKernel a A B)) (volume.prod volume) := by
    have : uncurry (truncKernel a A B) = (A ×ˢ B).indicator (uncurry (offDiagonalKernel a)) := by
      ext1 ⟨x, y⟩
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;> simp [truncKernel, hx, hy]
    rw [this]
    exact ((stronglyMeasurable_uncurry_offDiagonalKernel a).indicator
      (hA.prod hB)).aestronglyMeasurable
  have hrow : c * volume B ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB'.measure_lt_top.ne
  have hcol : c * volume A ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA'.measure_lt_top.ne
  have hA₀ : ∀ᵐ x, ∫⁻ y, ‖truncKernel a A B x y‖ₑ ≤ ((c * volume B).toNNReal : ℝ≥0∞) :=
    .of_forall fun x ↦ (ENNReal.coe_toNNReal hrow).symm ▸
      lintegral_enorm_row_le_of_le_indicator hB hle x
  have hB₀ : ∀ᵐ y, ∫⁻ x, ‖truncKernel a A B x y‖ₑ ≤ ((c * volume A).toNNReal : ℝ≥0∞) :=
    .of_forall fun y ↦ (ENNReal.coe_toNNReal hcol).symm ▸
      lintegral_enorm_column_le_of_le_indicator hA hle y
  refine ⟨integralOperatorLp (truncKernel a A B) 2 hK hA₀ hB₀, coeFn_integralOperatorLp, fun g ↦ ?_⟩
  rw [adjoint_integralOperatorLp]
  exact coeFn_integralOperatorLp g

/-! ### Kernel representation of the `L²` extension and of its adjoint -/

variable {T : Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
  Lp W 2 (volume : Measure (CoordinateSpace n))}

/-- If `T` is the bounded extension of `Op(a)` to `L²` and `f ∈ L²` vanishes outside a compact set
`s`, then on every compact set `A` disjoint from `s`, `T f` is given by the kernel of `Op(a)`. -/
private theorem IsUniform.ae_restrict_eq_integral_offDiagonalKernel (ha : a.IsUniform)
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    {s A : Set (CoordinateSpace n)} (hs : IsCompact s) (hA : IsCompact A) (hAs : Disjoint A s)
    (f : Lp V 2 volume) (hf : ∀ᵐ y, y ∉ s → f y = 0) :
    T f =ᵐ[volume.restrict A] fun x ↦ ∫ y, offDiagonalKernel a x y (f y) := by
  obtain ⟨δ, hδ, hdisj⟩ := hAs.exists_thickenings hA hs.isClosed
  -- The closed `δ / 2`-thickening `B` of `s` is at distance at least `δ / 2` from `A`.
  set B := cthickening (δ / 2) s
  have hB : IsCompact B := hs.cthickening
  have hsep : ∀ x ∈ A, ∀ y ∈ B, δ / 2 ≤ dist x y := fun _ hx _ hy ↦
    hdisj.half_le_dist_of_mem_cthickening hδ hx hy
  obtain ⟨R, hR, -⟩ := ha.exists_integralOperator_truncKernel hA.measurableSet hA.isBounded
    hB.measurableSet hB.isBounded (half_pos hδ) hsep
  -- On `A`, `R g` is given by the kernel for every `g` vanishing outside `B`.
  have hRB (g : Lp V 2 volume) (hg : ∀ᵐ y, y ∉ B → g y = 0) :
      R g =ᵐ[volume.restrict A] fun x ↦ ∫ y, offDiagonalKernel a x y (g y) := by
    filter_upwards [ae_restrict_of_ae (hR g), ae_restrict_mem hA.measurableSet] with x hx hxA
    rw [hx, integral_truncKernel_apply_eq hxA hg]
  -- The set of `g` with `T g = R g` on `A` is closed,
  set P := LpToLpRestrictCLM (CoordinateSpace n) W ℂ volume 2 A
  have hP (h : Lp W 2 volume) : P h = 0 ↔ h =ᵐ[volume.restrict A] 0 :=
    LpToLpRestrictCLM_eq_zero_iff A h
  have hclosed : IsClosed {g | P ((T - R) g) = 0} :=
    isClosed_eq (P.continuous.comp (T - R).continuous) continuous_const
  -- and contains the smooth approximations of `f` supported in `B`, so it contains `f`.
  choose g hgc hgs hgB hgf using fun k : ℕ ↦
    (Lp.memLp f).exist_contDiff_tsupport_subset_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two
      hs.isClosed (cthickening_mem_nhdsSet s (half_pos hδ)) hf (Nat.one_div_pos_of_nat (n := k))
  have hg (j : ℕ) : MemLp (g j) 2 volume := (hgs j).continuous.memLp_of_hasCompactSupport (hgc j)
  have hlim : Tendsto (fun j ↦ (hg j).toLp (g j)) atTop (𝓝 f) := by
    rw [← Lp.toLp_coeFn f (Lp.memLp f), Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ bot_le)
      fun k ↦ (eLpNorm_sub_comm _ _ _ _).trans_le (hgf k)
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmem (j : ℕ) : P ((T - R) ((hg j).toLp (g j))) = 0 := by
    set u := (hgc j).toSchwartzMap (hgs j)
    have hu : ⇑u = g j := funext ((hgc j).toSchwartzMap_toFun (hgs j))
    have hj : (hg j).toLp (g j) = u.toLp 2 :=
      Lp.ext ((MemLp.coeFn_toLp _).trans (hu ▸ u.coeFn_toLp 2 volume).symm)
    have huB (y : CoordinateSpace n) (hy : y ∉ B) : u y = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (hgB j (hu ▸ h))
    rw [hP, hj, sub_apply]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (T (u.toLp 2)) (R (u.toLp 2))),
      ae_restrict_of_ae (hT u), hRB _ ((u.coeFn_toLp 2 volume).mono fun y hy hyB ↦ by
        rw [hy, huB y hyB]), ae_restrict_mem hA.measurableSet] with x hsub hTx hRx hxA
    rw [hsub, Pi.sub_apply, hTx, hRx, Pi.zero_apply, sub_eq_zero,
      quantizeSchwartzValue_eq_integral_offDiagonalKernel a (hu ▸ hgc j)
        fun hx ↦ (hsep x hxA x (hgB j (hu ▸ hx))).not_gt (by simpa using half_pos hδ)]
    exact integral_congr_ae ((u.coeFn_toLp 2 volume).mono fun y hy ↦ by simp only [hy])
  have hf' := (hP _).1 (hclosed.mem_of_tendsto hlim (.of_forall hmem))
  filter_upwards [hf', ae_restrict_of_ae (Lp.coeFn_sub (T f) (R f)),
    hRB f (hf.mono fun y hy hyB ↦ hy fun hys ↦ hyB (self_subset_cthickening s hys))]
    with x hx hsub hRx
  rw [sub_apply, hsub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
  rw [hx, hRx]

/-- **Kernel representation of the `L²` extension.** If `T` is the bounded extension of `Op(a)`
to `L²` and `f ∈ L²` vanishes outside a compact set `s`, then
`T f (x) = ∫ K(x, y) f(y) dy` for almost every `x ∉ s`, where `K` is the off-diagonal kernel of
`Op(a)`. -/
theorem IsUniform.ae_eq_integral_offDiagonalKernel (ha : a.IsUniform)
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    {s : Set (CoordinateSpace n)} (hs : IsCompact s) (f : Lp V 2 volume)
    (hf : ∀ᵐ y, y ∉ s → f y = 0) :
    ∀ᵐ x, x ∉ s → T f x = ∫ y, offDiagonalKernel a x y (f y) :=
  ae_notMem_imp_of_forall_isCompact hs.isClosed fun _ hA hAs ↦
    ha.ae_restrict_eq_integral_offDiagonalKernel hT hs hA hAs f hf

/-- If `T` is the bounded extension of `Op(a)` to `L²` and `g ∈ L²` vanishes outside a compact set
`s`, then on every compact set `A` disjoint from `s`, `T† g` is given by the adjoint kernel. -/
private theorem IsUniform.adjoint_ae_restrict_eq_integral_offDiagonalKernel (ha : a.IsUniform)
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    {s A : Set (CoordinateSpace n)} (hs : IsCompact s) (hA : IsCompact A) (hAs : Disjoint A s)
    (g : Lp W 2 volume) (hg : ∀ᵐ x, x ∉ s → g x = 0) :
    adjoint T g =ᵐ[volume.restrict A] fun y ↦ ∫ x, adjoint (offDiagonalKernel a x y) (g x) := by
  obtain ⟨δ, hδ, hdisj⟩ := hAs.exists_thickenings hA hs.isClosed
  -- The closed `δ / 2`-thickening `B` of `A` is at distance at least `δ / 2` from `s`.
  set B := cthickening (δ / 2) A
  have hB : IsCompact B := hA.cthickening
  have hsep : ∀ x ∈ s, ∀ y ∈ B, δ / 2 ≤ dist x y := fun _ hx _ hy ↦
    hdisj.symm.half_le_dist_of_mem_cthickening hδ hx hy
  obtain ⟨R, hR, hR'⟩ := ha.exists_integralOperator_truncKernel hs.measurableSet hs.isBounded
    hB.measurableSet hB.isBounded (half_pos hδ) hsep
  -- `T φ = R φ` on `s` for every `φ` vanishing outside `A`.
  have hTR (φ : Lp V 2 volume) (hφ : ∀ᵐ y, y ∉ A → φ y = 0) : ∀ᵐ x, x ∈ s → T φ x = R φ x := by
    filter_upwards [(ae_restrict_iff' hs.measurableSet).1
      (ha.ae_restrict_eq_integral_offDiagonalKernel hT hA hs hAs.symm φ hφ), hR φ]
      with x hTx hRx hx
    rw [hTx hx, hRx, integral_truncKernel_apply_eq hx
      (hφ.mono fun y hy hyB ↦ hy fun hyA ↦ hyB (self_subset_cthickening A hyA))]
  -- Hence `T† g - R† g` is orthogonal to every `φ` vanishing outside `A`, so it vanishes on `A`.
  have hd := L2.ae_restrict_eq_zero_of_forall_inner_eq_zero (𝕜 := ℂ) hA.measurableSet
    (adjoint T g - adjoint R g) fun φ hφ ↦ by
      rw [inner_sub_right, adjoint_inner_right, adjoint_inner_right, sub_eq_zero, L2.inner_def,
        L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hTR φ hφ, hg] with x h₁ h₂
      by_cases hxs : x ∈ s
      · rw [h₁ hxs]
      · rw [h₂ hxs, inner_zero_right, inner_zero_right]
  -- On `A`, `T† g = R† g`, and `R† g` is given by the adjoint kernel.
  filter_upwards [hd, ae_restrict_of_ae (Lp.coeFn_sub (adjoint T g) (adjoint R g)),
    ae_restrict_of_ae (hR' g), ae_restrict_mem hA.measurableSet] with y hy0 hsub hRy hyA
  have hTR' : adjoint T g y = adjoint R g y := sub_eq_zero.1 (hsub.symm.trans hy0)
  rw [hTR', hRy]
  refine integral_congr_ae ?_
  filter_upwards [hg] with x hx
  by_cases hxs : x ∈ s
  · rw [truncKernel_of_mem hxs (self_subset_cthickening A hyA)]
  · rw [hx hxs, map_zero, map_zero]

/-- **Kernel representation of the adjoint of the `L²` extension.** If `T` is the bounded
extension of `Op(a)` to `L²` and `g ∈ L²` vanishes outside a compact set `s`, then
`T† g (y) = ∫ K(x, y)† g(x) dx` for almost every `y ∉ s`, where `K` is the off-diagonal kernel of
`Op(a)`. -/
theorem IsUniform.adjoint_ae_eq_integral_offDiagonalKernel (ha : a.IsUniform)
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    {s : Set (CoordinateSpace n)} (hs : IsCompact s) (g : Lp W 2 volume)
    (hg : ∀ᵐ x, x ∉ s → g x = 0) :
    ∀ᵐ y, y ∉ s → adjoint T g y = ∫ x, adjoint (offDiagonalKernel a x y) (g x) :=
  ae_notMem_imp_of_forall_isCompact hs.isClosed fun _ hA hAs ↦
    ha.adjoint_ae_restrict_eq_integral_offDiagonalKernel hT hs hA hAs g hg

/-! ### The `Lᵖ` bounds -/

/-- **`Lᵖ` bounds for the `L²` extension of `Op(a)`.** If `T` is the bounded extension to `L²` of
the quantization of a uniform symbol `a` of order `0`, then for every `1 < p < ∞` there is a
constant `C` with `‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L²`. This is the Calderón–Zygmund theorem
for `T`, whose kernel is a standard kernel. -/
theorem IsUniform.exists_eLpNorm_le_of_ae_eq_quantizeSchwartzValue (ha : a.IsUniform)
    (hT : ∀ u : 𝓢(CoordinateSpace n, V),
      T (u.toLp 2) =ᵐ[volume] quantizeSchwartzValue a.coefficient u)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : Lp V 2 volume, eLpNorm (T f) p volume ≤ C * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
  have hdim : (Module.finrank ℝ (CoordinateSpace n) : ℝ) = n := by simp
  obtain ⟨C₀, hC₀0, hC₀⟩ := ha.exists_norm_offDiagonalKernel_le_rpow
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_offDiagonalKernel_sub_right_le (δ := 1 / 2)
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨C', hC'0, hC'⟩ := ha.exists_norm_offDiagonalKernel_sub_left_le (δ := 1 / 2)
    (by norm_num) (by norm_num) (by positivity)
  have hadj : adjoint (T.restrictScalars ℝ) = (adjoint T).restrictScalars ℝ :=
    L2.adjoint_restrictScalars T
  have hKm := stronglyMeasurable_uncurry_offDiagonalKernel a
  have hrs := (restrictScalarsIsometry ℂ V W ℝ ℝ).continuous
  refine exists_eLpNorm_le_of_norm_sub_le_mul_rpow (V := CoordinateSpace n) (H := V) (K := W)
    (T.restrictScalars ℝ) (k := fun x y ↦ (offDiagonalKernel a x y).restrictScalars ℝ)
    (k' := fun x y ↦ (adjoint (offDiagonalKernel a y x)).restrictScalars ℝ)
    (hrs.comp_stronglyMeasurable hKm)
    ((restrictScalarsIsometry ℂ W V ℝ ℝ).continuous.comp_stronglyMeasurable
      ((adjoint (𝕜 := ℂ) (E := V) (F := W)).continuous.comp_stronglyMeasurable
        (hKm.comp_measurable measurable_swap)))
    (C₀ := C₀.toNNReal) (C₀' := C₀.toNNReal) (C := C.toNNReal) (C' := C'.toNNReal)
    (δ := 1 / 2) (δ' := 1 / 2) (by norm_num) (by norm_num) (fun x y hxy ↦ ?_) (fun x y hxy ↦ ?_)
    (fun x y y' h ↦ ?_) (fun x y y' h ↦ ?_)
    (fun f s hs hf ↦ ha.ae_eq_integral_offDiagonalKernel hT hs f hf)
    (fun g s hs hg ↦ hadj ▸ ha.adjoint_ae_eq_integral_offDiagonalKernel hT hs g hg) hp hp_top
  · rw [norm_restrictScalars, hdim, Real.coe_toNNReal _ hC₀0]
    exact hC₀ x y hxy
  · rw [norm_restrictScalars, LinearIsometryEquiv.norm_map, hdim, dist_comm,
      Real.coe_toNNReal _ hC₀0]
    exact hC₀ y x (Ne.symm hxy)
  · rw [← restrictScalars_sub, norm_restrictScalars]
    simpa [hdim, Real.coe_toNNReal _ hC0, dist_eq_norm, mul_assoc] using
      hC x y y' (by simpa [dist_eq_norm] using h)
  · rw [← restrictScalars_sub, ← map_sub, norm_restrictScalars, LinearIsometryEquiv.norm_map]
    simpa [hdim, Real.coe_toNNReal _ hC'0, dist_eq_norm, norm_sub_rev x y', mul_assoc] using
      hC' y y' x (by simpa [dist_eq_norm, norm_sub_rev x y'] using h)

/-- **`Lᵖ` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` between
complex Hilbert spaces whose estimates are uniform in the position, and every `1 < p < ∞`, there is
a constant `C` with `‖Op(a) u‖_p ≤ C ‖u‖_p` for every Schwartz function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt (ha : a.IsUniform)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) p volume ≤ C * eLpNorm u p volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZeroLp ha
  obtain ⟨C, hC⟩ := ha.exists_eLpNorm_le_of_ae_eq_quantizeSchwartzValue hT hp hp_top
  refine ⟨C, fun u ↦ ?_⟩
  have h := hC (u.toLp 2)
  rwa [eLpNorm_congr_ae (hT u), eLpNorm_congr_ae (u.coeFn_toLp 2 volume)] at h

/-- **The bounded extension of `Op(a)` to `Lᵖ`.** For a symbol `a` of order `0` between complex
Hilbert spaces whose estimates are uniform in the position, and every `1 < p < ∞`, the
quantization extends from Schwartz functions to a bounded operator `T : Lᵖ(ℝⁿ; V) → Lᵖ(ℝⁿ; W)`
with `T u = Op(a) u` almost everywhere for every Schwartz function `u`. -/
theorem exists_quantizeUniformOrderZeroLp_of_one_lt (a : Symbol n V W 0) (ha : a.IsUniform)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ T : Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W p volume,
      ∀ u : 𝓢(CoordinateSpace n, V),
        T (u.toLp p) =ᵐ[volume] quantizeSchwartzValue a.coefficient u := by
  obtain ⟨C, hC⟩ := ha.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt hp hp_top
  set e := SchwartzMap.toLpCLM ℂ V p (volume : Measure (CoordinateSpace n))
  set F := (SchwartzMap.toLpCLM ℂ W p (volume : Measure (CoordinateSpace n))).comp
    (quantizeUniformCLM a ha)
  have hdense : DenseRange e := SchwartzMap.denseRange_toLpCLM (F := V) hp_top
  have hnorm : ∃ C : ℝ, ∀ u, ‖F u‖ ≤ C * ‖e u‖ := by
    refine ⟨C, fun u ↦ ?_⟩
    simp only [F, e, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply,
      SchwartzMap.norm_toLp, coe_quantizeUniformCLM]
    rw [← ENNReal.coe_toReal, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ((u.memLp p volume).eLpNorm_ne_top)) (hC u)
  refine ⟨F.toLinearMap.extendOfNorm e.toLinearMap, fun u ↦ ?_⟩
  have h : F.toLinearMap.extendOfNorm e.toLinearMap (u.toLp p) = F u :=
    LinearMap.extendOfNorm_eq hdense hnorm u
  simp only [h, F, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply]
  simpa only [coe_quantizeUniformCLM] using (quantizeUniformCLM a ha u).coeFn_toLp p volume

end Symbol

end TauCeti
