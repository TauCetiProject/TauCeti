/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.MetricSpace.Holder

/-!
# Quasilinear divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the quasilinear Dirichlet problem

`-(A(x, u) u')' = f + F'` in `(x₀, x₁)`, `u(x₀) = g₀`, `u(x₁) = g₁`,

where the coefficient `A(x, y)` is a Carathéodory function on `(x₀, x₁)`, measurable in `x` and,
for almost every `x`, continuous in `y`, and is uniformly elliptic and bounded, `λ ≤ A ≤ M` with
`λ > 0`, and the data are `f ∈ L¹` and `F ∈ Lᵖ`, `1 ≤ p ≤ ∞`. A solution is `u ∈ W^{1,p}(x₀, x₁)`
whose continuous representative `ū` takes the boundary values and satisfies

`∫ A(t, ū t) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

This file proves that a solution exists
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`). No uniqueness is claimed, and
none holds for general `A(x, u)`. Since the solution solves the linear equation with the measurable
coefficient `a = A(·, ū)`, with `λ ≤ a ≤ M`, the global Hölder estimate
`TauCeti.PDE.exists_norm_intervalRepresentativeL_le_and_holderWith` applies to it, with a constant
that does not depend on `A` beyond `λ` and `M`.

Weak solutions are classical as soon as `A` and the data are regular
(`TauCeti.PDE.contDiffOn_intervalRepresentativeL_and_exists_holderOnWith_of_forall_setIntegral_eq`).
If `0 < α ≤ 1`, `A` is differentiable on `(x₀, x₁) × ℝ` with `A ≥ λ` and a derivative that is
`α`-Hölder on `(x₀, x₁) × [-R, R]` for every `R`, `f` is `α`-Hölder and `F` has an `α`-Hölder
derivative `F'`, then every solution has `ū ∈ C²(x₀, x₁)` with `ū''` `α`-Hölder on `(x₀, x₁)`, and
`-(A(x, ū) ū')' = f + F'` holds pointwise. The proof bootstraps through the linear theory of
`TauCeti/Analysis/PDE/Regularity/Interval.lean` with the frozen coefficient `a = A(·, ū)`:
continuity of `a` makes `ū` a `C¹` function with bounded derivative; then `a` is differentiable with
`a' = ∂ₓA(·, ū) + ∂ᵤA(·, ū) ū'` continuous and bounded, so `ū` is `C²` with bounded `ū''`; then `ū'`
is Lipschitz, `a'` is `α`-Hölder, and `ū''` is `α`-Hölder.

## The argument for existence

The proof is Schauder's compact-map argument. For a fixed measurable coefficient `a` with
`λ ≤ a ≤ M`, the linear problem `-(a u')' = f + F'` with the same boundary values is solved
explicitly in `TauCeti/Analysis/PDE/DirichletProblem/Interval.lean`: the flux `a u' + F` has
derivative `-f`, so `a u' = k - Φ - F` with `Φ t = ∫_{x₀}^t f`, and the constant `k` is fixed by
`∫ u' = g₁ - g₀` (`TauCeti.PDE.intervalDirichletSolution`). Freezing `a = A(·, v)` for
`v ∈ C([x₀, x₁])` defines a map `T` of `C([x₀, x₁])` into itself.

* `T` is continuous (`TauCeti.PDE.continuous_intervalDirichletSolution`): by dominated
  convergence, uniform convergence of `v` gives `L¹` convergence of the derivatives
  `a⁻¹ (k - Φ - F)`, hence uniform convergence of their primitives.
* `T` has relatively compact range
  (`TauCeti.PDE.isCompact_closure_range_intervalDirichletSolution`): since `∫ a⁻¹ ≥ (x₁ - x₀) / M`,
  every derivative is dominated by `λ⁻¹ (K + |Φ + F|)` with `K` independent of `v`, so the range of
  `T` is bounded and equicontinuous, and the Arzelà–Ascoli theorem applies.

Schauder's fixed-point theorem (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`) on a large
closed ball of `C([x₀, x₁])` then gives `u = T u`. By
`TauCeti.PDE.exists_w1p_intervalRepresentativeL_eq`, the fixed point is the continuous
representative of a Sobolev class solving the linear problem with coefficient `A(·, u)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 11.1 (Schauder's theorem) and Section 11.3 (the quasilinear Dirichlet problem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.4
  (one-dimensional boundary value problems).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped Distributions

namespace TauCeti.PDE

variable {x₀ x₁ lam M : ℝ} {G : ℝ → ℝ} {g₀ g₁ : ℝ}

/-- **The fixed point of the solution map.** Let `a v` be a coefficient depending on
`v ∈ C([x₀, x₁])`, with uniform bounds `λ ≤ a v ≤ M`, such that `a vₙ → a v` almost everywhere
whenever `vₙ → v`. Then for some `u ∈ C([x₀, x₁])`, `u` is the solution of the linear problem with
coefficient `a u`. -/
private theorem exists_intervalDirichletSolution_eq_self (hx : x₀ < x₁) (hlam : 0 < lam)
    {a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ}
    (ha : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M)
    (hlim : ∀ (vn : ℕ → C(Icc x₀ x₁, ℝ)) (v : C(Icc x₀ x₁, ℝ)), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)))
    (hG : IntegrableOn G (Ioo x₀ x₁))
    (hs : ∀ v, IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ G (a v)) (Ioo x₀ x₁)) :
    ∃ u, intervalDirichletSolution hx.le g₀ g₁ (hs u) = u := by
  have hcpt := isCompact_closure_range_intervalDirichletSolution hx hlam ha haM hG hs
  -- Schauder's fixed-point theorem on a closed ball of `C([x₀, x₁])` containing the range.
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall 0
  have hmem : ∀ v, intervalDirichletSolution hx.le g₀ g₁ (hs v) ∈ closedBall 0 R :=
    fun v => hR (subset_closure (mem_range_self v))
  obtain ⟨u, -, hu⟩ := schauderFixedPoint_closedConvex_continuousOn
    (C := closedBall (0 : C(Icc x₀ x₁, ℝ)) R) isClosed_closedBall (convex_closedBall _ _)
    (nonempty_closedBall.2 (dist_nonneg.trans (hmem 0)))
    (continuous_intervalDirichletSolution hx hlam ha (fun v => (haM v).mono fun _ h => h.1) hlim
      hG hs).continuousOn
    (fun v _ => hmem v) (hcpt.of_isClosed_subset isClosed_closure
      (closure_mono (image_subset_range _ _)))
  exact ⟨u, hu⟩

variable {p : ENNReal} [Fact (1 ≤ p)] {f F : ℝ → ℝ} {A : ℝ → ℝ → ℝ}

/-- **Existence for the quasilinear Dirichlet problem on an interval.** Let `x₀ < x₁` and let
`A : ℝ → ℝ → ℝ` be a Carathéodory function on `(x₀, x₁)`: `t ↦ A t y` is almost everywhere strongly
measurable on `(x₀, x₁)` for every `y`, and `A t` is continuous for almost every `t ∈ (x₀, x₁)`.
Assume `λ ≤ A t y ≤ M` for almost every `t ∈ (x₀, x₁)` and every `y`, where `λ > 0`. Let
`f ∈ L¹(x₀, x₁)`, `F ∈ Lᵖ(x₀, x₁)` with `1 ≤ p ≤ ∞`, and `g₀, g₁ ∈ ℝ`. Then there is
`u ∈ W^{1,p}(x₀, x₁)` whose continuous representative `ū` takes the boundary values `ū x₀ = g₀`,
`ū x₁ = g₁`, and which solves `-(A(x, u) u')' = f + F'` weakly:

`∫ A(t, ū t) u' φ' = ∫ f φ - ∫ F φ'` for every `φ ∈ C_c^∞(x₀, x₁)`. -/
theorem exists_intervalTraceL_eq_and_forall_setIntegral_eq (hx : x₀ < x₁) (hlam : 0 < lam)
    (hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g₀ g₁ : ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  -- Freeze the coefficient at `v ∈ C([x₀, x₁])`: `a v = A(·, v)`. It is measurable because `A`
  -- is a Carathéodory function.
  set a : C(Icc x₀ x₁, ℝ) → ℝ → ℝ := fun v t => A t (v (projIcc x₀ x₁ hx.le t))
  have ham : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)) := fun v =>
    (v.continuous.comp continuous_projIcc).aestronglyMeasurable.apply_of_forall_of_continuousAt
      hAm (hAc.mono fun _ ht => ht.continuousAt)
  have haM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M :=
    fun v => hA.mono fun _ ht => ht _
  have hlim : ∀ (vn : ℕ → C(Icc x₀ x₁, ℝ)) (v : C(Icc x₀ x₁, ℝ)), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)) :=
    fun vn v hv => hAc.mono fun _ ht =>
      (ht.tendsto _).comp (((continuous_eval_const _).tendsto v).comp hv)
  have hG : IntegrableOn (fun t => (∫ s in x₀..t, f s) + F t) (Ioo x₀ x₁) :=
    ((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)).integrableOn_Icc.mono_set Ioo_subset_Icc_self).add
      (hF.integrable Fact.out)
  -- A fixed point `ū` of the solution map solves the linear problem with coefficient `a ū`, and
  -- is the continuous representative of that solution.
  obtain ⟨ū, hū⟩ := exists_intervalDirichletSolution_eq_self hx hlam ham haM hlim hG fun v =>
    integrableOn_intervalDirichletSlope hlam g₀ g₁ (ham v) ((haM v).mono fun _ h => h.1) hG
  obtain ⟨u, hrep, htr, hweak⟩ := exists_w1p_intervalRepresentativeL_eq (p := p) hx hlam (ham ū)
    ((haM ū).mono fun _ h => h.1) hf hF g₀ g₁
  have hū' : W1p.intervalRepresentativeL hx u = ū := by
    ext y
    rw [hrep, ← DFunLike.congr_fun hū y, intervalDirichletSolution_apply]
  exact ⟨u, htr, by rwa [hū']⟩

/-! ### Regularity -/

section Regularity

open Function
open scoped NNReal

/-- On a bounded rectangle where `A` is differentiable with a Hölder derivative, the derivative and
`A` itself are bounded. -/
private theorem exists_norm_fderiv_le_and_abs_le {α KA R : ℝ≥0}
    (hA : DifferentiableOn ℝ (uncurry A) (Ioo x₀ x₁ ×ˢ univ))
    (hKA : HolderOnWith KA α (fderiv ℝ (uncurry A)) (Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R)) :
    ∃ MG MA : ℝ, (∀ q ∈ Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R,
      HasFDerivAt (uncurry A) (fderiv ℝ (uncurry A) q) q) ∧
      (∀ q ∈ Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R, ‖fderiv ℝ (uncurry A) q‖ ≤ MG) ∧
      ∀ q ∈ Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R, |uncurry A q| ≤ MA := by
  have hS : Bornology.IsBounded (Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R) :=
    (isBounded_Ioo x₀ x₁).prod (isBounded_Icc _ _)
  obtain ⟨MG, hMG⟩ := isBounded_iff_forall_norm_le.1 (hKA.isBounded_image hS)
  have hdA : ∀ q ∈ Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R,
      HasFDerivAt (uncurry A) (fderiv ℝ (uncurry A) q) q := fun q hq ↦
    (hA.differentiableAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hq.1, trivial⟩)).hasFDerivAt
  have hAL : LipschitzOnWith MG.toNNReal (uncurry A) (Ioo x₀ x₁ ×ˢ Icc (-(R : ℝ)) R) :=
    ((convex_Ioo x₀ x₁).prod (convex_Icc _ _)).lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
      (fun q hq ↦ (hdA q hq).hasFDerivWithinAt) fun q hq ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm]
        exact (hMG _ ⟨q, hq, rfl⟩).trans (Real.le_coe_toNNReal MG)
  obtain ⟨MA, hMA⟩ := isBounded_iff_forall_norm_le.1 (hAL.holderOnWith.isBounded_image hS)
  exact ⟨MG, MA, hdA, fun q hq ↦ hMG _ ⟨q, hq, rfl⟩, fun q hq ↦ hMA _ ⟨q, hq, rfl⟩⟩

/-- A Hölder datum `f` and a differentiable `F` with Hölder derivative are bounded, continuous and
integrable on `(x₀, x₁)`. -/
private theorem exists_norm_le_and_integrableOn {α Kf KF : ℝ≥0} (hα₀ : 0 < α) {F' : ℝ → ℝ}
    (hf : HolderOnWith Kf α f (Ioo x₀ x₁)) (hF : ∀ t ∈ Ioo x₀ x₁, HasDerivAt F (F' t) t)
    (hF' : HolderOnWith KF α F' (Ioo x₀ x₁)) :
    ∃ Mf MF' MF : ℝ, (∀ t ∈ Ioo x₀ x₁, ‖f t‖ ≤ Mf) ∧ (∀ t ∈ Ioo x₀ x₁, ‖F' t‖ ≤ MF') ∧
      (∀ t ∈ Ioo x₀ x₁, ‖F t‖ ≤ MF) ∧ ContinuousOn F (Ioo x₀ x₁) ∧
      IntegrableOn f (Ioo x₀ x₁) ∧ IntegrableOn F (Ioo x₀ x₁) := by
  obtain ⟨Mf, hMf⟩ := isBounded_iff_forall_norm_le.1 (hf.isBounded_image (isBounded_Ioo x₀ x₁))
  obtain ⟨MF', hMF'⟩ :=
    isBounded_iff_forall_norm_le.1 (hF'.isBounded_image (isBounded_Ioo x₀ x₁))
  have hFL : LipschitzOnWith MF'.toNNReal F (Ioo x₀ x₁) :=
    (convex_Ioo x₀ x₁).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
      (fun t ht ↦ (hF t ht).hasDerivWithinAt) fun t ht ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm]
        exact (hMF' _ ⟨t, ht, rfl⟩).trans (Real.le_coe_toNNReal MF')
  obtain ⟨MF, hMF⟩ :=
    isBounded_iff_forall_norm_le.1 (hFL.holderOnWith.isBounded_image (isBounded_Ioo x₀ x₁))
  have hFc : ContinuousOn F (Ioo x₀ x₁) := fun t ht ↦ (hF t ht).continuousAt.continuousWithinAt
  refine ⟨Mf, MF', MF, fun t ht ↦ hMf _ ⟨t, ht, rfl⟩, fun t ht ↦ hMF' _ ⟨t, ht, rfl⟩,
    fun t ht ↦ hMF _ ⟨t, ht, rfl⟩, hFc, ?_, ?_⟩
  · exact IntegrableOn.of_bound measure_Ioo_lt_top
      ((hf.continuousOn hα₀).aestronglyMeasurable measurableSet_Ioo) Mf
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ hMf _ ⟨t, ht, rfl⟩)
  · exact IntegrableOn.of_bound measure_Ioo_lt_top (hFc.aestronglyMeasurable measurableSet_Ioo) MF
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ hMF _ ⟨t, ht, rfl⟩)

/-- The first step of the bootstrap: for a continuous bounded elliptic coefficient `a`, the
continuous representative of a weak solution of `-(a u')' = f + F'` has a continuous bounded
derivative on `(x₀, x₁)`. -/
private theorem exists_hasDerivAt_and_norm_le_of_forall_integral_eq (hx : x₀ < x₁)
    (hlam : 0 < lam) {a : ℝ → ℝ} {MA Mf MF : ℝ} (hac : ContinuousOn a (Ioo x₀ x₁))
    (hla : ∀ t ∈ Ioo x₀ x₁, lam ≤ a t) (haM : ∀ t ∈ Ioo x₀ x₁, |a t| ≤ MA)
    (hfi : IntegrableOn f (Ioo x₀ x₁)) (hMf : ∀ t ∈ Ioo x₀ x₁, ‖f t‖ ≤ Mf)
    (hFc : ContinuousOn F (Ioo x₀ x₁)) (hFi : IntegrableOn F (Ioo x₀ x₁))
    (hMF : ∀ t ∈ Ioo x₀ x₁, ‖F t‖ ≤ MF) {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ q : ℝ → ℝ, ∃ Mq : ℝ, (∀ t ∈ Ioo x₀ x₁,
      HasDerivAt (fun s ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le s)) (q t) t) ∧
      ContinuousOn q (Ioo x₀ x₁) ∧ ∀ t ∈ Ioo x₀ x₁, ‖q t‖ ≤ Mq := by
  have ha0 : ∀ t ∈ Ioo x₀ x₁, a t ≠ 0 := fun t ht ↦ (hlam.trans_le (hla t ht)).ne'
  obtain ⟨k, hk⟩ := exists_hasDerivAt_intervalRepresentativeL_of_forall_integral_eq hx hac ha0 haM
    hfi hFi hFc hu
  have hΦc : ContinuousOn (fun t ↦ ∫ s in x₀..t, f s) (Ioo x₀ x₁) :=
    (intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hfi
      (left_mem_Icc.2 hx.le)).mono Ioo_subset_Icc_self
  refine ⟨_, (|k| + Mf * (x₁ - x₀) + MF) / lam, hk,
    ((continuousOn_const.sub hΦc).sub hFc).div hac ha0, fun t ht ↦ ?_⟩
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf t ht)
  have hMF0 : 0 ≤ MF := (norm_nonneg _).trans (hMF t ht)
  have : 0 ≤ x₁ - x₀ := sub_nonneg.2 hx.le
  have hΦ : ‖∫ s in x₀..t, f s‖ ≤ Mf * (x₁ - x₀) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀) (b := t) (C := Mf)
      fun s hs ↦ ?_).trans ?_
    · rw [uIoc_of_le ht.1.le] at hs
      exact hMf s ⟨hs.1, hs.2.trans_lt ht.2⟩
    · rw [abs_of_pos (sub_pos.2 ht.1)]
      gcongr
      exact ht.2.le
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
  refine div_le_div₀ (by positivity) ?_ hlam ((hla t ht).trans (le_abs_self _))
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add le_rfl ?_)) ?_)
  · simpa [Real.norm_eq_abs] using hΦ
  · simpa [Real.norm_eq_abs] using hMF t ht

/-- The second step of the bootstrap: a `C²` function on `(x₀, x₁)` with bounded second derivative
has a Lipschitz derivative there. -/
private theorem lipschitzOnWith_deriv_of_contDiffOn {U : ℝ → ℝ} {M : ℝ}
    (hU : ContDiffOn ℝ 2 U (Ioo x₀ x₁)) (hM : ∀ t ∈ Ioo x₀ x₁, |deriv (deriv U) t| ≤ M) :
    LipschitzOnWith M.toNNReal (deriv U) (Ioo x₀ x₁) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] at hU
  exact (convex_Ioo x₀ x₁).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
    (fun t ht ↦ ((hU.2.2.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds ht)).hasDerivAt.hasDerivWithinAt) fun t ht ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs]
        exact (hM t ht).trans (Real.le_coe_toNNReal _)

/-- The third step of the bootstrap: if the derivative `G` of `A` is `α`-Hölder and bounded on a
set containing the graph of a Lipschitz `U`, and `q` is Lipschitz and bounded, then
`t ↦ G (t, U t) (1, q t)` is `α`-Hölder. -/
private theorem exists_holderOnWith_apply_prodMk {α KA KU Kq : ℝ≥0} (hα : α ≤ 1)
    {S : Set (ℝ × ℝ)} {G : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ} {U q : ℝ → ℝ} {MG Mq : ℝ}
    (hG : HolderOnWith KA α G S) (hGM : ∀ z ∈ S, ‖G z‖ ≤ MG)
    (hUS : ∀ t ∈ Ioo x₀ x₁, (t, U t) ∈ S) (hU : LipschitzOnWith KU U (Ioo x₀ x₁))
    (hq : LipschitzOnWith Kq q (Ioo x₀ x₁)) (hqM : ∀ t ∈ Ioo x₀ x₁, ‖q t‖ ≤ Mq) :
    ∃ K : ℝ≥0, HolderOnWith K α (fun t ↦ G (t, U t) ((1 : ℝ), q t)) (Ioo x₀ x₁) := by
  have hGU : HolderOnWith (KA * (max 1 KU) ^ (α : ℝ)) α (fun t ↦ G (t, U t)) (Ioo x₀ x₁) := by
    simpa only [mul_one, Function.comp_def, id] using hG.comp
      ((LipschitzWith.id.lipschitzOnWith (s := Ioo x₀ x₁)).prodMk hU).holderOnWith hUS
  have hvM : ∀ t ∈ Ioo x₀ x₁, ‖((1 : ℝ), q t)‖ ≤ (max 1 Mq).toNNReal := fun t ht ↦ by
    rw [Prod.norm_mk, norm_one]
    exact (max_le_max le_rfl (hqM t ht)).trans (Real.le_coe_toNNReal _)
  have hv := ((LipschitzWith.const (1 : ℝ)).lipschitzOnWith (s := Ioo x₀ x₁)).prodMk
    hq |>.holderOnWith_of_norm_le hvM hα
  exact ⟨_, (ContinuousLinearMap.id ℝ (ℝ × ℝ →L[ℝ] ℝ)).holderOnWith_comp₂ hGU hv
    (Mf := MG.toNNReal) (fun t ht ↦ (hGM _ (hUS t ht)).trans (Real.le_coe_toNNReal _)) hvM⟩

/-- **`C^{2,α}` regularity for the quasilinear problem on an interval.** Let `0 < α ≤ 1` and
`λ > 0`. Let `A` be differentiable on `(x₀, x₁) × ℝ` with `A ≥ λ` there, and let its derivative
be `α`-Hölder on `(x₀, x₁) × [-R, R]` for every `R`. Let `f` be `α`-Hölder on `(x₀, x₁)`, and let
`F` be differentiable there with an `α`-Hölder derivative `F'`. If `u ∈ W^{1,p}(x₀, x₁)` solves
`-(A(x, u) u')' = f + F'` weakly, then its continuous representative `ū` is `C²` on `(x₀, x₁)`,
solves the equation there classically, and `ū''` is `α`-Hölder on `(x₀, x₁)`. -/
theorem contDiffOn_intervalRepresentativeL_and_exists_holderOnWith_of_forall_setIntegral_eq
    (hx : x₀ < x₁) {α : ℝ≥0} (hα₀ : 0 < α) (hα : α ≤ 1) (hlam : 0 < lam)
    (hA : DifferentiableOn ℝ (uncurry A) (Ioo x₀ x₁ ×ˢ univ))
    (hAlam : ∀ t ∈ Ioo x₀ x₁, ∀ y, lam ≤ A t y)
    (hA' : ∀ R, ∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ (uncurry A)) (Ioo x₀ x₁ ×ˢ Icc (-R) R))
    {F' : ℝ → ℝ} {Kf KF : ℝ≥0} (hf : HolderOnWith Kf α f (Ioo x₀ x₁))
    (hF : ∀ t ∈ Ioo x₀ x₁, HasDerivAt F (F' t) t) (hF' : HolderOnWith KF α F' (Ioo x₀ x₁))
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ContDiffOn ℝ 2 (fun s ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le s))
        (Ioo x₀ x₁) ∧
      (∀ t ∈ Ioo x₀ x₁, -deriv (fun s ↦
        A s (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le s)) *
          deriv (fun s ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le s)) s) t =
          f t + F' t) ∧
      ∃ K : ℝ≥0, HolderOnWith K α
        (deriv (deriv fun s ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le s)))
        (Ioo x₀ x₁) := by
  set ū := W1p.intervalRepresentativeL hx u
  have hUR : ∀ s, ū (projIcc x₀ x₁ hx.le s) ∈ Icc (-(‖ū‖₊ : ℝ)) ‖ū‖₊ := fun s ↦
    abs_le.1 (by simpa [Real.norm_eq_abs] using ū.norm_coe_le_norm (projIcc x₀ x₁ hx.le s))
  have hUc : Continuous fun s ↦ ū (projIcc x₀ x₁ hx.le s) :=
    W1p.continuous_intervalRepresentativeL_projIcc hx u
  -- Bounds on the rectangle `S = (x₀, x₁) × [-R, R]` containing the graph of `ū`.
  obtain ⟨KA, hKA⟩ := hA' ‖ū‖₊
  obtain ⟨MG, MA, hdA, hGM, hAM⟩ := exists_norm_fderiv_le_and_abs_le hA hKA
  have hγS : ∀ t ∈ Ioo x₀ x₁, (t, ū (projIcc x₀ x₁ hx.le t)) ∈ Ioo x₀ x₁ ×ˢ
      Icc (-(‖ū‖₊ : ℝ)) ‖ū‖₊ := fun t ht ↦ ⟨ht, hUR t⟩
  obtain ⟨Mf, MF', MF, hMf, hMF', hMF, hFc, hfi, hFi⟩ :=
    exists_norm_le_and_integrableOn hα₀ hf hF hF'
  -- First pass: `ū` is `C¹` with a continuous bounded derivative `q`.
  obtain ⟨q, Mq, hUq, hqc, hqM⟩ := exists_hasDerivAt_and_norm_le_of_forall_integral_eq hx hlam
    (hA.continuousOn.comp (continuous_id.prodMk hUc).continuousOn fun t ht ↦ ⟨ht, trivial⟩)
    (fun t ht ↦ hAlam t ht _) (fun t ht ↦ hAM _ (hγS t ht)) hfi hMf hFc hFi hMF hu
  -- The derivative of the coefficient, `a' = ∂ₜA + ∂ᵤA ū'`, is continuous and bounded.
  set G := fderiv ℝ (uncurry A)
  have ha : ∀ t ∈ Ioo x₀ x₁, HasDerivAt (fun s ↦ A s (ū (projIcc x₀ x₁ hx.le s)))
      (G (t, ū (projIcc x₀ x₁ hx.le t)) ((1 : ℝ), q t)) t := fun t ht ↦
    (hdA _ (hγS t ht)).comp_hasDerivAt (f := fun s ↦ (s, ū (projIcc x₀ x₁ hx.le s))) t
      ((hasDerivAt_id' t).prodMk (hUq t ht))
  have ha'M : ∀ t ∈ Ioo x₀ x₁,
      |G (t, ū (projIcc x₀ x₁ hx.le t)) ((1 : ℝ), q t)| ≤ (MG * max 1 Mq).toNNReal := fun t ht ↦
    (((G _).le_opNorm _).trans (mul_le_mul (hGM _ (hγS t ht))
      (by rw [Prod.norm_mk, norm_one]; exact max_le_max le_rfl (hqM t ht)) (norm_nonneg _)
      ((norm_nonneg _).trans (hGM _ (hγS t ht))))).trans (Real.le_coe_toNNReal _)
  -- Second pass: `ū` is `C²` with bounded `ū''`, so `ū' = q` is Lipschitz.
  obtain ⟨h2, -, Mdd, hMdd⟩ :=
    contDiffOn_intervalRepresentativeL_and_exists_abs_le_of_forall_integral_eq hx hlam ha
    (fun t ht ↦ hAlam t ht _)
    (((hKA.continuousOn hα₀).comp (continuous_id.prodMk hUc).continuousOn hγS).clm_apply
      (continuousOn_const.prodMk hqc)) ha'M (hf.continuousOn hα₀)
    (Mf := Mf.toNNReal) (fun t ht ↦ (hMf t ht).trans (Real.le_coe_toNNReal _)) hF
    (hF'.continuousOn hα₀) (MF' := MF'.toNNReal)
    (fun t ht ↦ (hMF' t ht).trans (Real.le_coe_toNNReal _)) hu
  have hqL : LipschitzOnWith Mdd.toNNReal q (Ioo x₀ x₁) := fun s hs t ht ↦ by
    rw [← (hUq s hs).deriv, ← (hUq t ht).deriv]
    exact lipschitzOnWith_deriv_of_contDiffOn h2 hMdd hs ht
  -- Third pass: `a'` is `α`-Hölder, so `ū''` is `α`-Hölder.
  obtain ⟨K, ha'H⟩ := exists_holderOnWith_apply_prodMk hα hKA hGM hγS
    ((convex_Ioo x₀ x₁).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
      (fun t ht ↦ (hUq t ht).hasDerivWithinAt) (C := Mq.toNNReal) fun t ht ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm]
        exact (hqM t ht).trans (Real.le_coe_toNNReal _)) hqL hqM
  exact contDiffOn_intervalRepresentativeL_and_exists_holderOnWith_of_forall_integral_eq hx hα₀ hα
    hlam ha (fun t ht ↦ hAlam t ht _) ha'H hf hF hF' hu

end Regularity

end TauCeti.PDE
