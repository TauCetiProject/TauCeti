/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Quasilinear divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the quasilinear Dirichlet problem

`-(A(x, u) u')' = f + F'` on `(x₀, x₁)`, `u(x₀) = g.1`, `u(x₁) = g.2`,

where the coefficient `A(x, r)` is measurable in `x`, continuous in `r`, and uniformly elliptic
and bounded: `λ ≤ A(x, r) ≤ M` with `λ > 0`. The data are `f ∈ L¹(x₀, x₁)` and
`F ∈ Lᵖ(x₀, x₁)`, `1 ≤ p ≤ ∞`. A solution is `u ∈ W^{1,p}(x₀, x₁)` whose continuous
representative `ū` takes the boundary values `g`, with

`∫ A(x, ū(x)) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_apply_intervalRepresentativeL_eq`
proves that such a solution exists. No uniqueness is claimed: Schauder's theorem gives
existence only.

## The argument

For `v ∈ C([x₀, x₁])` let `T(v)` be the continuous representative of the solution of the linear
problem with the frozen coefficient `a(x) = A(x, v(x))` and the same data
(`TauCeti.PDE.existsUnique_intervalTraceL_eq_and_forall_integral_eq`). A fixed point of `T` is a
solution of the quasilinear problem, and Schauder's fixed-point theorem
`TauCeti.schauderFixedPoint_closedConvex_continuousOn` produces one once `T` is continuous with
relatively compact range:

* if `vᵢ → v` uniformly, then `A(x, vᵢ(x)) → A(x, v(x))` for every `x` by continuity of `A` in
  its second variable, so `T(vᵢ) → T(v)` by the continuous dependence of the linear problem on
  the coefficient (`TauCeti.PDE.tendsto_intervalRepresentativeL_of_ae_tendsto`);
* the linear derivative bound `TauCeti.PDE.ae_abs_gradient_le_of_forall_integral_eq` gives
  `|T(v)'| ≤ K + |F| / λ` with `K` independent of `v`, since it depends on the coefficient only
  through `λ` and `M`. So the increments of every `T(v)` are controlled by those of the single
  absolutely continuous function `t ↦ ∫_{x₀}^t (K + |F| / λ)`: the range of `T` is
  equicontinuous and pointwise bounded, hence relatively compact by the Arzelà–Ascoli theorem.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 11.4 and Section 11.3 (quasilinear divergence-form equations by Schauder's theorem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.4
  (one-dimensional boundary value problems).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f F : ℝ → ℝ}

/-- **Existence for the quasilinear Dirichlet problem on an interval.** Let `A(x, r)` be
measurable in `x` and continuous in `r`, with `λ ≤ A(x, r) ≤ M` for `x ∈ (x₀, x₁)`, `λ > 0`, and
let `f ∈ L¹(x₀, x₁)` and `F ∈ Lᵖ(x₀, x₁)`, `1 ≤ p ≤ ∞`. Then for every pair `g` of endpoint
values there is `u ∈ W^{1,p}(x₀, x₁)` with endpoint trace `g` solving `-(A(x, ū) u')' = f + F'`
in the sense of distributions, where `ū` is the continuous representative of `u`. -/
theorem exists_intervalTraceL_eq_and_forall_integral_apply_intervalRepresentativeL_eq
    (hx : x₀ < x₁) {lam M : ℝ} (hlam : 0 < lam) {A : ℝ → ℝ → ℝ}
    (hAm : ∀ r, Measurable fun t => A t r) (hAc : ∀ t, Continuous (A t))
    (hAM : ∀ t ∈ Ioo x₀ x₁, ∀ r, lam ≤ A t r ∧ A t r ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g : ℝ × ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = g ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  -- The frozen coefficients `x ↦ A(x, v(x))` are measurable and satisfy the same bounds.
  set coef : C(Icc x₀ x₁, ℝ) → ℝ → ℝ := fun v t => A t (v (projIcc x₀ x₁ hx.le t)) with hcoef
  have hcm : ∀ v, AEStronglyMeasurable (coef v) (volume.restrict (Ioo x₀ x₁)) := fun v =>
    ((measurable_uncurry_of_continuous_of_measurable (u := fun r t => A t r) hAc hAm).comp
      ((v.continuous.comp continuous_projIcc).measurable.prodMk measurable_id)).aestronglyMeasurable
  have hcM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ coef v t ∧ coef v t ≤ M := fun v =>
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => hAM t ht _
  -- The solution map `S` of the linear problems and `T(v) = S(v)‾`.
  choose S hStr hSeq using fun v => exists_intervalTraceL_eq_and_forall_integral_eq hx hlam
    (hcm v) ((hcM v).mono fun _ ht => ht.1) hf hF g
  set T : C(Icc x₀ x₁, ℝ) → C(Icc x₀ x₁, ℝ) := fun v => W1p.intervalRepresentativeL hx (S v)
    with hT_def
  have hTc : Continuous T := continuous_iff_continuousAt.2 fun v =>
    tendsto_intervalRepresentativeL_of_ae_tendsto hx hlam hcm hcM (hcM v)
      (ae_of_all _ fun t => ((hAc t).tendsto _).comp
        ((continuous_eval_const _).tendsto v)) hf hF1 hSeq (hSeq v)
      fun w => (hStr w).trans (hStr v).symm
  -- A derivative bound `|S(v)'| ≤ h = K + |F| / λ` independent of `v`.
  set h : ℝ → ℝ := fun t => (M / (x₁ - x₀) * (|g.2 - g.1| + ((x₁ - x₀) *
    (∫ s in Ioo x₀ x₁, |f s|) + ∫ s in Ioo x₀ x₁, |F s|) / lam) + ∫ s in Ioo x₀ x₁, |f s|) / lam +
      |F t| / lam with hh_def
  have hbd : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), |W1p.gradient (S v) t| ≤ h t := fun v => by
    have := ae_abs_gradient_le_of_forall_integral_eq hx hlam (hcm v) (hcM v) hf hF1 (hSeq v)
    rwa [hStr v] at this
  have hhi : IntegrableOn h (Ioo x₀ x₁) := (integrableOn_const (by simp)).add (hF1.abs.div_const _)
  have hhii : ∀ y z : Icc x₀ x₁, IntervalIntegrable h volume y z := fun y z =>
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 hhi).mono_set
      (uIcc_subset_uIcc (by rw [uIcc_of_le hx.le]; exact y.2) (by rw [uIcc_of_le hx.le]; exact z.2))
  -- Every `T(v)` has increments bounded by those of the primitive `Ψ` of `h`.
  have hinc : ∀ v (y z : Icc x₀ x₁), |T v z - T v y| ≤ |∫ s in (y : ℝ)..z, h s| := by
    intro v y z
    rw [hT_def, ← W1p.integral_gradient_eq_intervalRepresentativeL_sub hx (S v) y z,
      ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_abs_of_norm_le ?_ (hhii y z)
    have hsub : uIoc (y : ℝ) z ⊆ Ioc x₀ x₁ := fun s hs => by
      rw [mem_uIoc] at hs
      rcases hs with hs | hs
      · exact ⟨y.2.1.trans_lt hs.1, hs.2.trans z.2.2⟩
      · exact ⟨z.2.1.trans_lt hs.1, hs.2.trans y.2.2⟩
    have hv := hbd v
    rw [restrict_Ioo_eq_restrict_Ioc] at hv
    exact (ae_restrict_of_ae_restrict_of_subset hsub hv).mono fun t ht => by
      rwa [Real.norm_eq_abs]
  set Ψ : ℝ → ℝ := fun t => ∫ s in x₀..t, h s with hΨ_def
  have hΨc : Continuous fun t : Icc x₀ x₁ => Ψ t :=
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hhi
      (left_mem_Icc.2 hx.le)).domRestrict
  have hΨsub : ∀ y z : Icc x₀ x₁, ∫ s in (y : ℝ)..z, h s = Ψ z - Ψ y := fun y z => by
    set y₀ : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
    exact (intervalIntegral.integral_interval_sub_left (hhii y₀ z) (hhii y₀ y)).symm
  -- Arzelà–Ascoli: the range of `T` is relatively compact.
  have hequi : Equicontinuous fun v => ⇑(T v) := fun y => by
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 (hΨc.tendsto y) ε hε] with z hz v
    rw [Real.dist_eq, abs_sub_comm]
    calc |T v z - T v y| ≤ |∫ s in (y : ℝ)..z, h s| := hinc v y z
      _ = dist (Ψ z) (Ψ y) := by rw [hΨsub, Real.dist_eq]
      _ < ε := hz
  have hpt : ∀ y, ∃ Q, IsCompact Q ∧ ∀ v, T v y ∈ Q := fun y => by
    set y₀ : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
    refine ⟨Metric.closedBall g.1 |∫ s in x₀..(y : ℝ), h s|, isCompact_closedBall _ _, fun v => ?_⟩
    have h₀ : T v y₀ = g.1 := by
      have := congrArg Prod.fst (hStr v)
      rwa [W1p.intervalTraceL_apply] at this
    rw [Metric.mem_closedBall, Real.dist_eq, ← h₀]
    exact hinc v y₀ y
  have hK : IsCompact (closure (T '' univ)) := by
    rw [image_univ]
    exact ArzelaAscoli.isCompact_closure_range_of_equicontinuous hequi hpt
  -- Schauder's theorem gives a fixed point `v = T(v)`, and `S(v)` solves the quasilinear problem.
  obtain ⟨v, -, hv⟩ := schauderFixedPoint_closedConvex_continuousOn isClosed_univ convex_univ
    univ_nonempty hTc.continuousOn (mapsTo_univ _ _) hK
  refine ⟨S v, hStr v, fun φ => ?_⟩
  have hvT : W1p.intervalRepresentativeL hx (S v) = v := hv
  rw [hvT]
  exact hSeq v φ

end TauCeti.PDE
