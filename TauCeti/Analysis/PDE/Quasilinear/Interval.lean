/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.Order.OrderClosed
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

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

In place of uniqueness, the solutions depend upper semicontinuously on the data. If `Aₙ → A`
locally uniformly in `y` for almost every `x`, with common bounds `λ ≤ Aₙ ≤ M`, and `fₙ → f`,
`Fₙ → F` in `L¹` and `gₙ → g`, then every sequence of solutions `uₙ` of the problems with data
`(Aₙ, fₙ, Fₙ, gₙ)` has a subsequence whose continuous representatives converge uniformly on
`[x₀, x₁]` to the representative of a solution of the limit problem
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq`). For a
constant sequence of problems this says that the set of continuous representatives of the
solutions is a compact subset of `C([x₀, x₁])`
(`TauCeti.PDE.isCompact_image_intervalRepresentativeL_setOf_forall_setIntegral_eq`).

## The argument

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

For the limits of solutions, every solution is the explicit solution of the linear problem with its
own frozen coefficient `aₙ = Aₙ(·, ūₙ)`
(`TauCeti.PDE.intervalRepresentativeL_eq_intervalDirichletSolution`). Replacing the data of the
`n`-th problem by the limit data changes it by `O(|gₙ - g| + ‖fₙ - f‖₁ + ‖Fₙ - F‖₁)` uniformly in
the coefficient, and the solutions with the limit data lie in the compact set above, so a
subsequence of `ūₙ` converges uniformly to some `w`
(`TauCeti.PDE.exists_strictMono_tendsto_intervalDirichletSolution`). Along it
`aₙ → A(·, w)` almost everywhere, and the joint continuity of the linear solution in coefficient and
data (`TauCeti.PDE.tendsto_intervalDirichletSolution`) shows that `w` solves the linear problem with
coefficient `A(·, w)`, that is, the limit problem.

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

/-- A fixed point `w` of the frozen-solution map, `w` the solution of the linear problem with
coefficient `A(·, w)`, is the continuous representative of a solution of the quasilinear
problem. -/
private theorem exists_intervalRepresentativeL_eq_of_intervalDirichletSolution_eq (hx : x₀ < x₁)
    (hlam : 0 < lam) {w : C(Icc x₀ x₁, ℝ)}
    (ha : AEStronglyMeasurable (fun t => A t (w (projIcc x₀ x₁ hx.le t)))
      (volume.restrict (Ioo x₀ x₁)))
    (hla : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ A t (w (projIcc x₀ x₁ hx.le t)))
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁))) {g₀ g₁ : ℝ}
    {hs : IntegrableOn (intervalDirichletSlope x₀ x₁ g₀ g₁ (fun t => (∫ s in x₀..t, f s) + F t)
      (fun t => A t (w (projIcc x₀ x₁ hx.le t)))) (Ioo x₀ x₁)}
    (hw : intervalDirichletSolution hx.le g₀ g₁ hs = w) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalRepresentativeL hx u = w ∧
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  obtain ⟨u, hrep, htr, hweak⟩ :=
    exists_w1p_intervalRepresentativeL_eq (p := p) hx hlam ha hla hf hF g₀ g₁
  have hū : W1p.intervalRepresentativeL hx u = w := by
    ext y
    rw [hrep, ← DFunLike.congr_fun hw y, intervalDirichletSolution_apply]
  exact ⟨u, hū, htr, by rwa [hū]⟩

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
  have hG := (intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf
    (left_mem_Icc.2 hx.le)).add (hF.integrable Fact.out)
  -- A fixed point `ū` of the solution map solves the linear problem with coefficient `a ū`, and
  -- is the continuous representative of that solution.
  obtain ⟨ū, hū⟩ := exists_intervalDirichletSolution_eq_self hx hlam ham haM hlim hG fun v =>
    integrableOn_intervalDirichletSlope hlam g₀ g₁ (ham v) ((haM v).mono fun _ h => h.1) hG
  obtain ⟨u, -, htr, hweak⟩ := exists_intervalRepresentativeL_eq_of_intervalDirichletSolution_eq
    (p := p) hx hlam (ham ū) ((haM ū).mono fun _ h => h.1) hf hF hū
  exact ⟨u, htr, hweak⟩

variable {An : ℕ → ℝ → ℝ → ℝ} {fn Fn : ℕ → ℝ → ℝ} {gn : ℕ → ℝ × ℝ} {g : ℝ × ℝ}

/-- Along a subsequence `ν`, if `vₙ → w` uniformly on `[x₀, x₁]` and `Aₙ(t, ·) → A(t, ·)` locally
uniformly, then `A_{ν n}(t, vₙ t) → A(t, w t)`. -/
private theorem ae_tendsto_apply_projIcc (hx : x₀ < x₁)
    (hAc : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (An n t))
    (hAlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      TendstoLocallyUniformly (fun n => An n t) (A t) atTop)
    {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) {vn : ℕ → C(Icc x₀ x₁, ℝ)} {w : C(Icc x₀ x₁, ℝ)}
    (hv : Tendsto vn atTop (𝓝 w)) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun n => An (ν n) t (vn n (projIcc x₀ x₁ hx.le t))) atTop
        (𝓝 (A t (w (projIcc x₀ x₁ hx.le t)))) := by
  filter_upwards [hAlim, ae_all_iff.2 hAc] with t ht hct
  exact (ht.comp_tendsto hν).tendsto_comp (ht.continuous (Frequently.of_forall hct)).continuousAt
    (((continuous_eval_const _).tendsto w).comp hv)

/-- **Limits of solutions of converging quasilinear problems.** For `n ∈ ℕ` let `Aₙ` be
Carathéodory functions on `(x₀, x₁)` with the common bounds `λ ≤ Aₙ ≤ M`, `λ > 0`, converging for
almost every `t` locally uniformly in the second variable: `Aₙ(t, ·) → A(t, ·)`. Let `fₙ → f` and
`Fₙ → F` in `L¹(x₀, x₁)`, with `F ∈ Lᵖ`, and let the endpoint values converge, `gₙ → g`. If
`uₙ ∈ W^{1,p}(x₀, x₁)` solves `-(Aₙ(x, uₙ) uₙ')' = fₙ + Fₙ'` with endpoint values `gₙ`, then a
subsequence of the continuous representatives `ūₙ` converges uniformly on `[x₀, x₁]` to the
continuous representative of a solution `u ∈ W^{1,p}(x₀, x₁)` of the limit problem
`-(A(x, u) u')' = f + F'` with endpoint values `g`.

This is the upper semicontinuity of the solution set in the data: no uniqueness is assumed, and
the subsequence is needed, since the limit problem may have several solutions. -/
theorem exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq (hx : x₀ < x₁)
    (hlam : 0 < lam)
    (hAm : ∀ n y, AEStronglyMeasurable (fun t => An n t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (An n t))
    (hA : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ An n t y ∧ An n t y ≤ M)
    (hAlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      TendstoLocallyUniformly (fun n => An n t) (A t) atTop)
    (hfn : ∀ n, IntegrableOn (fn n) (Ioo x₀ x₁)) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hflim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |fn n t - f t|) atTop (𝓝 0))
    (hFn : ∀ n, IntegrableOn (Fn n) (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (hFlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |Fn n t - F t|) atTop (𝓝 0))
    (hglim : Tendsto gn atTop (𝓝 g)) {un : ℕ → W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (htr : ∀ n, W1p.intervalTraceL hx (un n) = gn n)
    (hun : ∀ n, ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁,
          An n t (W1p.intervalRepresentativeL hx (un n) (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient (un n) t * deriv φ t =
        (∫ t in Ioo x₀ x₁, fn n t * φ t) - ∫ t in Ioo x₀ x₁, Fn n t * deriv φ t) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = g ∧
      (∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) ∧
      ∃ ν : ℕ → ℕ, StrictMono ν ∧
        Tendsto (fun n => W1p.intervalRepresentativeL hx (un (ν n))) atTop
          (𝓝 (W1p.intervalRepresentativeL hx u)) := by
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  have hx₀ := left_mem_Icc.2 hx.le
  have hPn n := intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo (hfn n) hx₀
  have hP := intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf hx₀
  have hGn n := (hPn n).add (hFn n)
  have hG := hP.add hF1
  -- The data `Gₙ = ∫_{x₀}^· fₙ + Fₙ` converge in `L¹`.
  have hGlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁,
      |(∫ s in x₀..t, fn n s) + Fn n t - ((∫ s in x₀..t, f s) + F t)|) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa using (intervalIntegral.tendsto_integral_norm_primitive_sub hfn hf hx₀
        (by simpa using hflim)).add hFlim)
    refine (integral_mono ((hGn n).sub hG).abs (((hPn n).sub hP).norm.add ((hFn n).sub hF1).abs)
      fun t => ?_).trans_eq (integral_add ((hPn n).sub hP).norm ((hFn n).sub hF1).abs)
    simp only [Pi.add_apply, Pi.sub_apply, add_sub_add_comm, Real.norm_eq_abs]
    exact abs_add_le _ _
  -- Freeze the coefficients at the solutions: `aₙ = Aₙ(·, ūₙ)`.
  set ū : ℕ → C(Icc x₀ x₁, ℝ) := fun n => W1p.intervalRepresentativeL hx (un n)
  set an : ℕ → ℝ → ℝ := fun n t => An n t (ū n (projIcc x₀ x₁ hx.le t))
  have han : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)) := fun n =>
    ((ū n).continuous.comp continuous_projIcc).aestronglyMeasurable.apply_of_forall_of_continuousAt
      (hAm n) ((hAc n).mono fun _ ht => ht.continuousAt)
  have hanM : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t ∧ an n t ≤ M :=
    fun n => (hA n).mono fun _ ht => ht _
  have hanl : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t :=
    fun n => (hanM n).mono fun _ h => h.1
  -- Each `ūₙ` is the explicit solution of the linear problem with coefficient `aₙ`.
  have hsn := fun n => integrableOn_intervalDirichletSlope hlam (gn n).1 (gn n).2 (han n) (hanl n)
    (hGn n)
  have hrep : ∀ n, ū n = intervalDirichletSolution hx.le (gn n).1 (gn n).2 (hsn n) := fun n =>
    intervalRepresentativeL_eq_intervalDirichletSolution hx hlam (han n) (hanM n) (hfn n) (hFn n)
      ((htr n).trans Prod.mk.eta.symm) (hun n) (hsn n)
  -- A subsequence of `ūₙ` converges uniformly to some `w`.
  obtain ⟨w, ν, hν, hwν⟩ := exists_strictMono_tendsto_intervalDirichletSolution hx hlam
    ((continuous_fst.tendsto g).comp hglim) ((continuous_snd.tendsto g).comp hglim) han hanM hGn
    hG hGlim hsn
  have hūν : Tendsto (fun n => ū (ν n)) atTop (𝓝 w) := hwν.congr fun n => (hrep (ν n)).symm
  -- Along the subsequence the frozen coefficients converge to `a = A(·, w)`.
  set a : ℝ → ℝ := fun t => A t (w (projIcc x₀ x₁ hx.le t))
  have hlimν : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun n => an (ν n) t) atTop (𝓝 (a t)) :=
    ae_tendsto_apply_projIcc hx hAc hAlim hν.tendsto_atTop hūν
  have ha := aestronglyMeasurable_of_tendsto_ae atTop (fun n => han (ν n)) hlimν
  have hla := eventually_ge_of_tendsto hlimν fun n => hanl (ν n)
  -- The limit `w` is the explicit solution of the linear problem with coefficient `a`.
  have hs := integrableOn_intervalDirichletSlope hlam g.1 g.2 ha hla hG
  have hw : w = intervalDirichletSolution hx.le g.1 g.2 hs := tendsto_nhds_unique hūν <|
    (tendsto_intervalDirichletSolution hx hlam
      ((continuous_fst.tendsto g).comp (hglim.comp hν.tendsto_atTop))
      ((continuous_snd.tendsto g).comp (hglim.comp hν.tendsto_atTop)) (fun n => han (ν n))
      (fun n => hanl (ν n)) (fun n => hGn (ν n)) hG (hGlim.comp hν.tendsto_atTop) hlimν
      (fun n => hsn (ν n)) hs).congr fun n => (hrep (ν n)).symm
  -- So `w` is the continuous representative of a solution of the limit problem.
  obtain ⟨u, hūu, htru, hweak⟩ :=
    exists_intervalRepresentativeL_eq_of_intervalDirichletSolution_eq hx hlam ha hla hf hF hw.symm
  exact ⟨u, htru.trans Prod.mk.eta, hweak, ν, hν, hūu ▸ hūν⟩

/-- **The solution set of the quasilinear problem is compact.** Under the hypotheses of the
existence theorem `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`, the continuous
representatives of the solutions `u ∈ W^{1,p}(x₀, x₁)` of `-(A(x, u) u')' = f + F'` with endpoint
values `g` form a compact subset of `C([x₀, x₁])`, nonempty by that theorem. -/
theorem isCompact_image_intervalRepresentativeL_setOf_forall_setIntegral_eq (hx : x₀ < x₁)
    (hlam : 0 < lam)
    (hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g : ℝ × ℝ) :
    IsCompact (W1p.intervalRepresentativeL hx '' {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p |
      W1p.intervalTraceL hx u = g ∧ ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t}) := by
  refine IsSeqCompact.isCompact fun w hw => ?_
  choose un hun hwn using hw
  -- The constant family of problems converges to itself.
  have hconst : ∀ t, TendstoLocallyUniformly (fun _ : ℕ => A t) (A t) atTop :=
    fun t U hU _ => ⟨univ, univ_mem, Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  obtain ⟨u, htr, hu, ν, hν, hlim⟩ :=
    exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq hx hlam
      (An := fun _ => A) (fn := fun _ => f) (Fn := fun _ => F) (gn := fun _ => g)
      (fun _ => hAm) (fun _ => hAc) (fun _ => hA) (ae_of_all _ hconst) (fun _ => hf) hf
      (by simp) (fun _ => hF.integrable Fact.out) hF (by simp) tendsto_const_nhds
      (fun n => (hun n).1) (fun n => (hun n).2)
  refine ⟨_, ⟨u, ⟨htr, hu⟩, rfl⟩, ν, hν, ?_⟩
  simpa only [Function.comp_def, ← hwn] using hlim

end TauCeti.PDE
