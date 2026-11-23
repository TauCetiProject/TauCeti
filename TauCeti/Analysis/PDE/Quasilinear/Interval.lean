/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Topology.Order.ProjIcc

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

When both boundary values equal `g`, every solution stays close to `g`: if `∫_{x₀}^t f + F t`
lies in an interval of length `N` for almost every `t`, then
`|ū y - g| ≤ min (y - x₀) (x₁ - y) * N / λ`
(`TauCeti.PDE.abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq`).

Without uniqueness, the solutions are described as a set, and that set behaves well under
perturbation of the data. Let `Aₙ → A` locally uniformly in `y` for almost every `x`, with common
bounds `λ ≤ Aₙ ≤ M`, let `fₙ → f` and `Fₙ → F` in `L¹`, and let the boundary values converge. Then
every sequence of solutions `uₙ` of the problems with data `(Aₙ, fₙ, Fₙ, gₙ)` has a subsequence
whose continuous representatives converge uniformly to that of a solution of the limit problem
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq`). Hence the
continuous representatives of the solutions of one problem form a compact subset of
`C([x₀, x₁])`
(`TauCeti.PDE.isCompact_image_intervalRepresentativeL_setOf_forall_setIntegral_eq`), and the
solution set depends upper semicontinuously on the data: every open set containing the solutions of
the limit problem contains those of the `n`-th problem for all large `n`
(`TauCeti.PDE.eventually_image_intervalRepresentativeL_setOf_forall_setIntegral_eq_subset`).

Every solution is as regular as the data allow
(`TauCeti.PDE.exists_contDiff_eq_intervalRepresentativeL_and_holderWith_deriv_deriv`): if `A` is
`C^{1,α}` jointly on `[x₀, x₁] × [-R, R]` for every `R`, `f` is `C^α` and `F` is `C^{1,α}` on
`[x₀, x₁]`, then `ū ∈ C^{2,α}([x₀, x₁])`, and `ū` solves the equation classically.

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

For the stability theorem, every solution `uₙ` is the explicit solution of the linear problem with
the frozen coefficient `aₙ = Aₙ(·, ūₙ)` and its own data
(`TauCeti.PDE.intervalRepresentativeL_eq_add_intervalIntegral_intervalDirichletSlope`). The
explicit solution depends Lipschitz continuously on the data
(`TauCeti.PDE.integral_abs_intervalDirichletSlope_sub_le`), so `ūₙ` is uniformly close to the
explicit solution `wₙ` with the coefficient `aₙ` and the limit data. The `wₙ` lie in a compact set,
so a subsequence converges to some `w`; along it `aₙ → A(·, w)` almost everywhere, by locally
uniform convergence, and continuity in the coefficient identifies `w` as the explicit solution with
coefficient `A(·, w)`, that is, as a solution of the limit problem.

For the regularity, the flux `A(·, ū) ū' + F` equals `k - Φ` for a constant `k`, so
`ū' = G / A(·, ū)` with `G = k - Φ - F`. With continuous data this makes `ū` a `C¹` function
(`TauCeti.PDE.exists_contDiff_eq_intervalRepresentativeL_and_deriv_eq`). Then `A(·, ū)` is `C¹`
by the chain rule, with derivative `∂ₜA + ∂ᵤA ū'`, so `ū'` is `C¹` with
`ū'' = (G' A(·, ū) - G (∂ₜA + ∂ᵤA ū')) / A(·, ū)²` and `G' = -(f + F')`. Each factor is `α`-Hölder
on `[x₀, x₁]`: `f`, `F'` and `DA` along the Lipschitz curve `t ↦ (t, ū t)` by hypothesis, and the
`C¹` functions `A(·, ū)`, `G` and their quotient `ū'` because they are Lipschitz. Integrating
`ū''`, extended by projection onto `[x₀, x₁]`, twice gives the `C²` extension of `ū`
(`TauCeti.exists_contDiff_two_eqOn_and_deriv_deriv_eq`).

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

/-- The coefficient `A(·, v)` frozen at `v ∈ C([x₀, x₁])` is almost everywhere strongly measurable
on `(x₀, x₁)` when `A` is a Carathéodory function there. -/
private theorem aestronglyMeasurable_apply_projIcc (hx : x₀ ≤ x₁)
    (hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t)) (v : C(Icc x₀ x₁, ℝ)) :
    AEStronglyMeasurable (fun t => A t (v (projIcc x₀ x₁ hx t))) (volume.restrict (Ioo x₀ x₁)) :=
  (v.continuous.comp continuous_projIcc).aestronglyMeasurable.apply_of_forall_of_continuousAt
    hAm (hAc.mono fun _ ht => ht.continuousAt)

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
  have ham : ∀ v, AEStronglyMeasurable (a v) (volume.restrict (Ioo x₀ x₁)) :=
    aestronglyMeasurable_apply_projIcc hx.le hAm hAc
  have haM : ∀ v, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a v t ∧ a v t ≤ M :=
    fun v => hA.mono fun _ ht => ht _
  have hlim : ∀ (vn : ℕ → C(Icc x₀ x₁, ℝ)) (v : C(Icc x₀ x₁, ℝ)), Tendsto vn atTop (𝓝 v) →
      ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun n => a (vn n) t) atTop (𝓝 (a v t)) :=
    fun vn v hv => hAc.mono fun _ ht =>
      (ht.tendsto _).comp (((continuous_eval_const _).tendsto v).comp hv)
  have hG := integrableOn_intervalIntegral_add hx hf (hF.integrable Fact.out)
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

/-- **Decay towards equal boundary values for the quasilinear problem.** Let `A` be a Carathéodory
function with `λ ≤ A t y ≤ M`, as in `exists_intervalTraceL_eq_and_forall_setIntegral_eq`, let `f`
and `F` be integrable on `(x₀, x₁)`, and let `G t = ∫_{x₀}^t f + F t` lie in `[m, m + N]` for
almost every `t ∈ (x₀, x₁)`. Then every solution `u ∈ W^{1,p}(x₀, x₁)` of `-(A(x, u) u')' = f + F'`
with the value `g` at both endpoints satisfies `|ū y - g| ≤ min (y - x₀) (x₁ - y) * N / λ`. The
bound holds for every solution, not only for the one constructed by Schauder's theorem, and
depends on `A` only through `λ`. -/
theorem abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq (hx : x₀ < x₁)
    (hlam : 0 < lam)
    (hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    {g : ℝ} (htr : W1p.intervalTraceL hx u = (g, g)) {m N : ℝ}
    (hG : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      m ≤ (∫ s in x₀..t, f s) + F t ∧ (∫ s in x₀..t, f s) + F t ≤ m + N)
    (y : Icc x₀ x₁) :
    |W1p.intervalRepresentativeL hx u y - g| ≤ min ((y : ℝ) - x₀) (x₁ - y) * N / lam :=
  -- `u` solves the linear problem with the frozen coefficient `A(·, ū)`.
  abs_intervalRepresentativeL_sub_le_min_mul_div hx hlam
    (aestronglyMeasurable_apply_projIcc hx.le hAm hAc _) (hA.mono fun _ ht => ht _) hf hF hu htr
    hG y

/-! ### Families of problems -/

/-- If `Aₖ t → A t` locally uniformly for almost every `t`, with `Aₖ t` continuous, and `vₖ → v` in
`C([x₀, x₁])`, then the frozen coefficients `Aₖ(·, vₖ)` converge almost everywhere on `(x₀, x₁)`
to `A(·, v)`. -/
private theorem ae_tendsto_apply_projIcc (hx : x₀ ≤ x₁) {An : ℕ → ℝ → ℝ → ℝ}
    (hAc : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (An n t))
    (hAlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      TendstoLocallyUniformly (fun n => An n t) (A t) atTop)
    {vk : ℕ → C(Icc x₀ x₁, ℝ)} {v : C(Icc x₀ x₁, ℝ)} (hv : Tendsto vk atTop (𝓝 v)) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun k => An k t (vk k (projIcc x₀ x₁ hx t)))
      atTop (𝓝 (A t (v (projIcc x₀ x₁ hx t)))) := by
  filter_upwards [hAlim, ae_all_iff.2 hAc] with t h1 h2
  exact h1.tendsto_comp (h1.continuous (Frequently.of_forall h2)).continuousAt
    (((continuous_eval_const _).tendsto v).comp hv)

/-- **Stability of the quasilinear problem under perturbation of the data.** Let `x₀ < x₁` and
`λ > 0`, and let `Aₙ` be Carathéodory functions on `(x₀, x₁)` with `λ ≤ Aₙ ≤ M` that converge, for
almost every `t`, locally uniformly in `y` to `A t`. Let `fₙ → f` and `Fₙ → F` in `L¹(x₀, x₁)`,
with `F ∈ Lᵖ`, and let the boundary values converge, `gₙ → g`. If each `uₙ ∈ W^{1,p}(x₀, x₁)` solves
the problem with data `(Aₙ, fₙ, Fₙ, gₙ)`,

`-(Aₙ(x, uₙ) uₙ')' = fₙ + Fₙ'`, `uₙ(x₀) = gₙ.1`, `uₙ(x₁) = gₙ.2`,

then a subsequence of the continuous representatives `ūₙ` converges uniformly on `[x₀, x₁]` to the
continuous representative of a solution `u ∈ W^{1,p}(x₀, x₁)` of the limit problem with data
`(A, f, F, g)`. No regularity of the limit coefficient `A` is assumed: it is a Carathéodory
function with the same bounds, being a locally uniform limit. -/
theorem exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq (hx : x₀ < x₁)
    (hlam : 0 < lam) {An : ℕ → ℝ → ℝ → ℝ} {fn Fn : ℕ → ℝ → ℝ} {gn : ℕ → ℝ × ℝ} {g : ℝ × ℝ}
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
    (hun : ∀ n, W1p.intervalTraceL hx (un n) = gn n ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, An n t (W1p.intervalRepresentativeL hx (un n) (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient (un n) t * deriv φ t =
          (∫ t in Ioo x₀ x₁, fn n t * φ t) - ∫ t in Ioo x₀ x₁, Fn n t * deriv φ t) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      (W1p.intervalTraceL hx u = g ∧
        ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
          ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
              W1p.gradient u t * deriv φ t =
            (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun k => W1p.intervalRepresentativeL hx (un (ψ k))) atTop
          (𝓝 (W1p.intervalRepresentativeL hx u)) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  -- The frozen coefficients `aₙ = Aₙ(·, ūₙ)`.
  set ū : ℕ → C(Icc x₀ x₁, ℝ) := fun n => W1p.intervalRepresentativeL hx (un n)
  set an : ℕ → ℝ → ℝ := fun n t => An n t (ū n (projIcc x₀ x₁ hx.le t))
  have ham : ∀ n, AEStronglyMeasurable (an n) (volume.restrict (Ioo x₀ x₁)) := fun n =>
    aestronglyMeasurable_apply_projIcc hx.le (hAm n) (hAc n) (ū n)
  have hanM : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ an n t ∧ an n t ≤ M :=
    fun n => (hA n).mono fun _ ht => ht _
  set G : ℝ → ℝ := fun t => (∫ s in x₀..t, f s) + F t
  have hG : IntegrableOn G (Ioo x₀ x₁) :=
    integrableOn_intervalIntegral_add hx hf (hF.integrable Fact.out)
  -- `ūₙ` is uniformly close to the explicit solution `wₙ` with the coefficient `aₙ` and the limit
  -- data.
  have hs : ∀ n, IntegrableOn (intervalDirichletSlope x₀ x₁ g.1 g.2 G (an n)) (Ioo x₀ x₁) :=
    fun n => integrableOn_intervalDirichletSlope hlam _ _ (ham n) ((hanM n).mono fun _ h => h.1) hG
  set w : ℕ → C(Icc x₀ x₁, ℝ) := fun n => intervalDirichletSolution hx.le g.1 g.2 (hs n)
  have hclose : Tendsto (fun n => dist (ū n) (w n)) atTop (𝓝 0) :=
    tendsto_dist_intervalRepresentativeL_intervalDirichletSolution hx hlam ham hanM hfn hf hflim
      hFn (hF.integrable Fact.out) hFlim hglim (fun n => (hun n).1) (fun n => (hun n).2) hs
  -- The explicit solutions `wₙ` lie in a compact set, so a subsequence converges, and so does the
  -- corresponding subsequence of `ūₙ`.
  obtain ⟨w', -, ψ, hψ, hwψ⟩ := (isCompact_closure_range_intervalDirichletSolution hx hlam ham
    hanM hG hs).tendsto_subseq fun n => subset_closure (mem_range_self n)
  have hūψ : Tendsto (fun k => ū (ψ k)) atTop (𝓝 w') :=
    hwψ.congr_dist ((hclose.comp hψ.tendsto_atTop).congr fun _ => dist_comm _ _)
  -- Along it the frozen coefficients converge almost everywhere to `a = A(·, w')`.
  set a : ℝ → ℝ := fun t => A t (w' (projIcc x₀ x₁ hx.le t))
  have halim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      Tendsto (fun k => an (ψ k) t) atTop (𝓝 (a t)) :=
    ae_tendsto_apply_projIcc hx.le (fun k => hAc (ψ k))
      (hAlim.mono fun _ ht => ht.comp_tendsto hψ.tendsto_atTop) hūψ
  have ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => ham (ψ k)) halim
  have haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M := by
    filter_upwards [halim, ae_all_iff.2 hanM] with t h1 h2
    exact ⟨ge_of_tendsto' h1 fun k => (h2 (ψ k)).1, le_of_tendsto' h1 fun k => (h2 (ψ k)).2⟩
  -- The limit `w'` is the explicit solution with coefficient `a` and the limit data.
  have hsa : IntegrableOn (intervalDirichletSlope x₀ x₁ g.1 g.2 G a) (Ioo x₀ x₁) :=
    integrableOn_intervalDirichletSlope hlam _ _ ha (haM.mono fun _ h => h.1) hG
  have hw' : w' = intervalDirichletSolution hx.le g.1 g.2 hsa :=
    tendsto_nhds_unique hwψ (tendsto_intervalDirichletSolution hx hlam g.1 g.2 (fun k => ham (ψ k))
      (fun k => (hanM (ψ k)).mono fun _ h => h.1) ha (haM.mono fun _ h => h.1) hG halim _ hsa)
  -- It is the continuous representative of a solution of the limit problem.
  obtain ⟨u, hrep, htr, hweak⟩ := exists_w1p_intervalRepresentativeL_eq (p := p) hx hlam ha
    (haM.mono fun _ h => h.1) hf hF g.1 g.2
  have hu : W1p.intervalRepresentativeL hx u = w' := by
    ext y
    rw [hrep, hw', intervalDirichletSolution_apply]
  exact ⟨u, ⟨htr, by rw [hu]; exact hweak⟩, ψ, hψ, by rw [hu]; exact hūψ⟩

/-- **The solution set is compact.** Under the hypotheses of the existence theorem
`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`, the continuous representatives
of all solutions `u ∈ W^{1,p}(x₀, x₁)` of the quasilinear problem with data `(A, f, F, g)` form a
compact subset of `C([x₀, x₁])`. It is nonempty by that theorem. -/
theorem isCompact_image_intervalRepresentativeL_setOf_forall_setIntegral_eq (hx : x₀ < x₁)
    (hlam : 0 < lam)
    (hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (A t))
    (hA : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ A t y ∧ A t y ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g : ℝ × ℝ) :
    IsCompact (W1p.intervalRepresentativeL hx ''
      {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p | W1p.intervalTraceL hx u = g ∧
        ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
          ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
              W1p.gradient u t * deriv φ t =
            (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t}) := by
  refine IsSeqCompact.isCompact fun v hv => ?_
  choose un hun hunv using hv
  -- The constant family of problems converges to the problem itself.
  have hAlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      TendstoLocallyUniformly (fun _ : ℕ => A t) (A t) atTop :=
    ae_of_all _ fun t => tendstoLocallyUniformly_const (A t)
  obtain ⟨u, hu, ψ, hψ, hlim⟩ :=
    exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq hx hlam (fun _ => hAm)
      (fun _ => hAc) (fun _ => hA) hAlim (fun _ => hf) hf (by simp)
      (fun _ => hF.integrable Fact.out) hF (by simp) tendsto_const_nhds hun
  refine ⟨_, ⟨u, hu, rfl⟩, ψ, hψ, ?_⟩
  simpa only [Function.comp_def, ← hunv] using hlim

/-- **Upper semicontinuity of the solution set.** Under the hypotheses of
`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq`, let `U` be an
open subset of `C([x₀, x₁])` containing the continuous representatives of all solutions of the
limit problem with data `(A, f, F, g)`. Then for all large `n`, `U` also contains the continuous
representatives of all solutions of the problem with data `(Aₙ, fₙ, Fₙ, gₙ)`. -/
theorem eventually_image_intervalRepresentativeL_setOf_forall_setIntegral_eq_subset
    (hx : x₀ < x₁) (hlam : 0 < lam) {An : ℕ → ℝ → ℝ → ℝ} {fn Fn : ℕ → ℝ → ℝ} {gn : ℕ → ℝ × ℝ}
    {g : ℝ × ℝ}
    (hAm : ∀ n y, AEStronglyMeasurable (fun t => An n t y) (volume.restrict (Ioo x₀ x₁)))
    (hAc : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Continuous (An n t))
    (hA : ∀ n, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ∀ y, lam ≤ An n t y ∧ An n t y ≤ M)
    (hAlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      TendstoLocallyUniformly (fun n => An n t) (A t) atTop)
    (hfn : ∀ n, IntegrableOn (fn n) (Ioo x₀ x₁)) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hflim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |fn n t - f t|) atTop (𝓝 0))
    (hFn : ∀ n, IntegrableOn (Fn n) (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (hFlim : Tendsto (fun n => ∫ t in Ioo x₀ x₁, |Fn n t - F t|) atTop (𝓝 0))
    (hglim : Tendsto gn atTop (𝓝 g)) {U : Set C(Icc x₀ x₁, ℝ)} (hU : IsOpen U)
    (hSU : W1p.intervalRepresentativeL hx ''
      {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p | W1p.intervalTraceL hx u = g ∧
        ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
          ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
              W1p.gradient u t * deriv φ t =
            (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t} ⊆ U) :
    ∀ᶠ n in atTop, W1p.intervalRepresentativeL hx ''
      {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p | W1p.intervalTraceL hx u = gn n ∧
        ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
          ∫ t in Ioo x₀ x₁, An n t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
              W1p.gradient u t * deriv φ t =
            (∫ t in Ioo x₀ x₁, fn n t * φ t) - ∫ t in Ioo x₀ x₁, Fn n t * deriv φ t} ⊆ U := by
  by_contra h
  -- Otherwise a subsequence of problems has solutions `uₖ` with `ūₖ ∉ U`.
  obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop (not_eventually.1 h)
  choose un hun hunU using fun k => not_subset.1 (hψU k)
  choose u' hu' hu'rep using hun
  have hψt := hψ.tendsto_atTop
  obtain ⟨u, hu, ψ', -, hlim⟩ :=
    exists_intervalTraceL_eq_and_forall_setIntegral_eq_and_tendsto_subseq hx hlam
      (fun k => hAm (ψ k)) (fun k => hAc (ψ k)) (fun k => hA (ψ k))
      (hAlim.mono fun _ ht => ht.comp_tendsto hψt)
      (fun k => hfn (ψ k)) hf (hflim.comp hψt) (fun k => hFn (ψ k)) hF (hFlim.comp hψt)
      (hglim.comp hψt) (un := u') hu'
  -- Their limit lies in `U`, which is open, so the `ūₖ` eventually do too.
  obtain ⟨k, hk⟩ := (hlim.eventually (hU.mem_nhds (hSU ⟨u, hu, rfl⟩))).exists
  exact hunU (ψ' k) (hu'rep (ψ' k) ▸ hk)

/-! ### Regularity of solutions -/

section Regularity

open scoped NNReal

variable {α : ℝ≥0}

/-- **The second derivative is Hölder.** If `w` is `C¹` with `w' = G / A(·, w)` on `[x₀, x₁]`,
where `A` and `G` are `C¹` and `A(·, w)` does not vanish there, then the expression
`(-(f + F') A(·, w) - G (∂ₜA + ∂ᵤA w')(·, w)) / A(·, w)²`, which is the derivative of
`G / A(·, w)` when `G' = -(f + F')`, is `α`-Hölder on `[x₀, x₁]`, provided `f`, `F'` and the
derivative of `A` near the graph of `w` are. -/
private theorem exists_holderOnWith_div_sq (hx : x₀ ≤ x₁) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hA : ContDiff ℝ 1 (Function.uncurry A))
    (hDA : ∀ R, ∃ C, HolderOnWith C α (fderiv ℝ (Function.uncurry A)) (Icc x₀ x₁ ×ˢ Icc (-R) R))
    {w G : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hG : ContDiff ℝ 1 G)
    (hb0 : ∀ t ∈ Icc x₀ x₁, A t (w t) ≠ 0) (hwG : ∀ t ∈ Icc x₀ x₁, deriv w t = G t / A t (w t))
    {Cf CF : ℝ≥0} (hf : HolderOnWith Cf α f (Icc x₀ x₁))
    (hDF : HolderOnWith CF α (deriv F) (Icc x₀ x₁)) :
    ∃ C, HolderOnWith C α (fun t => (-(f t + deriv F t) * A t (w t) -
      G t * fderiv ℝ (Function.uncurry A) (t, w t) (1, deriv w t)) / A t (w t) ^ 2)
        (Icc x₀ x₁) := by
  set s := Icc x₀ x₁
  have hs : IsCompact s := isCompact_Icc
  have hγ : ContDiff ℝ 1 fun t => (t, w t) := contDiff_id.prodMk hw
  have hb : ContDiff ℝ 1 fun t => A t (w t) := hA.comp hγ
  obtain ⟨Cb, hHb⟩ := hb.contDiffOn.exists_holderOnWith (convex_Icc x₀ x₁) hs hα₁
  obtain ⟨CG, hHG⟩ := hG.contDiffOn.exists_holderOnWith (convex_Icc x₀ x₁) hs hα₁
  -- `1 / A(·, w)` is Hölder, since `|A(·, w)|` attains a positive minimum on `[x₀, x₁]`.
  obtain ⟨t₀, ht₀, hmin⟩ := hs.exists_isMinOn (nonempty_Icc.2 hx) hb.continuous.norm.continuousOn
  have hHinv := hHb.inv₀ (m := ‖A t₀ (w t₀)‖₊) (nnNorm_pos.2 (hb0 t₀ ht₀)) fun t ht => hmin ht
  -- `w' = G / A(·, w)` is Hölder.
  obtain ⟨Cw, hHw⟩ := (ContinuousLinearMap.mul ℝ ℝ).exists_holderOnWith_comp₂_of_isCompact hs hα₀
    hHG hHinv
  have hHw' : HolderOnWith Cw α (deriv w) s :=
    hHw.congr fun t ht => by simp [hwG t ht, div_eq_mul_inv]
  -- The derivative `(∂ₜA + ∂ᵤA w')(·, w)` of `A(·, w)` is Hölder.
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuousOn hw.continuous.continuousOn
  obtain ⟨CA, hHA⟩ := hDA R
  obtain ⟨K, hK⟩ := hγ.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc x₀ x₁) hs
  have hHDA := hHA.comp hK.holderOnWith fun t ht => ⟨ht, abs_le.1 (hR t ht)⟩
  rw [mul_one] at hHDA
  have hHv : HolderOnWith Cw α (fun t => ((1 : ℝ), deriv w t)) s :=
    HolderOnWith.of_dist_le fun x hx y hy => by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact hHw'.dist_le hx hy
  obtain ⟨Cd, hHd⟩ :=
    (ContinuousLinearMap.id ℝ ((ℝ × ℝ) →L[ℝ] ℝ)).exists_holderOnWith_comp₂_of_isCompact hs hα₀
      hHDA hHv
  -- Assemble the numerator and divide by `A(·, w)²`.
  obtain ⟨C₁, hH₁⟩ := (-ContinuousLinearMap.mul ℝ ℝ).exists_holderOnWith_comp₂_of_isCompact hs hα₀
    (hf.add hDF) hHb
  obtain ⟨C₂, hH₂⟩ := (ContinuousLinearMap.mul ℝ ℝ).exists_holderOnWith_comp₂_of_isCompact hs hα₀
    hHG hHd
  obtain ⟨C₃, hH₃⟩ := (ContinuousLinearMap.mul ℝ ℝ).exists_holderOnWith_comp₂_of_isCompact hs hα₀
    hHinv hHinv
  obtain ⟨C, hH⟩ := (ContinuousLinearMap.mul ℝ ℝ).exists_holderOnWith_comp₂_of_isCompact hs hα₀
    (hH₁.sub hH₂) hH₃
  refine ⟨C, hH.congr fun t _ => ?_⟩
  simp only [neg_apply, ContinuousLinearMap.mul_apply', Pi.add_apply,
    Pi.sub_apply, ContinuousLinearMap.id_apply, Function.comp_apply]
  rw [div_eq_mul_inv, sq, mul_inv]
  ring

/-- **The flux form of the derivative.** Under the hypotheses of
`exists_contDiff_eq_intervalRepresentativeL_and_holderWith_deriv_deriv`, with `f` only continuous
on `[x₀, x₁]`, the continuous representative `ū` agrees on `[x₀, x₁]` with a `C¹` function `w`
satisfying `w' = G / A(·, w)` there, where the flux `G = k - ∫_{x₀}^t f - F` is `C¹` with
`G' = -(f + F')` on `[x₀, x₁]`. -/
private theorem exists_contDiff_deriv_eq_div (hx : x₀ < x₁)
    (hA : ContDiff ℝ 1 (Function.uncurry A)) (hf : ContinuousOn f (Icc x₀ x₁))
    (hF : ContDiff ℝ 1 F) {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hA0 : ∀ t : Icc x₀ x₁, A t (W1p.intervalRepresentativeL hx u t) ≠ 0)
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ w G : ℝ → ℝ, ContDiff ℝ 1 w ∧ ContDiff ℝ 1 G ∧
      (∀ t : Icc x₀ x₁, W1p.intervalRepresentativeL hx u t = w t) ∧
      (∀ t ∈ Icc x₀ x₁, HasDerivAt G (-(f t + deriv F t)) t) ∧
      ∀ t ∈ Icc x₀ x₁, deriv w t = G t / A t (w t) := by
  -- Continuous coefficients: `ū` is `C¹`, with `ū' = (k - ∫ f - F) / A(·, ū)`.
  obtain ⟨k, w, hw, hū, hdw⟩ := exists_contDiff_eq_intervalRepresentativeL_and_deriv_eq hx
    (hA.continuous.comp (continuous_id.prodMk
      (W1p.continuous_intervalRepresentativeL_projIcc hx u))).continuousOn
    (fun t ht => by simpa [projIcc_of_mem hx.le ht] using hA0 ⟨t, ht⟩)
    (hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hF.continuous.continuousOn hu
  -- Extend `f` by projection, so that the flux is defined and `C¹` on `ℝ`.
  set fₑ : ℝ → ℝ := fun t => f (projIcc x₀ x₁ hx.le t)
  have hfₑ : Continuous fₑ := hf.comp_projIcc hx.le
  set G : ℝ → ℝ := fun t => k - (∫ s in x₀..t, fₑ s) - F t
  have hG : ∀ t, HasDerivAt G (-(fₑ t + deriv F t)) t := fun t => by
    convert ((hfₑ.integral_hasStrictDerivAt x₀ t).hasDerivAt.const_sub k).sub
      (hF.differentiable one_ne_zero t).hasDerivAt using 1
    ring
  refine ⟨w, G, hw, contDiff_one_iff_deriv.2 ⟨fun t => (hG t).differentiableAt, ?_⟩, hū,
    fun t ht => by simpa [fₑ, projIcc_of_mem hx.le ht] using hG t, fun t ht => ?_⟩
  · rw [show deriv G = fun t => -(fₑ t + deriv F t) from funext fun t => (hG t).deriv]
    exact (hfₑ.add (hF.continuous_deriv le_rfl)).neg
  · have hΦ : ∫ s in x₀..t, f s = ∫ s in x₀..t, fₑ s := intervalIntegral.integral_congr
      fun s hs => by
        rw [uIcc_of_le ht.1] at hs
        simp [fₑ, projIcc_of_mem hx.le ⟨hs.1, hs.2.trans ht.2⟩]
    have hwt : w t = W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t) := by
      rw [projIcc_of_mem hx.le ht, hū]
    rw [hdw t ht, hΦ, hwt]
    simp only [G, Function.comp_apply, Function.uncurry_apply_pair, id_eq]

/-- **Solutions of the quasilinear problem on an interval are `C^{2,α}` up to the boundary.** Let
`x₀ < x₁` and `0 < α ≤ 1`. Let the coefficient `A(x, y)` be `C¹` jointly, with derivative
`α`-Hölder on `[x₀, x₁] × [-R, R]` for every `R`, let `f` be `α`-Hölder on `[x₀, x₁]`, and let
`F` be `C¹` with `F'` `α`-Hölder on `[x₀, x₁]`. Let `u ∈ W^{1,p}(x₀, x₁)` solve
`-(A(x, u) u')' = f + F'` weakly,

`∫ A(t, ū t) u' φ' = ∫ f φ - ∫ F φ'` for every `φ ∈ C_c^∞(x₀, x₁)`,

where `ū` is its continuous representative, and let the equation be nondegenerate along the
solution, `A(t, ū t) ≠ 0` on `[x₀, x₁]`. Then `ū` is `C^{2,α}` up to the boundary: it agrees on
`[x₀, x₁]` with a `C²` function `w` on `ℝ` whose second derivative is globally `α`-Hölder, and
`w` solves the equation classically, `(A(t, w t) w' t)' = -(f t + F' t)` on `(x₀, x₁)`.

When `A` satisfies these hypotheses and `A ≥ λ > 0`, this applies to the solutions constructed by
`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`. -/
theorem exists_contDiff_eq_intervalRepresentativeL_and_holderWith_deriv_deriv (hx : x₀ < x₁)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hA : ContDiff ℝ 1 (Function.uncurry A))
    (hDA : ∀ R, ∃ C, HolderOnWith C α (fderiv ℝ (Function.uncurry A)) (Icc x₀ x₁ ×ˢ Icc (-R) R))
    {Cf CF : ℝ≥0} (hf : HolderOnWith Cf α f (Icc x₀ x₁)) (hF : ContDiff ℝ 1 F)
    (hDF : HolderOnWith CF α (deriv F) (Icc x₀ x₁)) {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hA0 : ∀ t : Icc x₀ x₁, A t (W1p.intervalRepresentativeL hx u t) ≠ 0)
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A t (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ w : ℝ → ℝ, ContDiff ℝ 2 w ∧
      (∀ t : Icc x₀ x₁, W1p.intervalRepresentativeL hx u t = w t) ∧
      (∃ C, HolderWith C α (deriv (deriv w))) ∧
      ∀ t ∈ Ioo x₀ x₁, HasDerivAt (fun s => A s (w s) * deriv w s) (-(f t + deriv F t)) t := by
  obtain ⟨w₁, G, hw₁, hGc, hū, hG, hw₁G⟩ :=
    exists_contDiff_deriv_eq_div hx hA (hf.continuousOn hα₀) hF hA0 hu
  have hb0 : ∀ t ∈ Icc x₀ x₁, A t (w₁ t) ≠ 0 := fun t ht => by
    simpa [← hū ⟨t, ht⟩] using hA0 ⟨t, ht⟩
  -- On `(x₀, x₁)`, `w₁' = G / A(·, w₁)` has the derivative `h`, which is Hölder on `[x₀, x₁]`.
  set h : ℝ → ℝ := fun t => (-(f t + deriv F t) * A t (w₁ t) -
    G t * fderiv ℝ (Function.uncurry A) (t, w₁ t) (1, deriv w₁ t)) / A t (w₁ t) ^ 2
  obtain ⟨C, hH⟩ := exists_holderOnWith_div_sq hx.le hα₀ hα₁ hA hDA hw₁ hGc hb0 hw₁G hf hDF
  have hderiv : ∀ t ∈ Ioo x₀ x₁, HasDerivAt (deriv w₁) (h t) t := fun t ht => by
    have hb : HasDerivAt (fun s => A s (w₁ s))
        (fderiv ℝ (Function.uncurry A) (t, w₁ t) (1, deriv w₁ t)) t :=
      (hA.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hw₁.differentiable one_ne_zero t).hasDerivAt)
    exact (HasDerivAt.div (hG t (Ioo_subset_Icc_self ht)) hb
      (hb0 t (Ioo_subset_Icc_self ht))).congr_of_eventuallyEq
      (eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs => hw₁G s (Ioo_subset_Icc_self hs))
  -- Integrating `h` twice gives the `C²` extension `w` of `w₁`, with `w'' = h ∘ projIcc`.
  obtain ⟨w, hw, hw₁w, hdw₁w, hddw⟩ :=
    exists_contDiff_two_eqOn_and_deriv_deriv_eq hx.le hw₁ hderiv (hH.continuousOn hα₀)
  refine ⟨w, hw, fun t => (hū t).trans (hw₁w t.property), ?_, fun t ht => ?_⟩
  · -- `w''` is Hölder on `ℝ`, since `projIcc` is `1`-Lipschitz.
    have hπ : LipschitzWith 1 fun t => (projIcc x₀ x₁ hx.le t : ℝ) := by
      simpa [Function.comp_def] using
        (LipschitzWith.subtypeVal _).comp (LipschitzWith.projIcc hx.le)
    have hHₑ := hH.comp_holderWith hπ.holderWith fun t => (projIcc x₀ x₁ hx.le t).property
    rw [mul_one] at hHₑ
    rw [hddw]
    exact ⟨_, hHₑ⟩
  · -- On `(x₀, x₁)` the flux `A(·, w) w'` is `G`, whose derivative is `-(f + F')`.
    refine (hG t (Ioo_subset_Icc_self ht)).congr_of_eventuallyEq
      (eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs => ?_)
    have hs' := Ioo_subset_Icc_self hs
    beta_reduce
    rw [← hw₁w hs', ← hdw₁w hs', hw₁G s hs', mul_div_cancel₀ _ (hb0 s hs')]

end Regularity

end TauCeti.PDE
