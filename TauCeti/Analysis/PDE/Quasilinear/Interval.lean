/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

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
(`TauCeti.PDE.abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq`). For the
coefficient `A(y) = 1 + y² / (1 + y²)`, which lies between `1` and `2`, and `f = 1` on `(0, 1)`
with zero boundary values, this gives a solution with `|ū y| ≤ min y (1 - y) ≤ 1 / 2`
(`TauCeti.PDE.exists_intervalTraceL_eq_zero_and_forall_setIntegral_one_add_sq_div_and_abs_le_min`),
and the same bound shows that the frozen-coefficient map sends all of `C([0, 1])` into the closed
ball of radius `1 / 2` (`TauCeti.PDE.norm_intervalDirichletSolution_one_add_sq_div_le`).

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
    (((W1p.intervalRepresentativeL hx u).continuous.comp
      continuous_projIcc).aestronglyMeasurable.apply_of_forall_of_continuousAt hAm
        (hAc.mono fun _ ht => ht.continuousAt))
    (hA.mono fun _ ht => ht _) hf hF hu htr hG y

/-! ### An example: the coefficient `1 + u² / (1 + u²)` -/

/-- The coefficient `1 + y² / (1 + y²)` lies between `1` and `2`. -/
private theorem one_le_one_add_sq_div_and_le_two (y : ℝ) :
    1 ≤ 1 + y ^ 2 / (1 + y ^ 2) ∧ 1 + y ^ 2 / (1 + y ^ 2) ≤ 2 := by
  have h : 0 < 1 + y ^ 2 := by positivity
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  have : y ^ 2 / (1 + y ^ 2) ≤ 1 := (div_le_one h).2 (by linarith)
  linarith

/-- The data `f = 1`, `F = 0` on `(0, 1)` give `G t = ∫_0^t 1 + 0 = t`. -/
private theorem intervalIntegral_one_add_zero :
    (fun t : ℝ => (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0) = fun t => t := by
  ext t
  simp

/-- For the data `f = 1`, `F = 0`, the function `G t = ∫_0^t 1 + 0 = t` lies in `[0, 1]` on
`(0, 1)`. -/
private theorem ae_intervalIntegral_one_add_zero_mem_Icc :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0 ∧ (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0 ≤ 0 + 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [congrFun intervalIntegral_one_add_zero t]
  exact ⟨ht.1.le, by linarith [ht.2]⟩

/-- **The quasilinear problem `-((1 + u² / (1 + u²)) u')' = 1` on `(0, 1)`.** Its coefficient
`1 + y² / (1 + y²)` lies between `1` and `2`, so the problem with zero boundary values
`u(0) = u(1) = 0` has a solution `u ∈ W^{1,p}(0, 1)`. Its continuous representative `ū` satisfies
`|ū y| ≤ min y (1 - y)`, in particular `|ū| ≤ 1 / 2`; by
`abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq` the same bound holds
for every solution. -/
theorem exists_intervalTraceL_eq_zero_and_forall_setIntegral_one_add_sq_div_and_abs_le_min :
    ∃ u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p,
      W1p.intervalTraceL zero_lt_one u = (0, 0) ∧
      (∀ φ : 𝓓(⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo (0 : ℝ) 1,
            (1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2 /
              (1 + W1p.intervalRepresentativeL zero_lt_one u (projIcc 0 1 zero_le_one t) ^ 2)) *
              W1p.gradient u t * deriv φ t =
          ∫ t in Ioo (0 : ℝ) 1, φ t) ∧
      ∀ y : Icc (0 : ℝ) 1,
        |W1p.intervalRepresentativeL zero_lt_one u y| ≤ min (y : ℝ) (1 - y) := by
  set A : ℝ → ℝ → ℝ := fun _ y => 1 + y ^ 2 / (1 + y ^ 2)
  have hAm : ∀ y, AEStronglyMeasurable (fun t => A t y) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun _ => aestronglyMeasurable_const
  have hAc : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), Continuous (A t) :=
    ae_of_all _ fun _ => continuous_const.add <| (continuous_pow 2).div
      (continuous_const.add (continuous_pow 2)) fun y => by positivity
  have hA : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ y, 1 ≤ A t y ∧ A t y ≤ 2 :=
    ae_of_all _ fun _ => one_le_one_add_sq_div_and_le_two
  have hf : IntegrableOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    integrableOn_const measure_Ioo_lt_top.ne
  obtain ⟨u, htr, hu⟩ := exists_intervalTraceL_eq_and_forall_setIntegral_eq (p := p) zero_lt_one
    one_pos hAm hAc hA hf (MemLp.zero' (p := p)) 0 0
  refine ⟨u, htr, fun φ => by simpa using hu φ, fun y => ?_⟩
  simpa using abs_intervalRepresentativeL_sub_le_min_mul_div_of_forall_setIntegral_eq
    zero_lt_one one_pos hAm hAc hA hf integrableOn_zero hu htr
    ae_intervalIntegral_one_add_zero_mem_Icc y

/-- **The frozen-coefficient map of the example preserves the ball of radius `1 / 2`.** For every
`v ∈ C([0, 1])`, the explicit solution of the linear problem `-((1 + v² / (1 + v²)) u')' = 1`,
`u(0) = u(1) = 0`, has supremum norm at most `1 / 2`. So the frozen-coefficient map
`v ↦ intervalDirichletSolution` sends `C([0, 1])` into the closed ball of radius `1 / 2`, to which
Schauder's theorem applies. -/
theorem norm_intervalDirichletSolution_one_add_sq_div_le (v : C(Icc (0 : ℝ) 1, ℝ))
    (hs : IntegrableOn (intervalDirichletSlope 0 1 0 0 (fun t => t) fun t =>
      1 + v (projIcc 0 1 zero_le_one t) ^ 2 / (1 + v (projIcc 0 1 zero_le_one t) ^ 2))
      (Ioo 0 1)) :
    ‖intervalDirichletSolution zero_le_one 0 0 hs‖ ≤ 1 / 2 := by
  have hv : Continuous fun t : ℝ => v (projIcc 0 1 zero_le_one t) :=
    v.continuous.comp continuous_projIcc
  have ha : Continuous fun t : ℝ =>
      1 + v (projIcc 0 1 zero_le_one t) ^ 2 / (1 + v (projIcc 0 1 zero_le_one t) ^ 2) :=
    continuous_const.add ((hv.pow 2).div (continuous_const.add (hv.pow 2)) fun t => by positivity)
  -- The decay bound is stated for `G t = ∫_0^t 1 + 0`; rewrite the solution to that form of `G`.
  obtain ⟨hs', hsol⟩ : ∃ hs' : IntegrableOn
      (intervalDirichletSlope 0 1 0 0 (fun t => (∫ _ in (0 : ℝ)..t, (1 : ℝ)) + 0) fun t =>
        1 + v (projIcc 0 1 zero_le_one t) ^ 2 / (1 + v (projIcc 0 1 zero_le_one t) ^ 2))
      (Ioo 0 1),
      intervalDirichletSolution zero_le_one 0 0 hs =
        intervalDirichletSolution zero_le_one 0 0 hs' := by
    rw [intervalIntegral_one_add_zero]
    exact ⟨hs, rfl⟩
  refine (ContinuousMap.norm_le _ (by norm_num)).2 fun y => ?_
  have h := abs_intervalDirichletSolution_sub_le_min_mul_div zero_lt_one one_pos
    ha.aestronglyMeasurable (ae_of_all _ fun t => one_le_one_add_sq_div_and_le_two _)
    (integrableOn_const (C := (1 : ℝ)) measure_Ioo_lt_top.ne) integrableOn_zero 0
    ae_intervalIntegral_one_add_zero_mem_Icc hs' y
  rw [← hsol] at h
  simp only [sub_zero, mul_one, div_one] at h
  have hmin : min (y : ℝ) (1 - y) ≤ 1 / 2 := by
    rcases le_or_gt (y : ℝ) (1 / 2) with hy | hy
    · exact (min_le_left _ _).trans hy
    · exact (min_le_right _ _).trans (by linarith)
  rw [Real.norm_eq_abs]
  exact h.trans hmin

end TauCeti.PDE
