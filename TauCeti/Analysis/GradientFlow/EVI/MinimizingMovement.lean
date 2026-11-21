/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.Analysis.GradientFlow.MinimizingMovement
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.GradientFlow.MoreauYosida.ErrorEstimate
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.Topology.MetricSpace.Pseudo.Basic
import TauCeti.Topology.Order.Interval
import TauCeti.Topology.UniformSpace.UniformConvergence.Complete

/-!
# Convergence of minimizing movements of penalized convex energies to `EVI` solutions

Let `φ : X → EReal` be a lower semicontinuous energy on a metric space which is penalized convex
with parameter `m` (`TauCeti.PenalizedConvex`) for all small time steps, for instance an
`m`-geodesically convex energy on a CAT(0) space, or an energy on the quadratic Wasserstein space
which is `m`-convex along generalized geodesics. Then every continuous curve which is a limit, in
the metric, of piecewise constant interpolants of minimizing movements with time steps tending to
`0` is an `EVI_m` solution for `φ`: the discrete variational inequality of the implicit Euler
scheme passes to the limit. On a complete space the interpolants do converge, without any
compactness hypothesis, so the `EVI_m` flow exists.

Along a minimizing movement sequence `U` with time step `τ` and `r = 1 + m τ ≥ 0`, the discrete
energy regularization estimate `TauCeti.PenalizedConvex.apply_le` gives, for `M < N` and every `y`
of finite energy,

`φ (U N) ≤ φ y + (d(U M, y)² - r ^ (N - M) d(U N, y)²) / (2τ ∑_{n < N - M} r ^ n)`.

At the indices `M = ⌈s / τ⌉₊` and `N = ⌈t / τ⌉₊` of the piecewise constant interpolant, and as
`τ → 0`, the factor `r ^ (N - M)` tends to `exp (m (t - s))` and `τ ∑_{n < N - M} r ^ n` tends to
`∫₀^{t - s} exp (m r) dr` (`TauCeti.tendsto_one_add_mul_pow` and
`TauCeti.tendsto_mul_sum_one_add_mul_pow`). If the interpolants converge in the metric to a curve
`u`, the lower semicontinuity of `φ` passes the estimate to the limit, and gives the endpoint
regularization estimates which characterize `EVI_m` solutions
(`TauCeti.isEVISolution_iff_apply_le`).

Convergence of the interpolants is a hypothesis of
`TauCeti.isEVISolution_of_forall_mem_moreauYosidaResolvent`, and so is continuity of the limit
curve. For a generalized minimizing movement of a coercive energy
(`TauCeti.IsGeneralizedMinimizingMovement`, for the metric convergence) the limit is absolutely
continuous, so it is an `EVI_m` solution (`TauCeti.IsGeneralizedMinimizingMovement.isEVISolution`).
By uniqueness of `EVI_m` solutions, all generalized minimizing movements from one point agree.
When bounded subsets of sublevels of `φ` are relatively compact, generalized minimizing movements
exist, and so does the `EVI_m` flow from every point of finite energy
(`TauCeti.exists_isEVISolution`).

Without the compactness hypothesis, on a complete pseudometric space, a coercive
(`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0`, `x₁`) energy satisfying `PenalizedConvex m τ φ` for small
`τ > 0` (Ambrosio–Gigli–Savaré, Assumption 4.0.1) has minimizing movements from every `x₀` with
`φ x₀ ≠ ⊤` (`TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`). Cross-testing the
one-step variational inequalities of two schemes with time steps `τ` and `σ` and comparing with a
discrete heat-equation barrier (Crandall–Liggett, Kobayashi) bounds the squared distance of their
interpolants on `[0, T]` by a multiple of `√(τ + σ)`. Hence `t ↦ J ⌈t / τ⌉₊` converges uniformly on
`[0, T]` as `τ → 0` to an `EVI_m` solution starting at `x₀`
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`). Passing `η → 0` in the
sharp bilinear-interpolation estimate `TauCeti.dist_ceil_sq_le_of_penalizedConvex` (from
`TauCeti.Analysis.GradientFlow.MoreauYosida.ErrorEstimate`) yields the quantitative `O(√τ)` error
bound `TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex` against any `EVI_m` solution, which
extends uniform convergence to minimizing movements with converging initial points and uniformly
bounded initial energy (`TauCeti.IsEVISolution.tendstoUniformlyOn_of_penalizedConvex`) and
identifies generalized minimizing movements with respect to general auxiliary convergences
(`TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`).

Since `TauCeti.eviDomain m φ` is closed on a complete space (`TauCeti.isClosed_eviDomain`),
existence on `{x | φ x ≠ ⊤}` extends to every `x₀ ∈ closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_subset`,
`TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex`), giving
`TauCeti.eviDomain m φ = closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_penalizedConvex`). On a complete CAT(0) pseudometric space,
`m`-geodesically convex lower semicontinuous energies that never take the value `⊥` satisfy both
hypotheses automatically whenever the effective domain is nonempty; more generally, this holds
under Ambrosio–Gigli's curve-convexity Assumption 3.24.

## Main results

* `TauCeti.isEVISolution_of_forall_mem_moreauYosidaResolvent`: a continuous metric limit of
  piecewise constant interpolants of minimizing movements of a penalized convex energy is an
  `EVI_m` solution.
* `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution`: generalized minimizing movements of
  coercive penalized convex energies are `EVI_m` solutions.
* `TauCeti.IsGeneralizedMinimizingMovement.eqOn`: two such generalized minimizing movements from
  the same point agree on `[0, ∞)`.
* `TauCeti.exists_isEVISolution`: existence of the `EVI_m` flow from every point of finite energy
  when bounded subsets of sublevels are relatively compact.
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`: existence of the `EVI_m`
  solution and uniform convergence on compact time intervals of minimizing movement interpolants
  as `τ → 0`, on a complete space (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex`,
  `TauCeti.IsEVISolution.tendstoUniformlyOn_of_penalizedConvex`, and
  `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`: quantitative `O(√τ)`
  error bound against an `EVI_m` solution, uniform convergence from converging initial data with
  uniformly bounded energy, and `EVI_m` identification of generalized minimizing movements for
  general auxiliary convergences.
* `TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex` and
  `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: existence on `closure {x | φ x ≠ ⊤}` and
  `TauCeti.eviDomain m φ = closure {x | φ x ≠ ⊤}` under penalized convexity
  (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq` and
  `TauCeti.eviDomain_eq_closure_of_convexAlong_and_convexAlong_dist_sq`: generation of `EVI_λ`
  flows under Ambrosio–Gigli Assumption 3.24 and Theorem 3.25.
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn`,
  `TauCeti.GeodesicallyConvex.exists_isEVISolution_of_mem_closure`, and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`: CAT(0) corollaries (Jost; Mayer, Theorem 1.13).

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4 (Assumption 4.0.1, Theorems 4.0.4
  and 4.1.2, Section 4.1, and Section 4.2).
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, in *Modelling and Optimisation of
  Flows on Networks*, Lecture Notes in Math. 2062, Springer 2013, Section 3.3 (Assumption 3.24 and
  Theorem 3.25).
* M. G. Crandall, T. M. Liggett, *Generation of semi-groups of nonlinear transformations on general
  Banach spaces*, Amer. J. Math. 93 (1971), 265--298, Lemma 1.2.
* Y. Kobayashi, *Difference approximation of Cauchy problems for quasi-dissipative operators and
  generation of nonlinear semigroups*, J. Math. Soc. Japan 27 (1975), 640--665, Lemma 2.1.
* J. Jost, *Convex functionals and generalized harmonic maps into spaces of nonpositive curvature*,
  Comment. Math. Helv. 70 (1995), 659--673.
* U. F. Mayer, *Gradient flows on nonpositively curved metric spaces and harmonic maps*, Comm.
  Anal. Geom. 6 (1998), 199--253, Section 1 and Theorem 1.13.
-/

public section

noncomputable section

open Filter Set Topology Real
open scoped NNReal ENNReal

namespace TauCeti

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {φ : X → EReal} {τ : ℕ → ℝ≥0}
  {U : ℕ → ℕ → X} {u : ℝ → X}

/-- The discrete energy regularization estimate between the indices `⌈s / τ k⌉₊` and
`⌈t / τ k⌉₊` of the piecewise constant interpolants passes to their metric limit. -/
private theorem apply_le_of_forall_mem_moreauYosidaResolvent (hφ : LowerSemicontinuous φ)
    (hτ : ∀ k, 0 < τ k) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hconv : ∀ᶠ k in atTop, PenalizedConvex m (τ k) φ)
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n))
    (hlim : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (𝓝 (u t)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (m * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (m * r)) : ℝ) : EReal) := by
  have hτr : Tendsto (fun k ↦ (τ k : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  -- The interpolants at times `s` and `t` sit at the indices `M k ≤ N k`, `L k = N k - M k` steps
  -- apart, and these steps take the time `t - s` in the limit.
  set M : ℕ → ℕ := fun k ↦ ⌈s / τ k⌉₊
  set N : ℕ → ℕ := fun k ↦ ⌈t / τ k⌉₊
  set L : ℕ → ℕ := fun k ↦ N k - M k
  have hMN k : M k ≤ N k := Nat.ceil_mono (div_le_div_of_nonneg_right hst.le (τ k).property)
  have hL : Tendsto (fun k ↦ (L k : ℝ) * τ k) atTop (𝓝 (t - s)) :=
    tendsto_ceil_div_sub_ceil_div_mul hs hst.le (.of_forall fun k ↦ NNReal.coe_pos.2 (hτ k)) hτr
  -- The regularization terms `C k` of the discrete estimates converge to that of the limit.
  set C : ℕ → ℝ := fun k ↦ (dist (U k (M k)) y ^ 2 - (1 + m * τ k) ^ L k * dist (U k (N k)) y ^ 2) /
    (2 * τ k * ∑ n ∈ Finset.range (L k), (1 + m * τ k) ^ n)
  have hE := integral_exp_mul_pos m (sub_pos.2 hst)
  have hC : Tendsto (fun k ↦ ((C k : ℝ) : EReal)) atTop
      (𝓝 (((dist (u s) y ^ 2 - exp (m * (t - s)) * dist (u t) y ^ 2) /
        (2 * ∫ r in 0..(t - s), exp (m * r)) : ℝ) : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    simp only [C, mul_assoc]
    exact ((((hlim s hs).dist tendsto_const_nhds).pow 2).sub ((tendsto_one_add_mul_pow hτr hL).mul
      (((hlim t (hs.trans hst.le)).dist tendsto_const_nhds).pow 2))).div
      ((tendsto_mul_sum_one_add_mul_pow hτr hL).const_mul 2) (by positivity)
  -- Eventually the discrete estimate applies to the `L k` steps from `U k (M k)`.
  have hmτ : ∀ᶠ k in atTop, 0 ≤ 1 + m * τ k := by
    have : Tendsto (fun k ↦ 1 + m * (τ k : ℝ)) atTop (𝓝 1) := by
      simpa using (hτr.const_mul m).const_add 1
    exact (this.eventually (lt_mem_nhds one_pos)).mono fun _ h ↦ h.le
  have hLpos : ∀ᶠ k in atTop, 0 < L k := (hL.eventually (lt_mem_nhds (sub_pos.2 hst))).mono
    fun k hk ↦ Nat.cast_pos.1 (pos_of_mul_pos_left hk (τ k).property)
  have hreg : ∀ᶠ k in atTop, φ (U k (N k)) ≤ φ y + ((C k : ℝ) : EReal) := by
    filter_upwards [hconv, hmτ, hLpos] with k hk hmτk hLk
    have := hk.apply_le (hτ k) hmτk (U := fun n ↦ U k (M k + n)) (fun n ↦ hU k (M k + n)) hy hLk
    simpa only [add_zero, L, Nat.add_sub_cancel' (hMN k)] using this
  calc φ (u t)
      ≤ liminf (fun k ↦ φ (U k (N k))) atTop :=
        (hφ.le_liminf (u t)).trans (liminf_le_liminf_of_le (hlim t (hs.trans hst.le)))
    _ ≤ limsup (fun k ↦ φ y + ((C k : ℝ) : EReal)) atTop :=
      (liminf_le_liminf hreg).trans liminf_le_limsup
    _ ≤ limsup (fun _ ↦ φ y) atTop + limsup (fun k ↦ ((C k : ℝ) : EReal)) atTop :=
      EReal.limsup_add_le (.inr (by rw [hC.limsup_eq]; exact EReal.coe_ne_top _))
        (.inr (by rw [hC.limsup_eq]; exact EReal.coe_ne_bot _))
    _ = _ := by rw [hC.limsup_eq, limsup_const]

/-- **Limits of minimizing movements are `EVI_m` solutions.** Let `φ` be lower semicontinuous,
and penalized convex with parameter `m` for all but finitely many of the positive time steps
`τ k → 0`. Let `U k` be minimizing movement sequences with time steps `τ k`, whose piecewise
constant interpolants `t ↦ U k ⌈t / τ k⌉₊` converge in the metric at every time `t ≥ 0` to a
curve `u` that is continuous on `[0, ∞)`. If `φ` is not identically `⊤` and never takes the value
`⊥` along `u` at positive times, then `u` is an `EVI_m` solution for `φ`. This identifies the
limit in Ambrosio–Gigli–Savaré, Theorem 4.0.4, which also proves that the interpolants
converge. -/
theorem isEVISolution_of_forall_mem_moreauYosidaResolvent (hφ : LowerSemicontinuous φ)
    (hτ : ∀ k, 0 < τ k) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hconv : ∀ᶠ k in atTop, PenalizedConvex m (τ k) φ)
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n))
    (hlim : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k ↦ U k ⌈t / τ k⌉₊) atTop (𝓝 (u t)))
    (hu : ContinuousOn u (Ici 0)) (hdom : ∃ y, φ y ≠ ⊤) (hbot : ∀ t > 0, φ (u t) ≠ ⊥) :
    IsEVISolution m φ u :=
  isEVISolution_of_apply_le hφ hu hdom hbot fun _ hy _ _ hs hst ↦
    apply_le_of_forall_mem_moreauYosidaResolvent hφ hτ hτ0 hconv hU hlim hy hs hst

/-- **Generalized minimizing movements are `EVI_m` solutions.** Let `φ` be lower semicontinuous,
coercive, `φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0`, and penalized convex with parameter `m` for all
small positive time steps. Then every generalized minimizing movement of `φ` for the metric
convergence is an `EVI_m` solution for `φ`. -/
theorem IsGeneralizedMinimizingMovement.isEVISolution {x₀ x₁ : X} {τ₀ : ℝ≥0}
    (hφ : LowerSemicontinuous φ) (hconv : ∀ᶠ τ in 𝓝[>] 0, PenalizedConvex m τ φ)
    (hτ₀ : 0 < τ₀) (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (h : IsGeneralizedMinimizingMovement 𝓝 φ x₀ u) : IsEVISolution m φ u := by
  obtain ⟨τ, U, hτ, hτ0, hU, -, ⟨S, hS⟩, hlim⟩ := isGeneralizedMinimizingMovement_iff.1 h
  have hcont := h.continuousOn (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge) hτ₀ h₀
  have hconv' : ∀ᶠ k in atTop, PenalizedConvex m (τ k) φ :=
    (tendsto_nhdsWithin_iff.2 ⟨hτ0, Eventually.of_forall hτ⟩).eventually hconv
  exact isEVISolution_of_forall_mem_moreauYosidaResolvent hφ hτ hτ0 hconv' hU hlim hcont
    ⟨U 0 0, ne_top_of_le_ne_top (EReal.coe_ne_top S) (hS 0)⟩
    fun t _ ↦ apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top _ _) h₀

end PseudoMetricSpace

section MetricSpace

variable {X : Type*} [MetricSpace X] {m : ℝ} {φ : X → EReal} {u v : ℝ → X} {x₀ x₁ : X}
  {τ₀ : ℝ≥0}

/-- **Uniqueness of generalized minimizing movements.** Under the hypotheses of
`TauCeti.IsGeneralizedMinimizingMovement.isEVISolution`, two generalized minimizing movements of
`φ` from the same point, for the metric convergence, agree on `[0, ∞)`. -/
theorem IsGeneralizedMinimizingMovement.eqOn (hφ : LowerSemicontinuous φ)
    (hconv : ∀ᶠ τ in 𝓝[>] 0, PenalizedConvex m τ φ) (hτ₀ : 0 < τ₀)
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hu : IsGeneralizedMinimizingMovement 𝓝 φ x₀ u)
    (hv : IsGeneralizedMinimizingMovement 𝓝 φ x₀ v) : EqOn u v (Ici 0) :=
  (hu.isEVISolution hφ hconv hτ₀ h₀).eqOn (hv.isEVISolution hφ hconv hτ₀ h₀) hφ
    ((hu.apply_zero pure_le_nhds (fun _ _ _ _ ha hb ↦ (ha.edist hb).liminf_eq.ge)).trans
      (hv.apply_zero pure_le_nhds (fun _ _ _ _ ha hb ↦ (ha.edist hb).liminf_eq.ge)).symm)

/-- **Existence of the `EVI_m` flow under compactness.** Let `φ` be lower semicontinuous, coercive,
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0`, and penalized convex with parameter `m` for all small positive
time steps, and let every bounded subset of every sublevel set `{φ ≤ c}` be relatively compact.
Then from every point `x₀` of finite energy starts an `EVI_m` solution for `φ`, obtained as a
generalized minimizing movement. -/
theorem exists_isEVISolution (hφ : LowerSemicontinuous φ)
    (hconv : ∀ᶠ τ in 𝓝[>] 0, PenalizedConvex m τ φ)
    (hcpt : ∀ (c : ℝ) {s : Set X}, Bornology.IsBounded s →
      IsCompact (closure (s ∩ {y | φ y ≤ c})))
    (hτ₀ : 0 < τ₀) (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, IsEVISolution m φ u ∧ u 0 = x₀ := by
  -- A bounded sequence of bounded energy lies in a compact set, hence has a convergent
  -- subsequence.
  have hseq (c : ℝ) ⦃v : ℕ → X⦄ (hv : Metric.ediam (range v) ≠ ⊤) (hc : ∀ n, φ (v n) ≤ c) :
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (𝓝 y) := by
    obtain ⟨y, -, ψ, hψ, hy⟩ := (hcpt c (Metric.isBounded_iff_ediam_ne_top.2 hv)).tendsto_subseq
      fun n ↦ subset_closure ⟨mem_range_self n, hc n⟩
    exact ⟨y, ψ, hψ, hy⟩
  obtain ⟨u, hu, hu0, -⟩ := exists_isGeneralizedMinimizingMovement (fun _ ↦ pure_le_nhds _)
    (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge)
    (fun _ _ _ hv ↦ (hφ.le_liminf _).trans (liminf_le_liminf_of_le hv)) hseq hτ₀ h₀
    (edist_ne_top _ _) hx₀
  exact ⟨u, hu.isEVISolution hφ hconv hτ₀ h₀, hu0⟩

end MetricSpace

section DiscreteComparison

variable {X : Type*} [PseudoMetricSpace X] {m : ℝ} {φ : X → EReal}

private def barrierC (m T : ℝ) (τ' : ℝ≥0) : ℝ := (2 * |m| * (T + τ') + 5 / 4) / (3 / 2)

private def gridBarrier (τ σ : ℝ≥0) (C : ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ) * τ - (j : ℝ) * σ) ^ 2 + C * (τ + σ) * ((i : ℝ) * τ + (j : ℝ) * σ)

private def cauchyL (T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  A - (E - A) * Real.exp (8 * (T + τ') / τ')

private def cauchyM (m T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  2 * (E - cauchyL T τ' A E) * Real.exp (|m| * (T + τ'))

private def cauchyK (m T : ℝ) (τ' : ℝ≥0) (A E : ℝ) : ℝ :=
  Real.exp (4 * |m| * (T + τ')) * cauchyM m T τ' A E *
    Real.sqrt (2 * τ' + 2 * barrierC m T τ' * (T + τ'))

private lemma barrierC_nonneg (m : ℝ) {T : ℝ} {τ' : ℝ≥0} (hTτ' : 0 ≤ T + τ') :
    0 ≤ barrierC m T τ' := by
  unfold barrierC; positivity

private lemma cauchyL_le {T : ℝ} {τ' : ℝ≥0} {A E : ℝ} (hAE : A ≤ E) :
    cauchyL T τ' A E ≤ E := by
  have : 0 ≤ (E - A) * Real.exp (8 * (T + τ') / τ') :=
    mul_nonneg (sub_nonneg.2 hAE) (Real.exp_pos _).le
  unfold cauchyL; linarith

private lemma cauchyM_nonneg (m : ℝ) {T : ℝ} {τ' : ℝ≥0} {A E : ℝ} (hAE : A ≤ E) :
    0 ≤ cauchyM m T τ' A E :=
  mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 (cauchyL_le hAE))) (Real.exp_pos _).le

private lemma gridBarrier_ceil_le {τ σ τ' : ℝ≥0} {C T t : ℝ}
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hC : 0 ≤ C) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    gridBarrier τ σ C ⌈t / τ⌉₊ ⌈t / σ⌉₊ ≤ (2 * τ' + 2 * C * (T + τ')) * (τ + σ) := by
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hσr : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hn_lo : t ≤ (⌈t / τ⌉₊ : ℝ) * τ := le_ceil_div_mul hτr
  have hn_hi : (⌈t / τ⌉₊ : ℝ) * τ < t + τ := ceil_div_mul_lt_add ht0 hτr
  have hk_lo : t ≤ (⌈t / σ⌉₊ : ℝ) * σ := le_ceil_div_mul hσr
  have hk_hi : (⌈t / σ⌉₊ : ℝ) * σ < t + σ := ceil_div_mul_lt_add ht0 hσr
  have hdiff_sq : ((⌈t / τ⌉₊ : ℝ) * τ - (⌈t / σ⌉₊ : ℝ) * σ) ^ 2 ≤ (τ + σ) ^ 2 :=
    sq_le_sq.2 (by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ + σ)]
      exact abs_le.2 ⟨by linarith, by linarith⟩)
  have hsum_le : (⌈t / τ⌉₊ : ℝ) * τ + (⌈t / σ⌉₊ : ℝ) * σ ≤ 2 * (T + τ') := by linarith
  have hτσ_sq : ((τ : ℝ) + σ) ^ 2 ≤ 2 * τ' * (τ + σ) := by nlinarith
  unfold gridBarrier
  calc ((⌈t / τ⌉₊ : ℝ) * τ - (⌈t / σ⌉₊ : ℝ) * σ) ^ 2 +
          C * (τ + σ) * ((⌈t / τ⌉₊ : ℝ) * τ + (⌈t / σ⌉₊ : ℝ) * σ)
      ≤ 2 * τ' * (τ + σ) + C * (τ + σ) * (2 * (T + τ')) := by
        gcongr; exact hdiff_sq.trans hτσ_sq
    _ = (2 * τ' + 2 * C * (T + τ')) * (τ + σ) := by ring

/-- **Discrete comparison step** between two minimizing movement sequences `U` (step `τ`) and `V`
(step `σ`) (Kobayashi, Lemma 2.1; Mayer, Section 1; Ambrosio–Gigli–Savaré, Theorem 4.1.2):
cross-testing the one-step variational inequalities eliminates the energies and yields
`((1 + m τ) σ + (1 + m σ) τ) d(U (n + 1), V (k + 1))² ≤
  σ d(U n, V (k + 1))² + τ d(U (n + 1), V k)²`. -/
private theorem discrete_comparison_step {τ σ : ℝ≥0}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    (hUtop : ∀ n, φ (U n) ≠ ⊤) (hUbot : ∀ n, φ (U n) ≠ ⊥)
    (hVtop : ∀ k, φ (V k) ≠ ⊤) (hVbot : ∀ k, φ (V k) ≠ ⊥) (n k : ℕ) :
    ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ)) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
      σ * dist (U n) (V (k + 1)) ^ 2 + τ * dist (U (n + 1)) (V k) ^ 2 := by
  have h1 := hPenτ.apply_add_le_of_mem_moreauYosidaResolvent hτ (hU n) (hVtop (k + 1))
  have h2 := hPenσ.apply_add_le_of_mem_moreauYosidaResolvent hσ (hV k) (hUtop (n + 1))
  have ha : φ (U (n + 1)) = (φ (U (n + 1))).toReal :=
    (EReal.coe_toReal (hUtop (n + 1)) (hUbot (n + 1))).symm
  have hb : φ (V (k + 1)) = (φ (V (k + 1))).toReal :=
    (EReal.coe_toReal (hVtop (k + 1)) (hVbot (k + 1))).symm
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
  have h1m := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (τ : ℝ) * σ)
  have h2m := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * (τ : ℝ) * σ)
  field_simp at h1m h2m
  rw [dist_comm (V (k + 1)) (U (n + 1)), dist_comm (V k) (U (n + 1))] at h2m
  nlinarith [NNReal.coe_nonneg σ, NNReal.coe_nonneg τ,
    mul_nonneg (NNReal.coe_nonneg σ) (sq_nonneg (dist (U n) (U (n + 1)))),
    mul_nonneg (NNReal.coe_nonneg τ) (sq_nonneg (dist (V k) (V (k + 1))))]

/-- Weighted comparison inequality (Crandall–Liggett, Lemma 1.2): setting
`a n k = (1 + m τ) ^ n (1 + m σ) ^ k d(U n, V k)²` with weights `p + q = 1`, we have
`a (n + 1) (k + 1) ≤ p * a n (k + 1) + q * a (n + 1) k`. -/
private theorem weighted_comparison_step {τ σ : ℝ≥0}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hmτ : 0 < 1 + m * τ) (hmσ : 0 < 1 + m * σ)
    {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    (hUtop : ∀ n, φ (U n) ≠ ⊤) (hUbot : ∀ n, φ (U n) ≠ ⊥)
    (hVtop : ∀ k, φ (V k) ≠ ⊤) (hVbot : ∀ k, φ (V k) ≠ ⊥) (n k : ℕ) :
    (1 + m * τ) ^ (n + 1) * (1 + m * σ) ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2 ≤
      ((σ : ℝ) * (1 + m * τ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        ((1 + m * τ) ^ n * (1 + m * σ) ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
      ((τ : ℝ) * (1 + m * σ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        ((1 + m * τ) ^ (n + 1) * (1 + m * σ) ^ k * dist (U (n + 1)) (V k) ^ 2) := by
  have hstep := discrete_comparison_step hPenτ hPenσ hτ hσ hU hV hUtop hUbot hVtop hVbot n k
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  set γ : ℝ := (σ : ℝ) * r₁ + τ * r₂
  have hγ : 0 < γ :=
    add_pos (mul_pos (NNReal.coe_pos.2 hσ) hmτ) (mul_pos (NNReal.coe_pos.2 hτ) hmσ)
  have hmul := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep
      (mul_nonneg (pow_nonneg hmτ.le (n + 1)) (pow_nonneg hmσ.le (k + 1)))) hγ.le
  refine (le_of_eq ?_).trans (hmul.trans_eq ?_)
  · field_simp [hγ.ne']
  · rw [pow_succ r₁ n, pow_succ r₂ k]
    field_simp [hγ.ne']

/-- The discrete heat-equation barrier `gridBarrier` is a supersolution of the `(p, q)` random walk
on the grid `(n + 1) τ ≤ T + τ'`, `(k + 1) σ ≤ T + τ'` (Crandall–Liggett, Lemma 1.2;
Kobayashi, Lemma 2.1). -/
private theorem barrier_superharmonic {τ σ τ' : ℝ≥0} {T : ℝ}
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4) {n k : ℕ}
    (hn : ((n + 1 : ℕ) : ℝ) * τ ≤ T + τ') (hk : ((k + 1 : ℕ) : ℝ) * σ ≤ T + τ') :
    ((σ : ℝ) * (1 + m * τ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        gridBarrier τ σ (barrierC m T τ') n (k + 1) +
      ((τ : ℝ) * (1 + m * σ) / ((σ : ℝ) * (1 + m * τ) + τ * (1 + m * σ))) *
        gridBarrier τ σ (barrierC m T τ') (n + 1) k ≤
      gridBarrier τ σ (barrierC m T τ') (n + 1) (k + 1) := by
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  set γ : ℝ := (σ : ℝ) * r₁ + τ * r₂
  set C : ℝ := barrierC m T τ'
  have hτ0 : (0 : ℝ) ≤ τ := NNReal.coe_nonneg τ
  have hσ0 : (0 : ℝ) ≤ σ := NNReal.coe_nonneg σ
  have hr₁_lo : 3 / 4 ≤ r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  have hr₁_hi : r₁ ≤ 5 / 4 := by dsimp [r₁]; nlinarith [le_abs_self m]
  have hr₂_lo : 3 / 4 ≤ r₂ := by dsimp [r₂]; nlinarith [neg_abs_le m]
  have hr₂_hi : r₂ ≤ 5 / 4 := by dsimp [r₂]; nlinarith [le_abs_self m]
  have hr₁0 : 0 ≤ r₁ := by linarith
  have hr₂0 : 0 ≤ r₂ := by linarith
  have hTτ' : 0 ≤ T + τ' := le_trans (mul_nonneg (Nat.cast_nonneg _) hτ0) hn
  -- Bound the drift and variance terms against the linear drift `C (τ + σ) (r₁ + r₂)`.
  set x : ℝ := ((n + 1 : ℕ) : ℝ) * τ - ((k + 1 : ℕ) : ℝ) * σ
  have hx : |x| ≤ T + τ' := abs_le.2 ⟨by linarith [mul_nonneg (Nat.cast_nonneg (n + 1)) hτ0],
    by linarith [mul_nonneg (Nat.cast_nonneg (k + 1)) hσ0]⟩
  have hστ : |((σ : ℝ) - τ)| ≤ τ + σ :=
    (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hσ0, abs_of_nonneg hτ0]; ring)
  have hcross : 2 * x * m * ((σ : ℝ) - τ) ≤ 2 * |m| * (T + τ') * (τ + σ) := by
    calc 2 * x * m * ((σ : ℝ) - τ) ≤ |2 * x * m * ((σ : ℝ) - τ)| := le_abs_self _
      _ = 2 * |x| * |m| * |((σ : ℝ) - τ)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg two_pos.le]
      _ ≤ 2 * (T + τ') * |m| * (τ + σ) := by gcongr
      _ = 2 * |m| * (T + τ') * (τ + σ) := by ring
  have hconst : r₁ * τ + r₂ * σ ≤ 5 / 4 * (τ + σ) := by nlinarith
  have hC : (2 * |m| * (T + τ') + 5 / 4) * (τ + σ) ≤ C * (τ + σ) * (r₁ + r₂) := by
    have hC0 : 0 ≤ C * (τ + σ) := mul_nonneg (barrierC_nonneg m hTτ') (by positivity)
    calc (2 * |m| * (T + τ') + 5 / 4) * (τ + σ)
        = C * (τ + σ) * (3 / 2) := by unfold C barrierC; field_simp
      _ ≤ C * (τ + σ) * (r₁ + r₂) := by gcongr; linarith
  set rhs : ℝ := 2 * x * m * ((σ : ℝ) - τ) + r₁ * τ + r₂ * σ - C * (τ + σ) * (r₁ + r₂)
  have hmain : rhs ≤ 0 := by dsimp [rhs]; linarith
  -- Clear the positive denominator `γ` (treating the degenerate `τ = σ = 0` case separately).
  rcases eq_or_lt_of_le (show 0 ≤ γ by positivity) with hγ0 | hγpos
  · have hστ0 : (τ : ℝ) = 0 ∧ (σ : ℝ) = 0 :=
      ⟨by nlinarith [mul_nonneg hσ0 hr₁0], by nlinarith [mul_nonneg hτ0 hr₂0]⟩
    unfold gridBarrier
    rw [hστ0.1, hστ0.2]
    norm_num
  have hid : γ * (((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
      ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k -
      gridBarrier τ σ C (n + 1) (k + 1)) = (τ : ℝ) * σ * rhs := by
    unfold gridBarrier
    field_simp [hγpos.ne']
    dsimp [rhs, γ, r₁, r₂, x]
    push_cast
    ring
  have hneg : γ * (((σ : ℝ) * r₁ / γ) * gridBarrier τ σ C n (k + 1) +
      ((τ : ℝ) * r₂ / γ) * gridBarrier τ σ C (n + 1) k -
      gridBarrier τ σ C (n + 1) (k + 1)) ≤ 0 :=
    hid ▸ mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hτ0 hσ0) hmain
  nlinarith

/-- Every iterate of a minimizing movement sequence started at a finite-energy point `x₀` under a
coercive energy `φ_{τ'}(x₀) = A` has finite energy (`≠ ⊤` and `≠ ⊥`). -/
private lemma apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent
    {δ τ' : ℝ≥0} {x₀ : X} {A E : ℝ} (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    {W : ℕ → X} (hW0 : W 0 = x₀)
    (hW : ∀ n, W (n + 1) ∈ moreauYosidaResolvent φ δ (W n)) :
    (∀ n, φ (W n) ≠ ⊤) ∧ (∀ n, φ (W n) ≠ ⊥) := by
  refine ⟨fun n ↦ ?_, fun n ↦ apply_ne_bot_of_moreauYosida_ne_bot
    (edist_ne_top x₀ (W n)) (hA ▸ EReal.coe_ne_bot A)⟩
  have hle := antitone_comp_of_forall_mem_moreauYosidaResolvent hW (Nat.zero_le n)
  simp only [Function.comp_apply, hW0, hE] at hle
  exact ne_top_of_le_ne_top (EReal.coe_ne_top E) hle

/-- Boundary estimate at `k = 0`: for `n ≤ ⌈T / τ⌉₊`,
`(1 + m τ) ^ n * d(U n, x₀)² ≤ cauchyM * √(gridBarrier τ σ C n 0)`. -/
private theorem boundary_comparison_left {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hτ : 0 < τ) (hττ' : 4 * τ ≤ τ') (hmτ : |m| * τ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U : ℕ → X} (hU0 : U 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {n : ℕ} (hn : n ≤ ⌈T / τ⌉₊) :
    (1 + m * τ) ^ n * dist (U n) x₀ ^ 2 ≤
      cauchyM m T τ' A E * Real.sqrt (gridBarrier τ σ (barrierC m T τ') n 0) := by
  set r₁ : ℝ := 1 + m * τ
  set L : ℝ := cauchyL T τ' A E
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have hτ_le_τ' : (τ : ℝ) ≤ τ' := by linarith
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := cauchyM_nonneg m hAE
  have hC0 : 0 ≤ C := barrierC_nonneg m (add_nonneg hT (NNReal.coe_nonneg τ'))
  have hr₁0 : 0 ≤ r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  -- Combine the uniform energy lower bound `L ≤ φ (U n)` with the multi-step dissipation bound.
  have hlow_n : (L : EReal) ≤ φ (U n) :=
    (le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hU hτ hττ'
      (hU0 ▸ hA).ge (hU0 ▸ hE).le hT hn).1
  obtain ⟨htop_U, hbot_U⟩ :=
    apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent hA hE hU0 hU
  set en : ℝ := (φ (U n)).toReal
  have hen : φ (U n) = en := (EReal.coe_toReal (htop_U n) (hbot_U n)).symm
  have hL_en : L ≤ en := by exact_mod_cast hen ▸ hlow_n
  have hdist : dist (U n) x₀ ^ 2 ≤ 2 * (E - L) * ((n : ℝ) * τ) := by
    have hstep :=
      toReal_edist_sq_le_mul_sub_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le n) (hU0 ▸ hE)
        hen
    rw [Nat.sub_zero, hU0, ← dist_edist, dist_comm] at hstep
    calc dist (U n) x₀ ^ 2 ≤ 2 * ((n : ℝ) * τ) * (E - en) := hstep
      _ ≤ 2 * ((n : ℝ) * τ) * (E - L) := by gcongr
      _ = 2 * (E - L) * ((n : ℝ) * τ) := by ring
  have hr₁_exp : r₁ ^ n ≤ Real.exp (|m| * (T + τ')) := by
    have hr₁_le : r₁ ≤ 1 + |m| * τ := by dsimp [r₁]; nlinarith [le_abs_self m]
    calc r₁ ^ n ≤ (1 + |m| * τ) ^ n := pow_le_pow_left₀ hr₁0 hr₁_le n
      _ ≤ (1 + |m| * τ) ^ ⌈T / τ⌉₊ :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn
      _ ≤ Real.exp (|m| * (T + τ)) :=
          one_add_mul_pow_ceil_div_le_exp (abs_nonneg m) (add_nonneg hT hτr.le)
      _ ≤ Real.exp (|m| * (T + τ')) := Real.exp_le_exp.2 (by gcongr)
  have hnτ_sqrt : (n : ℝ) * τ ≤ Real.sqrt (gridBarrier τ σ C n 0) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : 0 ≤ C * ((τ : ℝ) + σ) * ((n : ℝ) * τ + 0) :=
      mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity)
    unfold gridBarrier
    simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero]
    linarith
  calc r₁ ^ n * dist (U n) x₀ ^ 2
      ≤ Real.exp (|m| * (T + τ')) * (2 * (E - L) * ((n : ℝ) * τ)) :=
        mul_le_mul hr₁_exp hdist (sq_nonneg _) (by positivity)
    _ = M * ((n : ℝ) * τ) := by unfold M cauchyM L; ring
    _ ≤ M * Real.sqrt (gridBarrier τ σ C n 0) := mul_le_mul_of_nonneg_left hnτ_sqrt hM0

/-- Inductive lattice barrier comparison (Crandall–Liggett, Lemma 1.2; Kobayashi, Lemma 2.1):
on the grid `n ≤ ⌈T / τ⌉₊`, `k ≤ ⌈T / σ⌉₊`, the weighted squared distance
`(1 + m τ) ^ n (1 + m σ) ^ k d(U n, V k)²` is bounded by `cauchyM * √(gridBarrier n k)`. -/
private theorem grid_comparison {τ σ τ' : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {n k : ℕ} (hn : n ≤ ⌈T / τ⌉₊) (hk : k ≤ ⌈T / σ⌉₊) :
    (1 + m * τ) ^ n * (1 + m * σ) ^ k * dist (U n) (V k) ^ 2 ≤
      cauchyM m T τ' A E * Real.sqrt (gridBarrier τ σ (barrierC m T τ') n k) := by
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  set Φ : ℕ → ℕ → ℝ := gridBarrier τ σ C
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hσr : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  have hr₁_pos : 0 < r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  have hr₂_pos : 0 < r₂ := by dsimp [r₂]; nlinarith [neg_abs_le m]
  obtain ⟨hUtop, hUbot⟩ := apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent hA hE hU0 hU
  obtain ⟨hVtop, hVbot⟩ := apply_ne_top_and_ne_bot_of_forall_mem_moreauYosidaResolvent hA hE hV0 hV
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := cauchyM_nonneg m hAE
  have hC0 : 0 ≤ C := barrierC_nonneg m (add_nonneg hT (NNReal.coe_nonneg τ'))
  have hΦ0 : ∀ i j : ℕ, 0 ≤ Φ i j := fun i j ↦ by
    unfold Φ gridBarrier
    exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity))
  -- Induct on `(n, k)`: the axes `n = 0` and `k = 0` use `boundary_comparison_left`; interior
  -- steps combine `weighted_comparison_step`, `Real.sqrt` concavity, and `barrier_superharmonic`.
  induction n generalizing k with
  | zero =>
    have hs := boundary_comparison_left (φ := φ) (x₀ := x₀) (m := m) (τ := σ) (σ := τ)
      hσ hστ' hmσ hA hE hT hV0 hV hk
    have hsymm : gridBarrier σ τ C k 0 = Φ 0 k := by
      unfold Φ gridBarrier
      simp only [Nat.cast_zero]
      ring
    rw [hU0, pow_zero, one_mul, dist_comm, ← hsymm]
    exact hs
  | succ n ihn =>
    induction k with
    | zero =>
      rw [hV0, pow_zero, mul_one]
      exact boundary_comparison_left (φ := φ) (x₀ := x₀) (m := m) (τ := τ) (σ := σ)
        hτ hττ' hmτ hA hE hT hU0 hU hn
    | succ k ihk =>
      have hn_lt : ((n + 1 : ℕ) : ℝ) * τ ≤ T + τ' :=
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hn) hτr.le).trans
          (ceil_div_mul_lt_add hT hτr).le).trans (by linarith)
      have hk_lt : ((k + 1 : ℕ) : ℝ) * σ ≤ T + τ' :=
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hσr.le).trans
          (ceil_div_mul_lt_add hT hσr).le).trans (by linarith)
      set γ : ℝ := σ * r₁ + τ * r₂
      set p : ℝ := σ * r₁ / γ
      set q : ℝ := τ * r₂ / γ
      have hγ : 0 < γ := add_pos (mul_pos hσr hr₁_pos) (mul_pos hτr hr₂_pos)
      have hp0 : 0 ≤ p := div_nonneg (mul_nonneg hσr.le hr₁_pos.le) hγ.le
      have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hτr.le hr₂_pos.le) hγ.le
      have hpq : p + q = 1 := by dsimp [p, q, γ]; field_simp
      have hstep := weighted_comparison_step hPenτ hPenσ hτ hσ hr₁_pos hr₂_pos hU hV
        hUtop hUbot hVtop hVbot n k
      have h1 := ihn (Nat.le_of_succ_le hn) hk
      have h2 := ihk (Nat.le_of_succ_le hk)
      have hbar := barrier_superharmonic (τ := τ) (σ := σ) (τ' := τ') (T := T)
        hmτ hmσ hn_lt hk_lt
      have hsqrt : p * Real.sqrt (Φ n (k + 1)) + q * Real.sqrt (Φ (n + 1) k) ≤
          Real.sqrt (Φ (n + 1) (k + 1)) :=
        (Real.strictConcaveOn_sqrt.concaveOn.2 (hΦ0 n (k + 1)) (hΦ0 (n + 1) k)
          hp0 hq0 hpq).trans (Real.sqrt_le_sqrt hbar)
      calc r₁ ^ (n + 1) * r₂ ^ (k + 1) * dist (U (n + 1)) (V (k + 1)) ^ 2
          ≤ p * (r₁ ^ n * r₂ ^ (k + 1) * dist (U n) (V (k + 1)) ^ 2) +
              q * (r₁ ^ (n + 1) * r₂ ^ k * dist (U (n + 1)) (V k) ^ 2) := hstep
        _ ≤ p * (M * Real.sqrt (Φ n (k + 1))) + q * (M * Real.sqrt (Φ (n + 1) k)) := by gcongr
        _ = M * (p * Real.sqrt (Φ n (k + 1)) + q * Real.sqrt (Φ (n + 1) k)) := by ring
        _ ≤ M * Real.sqrt (Φ (n + 1) (k + 1)) := by gcongr

/-- **Uniform Cauchy comparison between minimizing movement interpolants**
(Crandall–Liggett, Lemma 1.2; Kobayashi, Lemma 2.1; Mayer, Section 1;
Ambrosio–Gigli–Savaré, Section 4.2). For minimizing movement sequences `U`, `V`
started at `x₀` with `φ x₀ = E` and `φ_{τ'}(x₀) = A`, when `4 τ ≤ τ'`, `4 σ ≤ τ'`,
`|m| τ ≤ 1 / 4`, `|m| σ ≤ 1 / 4`, and `t ∈ [0, T]`, we have
`dist (U ⌈t / τ⌉₊) (V ⌈t / σ⌉₊) ^ 2 ≤ cauchyK m T τ' A E * √(τ + σ)`. -/
private theorem dist_ceil_sq_le_of_penalizedConvex_crandallLiggett {τ σ τ' : ℝ≥0} {x₀ : X}
    {T A E : ℝ} (hPenτ : PenalizedConvex m τ φ) (hPenσ : PenalizedConvex m σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : |m| * τ ≤ 1 / 4) (hmσ : |m| * σ ≤ 1 / 4)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) (hT : 0 ≤ T)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    dist (U ⌈t / τ⌉₊) (V ⌈t / σ⌉₊) ^ 2 ≤
      cauchyK m T τ' A E * Real.sqrt (τ + σ) := by
  set M : ℝ := cauchyM m T τ' A E
  set C : ℝ := barrierC m T τ'
  set Φ : ℕ → ℕ → ℝ := gridBarrier τ σ C
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hσr : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hτ_le_τ' : (τ : ℝ) ≤ τ' := by linarith
  have hσ_le_τ' : (σ : ℝ) ≤ τ' := by linarith
  set r₁ : ℝ := 1 + m * τ
  set r₂ : ℝ := 1 + m * σ
  have hr₁_lo : 1 / 2 ≤ r₁ := by dsimp [r₁]; nlinarith [neg_abs_le m]
  have hr₂_lo : 1 / 2 ≤ r₂ := by dsimp [r₂]; nlinarith [neg_abs_le m]
  have hr₁_pos : 0 < r₁ := by linarith
  have hr₂_pos : 0 < r₂ := by linarith
  have hAE : A ≤ E := by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀
  have hM0 : 0 ≤ M := cauchyM_nonneg m hAE
  have hC0 : 0 ≤ C := barrierC_nonneg m (add_nonneg hT (NNReal.coe_nonneg τ'))
  -- Evaluate `grid_comparison` along the near-diagonal indices `n = ⌈t / τ⌉₊`, `k = ⌈t / σ⌉₊`.
  set n := ⌈t / τ⌉₊
  set k := ⌈t / σ⌉₊
  have hnT : n ≤ ⌈T / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right htT hτr.le)
  have hkT : k ≤ ⌈T / σ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right htT hσr.le)
  have hsqrt_le : Real.sqrt (Φ n k) ≤
      Real.sqrt (2 * τ' + 2 * C * (T + τ')) * Real.sqrt (τ + σ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (gridBarrier_ceil_le hτ hσ hττ' hστ' hC0 ht0 htT)
  -- Unwind the weights `r₁ ^ n * r₂ ^ k` via `inv_one_add_mul_pow_ceil_div_le_exp`.
  have hinv_r₁ : r₁⁻¹ ^ n ≤ Real.exp (2 * |m| * (T + τ')) :=
    (inv_one_add_mul_pow_ceil_div_le_exp (by norm_num : (0 : ℝ) < 1 / 2) hr₁_lo
      (by linarith)).trans (Real.exp_le_exp.2 (by
        rw [div_div_eq_mul_div, div_one, mul_comm |m|]; gcongr))
  have hinv_r₂ : r₂⁻¹ ^ k ≤ Real.exp (2 * |m| * (T + τ')) :=
    (inv_one_add_mul_pow_ceil_div_le_exp (by norm_num : (0 : ℝ) < 1 / 2) hr₂_lo
      (by linarith)).trans (Real.exp_le_exp.2 (by
        rw [div_div_eq_mul_div, div_one, mul_comm |m|]; gcongr))
  have hinv_prod : r₁⁻¹ ^ n * r₂⁻¹ ^ k ≤ Real.exp (4 * |m| * (T + τ')) := by
    calc r₁⁻¹ ^ n * r₂⁻¹ ^ k
        ≤ Real.exp (2 * |m| * (T + τ')) * Real.exp (2 * |m| * (T + τ')) :=
          mul_le_mul hinv_r₁ hinv_r₂ (by positivity) (by positivity)
      _ = Real.exp (4 * |m| * (T + τ')) := by rw [← Real.exp_add]; ring_nf
  have hdist_eq : dist (U n) (V k) ^ 2 =
      (r₁⁻¹ ^ n * r₂⁻¹ ^ k) * (r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2) := by
    have hr₁_ne : r₁ ^ n ≠ 0 := pow_ne_zero n hr₁_pos.ne'
    have hr₂_ne : r₂ ^ k ≠ 0 := pow_ne_zero k hr₂_pos.ne'
    simp only [inv_pow]
    field_simp
  rw [hdist_eq]
  calc (r₁⁻¹ ^ n * r₂⁻¹ ^ k) * (r₁ ^ n * r₂ ^ k * dist (U n) (V k) ^ 2)
      ≤ Real.exp (4 * |m| * (T + τ')) * (M * Real.sqrt (Φ n k)) :=
        mul_le_mul hinv_prod
          (grid_comparison hPenτ hPenσ hτ hσ hττ' hστ' hmτ hmσ hA hE hT hU0 hV0 hU hV hnT hkT)
          (mul_nonneg (mul_nonneg (pow_nonneg hr₁_pos.le n) (pow_nonneg hr₂_pos.le k))
            (sq_nonneg _)) (by positivity)
    _ ≤ Real.exp (4 * |m| * (T + τ')) *
          (M * (Real.sqrt (2 * τ' + 2 * C * (T + τ')) * Real.sqrt (τ + σ))) := by gcongr
    _ = cauchyK m T τ' A E * Real.sqrt (τ + σ) := by unfold cauchyK; ring

end DiscreteComparison

section Existence

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}

/-- A pointwise limit of the piecewise constant interpolants of minimizing movements from `x₀`
with positive time steps `τc j → 0` is an `EVI_λ` solution: the absolute continuity estimate of
minimizing movements makes it continuous on `[0, ∞)`, and
`TauCeti.isEVISolution_of_forall_mem_moreauYosidaResolvent` applies. -/
private lemma isEVISolution_of_tendsto_ceil
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤)
    {τc : ℕ → ℝ≥0} {Jc : ℕ → ℕ → X} (hτc : ∀ j, 0 < τc j) (hτcτ₁ : ∀ j, τc j < τ₁)
    (hτc0 : Tendsto τc atTop (𝓝 0)) (hJc0 : ∀ j, Jc j 0 = x₀)
    (hJc : ∀ j k, Jc j (k + 1) ∈ moreauYosidaResolvent φ (τc j) (Jc j k))
    {u : ℝ → X} (hu_lim : ∀ t ≥ 0, Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 (u t))) :
    IsEVISolution lam φ u := by
  have hbot : ∀ z, φ z ≠ ⊥ := fun z ↦
    apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ z) h₀
  have hu_cont : ContinuousOn u (Ici 0) := continuousOn_Ici_of_forall_Icc fun T hT ↦ by
    have hS : ∀ j, φ (Jc j 0) ≤ (φ x₀).toReal := fun j ↦ by
      rw [hJc0 j, EReal.coe_toReal hx₀ (hbot x₀)]
    have hAC := absolutelyContinuousOnInterval_of_forall_mem_moreauYosidaResolvent
      (l := 𝓝) (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge) hτ₀ h₀ hτc hτc0 hJc
      (by simpa only [hJc0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x₀) atTop (𝓝 x₀)))
      hS (fun t ht ↦ hu_lim t ht.1) hT
    exact uIcc_of_le hT ▸ hAC.continuousOn'
  exact isEVISolution_of_forall_mem_moreauYosidaResolvent hφ hτc hτc0
    (.of_forall fun j ↦ hconv (τc j) (hτc j) (hτcτ₁ j)) hJc hu_lim hu_cont ⟨x₀, hx₀⟩
    fun t _ ↦ hbot (u t)

/-- **Existence of `EVI_λ` flows and uniform convergence of minimizing movements**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4; Ambrosio–Gigli, Theorem 3.25). Let `φ : X → EReal`
be lower semicontinuous on a complete pseudometric space, coercive (`φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0`), and `lam`-penalized convex for all sufficiently small `τ > 0`. Then from every
point `x₀` of finite energy starts an `EVI_λ` solution `u` with `u 0 = x₀`, and the piecewise
constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of every minimizing movement scheme eventually starting
at `x₀` with positive time steps `τ j → 0` converge to `u` uniformly on `[0, T]` for every `T : ℝ`.
-/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ᶠ j in atTop, J j 0 = x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  -- Step 1: Choose a common reference scale `τ'` where `φ_{τ'}(x₀)` is finite and `|lam| τ' ≤ 1/4`.
  set r₀ : ℝ := (4 * (|lam| + 1))⁻¹
  have hr₀ : 0 < r₀ := by positivity
  set τ' : ℝ≥0 := min (τ₀ / 2) (min (τ₁ / 2) r₀.toNNReal)
  have hτ' : 0 < τ' :=
    lt_min (half_pos hτ₀) (lt_min (half_pos hτ₁) (Real.toNNReal_pos.2 hr₀))
  have hτ'τ₀ : τ' < τ₀ := (min_le_left _ _).trans_lt (half_lt_self hτ₀)
  have hτ'τ₁ : τ' < τ₁ :=
    (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hτ₁))
  have hlamτ' : |lam| * (τ' : ℝ) ≤ 1 / 4 := by
    have hτ'le : (τ' : ℝ) ≤ r₀ :=
      (NNReal.coe_le_coe.2 ((min_le_right _ _).trans (min_le_right _ _))).trans_eq
        (Real.coe_toNNReal r₀ hr₀.le)
    calc |lam| * (τ' : ℝ) ≤ (|lam| + 1) * r₀ :=
          mul_le_mul (by linarith) hτ'le (NNReal.coe_nonneg _) (by positivity)
      _ = 1 / 4 := by dsimp [r₀]; field_simp
  have hAbot : moreauYosida φ τ' x₀ ≠ ⊥ :=
    moreauYosida_ne_bot_of_lt hτ'τ₀ (edist_ne_top x₀ x₁) h₀
  have hAtop : moreauYosida φ τ' x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀)
  set A : ℝ := (moreauYosida φ τ' x₀).toReal
  set E : ℝ := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A := (EReal.coe_toReal hAtop hAbot).symm
  have hE : φ x₀ = E :=
    (EReal.coe_toReal hx₀ (apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ x₀) h₀)).symm
  have hpair : ∀ {τ σ : ℝ≥0} {U V : ℕ → X} {T : ℝ}, 0 ≤ T →
      0 < τ → 0 < σ → 4 * τ ≤ τ' → 4 * σ ≤ τ' → U 0 = x₀ → V 0 = x₀ →
      (∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) →
      (∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k)) →
      ∀ t ∈ Icc 0 T,
        dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
          cauchyK lam T τ' A E * Real.sqrt ((τ : ℝ) + σ) := by
    intro τ σ U V T hT hτ hσ hττ' hστ' hU0 hV0 hU hV t ht
    have h4_le : ∀ {δ : ℝ≥0}, 4 * δ ≤ τ' → (δ : ℝ) ≤ τ' := fun {δ} h4 ↦ by
      have : (4 : ℝ) * δ ≤ τ' := by exact_mod_cast h4
      linarith [NNReal.coe_nonneg δ]
    have hττ₁ : τ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hττ')).trans_lt hτ'τ₁
    have hστ₁ : σ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hστ')).trans_lt hτ'τ₁
    have hmτ := (mul_le_mul_of_nonneg_left (h4_le hττ') (abs_nonneg _)).trans hlamτ'
    have hmσ := (mul_le_mul_of_nonneg_left (h4_le hστ') (abs_nonneg _)).trans hlamτ'
    exact dist_ceil_sq_le_of_penalizedConvex_crandallLiggett (hconv τ hτ hττ₁) (hconv σ hσ hστ₁)
      hτ hσ hττ' hστ' hmτ hmσ hA hE hT hU0 hV0 hU hV ht.1 ht.2
  -- Step 2: Construct a reference minimizing movement family `Jc` at step sizes `τ' / 4 / (j + 1)`
  -- and pass to its uniform limit `u` by completeness.
  set τc : ℕ → ℝ≥0 := fun j ↦ τ' / 4 / ↑(j + 1)
  have hτc : ∀ j, 0 < τc j := fun j ↦ div_pos (div_pos hτ' four_pos) (Nat.cast_pos.2 j.succ_pos)
  have hτcτ' : ∀ j, 4 * τc j ≤ τ' := fun j ↦
    (mul_le_mul_of_nonneg_left
      (div_le_self zero_le (Nat.one_le_cast.2 j.succ_pos)) zero_le).trans_eq
      (mul_div_cancel₀ τ' four_ne_zero)
  have hτc_le : ∀ j, τc j ≤ τ' := fun j ↦ by
    have h4 : (4 : ℝ) * τc j ≤ τ' := by exact_mod_cast hτcτ' j
    exact NNReal.coe_le_coe.1 (by linarith [NNReal.coe_nonneg (τc j)])
  have hτc0 : Tendsto τc atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (τ' / 4))
  have hlamτc : ∀ j, 0 < 1 + lam * (τc j : ℝ) := fun j ↦ by
    have habs : |lam| * (τc j : ℝ) ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (hτc_le j)) (abs_nonneg _)).trans hlamτ'
    nlinarith [neg_abs_le lam, NNReal.coe_nonneg (τc j)]
  choose Jc hJc0 hJc using fun j ↦
    PenalizedConvex.exists_forall_mem_moreauYosidaResolvent
      hφ (hconv (τc j) (hτc j) ((hτc_le j).trans_lt hτ'τ₁)) (hτc j) (hlamτc j)
      ((hτc_le j).trans_lt hτ'τ₀) h₀ x₀
  let Fc : ℕ → ℝ → X := fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊
  have huc : ∀ T ≥ (0 : ℝ), UniformCauchySeqOn Fc atTop (Icc 0 T) := fun T hT ↦ by
    set K : ℝ := cauchyK lam T τ' A E
    have herr : Tendsto (fun p : ℕ × ℕ ↦ Real.sqrt (K * Real.sqrt ((τc p.1 : ℝ) + τc p.2)))
        (atTop ×ˢ atTop) (𝓝 0) := by
      have hsum : Tendsto (fun p : ℕ × ℕ ↦ (τc p.1 : ℝ) + τc p.2) (atTop ×ˢ atTop) (𝓝 0) := by
        simpa using ((NNReal.tendsto_coe.2 hτc0).comp tendsto_fst).add
          ((NNReal.tendsto_coe.2 hτc0).comp tendsto_snd)
      have h0 : Tendsto (fun p : ℕ × ℕ ↦ K * Real.sqrt ((τc p.1 : ℝ) + τc p.2))
          (atTop ×ˢ atTop) (𝓝 0) :=
        (((Real.continuous_sqrt.tendsto 0).comp hsum).const_mul K).trans_eq (by simp)
      exact ((Real.continuous_sqrt.tendsto 0).comp h0).trans_eq (by simp)
    exact uniformCauchySeqOn_of_dist_le herr <| .of_forall fun p t ht ↦ Real.le_sqrt_of_sq_le <|
      hpair hT (hτc p.1) (hτc p.2) (hτcτ' p.1) (hτcτ' p.2) (hJc0 p.1) (hJc0 p.2)
        (hJc p.1) (hJc p.2) t ht
  obtain ⟨u₀, hu₀⟩ := exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn
    (𝔖 := {s | ∃ T ≥ (0 : ℝ), s = Icc 0 T}) (by rintro _ ⟨T, hT, rfl⟩; exact huc T hT)
  classical
  let u : ℝ → X := Function.update u₀ 0 x₀
  have hu0 : u 0 = x₀ := Function.update_self 0 x₀ u₀
  have hu_unif : ∀ T ≥ (0 : ℝ), TendstoUniformlyOn Fc u atTop (Icc 0 T) := fun T hT ↦
    (hu₀ _ ⟨T, hT, rfl⟩).congr_inseparable_right fun t ht ↦ by
      by_cases h0 : t = 0
      · subst h0
        simpa only [u, Function.update_self] using
          tendsto_nhds_unique_inseparable ((hu₀ _ ⟨T, hT, rfl⟩).tendsto_at ht)
            (by simpa only [Fc, zero_div, Nat.ceil_zero, hJc0] using tendsto_const_nhds)
      · simp only [u, Function.update_of_ne h0]; rfl
  have hu_lim : ∀ t ≥ 0, Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 (u t)) := fun t ht ↦
    (hu_unif t ht).tendsto_at ⟨ht, le_rfl⟩
  have hu_evi : IsEVISolution lam φ u :=
    isEVISolution_of_tendsto_ceil hφ hτ₀ hconv h₀ hx₀ hτc
      (fun j ↦ (hτc_le j).trans_lt hτ'τ₁) hτc0 hJc0 hJc hu_lim
  -- Step 3: Compare any minimizing movement scheme `(τ, J)` against `(τc, Jc)`.
  refine ⟨u, hu0, hu_evi, fun τ J hτ hτ0 hJ0 hJ T ↦ ?_⟩
  set T' : ℝ := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  suffices h :
      TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T') from
    h.mono (fun t ht ↦ ⟨ht.1, ht.2.trans (le_max_left _ _)⟩)
  set K : ℝ := cauchyK lam T' τ' A E
  have herr0 :
      Tendsto (fun j ↦ Real.sqrt (K * Real.sqrt ((τc j : ℝ) + τ j))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun j ↦ (τc j : ℝ) + τ j) atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_coe.2 hτc0).add (NNReal.tendsto_coe.2 hτ0)
    have h0 : Tendsto (fun j ↦ K * Real.sqrt ((τc j : ℝ) + τ j)) atTop (𝓝 0) :=
      (((Real.continuous_sqrt.tendsto 0).comp hsum).const_mul K).trans_eq (by simp)
    exact ((Real.continuous_sqrt.tendsto 0).comp h0).trans_eq (by simp)
  refine (hu_unif T' hT').congr_dist_le herr0 ?_
  filter_upwards [hτ, hJ0, hJ,
    hτ0.eventually (ge_mem_nhds (by positivity : (0 : ℝ≥0) < τ' / 4))] with j hjτ hj0 hjJ hj4 t ht
  have h4 : 4 * τ j ≤ τ' :=
    (mul_le_mul_of_nonneg_left hj4 (by positivity)).trans_eq (mul_div_cancel₀ _ four_ne_zero)
  exact Real.le_sqrt_of_sq_le
    (hpair hT' (hτc j) hjτ (hτcτ' j) h4 (hJc0 j) hj0 (hJc j) hjJ t ht)

/-- **Characterization of the `EVI_λ` domain** (Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under
the hypotheses of `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, the set
of initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) :
    eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ :=
      exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ hx
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- **Existence of `EVI_λ` flows on the closure of the effective domain**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, every point `x₀` in
`closure {x | φ x ≠ ⊤}` is the initial point of an `EVI_λ` solution. -/
theorem exists_isEVISolution_of_mem_closure_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X}
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (eviDomain_eq_closure_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ ▸ hx₀)

end Existence

section GeodesicallyConvex

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X]
  {lam : ℝ} {φ : X → EReal}

/-- **Existence and uniform convergence of minimizing movements for geodesically convex energies
on CAT(0) spaces** (Jost; Mayer, Theorem 1.13). Let `φ : X → EReal` be lower semicontinuous and
`lam`-geodesically convex on a complete CAT(0) pseudometric space, and let `x₀` be a point of
finite energy (`φ x₀ ≠ ⊤` and `φ x₀ ≠ ⊥`). Then there starts from `x₀` an `EVI_λ` solution `u`
with `u 0 = x₀`, and all minimizing movement interpolants eventually starting at `x₀` converge
uniformly to `u` on compact time intervals `[0, T]` as `τ → 0`. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ᶠ j in atTop, J j 0 = x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, h₀⟩ :=
    hconv.exists_moreauYosida_ne_bot (hφ.lowerSemicontinuousAt x₀) hx₀ hx₀bot x₀
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ one_pos
    (fun _ _ _ ↦ hconv.penalizedConvex) h₀ hx₀

/-- **Characterization of the `EVI_λ` domain for geodesically convex energies on CAT(0) spaces**
(Jost; Mayer, Theorem 1.13). If `φ` is lower semicontinuous, `lam`-geodesically convex, and never
equal to `⊥` on a complete CAT(0) pseudometric space, then the set `TauCeti.eviDomain lam φ` of
initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem GeodesicallyConvex.eviDomain_eq_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) : eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ := hconv.exists_isEVISolution_tendstoUniformlyOn hφ hx (hbot _)
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- **Existence of `EVI_λ` flows on `closure {x | φ x ≠ ⊤}` for geodesically convex energies on
CAT(0) spaces** (Jost; Mayer, Theorem 1.13). If `φ` is lower semicontinuous, `lam`-geodesically
convex, and never equal to `⊥` on a complete CAT(0) pseudometric space, then every point
`x₀ ∈ closure {x | φ x ≠ ⊤}` is the initial point of an `EVI_λ` solution. -/
theorem GeodesicallyConvex.exists_isEVISolution_of_mem_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (hconv.eviDomain_eq_closure hφ hbot ▸ hx₀)

end GeodesicallyConvex

section QuantitativeErrorAndCurveConvexity

/-- Extracts real energy values and bounds the energy drop `e 0 - e (⌊t / τ⌋₊ + 1)` along a
minimizing movement sequence satisfying a priori lower and upper energy bounds. -/
private theorem exists_toReal_apply_and_sub_le {X : Type*} [PseudoMetricSpace X] {φ : X → EReal}
    {τ₀ τ : ℝ≥0} (hτ : 0 < τ) (hτ_lt : τ < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {S L T t : ℝ} (hS : φ (U 0) ≤ S) (ht : t ∈ Icc 0 T)
    (hL : ∀ n ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U n)) :
    ∃ e : ℕ → ℝ, (∀ n, φ (U n) = e n) ∧
      0 ≤ e 0 - e (⌊t / τ⌋₊ + 1) ∧ e 0 - e (⌊t / τ⌋₊ + 1) ≤ max 0 (S - L) := by
  have he (n : ℕ) : φ (U n) = ((φ (U n)).toReal : EReal) := (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top S)
      ((antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le n)).trans hS))
    (ne_bot_of_le_ne_bot (moreauYosida_ne_bot_of_lt hτ_lt (edist_ne_top (U n) x₁) h₀)
      (moreauYosida_le_self φ τ (U n)))).symm
  have hn : ⌊t / (τ : ℝ)⌋₊ + 1 ≤ ⌈(T + 1) / τ⌉₊ := Nat.add_one_le_iff.2 (Nat.lt_ceil.2 <|
    (Nat.floor_le (div_nonneg ht.1 (NNReal.coe_nonneg τ))).trans_lt
      ((div_lt_div_iff_of_pos_right (NNReal.coe_pos.2 hτ)).2 (by linarith [ht.2])))
  have ha0 : 0 ≤ (φ (U 0)).toReal - (φ (U (⌊t / τ⌋₊ + 1))).toReal := sub_nonneg.2
    (EReal.coe_le_coe_iff.1 (he 0 ▸ he _ ▸
      antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le _)))
  exact ⟨fun n ↦ (φ (U n)).toReal, he, ha0,
    (sub_le_sub (EReal.coe_le_coe_iff.1 (he 0 ▸ hS))
      (EReal.coe_le_coe_iff.1 (he _ ▸ hL _ hn))).trans (le_max_right _ _)⟩

/-- `η → 0` limit of `TauCeti.dist_ceil_sq_le_of_penalizedConvex` against an `EVI_lam` solution
`u` whose initial point has finite energy `φ (u 0) ≠ ⊤`. -/
private theorem dist_ceil_sq_le_of_isEVISolution_of_apply_ne_top {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {τ₀ τ : ℝ≥0} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ η in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam η φ) (hu0 : φ (u 0) ≠ ⊤)
    (hτc : PenalizedConvex lam τ φ) (hτ : 0 < τ) (hmτ : |lam| * τ ≤ 1 / 2)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {eU : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (u t) ^ 2 ≤
      2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) * dist (U 0) (u 0) ^ 2 +
        (2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))) := by
  obtain ⟨δ, hδ, hconv_ball⟩ := Metric.mem_nhdsWithin_iff.1 hconv
  set τ₁ : ℝ≥0 := δ.toNNReal
  have hτ₁ : 0 < τ₁ := Real.toNNReal_pos.2 hδ
  have hconv_lt : ∀ η : ℝ≥0, 0 < η → η < τ₁ → PenalizedConvex lam η φ := fun η hη0 hη1 ↦
    hconv_ball ⟨by simpa [τ₁, NNReal.dist_eq, abs_of_nonneg (NNReal.coe_nonneg η),
      Real.coe_toNNReal _ hδ.le] using NNReal.coe_lt_coe.2 hη1, hη0⟩
  obtain ⟨v, hv0, hv, hunif⟩ := exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex
    hφ hτ₀ hτ₁ hconv_lt h₀ hu0
  have hd_vu : dist (v t) (u t) = 0 :=
    le_antisymm ((hv.dist_le hu hφ ht).trans_eq (by simp [hv0])) dist_nonneg
  have hdist_eq : dist (U ⌈t / τ⌉₊) (u t) = dist (U ⌈t / τ⌉₊) (v t) := le_antisymm
    ((dist_triangle _ (v t) _).trans_eq (by rw [hd_vu, add_zero]))
    ((dist_triangle _ (u t) _).trans_eq (by rw [dist_comm (u t), hd_vu, add_zero]))
  set r₀ : ℝ := (2 * (|lam| + 1))⁻¹
  have hr₀ : 0 < r₀ := by positivity
  set σ₀ : ℝ≥0 := min (τ₀ / 2) (min (τ₁ / 2) r₀.toNNReal)
  have hσ₀ : 0 < σ₀ := lt_min (half_pos hτ₀) (lt_min (half_pos hτ₁) (Real.toNNReal_pos.2 hr₀))
  set η : ℕ → ℝ≥0 := fun j ↦ σ₀ / ((j : ℝ≥0) + 1)
  have hη_pos (j : ℕ) : 0 < η j := div_pos hσ₀ (by positivity)
  have hη_le_σ₀ (j : ℕ) : η j ≤ σ₀ := div_le_self hσ₀.le (by norm_cast; omega)
  have hη_lt_τ₀ (j : ℕ) : η j < τ₀ :=
    (hη_le_σ₀ j).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hτ₀))
  have hη_lt_τ₁ (j : ℕ) : η j < τ₁ :=
    (hη_le_σ₀ j).trans_lt
      ((min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hτ₁)))
  have hmη (j : ℕ) : |lam| * (η j : ℝ) ≤ 1 / 2 := by
    have hle : (η j : ℝ) ≤ r₀ := (NNReal.coe_le_coe.2
      ((hη_le_σ₀ j).trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_eq
      (Real.coe_toNNReal r₀ hr₀.le)
    calc |lam| * (η j : ℝ) ≤ (|lam| + 1) * r₀ :=
          mul_le_mul (by linarith) hle (NNReal.coe_nonneg _) (by positivity)
      _ = 1 / 2 := by dsimp [r₀]; field_simp
  have hη0 : Tendsto η atTop (𝓝 0) := NNReal.tendsto_coe.1 <| by
    simpa [η, div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (σ₀ : ℝ)
  have hηc (j : ℕ) : PenalizedConvex lam (η j) φ := hconv_lt (η j) (hη_pos j) (hη_lt_τ₁ j)
  have hη_pos_mul (j : ℕ) : 0 < 1 + lam * (η j : ℝ) := by
    linarith [(abs_le.1 ((abs_mul lam (η j)).symm ▸ (abs_of_nonneg (NNReal.coe_nonneg (η j))).symm ▸
      hmη j)).1]
  choose V hV0 hV using fun j ↦ (hηc j).exists_forall_mem_moreauYosidaResolvent hφ (hη_pos j)
    (hη_pos_mul j) (hη_lt_τ₀ j) h₀ (u 0)
  have hSV (j : ℕ) : φ (V j 0) ≤ ((φ (u 0)).toReal : EReal) := by
    rw [hV0 j, EReal.coe_toReal hu0 (apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ _) h₀)]
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top (u 0) x₁) hη_pos hη0 hV
      (by simpa only [hV0] using tendsto_const_nhds) hSV (by positivity : 0 ≤ t + 1)
  have hlim : Tendsto (fun j ↦ V j ⌈t / (η j : ℝ)⌉₊) atTop (𝓝 (v t)) :=
    (hunif η V (Eventually.of_forall hη_pos) hη0 (Eventually.of_forall hV0)
      (Eventually.of_forall hV) t).tendsto_at ⟨ht, le_rfl⟩
  set K : ℝ → ℝ := fun r ↦ max 0 (-2 * lam + 2 * lam ^ 2 * τ + 2 * lam ^ 2 * r)
  set M : ℝ := max 0 ((φ (u 0)).toReal - L)
  set R : ℝ → ℝ := fun r ↦ 2 * exp (K r * t) * dist (U 0) (u 0) ^ 2 +
    (2 * exp (K r * t) + 8) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + r * M)
  have hR_cont : Continuous R := by fun_prop
  have hev : ∀ᶠ j in atTop, dist (U ⌈t / τ⌉₊) (V j ⌈t / η j⌉₊) ^ 2 ≤ R (η j) := by
    filter_upwards [hapriori] with j hjL
    obtain ⟨eV, heV, -, hdropV⟩ := exists_toReal_apply_and_sub_le (hη_pos j) (hη_lt_τ₀ j) h₀
      (hV j) (hSV j) ⟨ht, le_rfl⟩ fun n hn ↦ (hjL n hn).1
    have hbd := TauCeti.dist_ceil_sq_le_of_penalizedConvex hτc (hηc j) hτ (hη_pos j) hmτ (hmη j)
      hU (hV j) heU heV ht
    rw [hV0 j] at hbd
    have hmulV := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdropV (NNReal.coe_nonneg (η j)))
      (by positivity : 0 ≤ 2 * exp (K (η j) * t) + 8)
    dsimp only [R, K] at hmulV ⊢
    linarith [hbd, hmulV]
  rw [hdist_eq]
  simpa [R, K] using le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist hlim).pow 2)
    ((hR_cont.tendsto 0).comp (NNReal.tendsto_coe.2 hη0)) hev

/-- **Quantitative `O(√τ)` error bound between a minimizing movement sequence and an `EVI_λ`
solution.** On a complete pseudometric space, if `φ` is lower semicontinuous, satisfies
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0` and `x₁`, and is penalized convex for all sufficiently small
positive time steps, then for every `EVI_lam` solution `u` and every minimizing movement sequence
`U` with step `τ > 0` satisfying `TauCeti.PenalizedConvex lam τ φ`, `|lam| * τ ≤ 1 / 2`, and real
energies `eU`, the squared distance `d(U ⌈t / τ⌉₊, u t)²` at time `t ≥ 0` is bounded in terms of
`d(U 0, u 0)²` and `τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))`. -/
theorem IsEVISolution.dist_ceil_sq_le_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {τ₀ τ : ℝ≥0} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ η in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam η φ)
    (hτc : PenalizedConvex lam τ φ) (hτ : 0 < τ) (hmτ : |lam| * τ ≤ 1 / 2)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {eU : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (u t) ^ 2 ≤
      2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) * dist (U 0) (u 0) ^ 2 +
        (2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))) := by
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hu_add (r : ℝ) (hr : 0 ≤ r) : Tendsto (fun s ↦ u (r + s)) (𝓝[>] 0) (𝓝 (u r)) :=
    (hu.continuousOn r hr).tendsto.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((by fun_prop : Continuous (r + ·)).tendsto' 0 r (add_zero r)).mono_left
          nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) ↦ mem_Ici.2 (add_nonneg hr hs.le))
  refine le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist (hu_add t ht)).pow 2)
    ((((tendsto_const_nhds.dist (hu_add 0 le_rfl)).pow 2).const_mul _).add_const _) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact dist_ceil_sq_le_of_isEVISolution_of_apply_ne_top (hu.comp_add_const hs.le) hφ hτ₀ h₀
    hconv ((zero_add s).symm ▸ hu.apply_ne_top hs) hτc hτ hmτ hU heU ht

/-- **Uniform convergence of minimizing movements with converging initial data.** On a complete
pseudometric space, under coercivity and `TauCeti.PenalizedConvex lam τ φ` for small `τ > 0`, any
minimizing movement family `(τ j, U j)` with `τ j → 0`, initial points `U j 0 → u 0`, and
uniformly bounded initial energy converges uniformly on `[0, T]` to an `EVI_lam` solution `u`. -/
theorem IsEVISolution.tendstoUniformlyOn_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X} (hτ_pos : ∀ᶠ j in atTop, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 (u 0)))
    {S : ℝ} (hS : ∀ᶠ j in atTop, φ (U j 0) ≤ S)
    (hU : ∀ᶠ j in atTop, ∀ n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (T : ℝ) :
    TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Metric.tendstoUniformlyOn_iff, Icc_eq_empty hT.not_ge]
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hτ_pos.and (hS.and hU))
  set τ' : ℕ → ℝ≥0 := fun j ↦ τ (j + N₁)
  set U' : ℕ → ℕ → X := fun j ↦ U (j + N₁)
  have hτ' : ∀ j, 0 < τ' j := fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).1
  have hS' : ∀ j, φ (U' j 0) ≤ S := fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).2.1
  have hU' : ∀ j n, U' j (n + 1) ∈ moreauYosidaResolvent φ (τ' j) (U' j n) :=
    fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).2.2
  have hτ'0 : Tendsto τ' atTop (𝓝 0) := hτ0.comp (tendsto_add_atTop_nat N₁)
  have hU'0 : Tendsto (fun j ↦ U' j 0) atTop (𝓝 (u 0)) := hU0.comp (tendsto_add_atTop_nat N₁)
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top (u 0) x₁) hτ' hτ'0 hU' hU'0 hS' (by positivity : 0 ≤ T + 1)
  have hτr : Tendsto (fun j ↦ (τ' j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ'0
  have hτw : Tendsto τ' atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ'0 (Eventually.of_forall hτ')
  have hlam_ev : ∀ᶠ j in atTop, |lam| * (τ' j : ℝ) ≤ 1 / 2 :=
    (mul_zero |lam| ▸ hτr.const_mul |lam|).eventually (ge_mem_nhds (by norm_num))
  set Kmax : ℝ := 2 * |lam| + 2 * lam ^ 2; set M : ℝ := max 0 (S - L)
  set E : ℕ → ℝ := fun j ↦
    2 * exp (Kmax * T) * dist (U' j 0) (u 0) ^ 2 + (2 * exp (Kmax * T) + 8) * M * τ' j
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have hd0 : Tendsto (fun j ↦ dist (U' j 0) (u 0)) atTop (𝓝 0) := by
      simpa using hU'0.dist (tendsto_const_nhds (x := u 0))
    simpa [E] using ((hd0.pow 2).const_mul (2 * exp (Kmax * T))).add
      (hτr.const_mul ((2 * exp (Kmax * T) + 8) * M))
  suffices h : TendstoUniformlyOn (fun j t ↦ U' j ⌈t / (τ' j : ℝ)⌉₊) u atTop (Icc 0 T) by
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (h ε hε)
    exact eventually_atTop.2 ⟨N₁ + N₂, fun j hj t ht ↦ by
      simpa [U', τ', Nat.sub_add_cancel ((Nat.le_add_right N₁ N₂).trans hj)] using
        hN₂ (j - N₁) (Nat.le_sub_of_add_le' hj) t ht⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hτw.eventually hconv, hlam_ev, hτr.eventually (ge_mem_nhds one_pos),
    hτ'0.eventually (gt_mem_nhds hτ₀), hapriori,
    hE0.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hτc hmτ _ hτ_lt hL hEj t ht
  obtain ⟨eU, heU, haU, hdropU⟩ :=
    exists_toReal_apply_and_sub_le (hτ' j) hτ_lt h₀ (hU' j) (hS' j) ht fun n hn ↦ (hL n hn).1
  have hbd := hu.dist_ceil_sq_le_of_penalizedConvex hφ hτ₀ h₀ hconv hτc (hτ' j) hmτ (hU' j)
    heU ht.1
  have hexp : exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ' j) * t) ≤ exp (Kmax * T) :=
    exp_le_exp.2 <| mul_le_mul (max_le (by positivity) (by
      dsimp [Kmax]; nlinarith [neg_le_abs lam, sq_nonneg lam])) ht.2 ht.1 (by positivity)
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le_two)
    (sq_nonneg (dist (U' j 0) (u 0)))
  have h2 := mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_left hexp zero_le_two) 8)
    (mul_le_mul_of_nonneg_left hdropU (NNReal.coe_nonneg (τ' j)))
    (mul_nonneg (NNReal.coe_nonneg (τ' j)) haU) (by positivity)
  have hsq : dist (u t) (U' j ⌈t / (τ' j : ℝ)⌉₊) ^ 2 < ε ^ 2 := by
    rw [dist_comm]; dsimp only [E] at hEj; nlinarith [hbd, h1, h2, hEj]
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

/-- On a complete metric space, under coercivity and `TauCeti.PenalizedConvex` for small time
steps, every generalized minimizing movement of a lower semicontinuous energy with respect to an
auxiliary convergence `l` along which `edist z ·` is sequentially lower semicontinuous is an
`EVI_lam` solution. -/
theorem IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex {X : Type*}
    [MetricSpace X] [CompleteSpace X] {l : X → Filter X} {lam : ℝ} {φ : X → EReal} {x₀ : X}
    {v : ℝ → X} (hv : IsGeneralizedMinimizingMovement l φ x₀ v)
    (hd : ∀ (z : X) ⦃w : ℕ → X⦄ ⦃y : X⦄, Tendsto w atTop (l y) →
      edist z y ≤ liminf (fun n ↦ edist z (w n)) atTop)
    (hφ : LowerSemicontinuous φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) :
    IsEVISolution lam φ v := by
  obtain ⟨τ, U, hτ, hτ0, hU, hU0, ⟨S, hS⟩, hlim⟩ := isGeneralizedMinimizingMovement_iff.1 hv
  have hx₀ : φ x₀ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top S) <|
    ((hφ.le_liminf x₀).trans hU0.liminf_le_liminf_comp).trans
      ((liminf_le_liminf (Eventually.of_forall hS)).trans_eq (by simp [liminf_const]))
  obtain ⟨δ, hδ, hconv_ball⟩ := Metric.mem_nhdsWithin_iff.1 hconv
  set τ₁ : ℝ≥0 := δ.toNNReal
  have hτ₁ : 0 < τ₁ := Real.toNNReal_pos.2 hδ
  have hconv_lt : ∀ η : ℝ≥0, 0 < η → η < τ₁ → PenalizedConvex lam η φ := fun η hη0 hη1 ↦
    hconv_ball ⟨by simpa [τ₁, NNReal.dist_eq, abs_of_nonneg (NNReal.coe_nonneg η),
      Real.coe_toNNReal _ hδ.le] using NNReal.coe_lt_coe.2 hη1, hη0⟩
  obtain ⟨u, hu0, hu, _⟩ :=
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ hτ₁ hconv_lt h₀ hx₀
  refine hu.congr fun t (ht : 0 ≤ t) ↦ ?_
  have h1 := (hu.tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv (Eventually.of_forall hτ)
    hτ0 (hu0.symm ▸ hU0) (Eventually.of_forall hS) (Eventually.of_forall hU) t).tendsto_at
    (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  have hed := hd (u t) (hlim t ht)
  have hed0 : Tendsto (fun j ↦ edist (u t) (U j ⌈t / (τ j : ℝ)⌉₊)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := u t)).edist h1
  rw [hed0.liminf_eq] at hed
  exact edist_le_zero.1 hed

/-- **Generation of `EVI_λ` flows under convexity along curves** (Ambrosio–Gigli, Theorem 3.25).
Let `φ` be a lower semicontinuous energy on a complete pseudometric space that never takes the
value `⊥`. Suppose that for every base point `w` and any two points `v₀`, `v₁` of `{y | φ y ≠ ⊤}`
there is a curve `γ` from `v₀` to `v₁` along which `φ` is `lam`-convex and `z ↦ d(z, w)²` is
`2`-convex. Then coercivity holds automatically, and for every `x₀` with `φ x₀ ≠ ⊤` there is an
`EVI_lam` solution `u` from `x₀` to which minimizing movement interpolants with converging initial
points and uniformly bounded initial energy converge locally uniformly. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ᶠ j in atTop, 0 < τ j) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ᶠ j in atTop, φ (U j 0) ≤ S) →
        (∀ᶠ j in atTop, ∀ n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  set r₀ : ℝ := (2 * (|lam| + 1))⁻¹
  have hr₀ : 0 < r₀ := by positivity
  set τ₀ : ℝ≥0 := r₀.toNNReal
  have hτ₀ : 0 < τ₀ := Real.toNNReal_pos.2 hr₀
  have hmτ₀ : 0 < 1 + lam * (τ₀ : ℝ) := by
    have hle : (τ₀ : ℝ) ≤ r₀ := (Real.coe_toNNReal r₀ hr₀.le).le
    have habs : |lam * (τ₀ : ℝ)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg τ₀)]
      calc |lam| * (τ₀ : ℝ) ≤ (|lam| + 1) * r₀ :=
            mul_le_mul (by linarith) hle (NNReal.coe_nonneg _) (by positivity)
        _ = 1 / 2 := by dsimp [r₀]; field_simp
    linarith [(abs_le.1 habs).1]
  have h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥ :=
    moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq hφ hbot
      (fun v₀ _ h₀ h₁ ↦ hconv v₀ h₀ h₁) hmτ₀ x₀
  have hpen : ∀ τ : ℝ≥0, 0 < τ → τ < 1 → PenalizedConvex lam τ φ := fun _ _ _ ↦
    penalizedConvex_of_convexAlong_and_convexAlong_dist_sq hconv
  obtain ⟨u, hu0, hu, _⟩ := exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀
    one_pos hpen h₀ hx₀
  exact ⟨u, hu0, hu, fun τ U hτ hτ0 hU0 ⟨_, hS⟩ hU T ↦
    hu.tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀
      (Eventually.of_forall fun _ ↦ penalizedConvex_of_convexAlong_and_convexAlong_dist_sq hconv)
      hτ hτ0 (hu0.symm ▸ hU0) hS hU T⟩

/-- Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq`, the
domain of the `EVI_lam` flow equals `closure {y | φ y ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_convexAlong_and_convexAlong_dist_sq {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ :=
      exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq
        hφ hbot hconv hx
    mem_eviDomain.2 ⟨u, hu, hu0⟩

end QuantitativeErrorAndCurveConvexity

end TauCeti
