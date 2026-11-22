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
`φ x₀ ≠ ⊤` (`TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`). The sharp
bilinear-interpolation comparison estimate `TauCeti.dist_ceil_sq_le_of_penalizedConvex` (from
`TauCeti.Analysis.GradientFlow.MoreauYosida.ErrorEstimate`) bounds the squared distance between
the interpolants of two schemes with time steps `τ` and `σ` on `[0, T]` in terms of `d(U 0, V 0)²`
and `τ` and `σ` times their discrete energy drops—in particular by a multiple of `τ + σ`
(`O(√(τ + σ))` in distance) when `U 0 = V 0 = x₀`. Passing `η → 0` in
`TauCeti.dist_ceil_sq_le_of_penalizedConvex` yields the quantitative error bound
`TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex` against any `EVI_m` solution, bounding
`d(U ⌈t / τ⌉₊, u t)²` in terms of `d(U 0, u 0)²` and `τ` times the discrete energy drop (giving an
`O(√τ)` error in distance when `d(U 0, u 0) = O(√τ)` and the energy drop is bounded). This extends
uniform convergence on `[0, T]` as `τ → 0` to minimizing movements with converging initial points
and uniformly bounded initial energy
(`TauCeti.IsEVISolution.tendstoUniformlyOn_of_penalizedConvex`,
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`) and identifies generalized
minimizing movements with respect to general auxiliary convergences
(`TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`).

Since `TauCeti.eviDomain m φ` is closed on a complete space (`TauCeti.isClosed_eviDomain`),
existence on `{x | φ x ≠ ⊤}` extends to every `x₀ ∈ closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_subset`,
`TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex`), giving
`TauCeti.eviDomain m φ = closure {x | φ x ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_penalizedConvex`). On a complete CAT(0) pseudometric space,
`m`-geodesically convex lower semicontinuous energies that never take the value `⊥` satisfy both
hypotheses automatically whenever the effective domain is nonempty; more generally, this holds
under Ambrosio–Gigli's curve-convexity Assumption 3.24 (`TauCeti.ConvexWithDistSq`).

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
* `TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex`,
  `TauCeti.IsEVISolution.tendstoUniformlyOn_of_penalizedConvex`, and
  `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`: quantitative error
  bound against an `EVI_m` solution (in terms of `d(U 0, u 0)²` and `τ` times the energy drop, so
  `O(√τ)` in distance when `d(U 0, u 0) = O(√τ)` and the energy drop is bounded), uniform
  convergence from converging initial data with uniformly bounded energy, and `EVI_m`
  identification of generalized minimizing movements for general auxiliary convergences.
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`: existence of the `EVI_m`
  solution and uniform convergence on compact time intervals of minimizing movement interpolants
  with converging initial data as `τ → 0`, on a complete space
  (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex` and
  `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: existence on `closure {x | φ x ≠ ⊤}` and
  `TauCeti.eviDomain m φ = closure {x | φ x ≠ ⊤}` under penalized convexity
  (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.ConvexWithDistSq.exists_isEVISolution_tendstoUniformlyOn`,
  `TauCeti.ConvexWithDistSq.eviDomain_eq_closure`, and
  `TauCeti.ConvexWithDistSq.exists_isEVISolution_of_mem_closure`: generation of `EVI_λ` flows
  under Ambrosio–Gigli Assumption 3.24 and Theorem 3.25.
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

private lemma floor_div_add_one_le_ceil_add_one {τ : ℝ≥0} (hτ : 0 < τ) {t T : ℝ}
    (ht : t ∈ Icc 0 T) : ⌊t / (τ : ℝ)⌋₊ + 1 ≤ ⌈(T + 1) / τ⌉₊ :=
  Nat.add_one_le_iff.2 (Nat.lt_ceil.2 <|
    (Nat.floor_le (div_nonneg ht.1 (NNReal.coe_nonneg τ))).trans_lt
      ((div_lt_div_iff_of_pos_right (NNReal.coe_pos.2 hτ)).2 (by linarith [ht.2])))

/-- Extracts real energy values and bounds the energy drop `e 0 - e (⌊t / τ⌋₊ + 1)` along a
minimizing movement sequence satisfying a priori lower and upper energy bounds. -/
private theorem exists_toReal_apply_and_sub_le {X : Type*} [PseudoMetricSpace X] {φ : X → EReal}
    {τ₀ τ : ℝ≥0} (hτ_lt : τ < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {S L t : ℝ} (hS : φ (U 0) ≤ S) (hL : (L : EReal) ≤ φ (U (⌊t / τ⌋₊ + 1))) :
    ∃ e : ℕ → ℝ, (∀ n, φ (U n) = e n) ∧
      0 ≤ e 0 - e (⌊t / τ⌋₊ + 1) ∧ e 0 - e (⌊t / τ⌋₊ + 1) ≤ max 0 (S - L) := by
  have he (n : ℕ) : φ (U n) = ((φ (U n)).toReal : EReal) := (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top S)
      ((antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le n)).trans hS))
    (ne_bot_of_le_ne_bot (moreauYosida_ne_bot_of_lt hτ_lt (edist_ne_top (U n) x₁) h₀)
      (moreauYosida_le_self φ τ (U n)))).symm
  have ha0 : 0 ≤ (φ (U 0)).toReal - (φ (U (⌊t / τ⌋₊ + 1))).toReal := sub_nonneg.2
    (EReal.coe_le_coe_iff.1 (he 0 ▸ he _ ▸
      antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le _)))
  exact ⟨fun n ↦ (φ (U n)).toReal, he, ha0,
    (sub_le_sub (EReal.coe_le_coe_iff.1 (he 0 ▸ hS))
      (EReal.coe_le_coe_iff.1 (he _ ▸ hL))).trans (le_max_right _ _)⟩

/-- Lower bound on `φ (W (⌊t / δ⌋₊ + 1))` from `le_apply_of_forall_mem_moreauYosidaResolvent`
for `4 * δ ≤ τ'` and `t ∈ [0, T]`. -/
private lemma le_apply_floor_add_one_of_same_init {τ' δ : ℝ≥0} {x₀ : X} {T t A E : ℝ}
    (hδ : 0 < δ) (hδτ' : 4 * δ ≤ τ') (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    {W : ℕ → X} (hW0 : W 0 = x₀)
    (hW : ∀ n, W (n + 1) ∈ moreauYosidaResolvent φ δ (W n)) (ht : t ∈ Icc 0 T) :
    ((A - (E - A) * Real.exp (8 * (T + τ') / τ') : ℝ) : EReal) ≤
      φ (W (⌊t / (δ : ℝ)⌋₊ + 1)) := by
  have hδr : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
  have hδτ'r : (δ : ℝ) ≤ τ' := by
    have : (4 : ℝ) * δ ≤ τ' := by exact_mod_cast hδτ'
    linarith
  have hEA : 0 ≤ E - A := sub_nonneg.2 (by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀)
  have hfloor : ((⌊t / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ) * δ ≤ T + τ' := by
    push_cast
    calc ((⌊t / (δ : ℝ)⌋₊ : ℝ) + 1) * δ
        ≤ (t / δ + 1) * δ := by gcongr; exact Nat.floor_le (div_nonneg ht.1 hδr.le)
      _ = t + δ := by field_simp
      _ ≤ T + τ' := add_le_add ht.2 hδτ'r
  have hexp : (1 + 8 * (δ : ℝ) / τ') ^ (⌊t / (δ : ℝ)⌋₊ + 1) ≤ Real.exp (8 * (T + τ') / τ') :=
    calc (1 + 8 * (δ : ℝ) / τ') ^ (⌊t / (δ : ℝ)⌋₊ + 1)
        ≤ (Real.exp (8 * δ / τ')) ^ (⌊t / (δ : ℝ)⌋₊ + 1) := by
          gcongr; linarith [Real.add_one_le_exp (8 * (δ : ℝ) / τ')]
      _ = Real.exp (((⌊t / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ) * (8 * δ / τ')) :=
          (Real.exp_natCast_mul _ _).symm
      _ ≤ Real.exp (8 * (T + τ') / τ') := Real.exp_le_exp.2 (by
          rw [show ((⌊t / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ) * (8 * δ / τ') =
            8 * (((⌊t / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ) * δ) / τ' by ring]
          gcongr)
  have hlow := le_apply_of_forall_mem_moreauYosidaResolvent hW hδ hδτ' (hW0 ▸ hA) (hW0 ▸ hE)
    (⌊t / (δ : ℝ)⌋₊ + 1)
  have hmul : (E - A) * (1 + 8 * (δ : ℝ) / τ') ^ (⌊t / (δ : ℝ)⌋₊ + 1) ≤
      (E - A) * Real.exp (8 * (T + τ') / τ') := mul_le_mul_of_nonneg_left hexp hEA
  exact (EReal.coe_le_coe_iff.2 (by linarith)).trans hlow

/-- Quantitative Cauchy bound for two minimizing movement sequences from the same finite-energy
initial point `x₀`, derived from `TauCeti.dist_ceil_sq_le_of_penalizedConvex` and
`TauCeti.le_apply_of_forall_mem_moreauYosidaResolvent`. -/
private lemma dist_ceil_sq_le_of_same_init {τ' τ σ : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hτc : PenalizedConvex lam τ φ) (hσc : PenalizedConvex lam σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : |lam| * τ ≤ 1 / 2) (hmσ : |lam| * σ ≤ 1 / 2)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
      (2 * Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) + 8) *
        ((E - A) * (1 + Real.exp (8 * (T + τ') / τ'))) * ((τ : ℝ) + σ) := by
  have hlt : ∀ {δ : ℝ≥0}, 0 < δ → 4 * δ ≤ τ' → δ < τ' := fun {δ} hδ h4 ↦ NNReal.coe_lt_coe.1 <| by
    have : (4 : ℝ) * δ ≤ τ' := by exact_mod_cast h4
    linarith [NNReal.coe_pos.2 hδ]
  have hEA : 0 ≤ E - A := sub_nonneg.2 (by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀)
  set L : ℝ := A - (E - A) * Real.exp (8 * (T + τ') / τ')
  obtain ⟨eU, heU, hU0', hdropU⟩ := exists_toReal_apply_and_sub_le (hlt hτ hττ')
    (hA ▸ EReal.coe_ne_bot A) hU (hU0 ▸ hE).le
    (le_apply_floor_add_one_of_same_init hτ hττ' hA hE hU0 hU ht)
  obtain ⟨eV, heV, hV0', hdropV⟩ := exists_toReal_apply_and_sub_le (hlt hσ hστ')
    (hA ▸ EReal.coe_ne_bot A) hV (hV0 ▸ hE).le
    (le_apply_floor_add_one_of_same_init hσ hστ' hA hE hV0 hV ht)
  have hmax : max 0 (E - L) = (E - A) * (1 + Real.exp (8 * (T + τ') / τ')) := by
    rw [show E - L = (E - A) * (1 + Real.exp (8 * (T + τ') / τ')) by dsimp [L]; ring]
    exact max_eq_right (mul_nonneg hEA (by positivity))
  have hbd := TauCeti.dist_ceil_sq_le_of_penalizedConvex hτc hσc hτ hσ hmτ hmσ hU hV heU heV ht.1
  rw [hU0, hV0, dist_self, zero_pow two_ne_zero, mul_zero, zero_add] at hbd
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hexp : Real.exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ + 2 * lam ^ 2 * σ) * t) ≤
      Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) :=
    Real.exp_le_exp.2 <| mul_le_mul (max_le (by positivity) (by
      linarith [neg_le_abs lam, mul_le_mul_of_nonneg_left h4τ (sq_nonneg lam),
        mul_le_mul_of_nonneg_left h4σ (sq_nonneg lam)])) ht.2 ht.1 (by positivity)
  have hdrop : (τ : ℝ) * (eU 0 - eU (⌊t / (τ : ℝ)⌋₊ + 1)) +
      σ * (eV 0 - eV (⌊t / (σ : ℝ)⌋₊ + 1)) ≤
      (E - A) * (1 + Real.exp (8 * (T + τ') / τ')) * (τ + σ) := by
    rw [hmax] at hdropU hdropV
    nlinarith [NNReal.coe_nonneg τ, NNReal.coe_nonneg σ]
  refine hbd.trans ?_
  rw [mul_assoc (2 * Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) + 8)]
  exact mul_le_mul (by gcongr) hdrop
    (add_nonneg (mul_nonneg (NNReal.coe_nonneg _) hU0') (mul_nonneg (NNReal.coe_nonneg _) hV0'))
    (by positivity)

/-- Uniform Cauchy constant for minimizing movements starting at `x₀`. -/
private def cauchyConst (lam τ' A E T : ℝ) : ℝ :=
  (2 * Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) + 8) *
    ((E - A) * (1 + Real.exp (8 * (T + τ') / τ')))

/-- Pairwise comparison bound at scale `τ'` for two schemes starting at `x₀`. -/
private lemma dist_ceil_sq_le_cauchyConst {τ₁ τ' τ σ : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hτ'τ₁ : τ' < τ₁) (hlamτ' : |lam| * (τ' : ℝ) ≤ 1 / 4)
    (hconv : ∀ δ : ℝ≥0, 0 < δ → δ < τ₁ → PenalizedConvex lam δ φ)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
      cauchyConst lam τ' A E T * ((τ : ℝ) + σ) := by
  have h4_le : ∀ {δ : ℝ≥0}, 4 * δ ≤ τ' → (δ : ℝ) ≤ τ' := fun {δ} h4 ↦ by
    have : (4 : ℝ) * δ ≤ τ' := by exact_mod_cast h4
    linarith [NNReal.coe_nonneg δ]
  have hττ₁ : τ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hττ')).trans_lt hτ'τ₁
  have hστ₁ : σ < τ₁ := (NNReal.coe_le_coe.1 (h4_le hστ')).trans_lt hτ'τ₁
  have hmτ : |lam| * (τ : ℝ) ≤ 1 / 2 :=
    ((mul_le_mul_of_nonneg_left (h4_le hττ') (abs_nonneg _)).trans hlamτ').trans (by norm_num)
  have hmσ : |lam| * (σ : ℝ) ≤ 1 / 2 :=
    ((mul_le_mul_of_nonneg_left (h4_le hστ') (abs_nonneg _)).trans hlamτ').trans (by norm_num)
  exact dist_ceil_sq_le_of_same_init (hconv τ hτ hττ₁) (hconv σ hσ hστ₁)
    hτ hσ hττ' hστ' hmτ hmσ hA hE hU0 hV0 hU hV ht

/-- Constructs a reference minimizing movement family `(τc, Jc)` from `x₀` and passes to its
uniform limit `u`, which is an `EVI_lam` solution with `u 0 = x₀`. -/
private lemma exists_limit_const_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ τ' : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ' : 0 < τ')
    (hτ'τ₀ : τ' < τ₀) (hτ'τ₁ : τ' < τ₁) (hlamτ' : |lam| * (τ' : ℝ) ≤ 1 / 4)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤)
    {A E : ℝ} (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E) :
    ∃ (u : ℝ → X) (τc : ℕ → ℝ≥0) (Jc : ℕ → ℕ → X),
      u 0 = x₀ ∧ IsEVISolution lam φ u ∧ (∀ j, 0 < τc j) ∧ (∀ j, 4 * τc j ≤ τ') ∧
        Tendsto τc atTop (𝓝 0) ∧ (∀ j, Jc j 0 = x₀) ∧
        (∀ j k, Jc j (k + 1) ∈ moreauYosidaResolvent φ (τc j) (Jc j k)) ∧
        ∀ T ≥ (0 : ℝ), TendstoUniformlyOn (fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  set τc : ℕ → ℝ≥0 := fun j ↦ τ' / 4 / ↑(j + 1)
  have hτc : ∀ j, 0 < τc j := fun j ↦ div_pos (div_pos hτ' four_pos) (Nat.cast_pos.2 j.succ_pos)
  have hτcτ' : ∀ j, 4 * τc j ≤ τ' := fun j ↦
    (mul_le_mul_of_nonneg_left
      (div_le_self zero_le (Nat.one_le_cast.2 j.succ_pos)) zero_le).trans_eq
      (mul_div_cancel₀ τ' four_ne_zero)
  have hτc_le : ∀ j, τc j ≤ τ' := fun j ↦ NNReal.coe_le_coe.1 <| by
    have h4 : (4 : ℝ) * τc j ≤ τ' := by exact_mod_cast hτcτ' j
    linarith [NNReal.coe_nonneg (τc j)]
  have hτc0 : Tendsto τc atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (τ' / 4))
  have hlamτc : ∀ j, 0 < 1 + lam * (τc j : ℝ) := fun j ↦ one_add_mul_pos_of_abs_mul_le_half
    (τc j).property (((mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (hτc_le j))
      (abs_nonneg _)).trans hlamτ').trans (by norm_num))
  choose Jc hJc0 hJc using fun j ↦
    PenalizedConvex.exists_forall_mem_moreauYosidaResolvent
      hφ (hconv (τc j) (hτc j) ((hτc_le j).trans_lt hτ'τ₁)) (hτc j) (hlamτc j)
      ((hτc_le j).trans_lt hτ'τ₀) h₀ x₀
  let Fc : ℕ → ℝ → X := fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊
  have huc : ∀ T ≥ (0 : ℝ), UniformCauchySeqOn Fc atTop (Icc 0 T) := fun T _ ↦ by
    have herr : Tendsto (fun p : ℕ × ℕ ↦
        Real.sqrt (cauchyConst lam τ' A E T * ((τc p.1 : ℝ) + τc p.2))) (atTop ×ˢ atTop) (𝓝 0) :=
      (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp <| by
        simpa using (((NNReal.tendsto_coe.2 hτc0).comp tendsto_fst).add
          ((NNReal.tendsto_coe.2 hτc0).comp tendsto_snd)).const_mul (cauchyConst lam τ' A E T)
    exact uniformCauchySeqOn_of_dist_le herr <| .of_forall fun p t ht ↦ Real.le_sqrt_of_sq_le <|
      dist_ceil_sq_le_cauchyConst hτ'τ₁ hlamτ' hconv hA hE (hτc p.1) (hτc p.2)
        (hτcτ' p.1) (hτcτ' p.2) (hJc0 p.1) (hJc0 p.2) (hJc p.1) (hJc p.2) ht
  obtain ⟨u₀, hu₀⟩ := exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn
    (𝔖 := {s | ∃ T ≥ (0 : ℝ), s = Icc 0 T}) (by rintro _ ⟨T, hT, rfl⟩; exact huc T hT)
  classical
  let u : ℝ → X := Function.update u₀ 0 x₀
  have hu_unif : ∀ T ≥ (0 : ℝ), TendstoUniformlyOn Fc u atTop (Icc 0 T) := fun T hT ↦
    (hu₀ _ ⟨T, hT, rfl⟩).congr_inseparable_right fun t ht ↦ by
      by_cases h0 : t = 0
      · subst h0
        simpa only [u, Function.update_self] using
          tendsto_nhds_unique_inseparable ((hu₀ _ ⟨T, hT, rfl⟩).tendsto_at ht)
            (by simpa only [Fc, zero_div, Nat.ceil_zero, hJc0] using tendsto_const_nhds)
      · simp only [u, Function.update_of_ne h0]; rfl
  exact ⟨u, τc, Jc, Function.update_self 0 x₀ u₀,
    isEVISolution_of_tendsto_ceil hφ hτ₀ hconv h₀ hx₀ hτc
      (fun j ↦ (hτc_le j).trans_lt hτ'τ₁) hτc0 hJc0 hJc
      (fun t ht ↦ (hu_unif t ht).tendsto_at ⟨ht, le_rfl⟩),
    hτc, hτcτ', hτc0, hJc0, hJc, hu_unif⟩

/-- Constant-initial-data form of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, used internally to obtain the
solution and pass to `η → 0` in the quantitative comparison. -/
private theorem exists_isEVISolution_tendstoUniformlyOn_const_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ᶠ j in atTop, J j 0 = x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  -- Step 1: Choose a reference scale `τ'` with `τ' < min τ₀ τ₁` and `|lam| * τ' ≤ 1 / 4`.
  obtain ⟨τ', hτ', hτ'min, hlamτ'⟩ :=
    exists_pos_abs_mul_le lam (by norm_num : (0 : ℝ) < 1 / 4) (lt_min hτ₀ hτ₁)
  have hτ'τ₀ : τ' < τ₀ := hτ'min.trans_le (min_le_left _ _)
  have hτ'τ₁ : τ' < τ₁ := hτ'min.trans_le (min_le_right _ _)
  set A : ℝ := (moreauYosida φ τ' x₀).toReal
  set E : ℝ := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A := (EReal.coe_toReal
    (ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀))
    (moreauYosida_ne_bot_of_lt hτ'τ₀ (edist_ne_top x₀ x₁) h₀)).symm
  have hE : φ x₀ = E := (EReal.coe_toReal hx₀
    (apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ x₀) h₀)).symm
  -- Step 2: Obtain the reference limit `u` from `exists_limit_const_of_penalizedConvex`.
  obtain ⟨u, τc, Jc, hu0, hu_evi, hτc, hτcτ', hτc0, hJc0, hJc, hu_unif⟩ :=
    exists_limit_const_of_penalizedConvex hφ hτ₀ hτ' hτ'τ₀ hτ'τ₁ (hlamτ' le_rfl) hconv h₀ hx₀ hA hE
  -- Step 3: Compare any constant-initial-data scheme `(τ, J)` against `(τc, Jc)`.
  refine ⟨u, hu0, hu_evi, fun τ J hτ hτ0 hJ0 hJ T ↦ ?_⟩
  set T' : ℝ := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  suffices h : TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T') from
    h.mono (fun t ht ↦ ⟨ht.1, ht.2.trans (le_max_left _ _)⟩)
  have herr0 : Tendsto (fun j ↦
      Real.sqrt (cauchyConst lam τ' A E T' * ((τc j : ℝ) + τ j))) atTop (𝓝 0) :=
    (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp <| by
      simpa using ((NNReal.tendsto_coe.2 hτc0).add
        (NNReal.tendsto_coe.2 hτ0)).const_mul (cauchyConst lam τ' A E T')
  refine (hu_unif T' hT').congr_dist_le herr0 ?_
  filter_upwards [hτ, hJ0, hJ,
    hτ0.eventually (ge_mem_nhds (by positivity : (0 : ℝ≥0) < τ' / 4))] with j hjτ hj0 hjJ hj4 t ht
  have h4 : 4 * τ j ≤ τ' :=
    (mul_le_mul_of_nonneg_left hj4 (by positivity)).trans_eq (mul_div_cancel₀ _ four_ne_zero)
  exact Real.le_sqrt_of_sq_le (dist_ceil_sq_le_cauchyConst hτ'τ₁ (hlamτ' le_rfl) hconv hA hE
    (hτc j) hjτ (hτcτ' j) h4 (hJc0 j) hj0 (hJc j) hjJ ht)

end Existence

section QuantitativeErrorAndCurveConvexity

/-- Auxiliary sequence `η j → 0` strictly below `b` with `|lam| * η j ≤ 1 / 2` and
`0 < 1 + lam * η j`. -/
private lemma exists_pos_seq_tendsto_zero_lt (lam : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    ∃ η : ℕ → ℝ≥0, (∀ j, 0 < η j) ∧ (∀ j, η j < b) ∧ (∀ j, |lam| * (η j : ℝ) ≤ 1 / 2) ∧
      (∀ j, 0 < 1 + lam * (η j : ℝ)) ∧ Tendsto η atTop (𝓝 0) := by
  obtain ⟨σ₀, hσ₀, hσ₀b, hlamσ₀⟩ := exists_pos_abs_mul_le lam (by norm_num : (0 : ℝ) < 1 / 2) hb
  let η : ℕ → ℝ≥0 := fun j ↦ σ₀ / ((j : ℝ≥0) + 1)
  have hle (j : ℕ) : η j ≤ σ₀ := div_le_self hσ₀.le (by norm_cast; omega)
  have hpos (j : ℕ) : 0 < η j := div_pos hσ₀ (by positivity)
  exact ⟨η, hpos, fun j ↦ (hle j).trans_lt hσ₀b, fun j ↦ hlamσ₀ (hle j),
    fun j ↦ one_add_mul_pos_of_abs_mul_le_half (hpos j).le (hlamσ₀ (hle j)),
    NNReal.tendsto_coe.1 <| by
      simpa [η, div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (σ₀ : ℝ)⟩

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
  -- Identify `u` with the minimizing movement limit `v` from `u 0`.
  obtain ⟨τ₁, hτ₁, hconv_lt⟩ := ((nhdsGT_basis (0 : ℝ≥0)).eventually_iff).1 hconv
  obtain ⟨v, hv0, hv, hunif⟩ := exists_isEVISolution_tendstoUniformlyOn_const_of_penalizedConvex
    hφ hτ₀ hτ₁ (fun _ h0 h1 ↦ hconv_lt ⟨h0, h1⟩) h₀ hu0
  have hd_vu : dist (v t) (u t) = 0 :=
    le_antisymm ((hv.dist_le hu hφ ht).trans_eq (by simp [hv0])) dist_nonneg
  have hdist_eq : dist (U ⌈t / τ⌉₊) (u t) = dist (U ⌈t / τ⌉₊) (v t) := le_antisymm
    ((dist_triangle _ (v t) _).trans_eq (by rw [hd_vu, add_zero]))
    ((dist_triangle _ (u t) _).trans_eq (by rw [dist_comm (u t), hd_vu, add_zero]))
  -- Construct auxiliary schemes `(η j, V j)` starting at `u 0` with `η j → 0`.
  obtain ⟨η, hη_pos, hη_lt, hmη, hη_mul, hη0⟩ := exists_pos_seq_tendsto_zero_lt lam (lt_min hτ₀ hτ₁)
  have hη_lt_τ₀ j : η j < τ₀ := (hη_lt j).trans_le (min_le_left _ _)
  have hηc j : PenalizedConvex lam (η j) φ :=
    hconv_lt ⟨hη_pos j, (hη_lt j).trans_le (min_le_right _ _)⟩
  choose V hV0 hV using fun j ↦ (hηc j).exists_forall_mem_moreauYosidaResolvent hφ (hη_pos j)
    (hη_mul j) (hη_lt_τ₀ j) h₀ (u 0)
  have hSV (j : ℕ) : φ (V j 0) ≤ ((φ (u 0)).toReal : EReal) := by
    rw [hV0 j, EReal.coe_toReal hu0 (apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ _) h₀)]
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top (u 0) x₁) hη_pos hη0 hV
      (by simpa only [hV0] using tendsto_const_nhds) hSV (by positivity : 0 ≤ t + 1)
  have hlim : Tendsto (fun j ↦ V j ⌈t / (η j : ℝ)⌉₊) atTop (𝓝 (v t)) :=
    (hunif η V (Eventually.of_forall hη_pos) hη0 (Eventually.of_forall hV0)
      (Eventually.of_forall hV) t).tendsto_at ⟨ht, le_rfl⟩
  -- Pass `η j → 0` in `TauCeti.dist_ceil_sq_le_of_penalizedConvex` between `U` and `V j`.
  set K : ℝ → ℝ := fun r ↦ max 0 (-2 * lam + 2 * lam ^ 2 * τ + 2 * lam ^ 2 * r)
  set R : ℝ → ℝ := fun r ↦ 2 * exp (K r * t) * dist (U 0) (u 0) ^ 2 +
    (2 * exp (K r * t) + 8) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + r * max 0 ((φ (u 0)).toReal - L))
  have hev : ∀ᶠ j in atTop, dist (U ⌈t / τ⌉₊) (V j ⌈t / η j⌉₊) ^ 2 ≤ R (η j) := by
    filter_upwards [hapriori] with j hjL
    obtain ⟨eV, heV, -, hdropV⟩ := exists_toReal_apply_and_sub_le (hη_lt_τ₀ j) h₀ (hV j)
      (hSV j) (hjL _ (floor_div_add_one_le_ceil_add_one (hη_pos j) ⟨ht, le_rfl⟩)).1
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
    (((by fun_prop : Continuous R).tendsto 0).comp (NNReal.tendsto_coe.2 hη0)) hev

/-- **Quantitative error bound between a minimizing movement sequence and an `EVI_λ` solution.**
On a complete pseudometric space, if `φ` is lower semicontinuous, satisfies `φ_{τ₀}(x₁) > -∞` for
some `τ₀ > 0` and `x₁`, and is penalized convex for all sufficiently small positive time steps, then
for every `EVI_lam` solution `u` and every minimizing movement sequence `U` with step `τ > 0`
satisfying `TauCeti.PenalizedConvex lam τ φ`, `|lam| * τ ≤ 1 / 2`, and real energies `eU`, the
squared distance `d(U ⌈t / τ⌉₊, u t)²` at time `t ≥ 0` is bounded in terms of `d(U 0, u 0)²` and
`τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))` (giving an `O(√τ)` error in distance when `d(U 0, u 0) = O(√τ)`
and the energy drop is bounded). -/
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

/-- Core uniform convergence on `[0, T]` (`0 ≤ T`) when the minimizing movement hypotheses hold for
every `j`. -/
private lemma tendstoUniformlyOn_of_penalizedConvex_forall {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 (u 0))) {S : ℝ} (hS : ∀ j, φ (U j 0) ≤ S)
    (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  -- Obtain a uniform energy lower bound `L` on `[0, T + 1]` and an `O(dist² + τ)` bound `E j → 0`.
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top (u 0) x₁) hτ hτ0 hU hU0 hS (by positivity : 0 ≤ T + 1)
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  have hτw : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0 (Eventually.of_forall hτ)
  have hlam_ev : ∀ᶠ j in atTop, |lam| * (τ j : ℝ) ≤ 1 / 2 :=
    (mul_zero |lam| ▸ hτr.const_mul |lam|).eventually (ge_mem_nhds (by norm_num))
  set Kmax : ℝ := 2 * |lam| + 2 * lam ^ 2; set M : ℝ := max 0 (S - L)
  set E : ℕ → ℝ := fun j ↦
    2 * exp (Kmax * T) * dist (U j 0) (u 0) ^ 2 + (2 * exp (Kmax * T) + 8) * M * τ j
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have hd0 : Tendsto (fun j ↦ dist (U j 0) (u 0)) atTop (𝓝 0) := by
      simpa using hU0.dist (tendsto_const_nhds (x := u 0))
    simpa [E] using ((hd0.pow 2).const_mul (2 * exp (Kmax * T))).add
      (hτr.const_mul ((2 * exp (Kmax * T) + 8) * M))
  -- Apply `IsEVISolution.dist_ceil_sq_le_of_penalizedConvex` uniformly over `t ∈ [0, T]`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hτw.eventually hconv, hlam_ev, hτr.eventually (ge_mem_nhds one_pos),
    hτ0.eventually (gt_mem_nhds hτ₀), hapriori,
    hE0.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hτc hmτ _ hτ_lt hL hEj t ht
  obtain ⟨eU, heU, haU, hdropU⟩ := exists_toReal_apply_and_sub_le hτ_lt h₀ (hU j) (hS j)
    (hL _ (floor_div_add_one_le_ceil_add_one (hτ j) ht)).1
  have hbd := hu.dist_ceil_sq_le_of_penalizedConvex hφ hτ₀ h₀ hconv hτc (hτ j) hmτ (hU j) heU ht.1
  have hexp : exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ j) * t) ≤ exp (Kmax * T) :=
    exp_le_exp.2 <| mul_le_mul (max_le (by positivity) (by
      dsimp [Kmax]; nlinarith [neg_le_abs lam, sq_nonneg lam])) ht.2 ht.1 (by positivity)
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le_two)
    (sq_nonneg (dist (U j 0) (u 0)))
  have h2 := mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_left hexp zero_le_two) 8)
    (mul_le_mul_of_nonneg_left hdropU (NNReal.coe_nonneg (τ j)))
    (mul_nonneg (NNReal.coe_nonneg (τ j)) haU) (by positivity)
  have hsq : dist (u t) (U j ⌈t / (τ j : ℝ)⌉₊) ^ 2 < ε ^ 2 := by
    rw [dist_comm]; dsimp only [E] at hEj; nlinarith [hbd, h1, h2, hEj]
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

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
  have h := tendstoUniformlyOn_of_penalizedConvex_forall hu hφ hτ₀ h₀ hconv
    (fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).1) (hτ0.comp (tendsto_add_atTop_nat N₁))
    (hU0.comp (tendsto_add_atTop_nat N₁)) (fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).2.1)
    (fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).2.2) hT
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  rw [← Filter.map_add_atTop_eq_nat N₁, Filter.eventually_map]
  exact h ε hε

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
  obtain ⟨τ₁, hτ₁, hconv_lt⟩ := ((nhdsGT_basis (0 : ℝ≥0)).eventually_iff).1 hconv
  obtain ⟨u, hu0, hu, _⟩ := exists_isEVISolution_tendstoUniformlyOn_const_of_penalizedConvex
    hφ hτ₀ hτ₁ (fun _ h0 h1 ↦ hconv_lt ⟨h0, h1⟩) h₀ hx₀
  refine hu.congr fun t (ht : 0 ≤ t) ↦ ?_
  have h1 := (hu.tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv (Eventually.of_forall hτ)
    hτ0 (hu0.symm ▸ hU0) (Eventually.of_forall hS) (Eventually.of_forall hU) t).tendsto_at
    (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  have hed := hd (u t) (hlim t ht)
  have hed0 : Tendsto (fun j ↦ edist (u t) (U j ⌈t / (τ j : ℝ)⌉₊)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := u t)).edist h1
  rw [hed0.liminf_eq] at hed
  exact edist_le_zero.1 hed

/-- **Existence of `EVI_λ` flows and uniform convergence of minimizing movements**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4; Ambrosio–Gigli, Theorem 3.25). Let `φ : X → EReal`
be lower semicontinuous on a complete pseudometric space, coercive (`φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0`), and `lam`-penalized convex for all sufficiently small `τ > 0`. Then from every
point `x₀` of finite energy starts an `EVI_λ` solution `u` with `u 0 = x₀`, and the piecewise
constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of every minimizing movement scheme with positive
time steps `τ j → 0`, initial points `J j 0 → x₀`, and uniformly bounded initial energy converge
to `u` uniformly on `[0, T]` for every `T : ℝ`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → Tendsto (fun j ↦ J j 0) atTop (𝓝 x₀) →
        (∃ S : ℝ, ∀ᶠ j in atTop, φ (J j 0) ≤ S) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨u, hu0, hu, _⟩ :=
    exists_isEVISolution_tendstoUniformlyOn_const_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ hx₀
  have hconv_nhds : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ :=
    (nhdsGT_basis (0 : ℝ≥0)).eventually_iff.2 ⟨τ₁, hτ₁, fun _ hτ ↦ hconv _ hτ.1 hτ.2⟩
  exact ⟨u, hu0, hu, fun τ J hτ hτ0 hJ0 ⟨_, hS⟩ hJ T ↦
    hu.tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv_nhds hτ hτ0 (hu0.symm ▸ hJ0) hS hJ T⟩

/-- **Characterization of the `EVI_λ` domain** (Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under
the hypotheses of `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, the set
of initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
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
theorem exists_isEVISolution_of_mem_closure_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X}
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (eviDomain_eq_closure_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ ▸ hx₀)

/-- **Generation of `EVI_λ` flows under Ambrosio–Gigli Assumption 3.24** (Ambrosio–Gigli,
Theorem 3.25). Let `φ` be a lower semicontinuous energy on a complete pseudometric space satisfying
`TauCeti.ConvexWithDistSq lam φ`. Then for every `x₀` of finite energy (`φ x₀ ≠ ⊤` and
`φ x₀ ≠ ⊥`) there is an `EVI_lam` solution `u` from `x₀` to which minimizing movement interpolants
with converging initial points and uniformly bounded initial energy converge locally uniformly. -/
theorem ConvexWithDistSq.exists_isEVISolution_tendstoUniformlyOn {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hconv : ConvexWithDistSq lam φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ᶠ j in atTop, 0 < τ j) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ᶠ j in atTop, φ (U j 0) ≤ S) →
        (∀ᶠ j in atTop, ∀ n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, h₀⟩ :=
    hconv.exists_moreauYosida_ne_bot (hφ.lowerSemicontinuousAt x₀) hx₀ hx₀bot x₀
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ one_pos
    (fun _ _ _ ↦ hconv.penalizedConvex) h₀ hx₀

/-- Under the hypotheses of `TauCeti.ConvexWithDistSq.exists_isEVISolution_tendstoUniformlyOn` (with
`φ y ≠ ⊥` on the effective domain), the domain of the `EVI_lam` flow equals
`closure {y | φ y ≠ ⊤}`. -/
theorem ConvexWithDistSq.eviDomain_eq_closure {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hconv : ConvexWithDistSq lam φ)
    (hbot : ∀ y, φ y ≠ ⊤ → φ y ≠ ⊥) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ := hconv.exists_isEVISolution_tendstoUniformlyOn hφ hx (hbot _ hx)
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- Under `TauCeti.ConvexWithDistSq lam φ` on a complete pseudometric space, every point
`x₀ ∈ closure {y | φ y ≠ ⊤}` is the initial point of an `EVI_lam` solution. -/
theorem ConvexWithDistSq.exists_isEVISolution_of_mem_closure {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hconv : ConvexWithDistSq lam φ)
    (hbot : ∀ y, φ y ≠ ⊤ → φ y ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {y | φ y ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (hconv.eviDomain_eq_closure hφ hbot ▸ hx₀)

end QuantitativeErrorAndCurveConvexity

section GeodesicallyConvex

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X]
  {lam : ℝ} {φ : X → EReal}

/-- **Existence and uniform convergence of minimizing movements for geodesically convex energies
on CAT(0) spaces** (Jost; Mayer, Theorem 1.13). Let `φ : X → EReal` be lower semicontinuous and
`lam`-geodesically convex on a complete CAT(0) pseudometric space, and let `x₀` be a point of
finite energy (`φ x₀ ≠ ⊤` and `φ x₀ ≠ ⊥`). Then there starts from `x₀` an `EVI_λ` solution `u`
with `u 0 = x₀`, and all minimizing movement interpolants with positive step sizes `τ j → 0`,
converging initial points `J j 0 → x₀`, and uniformly bounded initial energy converge uniformly to
`u` on compact time intervals `[0, T]`. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) (hx₀bot : φ x₀ ≠ ⊥) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → Tendsto (fun j ↦ J j 0) atTop (𝓝 x₀) →
        (∃ S : ℝ, ∀ᶠ j in atTop, φ (J j 0) ≤ S) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) :=
  hconv.convexWithDistSq.exists_isEVISolution_tendstoUniformlyOn hφ hx₀ hx₀bot

/-- **Characterization of the `EVI_λ` domain for geodesically convex energies on CAT(0) spaces**
(Jost; Mayer, Theorem 1.13). If `φ` is lower semicontinuous, `lam`-geodesically convex, and never
equal to `⊥` on a complete CAT(0) pseudometric space, then the set `TauCeti.eviDomain lam φ` of
initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem GeodesicallyConvex.eviDomain_eq_closure
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) : eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  hconv.convexWithDistSq.eviDomain_eq_closure hφ fun _ _ ↦ hbot _

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

end TauCeti
