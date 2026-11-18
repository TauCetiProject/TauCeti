/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Basic
public import TauCeti.Analysis.GradientFlow.MinimizingMovement
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall

/-!
# Limits of minimizing movements of penalized convex energies are EVI solutions

Let `φ : X → EReal` be a lower semicontinuous energy on a metric space which is penalized convex
with parameter `m` (`TauCeti.PenalizedConvex`) for all small time steps, for instance an
`m`-geodesically convex energy on a CAT(0) space, or an energy on the quadratic Wasserstein space
which is `m`-convex along generalized geodesics. Then every continuous curve which is a limit, in
the metric, of piecewise constant interpolants of minimizing movements with time steps tending to
`0` is an `EVI_m` solution for `φ`: the discrete variational inequality of the implicit Euler
scheme passes to the limit.

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
(`TauCeti.exists_isEVISolution`). Ambrosio–Gigli–Savaré prove the existence of the `EVI_m` flow
without the compactness hypothesis, by showing that the discrete solutions form a Cauchy family
as `τ → 0`; that argument is not formalized here.

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

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4 (Assumption 4.0.1 and
  Theorem 4.0.4).
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, in *Modelling and Optimisation of
  Flows on Networks*, Lecture Notes in Math. 2062, Springer 2013, Section 3.3 (Assumption 3.24 and
  Theorem 3.25).
-/

public section

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
  have hτ' : Tendsto (fun k ↦ (τ k : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using NNReal.tendsto_coe.2 hτ0,
      Eventually.of_forall fun k ↦ NNReal.coe_pos.2 (hτ k)⟩
  -- The time `⌈r / τ k⌉₊ τ k` of the interpolant's node at time `r ≥ 0` tends to `r`.
  have hceil {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun k ↦ ⌈r / τ k⌉₊ * (τ k : ℝ)) atTop (𝓝 r) :=
    ((tendsto_nat_ceil_mul_div_atTop hr).comp (tendsto_inv_nhdsGT_zero.comp hτ')).congr
      fun k ↦ by simp [div_eq_mul_inv]
  -- The interpolants at times `s` and `t` sit at the indices `M k ≤ N k`, `L k = N k - M k` steps
  -- apart, and these steps take the time `t - s` in the limit.
  set M : ℕ → ℕ := fun k ↦ ⌈s / τ k⌉₊
  set N : ℕ → ℕ := fun k ↦ ⌈t / τ k⌉₊
  set L : ℕ → ℕ := fun k ↦ N k - M k
  have hMN k : M k ≤ N k := Nat.ceil_mono (div_le_div_of_nonneg_right hst.le (τ k).2)
  have hL : Tendsto (fun k ↦ (L k : ℝ) * τ k) atTop (𝓝 (t - s)) :=
    ((hceil (hs.trans hst.le)).sub (hceil hs)).congr
      fun k ↦ by simp only [L, Nat.cast_sub (hMN k), sub_mul]; rfl
  have hτr := tendsto_nhds_of_tendsto_nhdsWithin hτ'
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
    fun k hk ↦ Nat.cast_pos.1 (pos_of_mul_pos_left hk (τ k).2)
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

end TauCeti
