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
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.GradientFlow.MoreauYosida.ErrorEstimate
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.Topology.MetricSpace.Pseudo.Basic
import TauCeti.Topology.Order.Interval.Basic
import TauCeti.Topology.UniformSpace.UniformConvergence.Complete

/-!
# Convergence of minimizing movements of penalized convex energies to `EVI` solutions

Let `φ : X → EReal` be a lower semicontinuous energy on a metric space which is penalized convex
with parameter `m` (`TauCeti.PenalizedConvex`) for all small time steps. Every continuous metric
limit of piecewise constant interpolants of minimizing movements with `τ → 0` is an `EVI_m` solution
(`TauCeti.isEVISolution_of_forall_mem_moreauYosidaResolvent`), passing
`TauCeti.PenalizedConvex.apply_le` to the limit via `TauCeti.tendsto_one_add_mul_pow` and
`TauCeti.tendsto_mul_sum_one_add_mul_pow` to give `TauCeti.isEVISolution_iff_apply_le`. For coercive
energies, generalized minimizing movements are unique `EVI_m` solutions
(`TauCeti.IsGeneralizedMinimizingMovement.isEVISolution`,
`TauCeti.IsGeneralizedMinimizingMovement.eqOn`), giving existence under relative compactness of
bounded sublevel sets (`TauCeti.exists_isEVISolution`).

On a complete pseudometric space without compactness, coercivity (`φ_{τ₀}(x₁) > -∞`) and
`PenalizedConvex m τ φ` for small `τ > 0` yield minimizing movements everywhere
(`TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`). Passing `η → 0` in
`TauCeti.dist_ceil_sq_le_of_penalizedConvex` yields
`TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex` and, via the first resolvent step,
uniform convergence on `[0, T]` without bounded initial energy
(`TauCeti.IsEVISolution.tendstoUniformlyOn_of_penalizedConvex`,
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`), auxiliary-convergence GMM
identification (`TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`), and
`TauCeti.eviDomain m φ = closure {x | φ x ≠ ⊤}` (`TauCeti.eviDomain_eq_closure_of_penalizedConvex`,
`TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex`), with corollaries under pointwise
interpolation `TauCeti.ConvexWithDistSq` and geodesic convexity on complete CAT(0) spaces.

## Main results
* `TauCeti.isEVISolution_of_forall_mem_moreauYosidaResolvent`,
  `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution`,
  `TauCeti.IsGeneralizedMinimizingMovement.eqOn`, `TauCeti.exists_isEVISolution`.
* `TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex`,
  `TauCeti.IsEVISolution.tendstoUniformlyOn_of_penalizedConvex`,
  `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`.
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`,
  `TauCeti.exists_isEVISolution_of_mem_closure_of_penalizedConvex`,
  `TauCeti.eviDomain_eq_closure_of_penalizedConvex` (Ambrosio–Gigli–Savaré, Theorem 4.0.4).
* `TauCeti.ConvexWithDistSq.exists_isEVISolution_tendstoUniformlyOn`,
  `TauCeti.ConvexWithDistSq.eviDomain_eq_closure`,
  `TauCeti.ConvexWithDistSq.exists_isEVISolution_of_mem_closure` (Ambrosio–Gigli, Theorem 3.25).
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn`,
  `TauCeti.GeodesicallyConvex.exists_isEVISolution_of_mem_closure`,
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure` (Jost; Mayer, Theorem 1.13).

## References
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4 (Theorems 4.0.4, 4.1.2, Secs. 4.1–4.2).
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Math. 2062,
  Springer 2013, Section 3.3 (Assumption 3.24, Theorem 3.25).
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

/-- Extracts real energy values and bounds the energy drop `e 0 - e (⌊t / τ⌋₊ + 1)` along a
minimizing movement sequence satisfying a priori lower and upper energy bounds. -/
private theorem exists_toReal_apply_and_sub_le {X : Type*} [PseudoMetricSpace X] {φ : X → EReal}
    {τ₀ τ : ℝ≥0} (hτ_lt : τ < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {S L t T : ℝ} (htT : t ≤ T) (hS : φ (U 0) ≤ S) (hL : (L : EReal) ≤ φ (U (⌊T / τ⌋₊ + 1))) :
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
  have hLt : (L : EReal) ≤ φ (U (⌊t / τ⌋₊ + 1)) := hL.trans <|
    antitone_comp_of_forall_mem_moreauYosidaResolvent hU <|
      Nat.add_le_add_right (Nat.floor_mono (div_le_div_of_nonneg_right htT (NNReal.coe_nonneg τ))) 1
  exact ⟨fun n ↦ (φ (U n)).toReal, he, ha0,
    (sub_le_sub (EReal.coe_le_coe_iff.1 (he 0 ▸ hS))
      (EReal.coe_le_coe_iff.1 (he _ ▸ hLt))).trans (le_max_right _ _)⟩

private lemma le_of_four_mul_le {a b : ℝ≥0} (h : 4 * a ≤ b) : a ≤ b :=
  (le_mul_of_one_le_left zero_le (by norm_num : (1 : ℝ≥0) ≤ 4)).trans h

private lemma eventually_four_mul_le {τ : ℕ → ℝ≥0} (hτ0 : Tendsto τ atTop (𝓝 0))
    {τ' : ℝ≥0} (hτ' : 0 < τ') : ∀ᶠ j in atTop, 4 * τ j ≤ τ' :=
  (hτ0.eventually (ge_mem_nhds (by positivity : (0 : ℝ≥0) < τ' / 4))).mono
    fun _ hj ↦ (mul_le_mul_of_nonneg_left hj zero_le).trans_eq (mul_div_cancel₀ _ (by norm_num))

private lemma moreauYosida_and_apply_eq_toReal {X : Type*} [PseudoMetricSpace X] {φ : X → EReal}
    {τ₀ τ' : ℝ≥0} (hτ'τ₀ : τ' < τ₀) {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hx₀ : φ x₀ ≠ ⊤) :
    moreauYosida φ τ' x₀ = ((moreauYosida φ τ' x₀).toReal : EReal) ∧
      φ x₀ = ((φ x₀).toReal : EReal) :=
  ⟨(EReal.coe_toReal (ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀))
      (moreauYosida_ne_bot_of_lt hτ'τ₀ (edist_ne_top x₀ x₁) h₀)).symm,
    (EReal.coe_toReal hx₀ (apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ x₀) h₀)).symm⟩

private lemma exp_max_zero_mul_le {lam r₁ r₂ B t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr : 2 * lam ^ 2 * (r₁ + r₂) ≤ B) :
    exp (max 0 (-2 * lam + 2 * lam ^ 2 * r₁ + 2 * lam ^ 2 * r₂) * t) ≤
      exp ((2 * |lam| + B) * T) := by
  have : 0 ≤ B := (by positivity : 0 ≤ 2 * lam ^ 2 * (r₁ + r₂)).trans hr
  have : 0 ≤ T := ht0.trans htT
  exact exp_le_exp.2 <| mul_le_mul
    (max_le (by positivity) (by linarith [neg_le_abs lam])) htT ht0 (by positivity)

/-- Quantitative Cauchy bound for two minimizing movement sequences from the same finite-energy
initial point `x₀`, derived from `TauCeti.dist_ceil_sq_le_of_penalizedConvex` and
`TauCeti.le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent`. -/
private lemma dist_ceil_sq_le_of_same_init {τ' τ σ : ℝ≥0} {x₀ : X} {T A E : ℝ}
    (hτc : PenalizedConvex lam τ φ) (hσc : PenalizedConvex lam σ φ)
    (hτ : 0 < τ) (hσ : 0 < σ) (hττ' : 4 * τ ≤ τ') (hστ' : 4 * σ ≤ τ')
    (hmτ : (-lam) * τ ≤ 1 / 2) (hmσ : (-lam) * σ ≤ 1 / 2)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ σ (V k))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
      (2 * Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) + 8) *
        ((E - A) * (1 + Real.exp (8 * (T + 1 + τ') / τ'))) * ((τ : ℝ) + σ) := by
  have hEA : 0 ≤ E - A := sub_nonneg.2 (by exact_mod_cast hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀)
  obtain ⟨eU, heU, hU0', hdropU⟩ := exists_toReal_apply_and_sub_le
    ((lt_mul_left hτ (by norm_num)).trans_le hττ') (hA ▸ EReal.coe_ne_bot A) hU (t := t)
    ht.2 (hU0 ▸ hE).le
    (le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hU hτ hττ'
      (hU0 ▸ hA.ge) (hU0 ▸ hE.le) (T := T + 1) (by linarith [ht.1, ht.2])
      (floor_div_add_one_le_ceil_div (NNReal.coe_pos.2 hτ) (by linarith [ht.2])
        (by linarith [ht.1, ht.2]))).1
  obtain ⟨eV, heV, hV0', hdropV⟩ := exists_toReal_apply_and_sub_le
    ((lt_mul_left hσ (by norm_num)).trans_le hστ') (hA ▸ EReal.coe_ne_bot A) hV (t := t)
    ht.2 (hV0 ▸ hE).le
    (le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hV hσ hστ'
      (hV0 ▸ hA.ge) (hV0 ▸ hE.le) (T := T + 1) (by linarith [ht.1, ht.2])
      (floor_div_add_one_le_ceil_div (NNReal.coe_pos.2 hσ) (by linarith [ht.2])
        (by linarith [ht.1, ht.2]))).1
  have hEL : max 0 (E - (A - (E - A) * Real.exp (8 * (T + 1 + τ') / τ'))) =
      (E - A) * (1 + Real.exp (8 * (T + 1 + τ') / τ')) := by
    rw [show E - (A - (E - A) * Real.exp (8 * (T + 1 + τ') / τ')) =
      (E - A) * (1 + Real.exp (8 * (T + 1 + τ') / τ')) by ring]
    exact max_eq_right (mul_nonneg hEA (by positivity))
  have hbd := TauCeti.dist_ceil_sq_le_of_penalizedConvex hτc hσc hτ hσ hmτ hmσ hU hV heU heV ht.1
  rw [hU0, hV0, dist_self, zero_pow two_ne_zero, mul_zero, zero_add] at hbd
  have h4τ : (4 : ℝ) * τ ≤ τ' := by exact_mod_cast hττ'
  have h4σ : (4 : ℝ) * σ ≤ τ' := by exact_mod_cast hστ'
  have hexp := exp_max_zero_mul_le (B := lam ^ 2 * (τ' : ℝ)) ht.1 ht.2
    (NNReal.coe_nonneg τ) (NNReal.coe_nonneg σ) (by nlinarith [h4τ, h4σ, sq_nonneg lam])
  have hdrop : (τ : ℝ) * (eU 0 - eU (⌊t / (τ : ℝ)⌋₊ + 1)) +
      σ * (eV 0 - eV (⌊t / (σ : ℝ)⌋₊ + 1)) ≤
      (E - A) * (1 + Real.exp (8 * (T + 1 + τ') / τ')) * (τ + σ) := by
    rw [hEL] at hdropU hdropV; nlinarith [NNReal.coe_nonneg τ, NNReal.coe_nonneg σ]
  refine hbd.trans ?_
  rw [mul_assoc (2 * Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) + 8)]
  exact mul_le_mul (by gcongr) hdrop
    (add_nonneg (mul_nonneg (NNReal.coe_nonneg _) hU0') (mul_nonneg (NNReal.coe_nonneg _) hV0'))
    (by positivity)

/-- Uniform Cauchy constant for minimizing movements starting at `x₀`. -/
private def cauchyConst (lam τ' A E T : ℝ) : ℝ :=
  (2 * Real.exp ((2 * |lam| + lam ^ 2 * τ') * T) + 8) *
    ((E - A) * (1 + Real.exp (8 * (T + 1 + τ') / τ')))

/-- Uniform Cauchy property on `[0, T]` for minimizing movement interpolants from `x₀`. -/
private lemma uniformCauchySeqOn_of_same_init {τ' τ₁ : ℝ≥0} {x₀ : X} {A E : ℝ}
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ) (hτ'τ₁ : τ' < τ₁)
    (hA : moreauYosida φ τ' x₀ = A) (hE : φ x₀ = E)
    {τc : ℕ → ℝ≥0} (hτc : ∀ j, 0 < τc j) (hτcτ' : ∀ j, 4 * τc j ≤ τ')
    (hlam_neg : ∀ j, (-lam) * (τc j : ℝ) ≤ 1 / 2) (hτc0 : Tendsto τc atTop (𝓝 0))
    {Jc : ℕ → ℕ → X} (hJc0 : ∀ j, Jc j 0 = x₀)
    (hJc : ∀ j k, Jc j (k + 1) ∈ moreauYosidaResolvent φ (τc j) (Jc j k)) (T : ℝ) :
    UniformCauchySeqOn (fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (Icc 0 T) := by
  have herr : Tendsto (fun p : ℕ × ℕ ↦
      Real.sqrt (cauchyConst lam τ' A E T * ((τc p.1 : ℝ) + τc p.2))) (atTop ×ˢ atTop) (𝓝 0) :=
    (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp <| by
      simpa using (((NNReal.tendsto_coe.2 hτc0).comp tendsto_fst).add
        ((NNReal.tendsto_coe.2 hτc0).comp tendsto_snd)).const_mul (cauchyConst lam τ' A E T)
  exact uniformCauchySeqOn_of_dist_le herr <| .of_forall fun p t ht ↦ Real.le_sqrt_of_sq_le <|
    dist_ceil_sq_le_of_same_init
      (hconv (τc p.1) (hτc p.1) ((le_of_four_mul_le (hτcτ' p.1)).trans_lt hτ'τ₁))
      (hconv (τc p.2) (hτc p.2) ((le_of_four_mul_le (hτcτ' p.2)).trans_lt hτ'τ₁))
      (hτc p.1) (hτc p.2) (hτcτ' p.1) (hτcτ' p.2) (hlam_neg p.1) (hlam_neg p.2)
      hA hE (hJc0 p.1) (hJc0 p.2) (hJc p.1) (hJc p.2) ht

/-- Constructs a reference scale `τ'` and minimizing movement family `(τc, Jc)` from `x₀` and
passes to its uniform limit `u`, which is an `EVI_lam` solution with `u 0 = x₀`. -/
private lemma exists_limit_const_of_penalizedConvex [CompleteSpace X]
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ (τ' : ℝ≥0) (u : ℝ → X) (τc : ℕ → ℝ≥0) (Jc : ℕ → ℕ → X),
      τ' < τ₀ ∧ τ' < τ₁ ∧ u 0 = x₀ ∧ IsEVISolution lam φ u ∧
        (∀ j, 0 < τc j) ∧ (∀ j, 4 * τc j ≤ τ') ∧
        (∀ j, (-lam) * (τc j : ℝ) ≤ 1 / 2) ∧
        Tendsto τc atTop (𝓝 0) ∧ (∀ j, Jc j 0 = x₀) ∧
        (∀ j k, Jc j (k + 1) ∈ moreauYosidaResolvent φ (τc j) (Jc j k)) ∧
        ∀ T ≥ (0 : ℝ), TendstoUniformlyOn (fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  -- Choose reference scale `τ' < min τ₀ τ₁` with `|lam| * τ' ≤ 1 / 4` and dyadic steps `τc j`.
  obtain ⟨τ'r, hτ'r, hτ'min, hlamτ'r⟩ :=
    exists_pos_abs_mul_le lam (by norm_num : (0 : ℝ) < 1 / 4) (NNReal.coe_pos.2 (lt_min hτ₀ hτ₁))
  let τ' : ℝ≥0 := ⟨τ'r, hτ'r.le⟩
  have hτ' : 0 < τ' := hτ'r
  have hτ'min' : τ' < min τ₀ τ₁ := NNReal.coe_lt_coe.1 hτ'min
  have hτ'τ₀ : τ' < τ₀ := hτ'min'.trans_le (min_le_left _ _)
  have hτ'τ₁ : τ' < τ₁ := hτ'min'.trans_le (min_le_right _ _)
  obtain ⟨hA, hE⟩ := moreauYosida_and_apply_eq_toReal hτ'τ₀ h₀ hx₀
  set τc : ℕ → ℝ≥0 := fun j ↦ τ' / 4 / ↑(j + 1)
  have hτc (j) : 0 < τc j := div_pos (div_pos hτ' four_pos) (Nat.cast_pos.2 j.succ_pos)
  have hτcτ' (j) : 4 * τc j ≤ τ' := (mul_le_mul_of_nonneg_left
    (div_le_self zero_le (Nat.one_le_cast.2 j.succ_pos)) zero_le).trans_eq
    (mul_div_cancel₀ τ' four_ne_zero)
  have hτc0 : Tendsto τc atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (τ' / 4))
  have hlam_abs (j) : |lam| * (τc j : ℝ) ≤ 1 / 2 := ((mul_le_mul_of_nonneg_left
    (NNReal.coe_le_coe.2 (le_of_four_mul_le (hτcτ' j))) (abs_nonneg _)).trans
      (hlamτ'r hτ'r.le le_rfl)).trans (by norm_num)
  have hlam_neg (j) : (-lam) * (τc j : ℝ) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (neg_le_abs lam) (NNReal.coe_nonneg _)).trans (hlam_abs j)
  choose Jc hJc0 hJc using fun j ↦ PenalizedConvex.exists_forall_mem_moreauYosidaResolvent
    hφ (hconv (τc j) (hτc j) ((le_of_four_mul_le (hτcτ' j)).trans_lt hτ'τ₁)) (hτc j)
    (one_add_mul_pos_of_abs_mul_lt_one (τc j).property ((hlam_abs j).trans_lt (by norm_num)))
    ((le_of_four_mul_le (hτcτ' j)).trans_lt hτ'τ₀) h₀ x₀
  -- Pass to the uniform limit on compact intervals `[0, T]` and update value at `0` to `x₀`.
  obtain ⟨u₀, hu₀⟩ := exists_forall_tendstoUniformlyOn_of_uniformCauchySeqOn
    (𝔖 := {s | ∃ T ≥ (0 : ℝ), s = Icc 0 T})
    (by rintro _ ⟨T, _, rfl⟩
        exact uniformCauchySeqOn_of_same_init hconv hτ'τ₁ hA hE hτc hτcτ' hlam_neg hτc0 hJc0 hJc T)
  classical
  let u : ℝ → X := Function.update u₀ 0 x₀
  have hu_unif : ∀ T ≥ (0 : ℝ),
      TendstoUniformlyOn (fun j t ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) u atTop (Icc 0 T) := fun T hT ↦
    (hu₀ _ ⟨T, hT, rfl⟩).congr_inseparable_right fun t ht ↦ by
      by_cases h0 : t = 0
      · subst h0; simpa only [u, Function.update_self] using tendsto_nhds_unique_inseparable
          ((hu₀ _ ⟨T, hT, rfl⟩).tendsto_at ht) (by simpa only [zero_div, Nat.ceil_zero, hJc0]
            using tendsto_const_nhds)
      · simp only [u, Function.update_of_ne h0]; rfl
  exact ⟨τ', u, τc, Jc, hτ'τ₀, hτ'τ₁, Function.update_self 0 x₀ u₀,
    isEVISolution_of_tendsto_ceil hφ hτ₀ hconv h₀ hx₀ hτc
      (fun j ↦ (le_of_four_mul_le (hτcτ' j)).trans_lt hτ'τ₁)
      hτc0 hJc0 hJc (fun t ht ↦ (hu_unif t ht).tendsto_at ⟨ht, le_rfl⟩),
    hτc, hτcτ', hlam_neg, hτc0, hJc0, hJc, hu_unif⟩

end Existence

section QuantitativeErrorAndCurveConvexity

/-- `η → 0` limit of `TauCeti.dist_ceil_sq_le_of_penalizedConvex` against an `EVI_lam` solution
`u` whose initial point has finite energy `φ (u 0) ≠ ⊤`. -/
private theorem dist_ceil_sq_le_of_isEVISolution_of_apply_ne_top {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {τ₀ τ : ℝ≥0} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ η in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam η φ) (hu0 : φ (u 0) ≠ ⊤)
    (hτc : PenalizedConvex lam τ φ) (hτ : 0 < τ) (hmτ : (-lam) * τ ≤ 1 / 2)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {eU : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (u t) ^ 2 ≤
      2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) * dist (U 0) (u 0) ^ 2 +
        (2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))) := by
  -- Construct the reference minimizing movement limit `v` from `u 0` and match it with `u`.
  obtain ⟨τ₁, hτ₁, hconv_lt⟩ := ((nhdsGT_basis (0 : ℝ≥0)).eventually_iff).1 hconv
  obtain ⟨τ', v, τc, Jc, hτ'τ₀, hτ'τ₁, hv0, hv, hτc_pos, hτcτ', hmτc, hτc0, hJc0, hJc, hunif⟩ :=
    exists_limit_const_of_penalizedConvex hφ hτ₀ hτ₁ (fun _ h0 h1 ↦ hconv_lt ⟨h0, h1⟩) h₀ hu0
  have hd_vu : dist (v t) (u t) = 0 :=
    le_antisymm ((hv.dist_le hu hφ ht).trans_eq (by simp [hv0])) dist_nonneg
  have hlim : Tendsto (fun j ↦ Jc j ⌈t / (τc j : ℝ)⌉₊) atTop (𝓝 (v t)) :=
    (hunif t ht).tendsto_at ⟨ht, le_rfl⟩
  -- Pass `τc j → 0` in `TauCeti.dist_ceil_sq_le_of_penalizedConvex` between `U` and `Jc j`.
  obtain ⟨hA, hE⟩ := moreauYosida_and_apply_eq_toReal hτ'τ₀ h₀ hu0
  set A : ℝ := (moreauYosida φ τ' (u 0)).toReal; set E : ℝ := (φ (u 0)).toReal
  set L : ℝ := A - (E - A) * Real.exp (8 * (t + 1 + τ') / τ')
  set K : ℝ → ℝ := fun r ↦ max 0 (-2 * lam + 2 * lam ^ 2 * τ + 2 * lam ^ 2 * r)
  set R : ℝ → ℝ := fun r ↦ 2 * exp (K r * t) * dist (U 0) (u 0) ^ 2 +
    (2 * exp (K r * t) + 8) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + r * max 0 (E - L))
  have hev : ∀ j, dist (U ⌈t / τ⌉₊) (Jc j ⌈t / (τc j : ℝ)⌉₊) ^ 2 ≤ R (τc j) := fun j ↦ by
    obtain ⟨eJ, heJ, -, hdropJ⟩ := exists_toReal_apply_and_sub_le
      ((lt_mul_left (hτc_pos j) (by norm_num)).trans_le (hτcτ' j)) (hA ▸ EReal.coe_ne_bot A)
      (hJc j) (t := t) le_rfl (hJc0 j ▸ hE).le
      (le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
        (hJc j) (hτc_pos j) (hτcτ' j) (hJc0 j ▸ hA.ge) (hJc0 j ▸ hE.le) (T := t + 1)
        (by positivity) (floor_div_add_one_le_ceil_div (NNReal.coe_pos.2 (hτc_pos j))
          (lt_add_one t) (by positivity))).1
    have hbd := TauCeti.dist_ceil_sq_le_of_penalizedConvex hτc
      (hconv_lt ⟨hτc_pos j, (le_of_four_mul_le (hτcτ' j)).trans_lt hτ'τ₁⟩)
      hτ (hτc_pos j) hmτ (hmτc j) hU (hJc j) heU heJ ht
    rw [hJc0 j] at hbd
    have hmulJ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdropJ (NNReal.coe_nonneg (τc j)))
      (by positivity : 0 ≤ 2 * exp (K (τc j) * t) + 8)
    dsimp only [R, K, L] at hmulJ ⊢; linarith [hbd, hmulJ]
  rw [(dist_congr_left hd_vu).symm]
  simpa [R, K] using le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist hlim).pow 2)
    (((by fun_prop : Continuous R).tendsto 0).comp (NNReal.tendsto_coe.2 hτc0)) (.of_forall hev)

/-- **Quantitative error bound between a minimizing movement sequence and an `EVI_λ` solution.**
On a complete pseudometric space, if `φ` is lower semicontinuous, satisfies `φ_{τ₀}(x₁) > -∞` for
some `τ₀ > 0` and `x₁`, and is penalized convex for all sufficiently small positive time steps, then
for every `EVI_lam` solution `u` and every minimizing movement sequence `U` with step `τ > 0`
satisfying `TauCeti.PenalizedConvex lam τ φ`, `(-lam) * τ ≤ 1 / 2`, and real energies `eU`, the
squared distance `d(U ⌈t / τ⌉₊, u t)²` at time `t ≥ 0` is bounded in terms of `d(U 0, u 0)²` and
`τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))` (giving an `O(√τ)` error in distance when `d(U 0, u 0) = O(√τ)`
and the energy drop is bounded). -/
theorem IsEVISolution.dist_ceil_sq_le_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {τ₀ τ : ℝ≥0} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ η in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam η φ)
    (hτc : PenalizedConvex lam τ φ) (hτ : 0 < τ) (hmτ : (-lam) * τ ≤ 1 / 2)
    {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {eU : ℕ → ℝ} (heU : ∀ n, φ (U n) = eU n) {t : ℝ} (ht : 0 ≤ t) :
    dist (U ⌈t / τ⌉₊) (u t) ^ 2 ≤
      2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) * dist (U 0) (u 0) ^ 2 +
        (2 * exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ) * t) + 8) *
          (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1))) := by
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hu_add (r : ℝ) (hr : 0 ≤ r) : Tendsto (fun s ↦ u (r + s)) (𝓝[>] 0) (𝓝 (u r)) :=
    (hu.continuousOn r hr).tendsto.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous (r + ·)).tendsto' 0 r (add_zero r)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) ↦ mem_Ici.2 (add_nonneg hr hs.le))
  refine le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist (hu_add t ht)).pow 2)
    ((((tendsto_const_nhds.dist (hu_add 0 le_rfl)).pow 2).const_mul _).add_const _) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact dist_ceil_sq_le_of_isEVISolution_of_apply_ne_top (hu.comp_add_const hs.le) hφ hτ₀ h₀
    hconv ((zero_add s).symm ▸ hu.apply_ne_top hs) hτc hτ hmτ hU heU ht

/-- One-step energy and step-size comparison for `U j 1 ∈ J_{τ j} (U j 0)` against any point `v`
of finite energy. -/
private lemma first_step_dist_sq_and_toReal_le {X : Type*} [PseudoMetricSpace X]
    {φ : X → EReal} {τ₀ τ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ : 0 < τ) {x₁ : X} {A₀ : ℝ}
    (hA₀ : moreauYosida φ τ₀ x₁ = A₀) (hbot : ∀ z, φ z ≠ ⊥)
    (hmy_top : ∀ σ : ℝ≥0, 0 < σ → ∀ a, moreauYosida φ σ a ≠ ⊤) {x y v : X}
    (hy : y ∈ moreauYosidaResolvent φ τ x) (hv : φ v ≠ ⊤) :
    (φ y).toReal ≤ (φ v).toReal + dist x v ^ 2 / (2 * τ) ∧
      (4 * τ ≤ τ₀ → dist x y ^ 2 ≤
        4 * τ * ((φ v).toReal - A₀ + dist x₁ x ^ 2 / τ₀) + 2 * dist x v ^ 2) := by
  have hy_eq : φ y = ((φ y).toReal : EReal) :=
    (EReal.coe_toReal (apply_ne_top_of_mem_moreauYosidaResolvent hy (hmy_top τ hτ x))
      (hbot y)).symm
  have hv_eq : φ v = ((φ v).toReal : EReal) := (EReal.coe_toReal hv (hbot v)).symm
  have hmin := apply_add_le_apply_add_of_mem_moreauYosidaResolvent hτ hy v
  rw [hy_eq, hv_eq] at hmin; norm_cast at hmin; push_cast at hmin
  refine ⟨by linarith [show 0 ≤ dist x y ^ 2 / (2 * (τ : ℝ)) by positivity], fun h4 ↦ ?_⟩
  have hlow := (moreauYosida_le φ τ₀ (edist_ne_top x₁ y)).trans_eq
    (congr_arg (φ y + ·) (coe_edist_sq_div_eq_coe_dist_sq_div hτ₀ x₁ y))
  rw [hA₀, hy_eq] at hlow; norm_cast at hlow; push_cast at hlow
  have htri : dist x₁ y ^ 2 ≤ 2 * dist x₁ x ^ 2 + 2 * dist x y ^ 2 := by
    nlinarith [dist_triangle x₁ x y, dist_nonneg (x := x₁) (y := y),
      sq_nonneg (dist x₁ x - dist x y)]
  have hlow' : A₀ - dist x₁ x ^ 2 / τ₀ ≤ (φ y).toReal + dist x y ^ 2 / τ₀ := by
    linarith [div_le_div_of_nonneg_right htri (by positivity : (0 : ℝ) ≤ 2 * τ₀),
      show (2 * dist x₁ x ^ 2 + 2 * dist x y ^ 2) / (2 * (τ₀ : ℝ)) =
        dist x₁ x ^ 2 / τ₀ + dist x y ^ 2 / τ₀ by ring]
  have hinv : (4 * (τ : ℝ))⁻¹ ≤ (2 * (τ : ℝ))⁻¹ - (τ₀ : ℝ)⁻¹ := by
    linarith [inv_anti₀ (by positivity : (0 : ℝ) < 4 * τ) (by exact_mod_cast h4 : (4 : ℝ) * τ ≤ τ₀),
      show (2 * (τ : ℝ))⁻¹ = 2 * (4 * (τ : ℝ))⁻¹ by ring]
  have hres : dist x y ^ 2 / (4 * τ) ≤
      (φ v).toReal - A₀ + dist x₁ x ^ 2 / τ₀ + dist x v ^ 2 / (2 * τ) := by
    have := mul_le_mul_of_nonneg_left hinv (sq_nonneg (dist x y))
    rw [← div_eq_mul_inv, mul_sub, ← div_eq_mul_inv, ← div_eq_mul_inv] at this; linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * τ)] at hres
  have hne : (τ : ℝ) ≠ 0 := (NNReal.coe_pos.2 hτ).ne'
  linarith [show dist x v ^ 2 / (2 * (τ : ℝ)) * (4 * τ) = 2 * dist x v ^ 2 by field_simp; ring]

private lemma moreauYosida_ne_top_of_exists_ne_top {X : Type*} [PseudoMetricSpace X]
    {φ : X → EReal} (hdom : ∃ w, φ w ≠ ⊤) {σ : ℝ≥0} (hσ : 0 < σ) (a : X) :
    moreauYosida φ σ a ≠ ⊤ :=
  let ⟨w, hw⟩ := hdom
  ne_top_of_le_ne_top (EReal.add_ne_top hw (EReal.coe_ne_top _))
    ((moreauYosida_le φ σ (edist_ne_top a w)).trans_eq
      (congr_arg (φ w + ·) (coe_edist_sq_div_eq_coe_dist_sq_div hσ a w)))

private lemma tendsto_first_step_of_mem_closure {X : Type*} [PseudoMetricSpace X]
    {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ x₀ : X}
    (hA₀ : moreauYosida φ τ₀ x₁ = ((moreauYosida φ τ₀ x₁).toReal : EReal))
    (hbot : ∀ z, φ z ≠ ⊥) (hmy_top : ∀ σ : ℝ≥0, 0 < σ → ∀ a, moreauYosida φ σ a ≠ ⊤)
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X}
    (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀))
    (hU1 : ∀ j, U j 1 ∈ moreauYosidaResolvent φ (τ j) (U j 0)) :
    Tendsto (fun j ↦ U j 1) atTop (𝓝 x₀) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  obtain ⟨v, hv, hv_d⟩ := Metric.mem_closure_iff.1 hx₀ (ε / 6) (by positivity)
  have hτ_ev : ∀ᶠ j in atTop, 4 * (τ j : ℝ) * ((φ v).toReal -
      (moreauYosida φ τ₀ x₁).toReal + dist x₁ (U j 0) ^ 2 / τ₀) < (ε / 6) ^ 2 :=
    (((NNReal.tendsto_coe.2 hτ0).const_mul 4).mul ((tendsto_const_nhds.sub tendsto_const_nhds).add
      (((tendsto_const_nhds.dist hU0).pow 2).div_const _))).eventually <| by
        simpa using gt_mem_nhds (sq_pos_of_pos (by positivity : 0 < ε / 6))
  filter_upwards [eventually_four_mul_le hτ0 hτ₀,
    hU0.eventually (Metric.ball_mem_nhds x₀ (by positivity : 0 < ε / 6)), hτ_ev] with j hj4 hj0 hjτ
  have hdv_sq : dist (U j 0) v ^ 2 < (ε / 3) ^ 2 := pow_lt_pow_left₀
    ((dist_triangle (U j 0) x₀ v).trans_lt (by linarith [Metric.mem_ball.1 hj0, hv_d]))
    dist_nonneg two_ne_zero
  have hd1 : dist (U j 0) (U j 1) < ε / 2 :=
    (pow_lt_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 <|
      ((first_step_dist_sq_and_toReal_le hτ₀ (hτ j) hA₀ hbot hmy_top
        (hU1 j) hv).2 hj4).trans_lt (by linarith)
  exact (dist_triangle (U j 1) (U j 0) x₀).trans_lt <|
    by rw [dist_comm (U j 1) (U j 0)]; linarith [Metric.mem_ball.1 hj0]

private lemma tendsto_mul_apply_sub_of_mem_closure {X : Type*} [PseudoMetricSpace X]
    {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ x₀ : X}
    (hA₀ : moreauYosida φ τ₀ x₁ = ((moreauYosida φ τ₀ x₁).toReal : EReal))
    (hbot : ∀ z, φ z ≠ ⊥) (hmy_top : ∀ σ : ℝ≥0, 0 < σ → ∀ a, moreauYosida φ σ a ≠ ⊤)
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X}
    (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀))
    (hU1 : ∀ j, U j 1 ∈ moreauYosidaResolvent φ (τ j) (U j 0))
    {A : ℝ} (hA_ev : ∀ᶠ j in atTop,
      (A : EReal) ≤ moreauYosida φ (τ₀ / 2) (U j 1) ∧ φ (U j 1) ≠ ⊤ ∧ φ (U j 1) ≠ ⊥) :
    Tendsto (fun j ↦ (τ j : ℝ) * ((φ (U j 1)).toReal - A)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  obtain ⟨v, hv, hv_d⟩ := Metric.mem_closure_iff.1 hx₀ (Real.sqrt (ε / 2) / 2) (by positivity)
  have hτ_ev : ∀ᶠ j in atTop, (τ j : ℝ) * ((φ v).toReal - A) < ε / 2 :=
    (zero_mul ((φ v).toReal - A) ▸ (NNReal.tendsto_coe.2 hτ0).mul_const _).eventually
      (gt_mem_nhds (by positivity : 0 < ε / 2))
  filter_upwards [hA_ev,
    hU0.eventually (Metric.ball_mem_nhds x₀ (by positivity : 0 < Real.sqrt (ε / 2) / 2)),
    hτ_ev] with j ⟨hAj, htopj, hbotj⟩ hj0 hjτ
  have h0 : A ≤ (φ (U j 1)).toReal := EReal.coe_le_coe_iff.1 <|
    (hAj.trans (moreauYosida_le_self φ (τ₀ / 2) (U j 1))).trans_eq
      (EReal.coe_toReal htopj hbotj).symm
  have hdv : dist (U j 0) v < Real.sqrt (ε / 2) :=
    (dist_triangle (U j 0) x₀ v).trans_lt (by linarith [Metric.mem_ball.1 hj0, hv_d])
  have hdv_sq : dist (U j 0) v ^ 2 < ε / 2 :=
    Real.sq_sqrt (by positivity : 0 ≤ ε / 2) ▸ pow_lt_pow_left₀ hdv dist_nonneg two_ne_zero
  have h1 := (first_step_dist_sq_and_toReal_le hτ₀ (hτ j) hA₀ hbot hmy_top (hU1 j) hv).1
  have hne : (τ j : ℝ) ≠ 0 := (NNReal.coe_pos.2 (hτ j)).ne'
  have h2 : (τ j : ℝ) * ((φ (U j 1)).toReal - A) ≤
      (τ j : ℝ) * ((φ v).toReal - A) + dist (U j 0) v ^ 2 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right h1 A) (NNReal.coe_nonneg _)).trans_eq
      (by rw [add_sub_right_comm, mul_add]; congr 1; field_simp)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (sub_nonneg.2 h0))]
  linarith

/-- When `U j 0 → x₀ ∈ closure {x | φ x ≠ ⊤}` and `τ j → 0`, the first resolvent steps `U j 1`
converge to `x₀`, enjoy a uniform coercivity lower bound on `φ_{τ₀ / 2}`, and satisfy
`τ j * (φ (U j 1) - A) → 0`. -/
private lemma tendsto_first_step_and_mul_apply_of_mem_closure {X : Type*} [PseudoMetricSpace X]
    {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X}
    (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀))
    (hU1 : ∀ j, U j 1 ∈ moreauYosidaResolvent φ (τ j) (U j 0)) :
    ∃ A : ℝ, Tendsto (fun j ↦ U j 1) atTop (𝓝 x₀) ∧
      (∀ᶠ j in atTop,
        (A : EReal) ≤ moreauYosida φ (τ₀ / 2) (U j 1) ∧ φ (U j 1) ≠ ⊤ ∧ φ (U j 1) ≠ ⊥) ∧
      Tendsto (fun j ↦ (τ j : ℝ) * ((φ (U j 1)).toReal - A)) atTop (𝓝 0) := by
  obtain ⟨w, hw, -⟩ := Metric.mem_closure_iff.1 hx₀ 1 one_pos
  have hbot : ∀ z, φ z ≠ ⊥ := fun z ↦ apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ z) h₀
  have hmy_top : ∀ σ : ℝ≥0, 0 < σ → ∀ a, moreauYosida φ σ a ≠ ⊤ :=
    fun _ hσ a ↦ moreauYosida_ne_top_of_exists_ne_top ⟨w, hw⟩ hσ a
  have hA₀ : moreauYosida φ τ₀ x₁ = ((moreauYosida φ τ₀ x₁).toReal : EReal) :=
    (EReal.coe_toReal (hmy_top τ₀ hτ₀ x₁) h₀).symm
  have hU1_tend :=
    tendsto_first_step_of_mem_closure hτ₀ hA₀ hbot hmy_top hx₀ hτ hτ0 hU0 hU1
  set A : ℝ := (moreauYosida φ τ₀ x₁).toReal - (dist x₀ x₁ + 1) ^ 2 / (2 * (τ₀ - (τ₀ / 2 : ℝ≥0)))
  have hA_ev : ∀ᶠ j in atTop,
      (A : EReal) ≤ moreauYosida φ (τ₀ / 2) (U j 1) ∧ φ (U j 1) ≠ ⊤ ∧ φ (U j 1) ≠ ⊥ := by
    filter_upwards [hU1_tend.eventually (Metric.ball_mem_nhds x₀ one_pos)] with j hj
    refine ⟨coe_sub_div_le_moreauYosida (half_lt_self hτ₀) hA₀ (by positivity) ?_,
      apply_ne_top_of_mem_moreauYosidaResolvent (hU1 j) (hmy_top (τ j) (hτ j) (U j 0)), hbot _⟩
    rw [edist_dist]; exact ENNReal.ofReal_le_ofReal
      ((dist_triangle (U j 1) x₀ x₁).trans (by linarith [Metric.mem_ball.1 hj]))
  exact ⟨A, hU1_tend, hA_ev,
    tendsto_mul_apply_sub_of_mem_closure hτ₀ hA₀ hbot hmy_top hx₀ hτ hτ0 hU0 hU1 hA_ev⟩

/-- Distance bound for `t > τ` using the shifted minimizing movement sequence `k ↦ U (k + 1)`. -/
private lemma dist_shifted_ceil_lt {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {lam : ℝ} {φ : X → EReal} {u : ℝ → X} (hu : IsEVISolution lam φ u)
    (hφ : LowerSemicontinuous φ) {τ₀ τ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hconv : ∀ᶠ η in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam η φ)
    (hτc : PenalizedConvex lam τ φ) (hτ : 0 < τ) (hmτ : (-lam) * τ ≤ 1 / 2) (hτ1 : (τ : ℝ) ≤ 1)
    (hj4 : 4 * τ ≤ τ₀ / 2) {U : ℕ → X} (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    {A T ε : ℝ} (hAj : (A : EReal) ≤ moreauYosida φ (τ₀ / 2) (U 1)) (htopj : φ (U 1) ≠ ⊤)
    (hEj : 2 * exp ((2 * |lam| + 2 * lam ^ 2) * T) * dist (U 1) (u 0) ^ 2 +
      (2 * exp ((2 * |lam| + 2 * lam ^ 2) * T) + 8) *
        (1 + Real.exp (8 * (T + 1 + (τ₀ / 2 : ℝ≥0)) / (τ₀ / 2 : ℝ≥0))) *
          ((τ : ℝ) * ((φ (U 1)).toReal - A)) < (ε / 2) ^ 2)
    (hε : 0 < ε) {s : ℝ} (hs : s ∈ Icc 0 T) :
    dist (U (⌈s / (τ : ℝ)⌉₊ + 1)) (u s) < ε / 2 := by
  let V : ℕ → X := fun k ↦ U (k + 1)
  have hV : ∀ k, V (k + 1) ∈ moreauYosidaResolvent φ τ (V k) := fun k ↦ hU (k + 1)
  have hτ' : τ < τ₀ / 2 := (lt_mul_left hτ (by norm_num)).trans_le hj4
  have hA_bot : moreauYosida φ (τ₀ / 2) (V 0) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot A) hAj
  have hV0_eq : φ (V 0) = ((φ (V 0)).toReal : EReal) :=
    (EReal.coe_toReal htopj (apply_ne_bot_of_moreauYosida_ne_bot (edist_ne_top x₁ _) h₀)).symm
  have hA_le : A ≤ (φ (V 0)).toReal := EReal.coe_le_coe_iff.1 <|
    (hAj.trans (moreauYosida_le_self φ (τ₀ / 2) (V 0))).trans_eq hV0_eq
  have hlow := (le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hV hτ hj4 hAj hV0_eq.le
    (T := T + 1) (by linarith [hs.1, hs.2])
    (floor_div_add_one_le_ceil_div (NNReal.coe_pos.2 hτ) (by linarith [hs.2])
      (by linarith [hs.1, hs.2]))).1
  obtain ⟨eV, heV, hdrop0, hdropB⟩ :=
    exists_toReal_apply_and_sub_le hτ' hA_bot hV (t := s) hs.2 hV0_eq.le hlow
  set B : ℝ := Real.exp (8 * (T + 1 + (τ₀ / 2 : ℝ≥0)) / (τ₀ / 2 : ℝ≥0))
  have hmax : max 0 ((φ (V 0)).toReal - (A - ((φ (V 0)).toReal - A) * B)) =
      (1 + B) * ((φ (V 0)).toReal - A) := by
    rw [show (φ (V 0)).toReal - (A - ((φ (V 0)).toReal - A) * B) =
      (1 + B) * ((φ (V 0)).toReal - A) by ring]
    exact max_eq_right (mul_nonneg (by positivity) (sub_nonneg.2 hA_le))
  rw [hmax] at hdropB
  have hbd := hu.dist_ceil_sq_le_of_penalizedConvex hφ hτ₀ h₀ hconv hτc hτ hmτ hV heV hs.1
  have hexp : exp (max 0 (-2 * lam + 2 * lam ^ 2 * (τ : ℝ)) * s) ≤
      exp ((2 * |lam| + 2 * lam ^ 2) * T) := by
    simpa only [mul_zero, add_zero] using exp_max_zero_mul_le hs.1 hs.2
      (NNReal.coe_nonneg τ) le_rfl (by nlinarith [hτ1, sq_nonneg lam])
  have hsq : dist (V ⌈s / (τ : ℝ)⌉₊) (u s) ^ 2 < (ε / 2) ^ 2 := by
    have hm1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdropB (NNReal.coe_nonneg τ))
      (by positivity : 0 ≤ 2 * exp ((2 * |lam| + 2 * lam ^ 2) * T) + 8)
    have hm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le_two)
      (sq_nonneg (dist (V 0) (u 0)))
    have hm3 := mul_le_mul_of_nonneg_right (add_le_add_right
      (mul_le_mul_of_nonneg_left hexp zero_le_two) 8)
      (mul_nonneg (NNReal.coe_nonneg τ) hdrop0)
    dsimp only [V] at hbd hm1 hm2 hm3; simp only [zero_add] at hbd hm1 hm2 hm3; linarith
  exact (pow_lt_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 hsq

/-- Core uniform convergence on `[0, T]` (`0 ≤ T`) when the minimizing movement hypotheses hold for
every `j`, without requiring bounded initial energy or finite energy at `u 0`. -/
private lemma tendstoUniformlyOn_of_penalizedConvex_forall {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 (u 0)))
    (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  -- Extract first-step convergence `U j 1 → u 0` and vanishing `τ j * (φ (U j 1) - A)`.
  obtain ⟨A, hU1, hA_ev, hmul⟩ := tendsto_first_step_and_mul_apply_of_mem_closure hτ₀ h₀
    (eviDomain_subset_closure (mem_eviDomain.2 ⟨u, hu, rfl⟩)) hτ hτ0 hU0 (fun j ↦ hU j 0)
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
  obtain ⟨δ, hδ, hu_unif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (hu.continuousOn.mono Icc_subset_Ici_self))
    (ε / 2) (by positivity)
  set τ' : ℝ≥0 := τ₀ / 2; set B : ℝ := Real.exp (8 * (T + 1 + τ') / τ')
  set Kmax : ℝ := 2 * |lam| + 2 * lam ^ 2
  set E : ℕ → ℝ := fun j ↦ 2 * exp (Kmax * T) * dist (U j 1) (u 0) ^ 2 +
    (2 * exp (Kmax * T) + 8) * (1 + B) * ((τ j : ℝ) * ((φ (U j 1)).toReal - A))
  have hE0 : Tendsto E atTop (𝓝 0) := by
    simpa [E] using (((by simpa using hU1.dist (tendsto_const_nhds (x := u 0)) :
      Tendsto (fun j ↦ dist (U j 1) (u 0)) atTop (𝓝 0)).pow 2).const_mul
      (2 * exp (Kmax * T))).add (hmul.const_mul ((2 * exp (Kmax * T) + 8) * (1 + B)))
  have hτr := NNReal.tendsto_coe.2 hτ0
  have hlam_ev : ∀ᶠ j in atTop, (-lam) * (τ j : ℝ) ≤ 1 / 2 :=
    (mul_zero (-lam) ▸ hτr.const_mul (-lam)).eventually (ge_mem_nhds (by norm_num))
  filter_upwards [(tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0
      (.of_forall hτ)).eventually hconv, hlam_ev, hτr.eventually (ge_mem_nhds one_pos),
    eventually_four_mul_le hτ0 (half_pos hτ₀), hτr.eventually (gt_mem_nhds hδ), hA_ev,
    hU0.eventually (Metric.ball_mem_nhds (u 0) hε),
    hU1.eventually (Metric.ball_mem_nhds (u 0) (by positivity : 0 < ε / 2)),
    hE0.eventually (gt_mem_nhds (sq_pos_of_pos (by positivity : 0 < ε / 2)))] with
    j hτc hmτ hτ1 hj4 hτδ ⟨hAj, htopj, _⟩ hU0j hU1j hEj t ht
  -- Split on `t = 0`, `0 < t ≤ τ j` (first step), and `τ j < t` (shifted sequence).
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · simpa [dist_comm] using hU0j
  rcases le_or_gt t (τ j : ℝ) with hle | hlt
  · have hc1 : ⌈t / (τ j : ℝ)⌉₊ = 1 := (Nat.ceil_eq_iff one_ne_zero).2
      ⟨by simpa using div_pos ht_pos (NNReal.coe_pos.2 (hτ j)),
        by simpa using div_le_one_of_le₀ hle (NNReal.coe_nonneg _)⟩
    have hut : dist (u t) (u 0) < ε / 2 := hu_unif t ht 0 ⟨le_rfl, hT⟩ <| by
      simpa [Real.dist_eq, abs_of_pos ht_pos] using hle.trans_lt hτδ
    rw [hc1]; exact (dist_triangle (u t) (u 0) (U j 1)).trans_lt
      ((add_lt_add hut (dist_comm (u 0) (U j 1) ▸ hU1j)).trans_eq (add_halves ε))
  · set s := t - (τ j : ℝ)
    have hs : s ∈ Icc 0 T := ⟨sub_nonneg.2 hlt.le, (sub_le_self t (NNReal.coe_nonneg _)).trans ht.2⟩
    have hτne := (NNReal.coe_pos.2 (hτ j)).ne'
    have hceil : ⌈t / (τ j : ℝ)⌉₊ = ⌈s / (τ j : ℝ)⌉₊ + 1 := by
      rw [show t / (τ j : ℝ) = s / τ j + 1 by dsimp [s]; field_simp; ring,
        Nat.ceil_add_one (div_nonneg hs.1 (NNReal.coe_nonneg _))]
    have huts : dist (u t) (u s) < ε / 2 := hu_unif t ht s hs <| by
      simpa [s, Real.dist_eq, abs_of_pos (NNReal.coe_pos.2 (hτ j))] using hτδ
    have hVus := dist_comm (U j (⌈s / (τ j : ℝ)⌉₊ + 1)) (u s) ▸
      dist_shifted_ceil_lt hu hφ hτ₀ h₀ hconv hτc (hτ j) hmτ hτ1 hj4 (hU j) hAj htopj hEj hε hs
    rw [hceil]; exact (dist_triangle (u t) (u s) _).trans_lt
      ((add_lt_add huts hVus).trans_eq (add_halves ε))

/-- **Uniform convergence of minimizing movements with converging initial data.** On a complete
pseudometric space, under coercivity and `TauCeti.PenalizedConvex lam τ φ` for small `τ > 0`, any
minimizing movement family `(τ j, U j)` with `τ j → 0` and initial points `U j 0 → u 0` converges
uniformly on `[0, T]` to the `EVI_lam` solution `u`, without requiring bounded initial energy or
`φ (u 0) ≠ ⊤`. -/
theorem IsEVISolution.tendstoUniformlyOn_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    {u : ℝ → X} (hu : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {τ : ℕ → ℝ≥0} {U : ℕ → ℕ → X} (hτ_pos : ∀ᶠ j in atTop, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 (u 0)))
    (hU : ∀ᶠ j in atTop, ∀ n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (T : ℝ) :
    TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Metric.tendstoUniformlyOn_iff, Icc_eq_empty hT.not_ge]
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hτ_pos.and hU)
  have h := tendstoUniformlyOn_of_penalizedConvex_forall hu hφ hτ₀ h₀ hconv
    (fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).1) (hτ0.comp (tendsto_add_atTop_nat N₁))
    (hU0.comp (tendsto_add_atTop_nat N₁)) (fun j ↦ (hN₁ _ (Nat.le_add_left N₁ j)).2) hT
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε; rw [← Filter.map_add_atTop_eq_nat N₁, Filter.eventually_map]; exact h ε hε

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
  obtain ⟨_, u, _, _, _, _, hu0, hu, _⟩ :=
    exists_limit_const_of_penalizedConvex hφ hτ₀ hτ₁ (fun _ h0 h1 ↦ hconv_lt ⟨h0, h1⟩) h₀ hx₀
  refine hu.congr fun t (ht : 0 ≤ t) ↦ ?_
  have h1 := (hu.tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv (Eventually.of_forall hτ)
    hτ0 (hu0.symm ▸ hU0) (Eventually.of_forall hU) t).tendsto_at (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  have hed := hd (u t) (hlim t ht)
  have hed0 : Tendsto (fun j ↦ edist (u t) (U j ⌈t / (τ j : ℝ)⌉₊)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := u t)).edist h1
  rw [hed0.liminf_eq] at hed; exact edist_le_zero.1 hed

/-- **Characterization of the `EVI_λ` domain** (Ambrosio–Gigli–Savaré, Theorem 4.0.4). If `φ` is
lower semicontinuous on a complete pseudometric space, coercive (`φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0`), and `lam`-penalized convex for all sufficiently small `τ > 0`, then the set
`TauCeti.eviDomain lam φ` of initial points of `EVI_λ` solutions equals `closure {x | φ x ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) :
    eviDomain lam φ = closure {x | φ x ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨_, u, _, _, _, _, hu0, hu, _⟩ :=
      exists_limit_const_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ hx
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- **Existence of `EVI_λ` flows on the closure of the effective domain**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4). Under the hypotheses of
`TauCeti.eviDomain_eq_closure_of_penalizedConvex`, every point `x₀ ∈ closure {x | φ x ≠ ⊤}` is the
initial point of an `EVI_λ` solution. -/
theorem exists_isEVISolution_of_mem_closure_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X}
    (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, IsEVISolution lam φ u ∧ u 0 = x₀ :=
  mem_eviDomain.1 (eviDomain_eq_closure_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ ▸ hx₀)

/-- **Existence of `EVI_λ` flows and uniform convergence of minimizing movements**
(Ambrosio–Gigli–Savaré, Theorem 4.0.4; Ambrosio–Gigli, Theorem 3.25). Let `φ : X → EReal`
be lower semicontinuous on a complete pseudometric space, coercive (`φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0`), and `lam`-penalized convex for all sufficiently small `τ > 0`. Then from every point
`x₀ ∈ closure {x | φ x ≠ ⊤}` starts an `EVI_λ` solution `u` with `u 0 = x₀`, and the piecewise
constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of every minimizing movement scheme with positive
time steps `τ j → 0` and initial points `J j 0 → x₀` converge to `u` uniformly on `[0, T]` for
every `T : ℝ` (without requiring bounded initial energy). -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ τ₁ : ℝ≥0} (hτ₀ : 0 < τ₀) (hτ₁ : 0 < τ₁)
    (hconv : ∀ τ : ℝ≥0, 0 < τ → τ < τ₁ → PenalizedConvex lam τ φ)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → Tendsto (fun j ↦ J j 0) atTop (𝓝 x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨u, hu, hu0⟩ :=
    exists_isEVISolution_of_mem_closure_of_penalizedConvex hφ hτ₀ hτ₁ hconv h₀ hx₀
  have hconv_nhds : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ :=
    (nhdsGT_basis (0 : ℝ≥0)).eventually_iff.2 ⟨τ₁, hτ₁, fun _ hτ ↦ hconv _ hτ.1 hτ.2⟩
  exact ⟨u, hu0, hu, fun τ J hτ hτ0 hJ0 hJ T ↦
    hu.tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv_nhds hτ hτ0 (hu0.symm ▸ hJ0) hJ T⟩

/-- **Generation of `EVI_λ` flows under Ambrosio–Gigli Assumption 3.24** (Ambrosio–Gigli,
Theorem 3.25). Let `φ` be a lower semicontinuous energy on a complete pseudometric space satisfying
the pointwise interpolation condition `TauCeti.ConvexWithDistSq lam φ` (no path continuity
required) and `φ y ≠ ⊥` whenever `φ y ≠ ⊤`. Then for every `x₀ ∈ closure {y | φ y ≠ ⊤}` there
is an `EVI_lam` solution `u` from `x₀` to which minimizing movement interpolants with converging
initial points `U j 0 → x₀` converge uniformly on `[0, T]`, without bounded initial energy. -/
theorem ConvexWithDistSq.exists_isEVISolution_tendstoUniformlyOn {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hconv : ConvexWithDistSq lam φ)
    (hbot : ∀ y, φ y ≠ ⊤ → φ y ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {y | φ y ≠ ⊤}) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ᶠ j in atTop, 0 < τ j) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) →
        (∀ᶠ j in atTop, ∀ n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨y₀, hy₀, -⟩ := Metric.mem_closure_iff.1 hx₀ 1 one_pos
  obtain ⟨τ₀, hτ₀, h₀⟩ :=
    hconv.exists_moreauYosida_ne_bot (hφ.lowerSemicontinuousAt y₀) hy₀ (hbot y₀ hy₀) y₀
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ one_pos
    (fun _ _ _ ↦ hconv.penalizedConvex) h₀ hx₀

/-- Under the hypotheses of `TauCeti.ConvexWithDistSq.exists_isEVISolution_tendstoUniformlyOn`,
the domain of the `EVI_lam` flow equals `closure {y | φ y ≠ ⊤}`. -/
theorem ConvexWithDistSq.eviDomain_eq_closure {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hconv : ConvexWithDistSq lam φ)
    (hbot : ∀ y, φ y ≠ ⊤ → φ y ≠ ⊥) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hx ↦
    let ⟨u, hu0, hu, _⟩ := hconv.exists_isEVISolution_tendstoUniformlyOn hφ hbot (subset_closure hx)
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- Under `TauCeti.ConvexWithDistSq lam φ` (pointwise interpolation, no path continuity required) on
a complete pseudometric space, if `φ` is lower semicontinuous and satisfies `φ y ≠ ⊥` whenever
`φ y ≠ ⊤`, then every point `x₀ ∈ closure {y | φ y ≠ ⊤}` is the initial point of an `EVI_lam`
solution. -/
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
on CAT(0) spaces** (Jost; Mayer, Theorem 1.13). Let `φ : X → EReal` be lower semicontinuous,
`lam`-geodesically convex, and never equal to `⊥` on a complete CAT(0) pseudometric space, and let
`x₀ ∈ closure {x | φ x ≠ ⊤}`. Then there starts from `x₀` an `EVI_λ` solution `u` with
`u 0 = x₀`, and all minimizing movement interpolants with positive step sizes `τ j → 0` and
converging initial points `J j 0 → x₀` converge uniformly to `u` on compact time intervals
`[0, T]` (without bounded initial energy). -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn
    (hφ : LowerSemicontinuous φ) (hconv : GeodesicallyConvex lam φ)
    (hbot : ∀ z, φ z ≠ ⊥) {x₀ : X} (hx₀ : x₀ ∈ closure {x | φ x ≠ ⊤}) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → Tendsto (fun j ↦ J j 0) atTop (𝓝 x₀) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) :=
  hconv.convexWithDistSq.exists_isEVISolution_tendstoUniformlyOn hφ (fun _ _ ↦ hbot _) hx₀

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
