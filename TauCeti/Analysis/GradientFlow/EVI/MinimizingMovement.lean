/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.Analysis.GradientFlow.MinimizingMovement
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import TauCeti.Analysis.GradientFlow.EVI.Stability
import TauCeti.Analysis.GradientFlow.MoreauYosida.ErrorEstimate
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.Topology.Order.Interval

/-!
# Generation of `EVI_λ` flows by minimizing movements

Let `φ : X → EReal` be a lower semicontinuous energy on a complete pseudometric space and `λ : ℝ`.
When `φ` satisfies Ambrosio–Gigli–Savaré's penalized convexity condition
`TauCeti.PenalizedConvex λ τ φ` for all sufficiently small positive time steps `τ` (their
Assumption 4.0.1) and is coercive (`φ_{τ₀}(x₁) > -∞`), De Giorgi's minimizing movement scheme
converges in the metric — with no compactness hypothesis on energy sublevels — to an `EVI_λ`
solution (`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`, Theorem 4.0.4 of
Ambrosio–Gigli–Savaré).

Feeding the discrete two-step comparison bound `TauCeti.dist_ceil_sq_le_of_penalizedConvex`
(from `TauCeti.Analysis.GradientFlow.MoreauYosida.ErrorEstimate`) and a priori coercivity estimates
into a complete pseudometric space yields, for every `x₀` with `φ x₀ ≠ ⊤`:

* a reference minimizing movement family whose piecewise constant interpolants are uniformly Cauchy
  on `[0, T]` and converge to a continuous curve `u` with `u 0 = x₀` (locally absolutely continuous
  by `TauCeti.absolutelyContinuousOnInterval_of_forall_mem_moreauYosidaResolvent`); passing
  `TauCeti.PenalizedConvex.apply_le` to the limit shows that `u` is an `EVI_λ` solution;
* letting the second time step `η → 0` yields the quantitative `O(√τ)` error bound
  `TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex` against any `EVI_λ` solution, which
  implies locally uniform convergence of arbitrary minimizing movement sequences with converging
  initial data and uniformly bounded initial energy;
* by `λ`-contraction (`TauCeti.IsEVISolution.dist_le`) and stability
  (`TauCeti.TendstoGamma.isEVISolution_of_tendsto`), the `EVI_λ` domain is the full closure
  `closure {x | φ x ≠ ⊤}` (`TauCeti.eviDomain_eq_closure_of_penalizedConvex`).

When `φ` never takes `⊥` and is `λ`-convex along curves along which `d(·, w)²` is `2`-convex
(Ambrosio–Gigli Assumption 3.24 and Theorem 3.25), both penalized convexity and coercivity hold
automatically; in particular, this applies to `λ`-geodesically convex energies on complete CAT(0)
spaces.

## Main results

* `TauCeti.IsEVISolution.dist_ceil_sq_le_of_penalizedConvex`: quantitative `O(√τ)` error bound
  between a minimizing movement sequence and an `EVI_λ` solution.
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex`: existence of an `EVI_λ`
  solution and locally uniform convergence of minimizing movements under `TauCeti.PenalizedConvex`.
* `TauCeti.IsGeneralizedMinimizingMovement.isEVISolution_of_penalizedConvex`: on a complete metric
  space, every generalized minimizing movement for a convergence along which `edist` is lower
  semicontinuous is an `EVI_λ` solution.
* `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: the `EVI_λ` domain equals the closure of
  `{x | φ x ≠ ⊤}`.
* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq` and
  `TauCeti.eviDomain_eq_closure_of_convexAlong_and_convexAlong_dist_sq`: generation of `EVI_λ` flows
  under `λ`-convexity of `φ` and `2`-convexity of `d(·, w)²` along curves.
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn` and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`: specialization to complete CAT(0) spaces.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4 and Section 4.1.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Math. 2062,
  Springer 2013, Assumption 3.24 and Theorem 3.25.
-/

public section

noncomputable section

open Filter Set Topology Real Finset
open scoped NNReal

namespace TauCeti

/-! ### Discrete-to-continuous EVI passage and locally uniform convergence -/

section Convergence

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

/-- Uniform eventual bound on `d(U i ⌈t / τ i⌉₊, U j ⌈t / τ j⌉₊)²` over `t ∈ [0, T]` along a
minimizing movement family with `τ j → 0`. -/
private theorem exists_eventually_dist_ceil_sq_le {X : Type*} [PseudoMetricSpace X]
    {lam : ℝ} {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {x₀ : X} {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀)) {S : ℝ} (hS : ∀ j, φ (U j 0) ≤ S)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (C₁ C₂ : ℝ) (N₀ : ℕ), 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ i ≥ N₀, ∀ j ≥ N₀, ∀ t ∈ Icc 0 T,
      dist (U i ⌈t / τ i⌉₊) (U j ⌈t / τ j⌉₊) ^ 2 ≤
        C₁ * dist (U i 0) (U j 0) ^ 2 + C₂ * ((τ i : ℝ) + τ j) := by
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top x₀ x₁) hτ hτ0 hU hU0 hS (by positivity : 0 ≤ T + 1)
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  have hτw : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0 (Eventually.of_forall hτ)
  have hlam_ev : ∀ᶠ j in atTop, |lam| * (τ j : ℝ) ≤ 1 / 2 :=
    (mul_zero |lam| ▸ hτr.const_mul |lam|).eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 <| (hτw.eventually hconv).and <| hlam_ev.and <|
    (hτr.eventually (ge_mem_nhds one_pos)).and <| (hτ0.eventually (gt_mem_nhds hτ₀)).and hapriori
  set Kmax : ℝ := 2 * |lam| + 4 * lam ^ 2; set M : ℝ := max 0 (S - L)
  refine ⟨2 * exp (Kmax * T), (2 * exp (Kmax * T) + 8) * M, N₀, by positivity, by positivity,
    fun i hi j hj t ht ↦ ?_⟩
  obtain ⟨hci, hmi, hi1, hiτ₀, hiL⟩ := hN₀ i hi
  obtain ⟨hcj, hmj, hj1, hjτ₀, hjL⟩ := hN₀ j hj
  obtain ⟨eU, heU, haU, hdropU⟩ :=
    exists_toReal_apply_and_sub_le (hτ i) hiτ₀ h₀ (hU i) (hS i) ht fun n hn ↦ (hiL n hn).1
  obtain ⟨eV, heV, haV, hdropV⟩ :=
    exists_toReal_apply_and_sub_le (hτ j) hjτ₀ h₀ (hU j) (hS j) ht fun n hn ↦ (hjL n hn).1
  have hbd := dist_ceil_sq_le_of_penalizedConvex hci hcj (hτ i) (hτ j) hmi hmj
    (hU i) (hU j) heU heV ht.1
  have hexp_le : exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ i + 2 * lam ^ 2 * τ j) * t) ≤
      exp (Kmax * T) := exp_le_exp.2 <| mul_le_mul (max_le (by positivity) (by
        dsimp [Kmax]
        nlinarith [neg_le_abs lam, sq_nonneg lam]))
      ht.2 ht.1 (by positivity)
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le zero_le_two)
    (sq_nonneg (dist (U i 0) (U j 0)))
  have h2 := mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_left hexp_le zero_le_two) 8)
    (add_le_add (mul_le_mul_of_nonneg_left hdropU (NNReal.coe_nonneg (τ i)))
      (mul_le_mul_of_nonneg_left hdropV (NNReal.coe_nonneg (τ j))))
    (add_nonneg (mul_nonneg (NNReal.coe_nonneg (τ i)) haU)
      (mul_nonneg (NNReal.coe_nonneg (τ j)) haV)) (by positivity)
  nlinarith [hbd, h1, h2]

/-- Uniform Cauchy property of piecewise constant interpolants on `[0, T]` under
`PenalizedConvex`. -/
private theorem uniformCauchySeqOn_ceil_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    {lam : ℝ} {φ : X → EReal} {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {x₀ : X} {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j) (hτ0 : Tendsto τ atTop (𝓝 0))
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    (hU0 : Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀)) {S : ℝ} (hS : ∀ j, φ (U j 0) ≤ S)
    {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) atTop (Icc 0 T) := by
  obtain ⟨C₁, C₂, N₀, hC₁, -, hbd⟩ :=
    exists_eventually_dist_ceil_sq_le hτ₀ h₀ hconv hτ hτ0 hU hU0 hS hT
  have hd0 : Tendsto (fun j ↦ dist (U j 0) x₀) atTop (𝓝 0) := by
    simpa using hU0.dist (tendsto_const_nhds (x := x₀))
  have herr : Tendsto (fun j ↦ 2 * C₁ * dist (U j 0) x₀ ^ 2 + C₂ * (τ j : ℝ)) atTop (𝓝 0) := by
    simpa using ((hd0.pow 2).const_mul (2 * C₁)).add ((NNReal.tendsto_coe.2 hτ0).const_mul C₂)
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (herr.eventually (gt_mem_nhds (half_pos (sq_pos_of_pos hε))))
  refine ⟨max N₀ N₁, fun i hi j hj t ht ↦ ?_⟩
  have htri : dist (U i 0) (U j 0) ^ 2 ≤ 2 * dist (U i 0) x₀ ^ 2 + 2 * dist (U j 0) x₀ ^ 2 := by
    have h1 := pow_le_pow_left₀ dist_nonneg (dist_triangle_right (U i 0) (U j 0) x₀) 2
    nlinarith [sq_nonneg (dist (U i 0) x₀ - dist (U j 0) x₀), h1]
  have hsq : dist (U i ⌈t / τ i⌉₊) (U j ⌈t / τ j⌉₊) ^ 2 < ε ^ 2 := by
    linarith [hbd i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) t ht,
      mul_le_mul_of_nonneg_left htri hC₁,
      hN₁ i ((le_max_right _ _).trans hi), hN₁ j ((le_max_right _ _).trans hj)]
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

/-- Passes `PenalizedConvex.apply_le` to a pointwise limit of minimizing movement interpolants on a
single positive-length interval `[s, t]`. -/
private theorem apply_le_of_tendsto_ceil {X : Type*} [PseudoMetricSpace X] {lam : ℝ}
    {φ : X → EReal} (hφ : LowerSemicontinuous φ) {τ : ℕ → ℝ≥0} (hτ : ∀ j, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hconv : ∀ j, PenalizedConvex lam (τ j) φ)
    {U : ℕ → ℕ → X} (hU : ∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n))
    {u : ℝ → X} (hlim : ∀ r ≥ 0, Tendsto (fun j ↦ U j ⌈r / (τ j : ℝ)⌉₊) atTop (𝓝 (u r)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal) := by
  set N : ℕ → ℕ := fun j ↦ ⌈t / τ j⌉₊ - ⌈s / τ j⌉₊
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  have hN_lim := tendsto_natCast_sub_ceil_mul
    (Eventually.of_forall fun j ↦ NNReal.coe_pos.2 (hτ j)) hτr hs hst.le
  have hpow := tendsto_one_add_mul_pow_exp lam (t - s) hτr hN_lim
  have hsum := tendsto_mul_sum_one_add_mul_pow lam (t - s) hτr hN_lim
  have hIpos : 0 < 2 * ∫ r in 0..(t - s), exp (lam * r) :=
    mul_pos two_pos (integral_exp_mul_pos lam (sub_pos.2 hst))
  set R : ℕ → ℝ := fun j ↦
    (dist (U j ⌈s / τ j⌉₊) y ^ 2 - (1 + lam * τ j) ^ N j * dist (U j ⌈t / τ j⌉₊) y ^ 2) /
      (2 * τ j * ∑ n ∈ range (N j), (1 + lam * τ j) ^ n)
  have hR_lim : Tendsto (fun j ↦ (R j : EReal)) atTop (𝓝 ((((dist (u s) y ^ 2 -
      exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 <|
      ((((hlim s hs).dist tendsto_const_nhds).pow 2).sub
        (hpow.mul (((hlim t (hs.trans hst.le)).dist tendsto_const_nhds).pow 2))).div
      (by simpa [mul_assoc] using hsum.const_mul 2) hIpos.ne'
  have hev : ∀ᶠ j in atTop, φ (U j ⌈t / τ j⌉₊) ≤ φ y + (R j : EReal) := by
    filter_upwards [hN_lim.eventually (lt_mem_nhds (sub_pos.2 hst)),
      hτr.eventually (eventually_one_add_mul_pos lam)] with j hjN hpos
    have hNpos : 0 < N j := by
      by_contra h0; push Not at h0; dsimp only [N] at h0
      rw [Nat.le_zero.1 h0, Nat.cast_zero, zero_mul] at hjN
      exact lt_irrefl 0 hjN
    have hle_st : ⌈s / τ j⌉₊ ≤ ⌈t / τ j⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right hst.le (NNReal.coe_nonneg _))
    simpa [R, N, Nat.add_sub_cancel' hle_st] using (hconv j).apply_le (hτ j) hpos.le
      (U := fun n ↦ U j (⌈s / τ j⌉₊ + n))
      (fun n ↦ by simpa [Nat.add_assoc] using hU j (⌈s / τ j⌉₊ + n)) hy hNpos
  calc φ (u t) ≤ liminf (fun j ↦ φ (U j ⌈t / τ j⌉₊)) atTop :=
        (hφ.le_liminf (u t)).trans (hlim t (hs.trans hst.le)).liminf_le_liminf_comp
    _ ≤ limsup (fun j ↦ φ y + (R j : EReal)) atTop := (liminf_le_liminf hev).trans liminf_le_limsup
    _ ≤ limsup (fun _ : ℕ ↦ φ y) atTop + limsup (fun j ↦ (R j : EReal)) atTop :=
        EReal.limsup_add_le (.inr (by rw [hR_lim.limsup_eq]; exact EReal.coe_ne_top _))
          (.inr (by rw [hR_lim.limsup_eq]; exact EReal.coe_ne_bot _))
    _ = _ := by rw [limsup_const, hR_lim.limsup_eq]

/-- Builds a concrete positive time-step sequence `τ_ref j → 0` small enough for penalized
convexity, `1 + lam * τ_ref j > 0`, and global coercivity. -/
private theorem exists_ref_step_seq {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) :
    ∃ τ_ref : ℕ → ℝ≥0, (∀ j, 0 < τ_ref j) ∧ Tendsto τ_ref atTop (𝓝 0) ∧
      (∀ j, PenalizedConvex lam (τ_ref j) φ) ∧ (∀ j, 0 < 1 + lam * τ_ref j) ∧
      ∀ j z, moreauYosida φ (τ_ref j) z ≠ ⊥ := by
  set σ : ℕ → ℝ≥0 := fun j ↦ ((j : ℝ≥0) + 1)⁻¹
  have hσ_pos (j : ℕ) : 0 < σ j := by positivity
  have hσ0 : Tendsto σ atTop (𝓝 0) := NNReal.tendsto_coe.1 <| by
    simpa [σ, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hσw : Tendsto σ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσ0 (Eventually.of_forall hσ_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 <| (hσw.eventually hconv).and <|
    ((NNReal.tendsto_coe.2 hσ0).eventually (eventually_one_add_mul_pos lam)).and
      (hσ0.eventually (gt_mem_nhds hτ₀))
  exact ⟨fun j ↦ σ (j + N), fun j ↦ hσ_pos _, hσ0.comp (tendsto_add_atTop_nat N),
    fun j ↦ (hN _ (Nat.le_add_left N j)).1, fun j ↦ (hN _ (Nat.le_add_left N j)).2.1,
    fun j z ↦ moreauYosida_ne_bot_of_lt (hN _ (Nat.le_add_left N j)).2.2 (edist_ne_top z x₁) h₀⟩

/-- Constructs a pointwise limit curve `u` on `[0, ∞)` with `u 0 = x₀` from a family
`F : ℕ → ℝ → X` that is uniformly Cauchy on `[0, T]` for every `T ≥ 0` and satisfies
`F k 0 → x₀`. -/
private theorem exists_tendsto_Ici_of_uniformCauchySeqOn {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {F : ℕ → ℝ → X} {x₀ : X}
    (huc : ∀ {T : ℝ}, 0 ≤ T → UniformCauchySeqOn F atTop (Icc 0 T))
    (h0 : Tendsto (fun k ↦ F k 0) atTop (𝓝 x₀)) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ ∀ t ≥ 0, Tendsto (fun k ↦ F k t) atTop (𝓝 (u t)) := by
  choose u_pos hu_pos using fun (t : {t : ℝ // 0 < t}) ↦
    cauchySeq_tendsto_of_complete ((huc t.2.le).cauchySeq ⟨t.2.le, le_rfl⟩)
  refine ⟨fun t ↦ if ht : 0 < t then u_pos ⟨t, ht⟩ else x₀, by simp, fun t ht ↦ ?_⟩
  rcases ht.eq_or_lt with rfl | ht_pos
  · simpa using h0
  · simpa [ht_pos] using hu_pos ⟨t, ht_pos⟩

/-- Constructs a reference minimizing movement family `(τ_ref, U_ref)` starting at `x₀` whose
piecewise constant interpolants converge pointwise on `[0, ∞)` to an `EVI_lam` solution `u` with
`u 0 = x₀`. -/
private theorem exists_ref_minimizingMovement {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {lam : ℝ} {φ : X → EReal} (hφ : LowerSemicontinuous φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀)
    {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ (τ_ref : ℕ → ℝ≥0) (U_ref : ℕ → ℕ → X) (u : ℝ → X),
      (∀ j, 0 < τ_ref j) ∧ Tendsto τ_ref atTop (𝓝 0) ∧ (∀ j, U_ref j 0 = x₀) ∧
      (∀ j, φ (U_ref j 0) ≤ ((φ x₀).toReal : EReal)) ∧
      (∀ j n, U_ref j (n + 1) ∈ moreauYosidaResolvent φ (τ_ref j) (U_ref j n)) ∧
      u 0 = x₀ ∧ (∀ t ≥ 0, Tendsto (fun j ↦ U_ref j ⌈t / (τ_ref j : ℝ)⌉₊) atTop (𝓝 (u t))) ∧
      IsEVISolution lam φ u := by
  obtain ⟨τ_ref, hτ_pos, hτ_0, hconv_ref, hm_ref, hne_bot⟩ := exists_ref_step_seq hτ₀ h₀ hconv
  choose U_ref hU_ref0 hU_ref using fun j ↦
    (hconv_ref j).exists_forall_mem_moreauYosidaResolvent hφ (hτ_pos j) (hm_ref j) (hne_bot j) x₀
  have hU_ref0_lim : Tendsto (fun j ↦ U_ref j 0) atTop (𝓝 x₀) := by
    simpa only [hU_ref0] using tendsto_const_nhds
  have hS_ref (j : ℕ) : φ (U_ref j 0) ≤ ((φ x₀).toReal : EReal) := by
    rw [hU_ref0 j,
      EReal.coe_toReal hx₀ (apply_ne_bot_of_moreauYosida_ne_bot h₀ (edist_ne_top _ _))]
  obtain ⟨u, hu0, hlim_ref⟩ := exists_tendsto_Ici_of_uniformCauchySeqOn
    (fun hT ↦ uniformCauchySeqOn_ceil_of_penalizedConvex hτ₀ h₀ hconv hτ_pos hτ_0 hU_ref
      hU_ref0_lim hS_ref hT)
    (by simpa only [zero_div, Nat.ceil_zero] using hU_ref0_lim)
  have hu_cont : ContinuousOn u (Ici 0) := continuousOn_Ici_of_forall_Icc fun T hT ↦
    uIcc_of_le hT ▸ (absolutelyContinuousOnInterval_of_forall_mem_moreauYosidaResolvent
      (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge) hτ₀ h₀ hτ_pos hτ_0 hU_ref hU_ref0_lim
      hS_ref (fun t ht ↦ hlim_ref t ht.1) hT).continuousOn'
  refine ⟨τ_ref, U_ref, u, hτ_pos, hτ_0, hU_ref0, hS_ref, hU_ref, hu0, hlim_ref, ?_⟩
  exact isEVISolution_of_apply_le hφ hu_cont
    (fun t ht ↦ ne_top_of_le_ne_top (EReal.add_ne_top hx₀ (EReal.coe_ne_top _))
      (apply_le_of_tendsto_ceil hφ hτ_pos hτ_0 hconv_ref hU_ref hlim_ref hx₀ le_rfl ht))
    (fun t _ ↦ apply_ne_bot_of_moreauYosida_ne_bot h₀ (edist_ne_top x₁ (u t)))
    (fun _ hy _ _ hs hst ↦
      apply_le_of_tendsto_ceil hφ hτ_pos hτ_0 hconv_ref hU_ref hlim_ref hy hs hst)

/-- `η → 0` limit of `dist_ceil_sq_le_of_penalizedConvex` against an `EVI_lam` solution `u` whose
initial point has finite energy `φ (u 0) ≠ ⊤`. -/
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
  obtain ⟨η, V, v, hη_pos, hη0, hV0, hSV, hV, hv0, hlim, hv⟩ :=
    exists_ref_minimizingMovement hφ hτ₀ h₀ hconv hu0
  have hd_vu : dist (v t) (u t) = 0 :=
    le_antisymm ((hv.dist_le hu hφ ht).trans_eq (by simp [hv0])) dist_nonneg
  have hdist_eq : dist (U ⌈t / τ⌉₊) (u t) = dist (U ⌈t / τ⌉₊) (v t) := le_antisymm
    ((dist_triangle _ (v t) _).trans_eq (by rw [hd_vu, add_zero]))
    ((dist_triangle _ (u t) _).trans_eq (by rw [dist_comm (u t), hd_vu, add_zero]))
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top (u 0) x₁) hη_pos hη0 hV
      (by simpa only [hV0] using tendsto_const_nhds) hSV (by positivity : 0 ≤ t + 1)
  have hηr : Tendsto (fun j ↦ (η j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hη0
  have hηw : Tendsto η atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hη0 (Eventually.of_forall hη_pos)
  have hlam_ev : ∀ᶠ j in atTop, |lam| * (η j : ℝ) ≤ 1 / 2 :=
    (mul_zero |lam| ▸ hηr.const_mul |lam|).eventually (ge_mem_nhds (by norm_num))
  set K : ℝ → ℝ := fun r ↦ max 0 (-2 * lam + 2 * lam ^ 2 * τ + 2 * lam ^ 2 * r)
  set M : ℝ := max 0 ((φ (u 0)).toReal - L)
  set R : ℝ → ℝ := fun r ↦ 2 * exp (K r * t) * dist (U 0) (u 0) ^ 2 +
    (2 * exp (K r * t) + 8) * (τ * (eU 0 - eU (⌊t / τ⌋₊ + 1)) + r * M)
  have hR_cont : Continuous R := by fun_prop
  have hev : ∀ᶠ j in atTop, dist (U ⌈t / τ⌉₊) (V j ⌈t / η j⌉₊) ^ 2 ≤ R (η j) := by
    filter_upwards [hηw.eventually hconv, hlam_ev, hη0.eventually (gt_mem_nhds hτ₀),
      hapriori] with j hηc hmη hjτ₀ hjL
    obtain ⟨eV, heV, -, hdropV⟩ := exists_toReal_apply_and_sub_le (hη_pos j) hjτ₀ h₀ (hV j)
      (hSV j) ⟨ht, le_rfl⟩ fun n hn ↦ (hjL n hn).1
    have hbd := dist_ceil_sq_le_of_penalizedConvex hτc hηc hτ (hη_pos j) hmτ hmη hU (hV j)
      heU heV ht
    rw [hV0 j] at hbd
    have hmulV := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdropV (NNReal.coe_nonneg (η j)))
      (by positivity : 0 ≤ 2 * exp (K (η j) * t) + 8)
    dsimp only [R, K] at hmulV ⊢
    linarith [hbd, hmulV]
  rw [hdist_eq]
  simpa [R, K] using le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist (hlim t ht)).pow 2)
    ((hR_cont.tendsto 0).comp hηr) hev

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

/-- **Generation of `EVI_λ` solutions by minimizing movements** (Ambrosio–Gigli–Savaré,
Theorem 4.0.4). Let `φ` be a lower semicontinuous energy on a complete pseudometric space such that
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0` and `x₁`, and suppose `TauCeti.PenalizedConvex lam τ φ` holds
for all sufficiently small `τ > 0`. Then for every `x₀` with `φ x₀ ≠ ⊤` there exists an `EVI_lam`
solution `u` starting at `x₀` such that along any positive time steps `τ j → 0` and any minimizing
movement sequences `U j` whose initial points converge to `x₀` with uniformly bounded energy, the
piecewise constant interpolants `t ↦ U j ⌈t / τ j⌉₊` converge to `u` uniformly on `[0, T]` for
every `T`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ j, φ (U j 0) ≤ S) →
        (∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨-, -, u, -, -, -, -, -, hu0, -, hevi⟩ :=
    exists_ref_minimizingMovement hφ hτ₀ h₀ hconv hx₀
  refine ⟨u, hu0, hevi, fun τ U hτ_ne hτ0 hU0 ⟨S, hS⟩ hU T ↦ ?_⟩
  rcases lt_or_ge T 0 with hT | hT
  · simp [Metric.tendstoUniformlyOn_iff, Icc_eq_empty hT.not_ge]
  have hτ (j : ℕ) : 0 < τ j := pos_iff_ne_zero.2 (hτ_ne j)
  obtain ⟨L, _, -, hapriori⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent
      hτ₀ h₀ (edist_ne_top x₀ x₁) hτ hτ0 hU hU0 hS (by positivity : 0 ≤ T + 1)
  have hτr : Tendsto (fun j ↦ (τ j : ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.2 hτ0
  have hτw : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0 (Eventually.of_forall hτ)
  have hlam_ev : ∀ᶠ j in atTop, |lam| * (τ j : ℝ) ≤ 1 / 2 :=
    (mul_zero |lam| ▸ hτr.const_mul |lam|).eventually (ge_mem_nhds (by norm_num))
  set Kmax : ℝ := 2 * |lam| + 2 * lam ^ 2; set M : ℝ := max 0 (S - L)
  set E : ℕ → ℝ := fun j ↦
    2 * exp (Kmax * T) * dist (U j 0) x₀ ^ 2 + (2 * exp (Kmax * T) + 8) * M * τ j
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have hd0 : Tendsto (fun j ↦ dist (U j 0) x₀) atTop (𝓝 0) := by
      simpa using hU0.dist (tendsto_const_nhds (x := x₀))
    simpa [E] using ((hd0.pow 2).const_mul (2 * exp (Kmax * T))).add
      (hτr.const_mul ((2 * exp (Kmax * T) + 8) * M))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hτw.eventually hconv, hlam_ev, hτr.eventually (ge_mem_nhds one_pos),
    hτ0.eventually (gt_mem_nhds hτ₀), hapriori,
    hE0.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with j hτc hmτ hτ1 hτ_lt hL hEj t ht
  obtain ⟨eU, heU, haU, hdropU⟩ :=
    exists_toReal_apply_and_sub_le (hτ j) hτ_lt h₀ (hU j) (hS j) ht fun n hn ↦ (hL n hn).1
  have hbd := hevi.dist_ceil_sq_le_of_penalizedConvex hφ hτ₀ h₀ hconv hτc (hτ j) hmτ (hU j)
    heU ht.1
  rw [hu0] at hbd
  have hexp : exp (max 0 (-2 * lam + 2 * lam ^ 2 * τ j) * t) ≤ exp (Kmax * T) :=
    exp_le_exp.2 <| mul_le_mul (max_le (by positivity) (by
      dsimp [Kmax]; nlinarith [neg_le_abs lam, sq_nonneg lam])) ht.2 ht.1 (by positivity)
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le_two)
    (sq_nonneg (dist (U j 0) x₀))
  have h2 := mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_left hexp zero_le_two) 8)
    (mul_le_mul_of_nonneg_left hdropU (NNReal.coe_nonneg (τ j)))
    (mul_nonneg (NNReal.coe_nonneg (τ j)) haU) (by positivity)
  have hsq : dist (u t) (U j ⌈t / (τ j : ℝ)⌉₊) ^ 2 < ε ^ 2 := by
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
  obtain ⟨u, -, hu, hunif⟩ :=
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv hx₀
  refine hu.congr fun t (ht : 0 ≤ t) ↦ ?_
  have h1 := (hunif τ U (fun j ↦ (hτ j).ne') hτ0 hU0 ⟨S, hS⟩ hU t).tendsto_at
    (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  have hed := hd (u t) (hlim t ht)
  have hed0 : Tendsto (fun j ↦ edist (u t) (U j ⌈t / (τ j : ℝ)⌉₊)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := u t)).edist h1
  rw [hed0.liminf_eq] at hed
  exact edist_le_zero.1 hed

/-- **Domain of the `EVI_λ` flow under penalized convexity** (Ambrosio–Gigli–Savaré,
Theorem 4.0.4). On a complete pseudometric space, if `φ` is lower semicontinuous, satisfies
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0` and `x₁`, and is penalized convex for all sufficiently small
positive time steps, then an `EVI_lam` solution starts from a point `x` if and only if `x` lies in
the closure of `{y | φ y ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] {lam : ℝ} {φ : X → EReal} (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥)
    (hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ φ) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} := by
  refine Subset.antisymm eviDomain_subset_closure fun x hx ↦ ?_
  obtain ⟨x_seq, hx_top, hx_lim⟩ := mem_closure_iff_seq_limit.1 hx
  choose u_seq hu_seq0 hu_seq _ using fun k ↦
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ h₀ hconv (hx_top k)
  have huc (T : ℝ) : UniformCauchySeqOn u_seq atTop (Icc 0 T) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.1 hx_lim.cauchySeq)
      (ε / (exp (|lam| * T) + 1)) (by positivity)
    refine ⟨N, fun i hi j hj t ht ↦ ?_⟩
    have hd := (hu_seq i).dist_le (hu_seq j) hφ ht.1
    rw [hu_seq0 i, hu_seq0 j] at hd
    have hexp : exp (-(lam * t)) ≤ exp (|lam| * T) := exp_le_exp.2 <| by
      nlinarith [neg_le_abs lam, ht.1, ht.2, abs_nonneg lam]
    calc dist (u_seq i t) (u_seq j t)
        ≤ exp (|lam| * T) * dist (x_seq i) (x_seq j) :=
          hd.trans (mul_le_mul_of_nonneg_right hexp dist_nonneg)
      _ < (exp (|lam| * T) + 1) * (ε / (exp (|lam| * T) + 1)) := by
          nlinarith [hN i hi j hj, dist_nonneg (x := x_seq i) (y := x_seq j), exp_pos (|lam| * T)]
      _ = ε := mul_div_cancel₀ _ (by positivity)
  obtain ⟨u, hu0, hlim⟩ := exists_tendsto_Ici_of_uniformCauchySeqOn
    (fun _ ↦ huc _) (by simpa only [hu_seq0] using hx_lim)
  have hu_cont : ContinuousOn u (Ici 0) := continuousOn_Ici_of_forall_Icc fun T _ ↦
    ((huc T).tendstoUniformlyOn_of_tendsto fun t ht ↦ hlim t ht.1).continuousOn
      (Eventually.of_forall fun k ↦ (hu_seq k).continuousOn.mono Icc_subset_Ici_self).frequently
  exact mem_eviDomain.2 ⟨u, (hφ.tendstoGamma_const).isEVISolution_of_tendsto (fun _ ↦ hφ)
    hu_seq hlim hu_cont ⟨x_seq 0, hx_top 0⟩
    (fun t _ ↦ apply_ne_bot_of_moreauYosida_ne_bot h₀ (edist_ne_top x₁ (u t))), hu0⟩

end Convergence

/-! ### Convexity along curves with `2`-convex squared distance and CAT(0) spaces -/

section CurveConvexity

/-- **Generation of `EVI_λ` flows under convexity along curves** (Ambrosio–Gigli, Theorem 3.25).
Let `φ` be a lower semicontinuous energy on a complete pseudometric space that never takes the
value `⊥`. Suppose that for every base point `w` and any two points `v₀`, `v₁` of `{y | φ y ≠ ⊤}`
there is a curve `γ` from `v₀` to `v₁` along which `φ` is `lam`-convex and `z ↦ d(z, w)²` is
`2`-convex. Then coercivity holds automatically, and for every `x₀` with `φ x₀ ≠ ⊤` there is an
`EVI_lam` solution `u` from `x₀` to which minimizing movement interpolants converge locally
uniformly. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ j, φ (U j 0) ≤ S) →
        (∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, hmτ₀⟩ := exists_pos_one_add_mul_pos lam
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀
    (moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq hφ hbot
      (fun v₀ _ h₀ h₁ ↦ hconv v₀ h₀ h₁) hmτ₀ x₀)
    (Eventually.of_forall fun _ ↦ penalizedConvex_of_convexAlong_and_convexAlong_dist_sq hconv)
    hx₀

/-- Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_convexAlong_and_convexAlong_dist_sq`, the
domain of the `EVI_lam` flow equals `closure {y | φ y ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_convexAlong_and_convexAlong_dist_sq {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {lam : ℝ} {φ : X → EReal}
    (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    (hconv : ∀ (w : X) ⦃v₀ v₁ : X⦄, φ v₀ ≠ ⊤ → φ v₁ ≠ ⊤ → ∃ γ : ℝ → X, γ 0 = v₀ ∧ γ 1 = v₁ ∧
      ConvexAlong lam φ γ ∧ ConvexAlong 2 (fun z ↦ ((dist z w ^ 2 : ℝ) : EReal)) γ) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} := by
  rcases Set.eq_empty_or_nonempty {y : X | φ y ≠ ⊤} with hemp | ⟨x₁, -⟩
  · exact Subset.antisymm (eviDomain_subset_closure.trans (by simp [hemp])) (by simp [hemp])
  obtain ⟨τ₀, hτ₀, hmτ₀⟩ := exists_pos_one_add_mul_pos lam
  exact eviDomain_eq_closure_of_penalizedConvex hφ hτ₀
    (moreauYosida_ne_bot_of_convexAlong_and_convexAlong_dist_sq hφ hbot
      (fun v₀ _ h₀ h₁ ↦ hconv v₀ h₀ h₁) hmτ₀ x₁)
    (Eventually.of_forall fun _ ↦ penalizedConvex_of_convexAlong_and_convexAlong_dist_sq hconv)

/-- **Generation of `EVI_λ` flows on CAT(0) spaces.** On a complete CAT(0) space, every lower
semicontinuous `lam`-geodesically convex energy that never takes the value `⊥` generates an
`EVI_lam` solution from each `x₀` with `φ x₀ ≠ ⊤`, obtained as the locally uniform metric limit of
minimizing movement interpolants. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X] {lam : ℝ} {φ : X → EReal}
    (h : GeodesicallyConvex lam φ) (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥)
    {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ U j 0) atTop (𝓝 x₀) → (∃ S : ℝ, ∀ j, φ (U j 0) ≤ S) →
        (∀ j n, U j (n + 1) ∈ moreauYosidaResolvent φ (τ j) (U j n)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j t ↦ U j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, hmτ₀⟩ := exists_pos_one_add_mul_pos lam
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀
    (h.moreauYosida_ne_bot hφ hbot hmτ₀ x₀) (Eventually.of_forall fun _ ↦ h.penalizedConvex) hx₀

/-- On a complete CAT(0) space, the `EVI_lam` domain of a lower semicontinuous `lam`-geodesically
convex energy that never takes the value `⊥` equals `closure {y | φ y ≠ ⊤}`. -/
theorem GeodesicallyConvex.eviDomain_eq_closure {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] [IsCATZeroSpace X] {lam : ℝ} {φ : X → EReal}
    (h : GeodesicallyConvex lam φ) (hφ : LowerSemicontinuous φ) (hbot : ∀ y, φ y ≠ ⊥) :
    eviDomain lam φ = closure {y | φ y ≠ ⊤} := by
  rcases Set.eq_empty_or_nonempty {y : X | φ y ≠ ⊤} with hemp | ⟨x₁, -⟩
  · exact Subset.antisymm (eviDomain_subset_closure.trans (by simp [hemp])) (by simp [hemp])
  obtain ⟨τ₀, hτ₀, hmτ₀⟩ := exists_pos_one_add_mul_pos lam
  exact eviDomain_eq_closure_of_penalizedConvex hφ hτ₀
    (h.moreauYosida_ne_bot hφ hbot hmτ₀ x₁) (Eventually.of_forall fun _ ↦ h.penalizedConvex)

end CurveConvexity

end TauCeti
