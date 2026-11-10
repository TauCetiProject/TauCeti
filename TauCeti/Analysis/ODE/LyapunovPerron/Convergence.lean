/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Local
public import TauCeti.Analysis.ODE.LyapunovPerron.DerivativePerturbation

/-!
# C¹ convergence of local invariant graphs

For a fixed exponential dichotomy, local stable and unstable graphs depend continuously in
C¹ on the nonlinear remainder. More precisely, suppose the remainders vanish at zero, share
a small Lipschitz bound on a common ball, and converge there uniformly together with their
derivatives. On every bounded parameter set whose solution bound stays strictly inside that
ball, the derivatives of the local graph maps converge uniformly in operator norm. The graph
values already converge uniformly by `ContinuousLinearMap.tendstoUniformly_localStableGraphMap`
and its unstable counterpart.

Only local differentiability is required: the radial cutoff used to construct the graphs need
not be differentiable at the boundary of the confinement ball. The strict solution bound keeps
all trajectories in the region where that cutoff is the identity. Uniform continuity of the
limiting remainder derivative converts convergence of trajectories into convergence of their
linearized coefficients; the variational perturbation estimate then controls graph derivatives.
The linear part and its splitting are fixed here, not varied with the remainder.

## References

* C. Chicone, *Ordinary Differential Equations with Applications*, second edition,
  Springer, 2006, §4.3 (dependence of invariant manifolds on the vector field).
* W. A. Coppel, *Dichotomies in Stability Theory*, Springer, 1978, Chapter 5
  (the Lyapunov--Perron construction).
-/

public section

open Filter Metric NormedSpace Set Topology
open scoped NNReal BoundedContinuousFunction

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {ι : Type*} {l : Filter ι} {A P : X →L[ℝ] X} {K α ε : ℝ≥0}
  {N : X → X} {F : ι → X → X} {N' : X → X →L[ℝ] X} {F' : ι → X → X →L[ℝ] X}
  {r ρ : ℝ} {U : Set X}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
    ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
    ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
  (hF : ∀ i, LipschitzOnWith ε (F i) (closedBall 0 r))
  (hsmall : 2 * K * (ε * 2) < α)

/-- Uniform convergence on the confinement ball gives uniform convergence, in the sup norm
over the whole forward half-line, of the cut-off Lyapunov--Perron solutions. This convergence
is uniform over all stable parameters. -/
theorem tendstoUniformly_lyapunovPerronSolution_comp_radialRetraction (hα : 0 < α)
    (hFN : TendstoUniformlyOn F N l (closedBall 0 r)) :
    TendstoUniformly
      (fun i ↦ lyapunovPerronSolution A P (F i ∘ TauCeti.radialRetraction r)
        hs hu hα ((hF i).comp_radialRetraction hr) hsmall)
      (lyapunovPerronSolution A P (N ∘ TauCeti.radialRetraction r)
        hs hu hα (hN.comp_radialRetraction hr) hsmall) l := by
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  let C : ℝ := (2 * K / α) / (1 - 2 * K * ((ε : ℝ) * 2) / α)
  have hC : 0 ≤ C := div_nonneg (by positivity)
    (sub_nonneg.2 ((div_le_one (show (0 : ℝ) < α from hα)).2 hsmallR.le))
  refine Metric.tendstoUniformly_iff.2 fun e he ↦ ?_
  have hd : 0 < e / (C + 1) := div_pos he (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hFN _ hd] with i hi ξ
  have hb := dist_lyapunovPerronSolution_le_of_norm_sub_le hs hu hα
    (hN.comp_radialRetraction hr) ((hF i).comp_radialRetraction hr) hsmall hsmall
    (fun z ↦ by simpa only [dist_eq_norm, Function.comp_apply] using
      (hi _ (TauCeti.radialRetraction_mem_closedBall hr z)).le) ξ
  have hCe : C * (e / (C + 1)) < e := by
    have := mul_lt_mul_of_pos_right (show C < C + 1 by linarith) hd
    simpa only [mul_div_cancel₀ e (show C + 1 ≠ 0 by positivity)] using this
  calc
    _ ≤ C * (e / (C + 1)) := by convert hb using 1; dsimp [C]; ring
    _ < e := hCe

/-- The cutoff has the original derivative along every uniformly confined trajectory. -/
private theorem exists_localGraph_derivative_data (hα : 0 < α)
    (hN0 : N 0 = 0) (hNd : ∀ z ∈ ball (0 : X) r, HasFDerivAt N (N' z) z)
    (hU : ∀ ξ ∈ U, ‖ξ‖ ≤ ρ)
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r) :
    ∃ δ > 0,
      (∀ z ∈ ball (0 : X) r,
        HasFDerivAt (N ∘ TauCeti.radialRetraction r) (N' z) z) ∧
      ∀ ξ ∈ U, ∀ t : ℝ≥0,
        ball (lyapunovPerronSolution A P (N ∘ TauCeti.radialRetraction r)
          hs hu hα (hN.comp_radialRetraction hr) hsmall ξ t) δ ⊆ ball 0 r := by
  let B : ℝ := K / (1 - 2 * K * ((ε : ℝ) * 2) / α)
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  have hB : 0 ≤ B := div_nonneg K.coe_nonneg
    (sub_nonneg.2 ((div_le_one (show (0 : ℝ) < α from hα)).2 hsmallR.le))
  refine ⟨r - B * ρ, sub_pos.2 hρ, fun z hz ↦ ?_, fun ξ hξ t ↦ ?_⟩
  · exact (hNd z hz).congr_of_eventuallyEq
      ((TauCeti.radialRetraction_eventuallyEq_id (mem_ball_zero_iff.1 hz)).fun_comp N)
  · apply ball_subset_ball'
    rw [dist_zero_right]
    have hb := norm_lyapunovPerronSolution_le_mul_norm hs hu hα
      (hN.comp_radialRetraction hr) hsmall (by simp [hN0]) ξ t
    have hbound := hb.trans (mul_le_mul_of_nonneg_left (hU ξ hξ) hB)
    simp only [NNReal.coe_mul, NNReal.coe_ofNat] at hbound
    dsimp only [B]
    linarith only [hbound]

/-- Uniform C¹ convergence of nonlinear remainders on a common confinement ball implies
uniform convergence of the local stable graph derivatives on any bounded parameter set with
a strict solution reserve. The same small Lipschitz bound is used for every remainder. -/
theorem tendstoUniformlyOn_fderiv_localStableGraphMap
    (hN0 : N 0 = 0) (hF0 : ∀ i, F i 0 = 0)
    (hNd : ∀ z ∈ ball (0 : X) r, HasFDerivAt N (N' z) z)
    (hFd : ∀ i z, z ∈ ball (0 : X) r → HasFDerivAt (F i) (F' i z) z)
    (hN' : UniformContinuousOn N' (ball (0 : X) r))
    (hF' : ∀ i, UniformContinuousOn (F' i) (ball (0 : X) r))
    (hFN : TendstoUniformlyOn F N l (closedBall 0 r))
    (hFN' : TendstoUniformlyOn F' N' l (ball (0 : X) r))
    (hU : ∀ ξ ∈ U, ‖ξ‖ ≤ ρ)
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r) :
    TendstoUniformlyOn
      (fun i ↦ fderiv ℝ (localStableGraphMap A P (F i) r hs hu hr (hF i) hsmall))
      (fderiv ℝ (localStableGraphMap A P N r hs hu hr hN hsmall)) l U := by
  have hα : 0 < α := lt_of_le_of_lt zero_le hsmall
  have hαR : (0 : ℝ) < α := hα
  have hsmallR : 2 * (K : ℝ) * ((ε : ℝ) * 2) < α := by exact_mod_cast hsmall
  have hq : 0 < 1 - 2 * (K : ℝ) * ((ε : ℝ) * 2) / α :=
    sub_pos.2 ((div_lt_one hαR).2 hsmallR)
  let B : ℝ := K / (1 - 2 * K * ((ε : ℝ) * 2) / α)
  let D : ℝ := (2 * K / α * B) / (1 - 2 * K * ((ε : ℝ) * 2) / α)
  have hB : 0 ≤ B := div_nonneg K.coe_nonneg hq.le
  have hD : 0 ≤ D := div_nonneg (mul_nonneg (by positivity) hB) hq.le
  let Nc := N ∘ TauCeti.radialRetraction r
  let Fc := fun i ↦ F i ∘ TauCeti.radialRetraction r
  have hNc : LipschitzWith (ε * 2) Nc := hN.comp_radialRetraction hr
  have hFc (i) : LipschitzWith (ε * 2) (Fc i) := (hF i).comp_radialRetraction hr
  let γ := lyapunovPerronSolution A P Nc hs hu hα hNc hsmall
  let γi := fun i ↦ lyapunovPerronSolution A P (Fc i) hs hu hα (hFc i) hsmall
  -- The strict solution bound makes the nonsmooth part of the cutoff invisible.
  obtain ⟨δ, hδ, hNcd, hγN⟩ :=
    exists_localGraph_derivative_data hs hu hr hN hsmall hα hN0 hNd hU hρ
  have hdata (i) := exists_localGraph_derivative_data hs hu hr (hF i) hsmall hα
    (hF0 i) (hFd i) hU hρ
  choose δi hδi hFcd hγF using hdata
  refine Metric.tendstoUniformlyOn_iff.2 fun e he ↦ ?_
  let d := e / (2 * (D + 1))
  have hd : 0 < d := div_pos he (by positivity)
  obtain ⟨η, hη, hηd⟩ := Metric.uniformContinuousOn_iff.1 hN' d hd
  -- Uniform convergence of trajectories and of remainder derivatives controls every
  -- linearized coefficient, simultaneously in the parameter and time.
  have hsolutions := tendstoUniformly_lyapunovPerronSolution_comp_radialRetraction
    hs hu hr hN hF hsmall hα hFN
  filter_upwards [Metric.tendstoUniformly_iff.1 hsolutions η hη,
    Metric.tendstoUniformlyOn_iff.1 hFN' _ hd] with i hi hi' ξ hξ
  have hdist (t : ℝ≥0) : dist (γ ξ t) (γi i ξ t) < η :=
    (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt (hi ξ)
  have hderiv (t : ℝ≥0) : ‖N' (γ ξ t) - F' i (γi i ξ t)‖ ≤ 2 * d := by
    have hn := hγN ξ hξ t (mem_ball_self hδ)
    have hf := hγF i ξ hξ t (mem_ball_self (hδi i))
    have hnear := hηd _ hn _ hf (hdist t)
    have happrox := hi' _ hf
    rw [← dist_eq_norm]
    exact (dist_triangle _ (N' (γi i ξ t)) _).trans (by linarith)
  -- The variational estimate turns coefficient control into operator-norm control.
  have hb := norm_fderiv_lyapunovPerronGraphMap_sub_le hs hu hα hNc (hFc i)
    hsmall hsmall hNcd hN' (hFcd i) (hF' i) hδ (hδi i)
    (hγN ξ hξ) (hγF i ξ hξ) hderiv
  have hDe : D * (2 * d) < e := by
    have := mul_lt_mul_of_pos_right (show D < D + 1 by linarith)
      (mul_pos (by norm_num : (0 : ℝ) < 2) hd)
    have heq : (D + 1) * (2 * d) = e := by
      dsimp [d]
      field_simp
    linarith
  calc
    _ = ‖fderiv ℝ (lyapunovPerronGraphMap A P Nc hs hu hα hNc hsmall) ξ -
        fderiv ℝ (lyapunovPerronGraphMap A P (Fc i) hs hu hα (hFc i) hsmall) ξ‖ := by
      rw [dist_eq_norm, localStableGraphMap_def A P N r hs hu hr hN hsmall hα,
        localStableGraphMap_def A P (F i) r hs hu hr (hF i) hsmall hα]
    _ ≤ D * (2 * d) := by convert hb using 1; dsimp [D, B]; ring
    _ < e := hDe

/-- Under the same local C¹ convergence and confinement hypotheses, the derivatives of the
local unstable graph maps converge uniformly on the bounded parameter set. -/
theorem tendstoUniformlyOn_fderiv_localUnstableGraphMap
    (hN0 : N 0 = 0) (hF0 : ∀ i, F i 0 = 0)
    (hNd : ∀ z ∈ ball (0 : X) r, HasFDerivAt N (N' z) z)
    (hFd : ∀ i z, z ∈ ball (0 : X) r → HasFDerivAt (F i) (F' i z) z)
    (hN' : UniformContinuousOn N' (ball (0 : X) r))
    (hF' : ∀ i, UniformContinuousOn (F' i) (ball (0 : X) r))
    (hFN : TendstoUniformlyOn F N l (closedBall 0 r))
    (hFN' : TendstoUniformlyOn F' N' l (ball (0 : X) r))
    (hU : ∀ ξ ∈ U, ‖ξ‖ ≤ ρ)
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r) :
    TendstoUniformlyOn
      (fun i ↦ fderiv ℝ (localUnstableGraphMap A P (F i) r hs hu hr (hF i) hsmall))
      (fderiv ℝ (localUnstableGraphMap A P N r hs hu hr hN hsmall)) l U := by
  have hs' (t : ℝ) (ht : 0 ≤ t) (v : X) :
      ‖exp (t • (-A)) ((ContinuousLinearMap.id ℝ X - P) v)‖ ≤
        K * Real.exp (-α * t) * ‖v‖ := by
    simpa only [sub_apply, id_apply, smul_neg, neg_smul, neg_neg, mul_neg, neg_mul]
      using hu (-t) (neg_nonpos.mpr ht) v
  have hu' (t : ℝ) (ht : t ≤ 0) (v : X) :
      ‖exp (t • (-A)) (v - (ContinuousLinearMap.id ℝ X - P) v)‖ ≤
        K * Real.exp (α * t) * ‖v‖ := by
    simpa only [sub_apply, id_apply, sub_sub_cancel, smul_neg, neg_smul,
      neg_neg, mul_neg, neg_mul] using hs (-t) (neg_nonneg.mpr ht) v
  simp_rw [localUnstableGraphMap_def A P _ r hs hu hr _ hsmall hs' hu']
  exact tendstoUniformlyOn_fderiv_localStableGraphMap hs' hu' hr hN.neg
    (fun i ↦ (hF i).neg) hsmall (by simpa using congrArg Neg.neg hN0)
    (fun i ↦ by simpa using congrArg Neg.neg (hF0 i))
    (fun z hz ↦ (hNd z hz).neg) (fun i z hz ↦ (hFd i z hz).neg)
    (uniformContinuous_neg.comp_uniformContinuousOn hN')
    (fun i ↦ uniformContinuous_neg.comp_uniformContinuousOn (hF' i)) hFN.neg hFN'.neg hU hρ

end ContinuousLinearMap
