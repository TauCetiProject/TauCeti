/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import TauCeti.Analysis.ODE.LyapunovPerron.Local
public import TauCeti.Analysis.ODE.LyapunovPerron.DerivativePerturbation

/-!
# C¹ convergence of local invariant graphs

For a fixed exponential dichotomy, local stable and unstable graphs depend continuously in
C¹ on the nonlinear remainder. More precisely, suppose the approximating remainders vanish at
zero, have uniformly continuous derivatives on the open interior of a common ball, and converge
uniformly together with their derivatives (values on the closed ball, derivatives on the open
ball). Suppose also that the approximants and limit share a small Lipschitz bound on that ball.
On every bounded parameter set whose solution bound stays strictly inside that ball, the
derivatives of the local graph maps converge uniformly in operator norm.
The graph values already converge uniformly by
`ContinuousLinearMap.tendstoUniformly_localStableGraphMap`
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
  refine ⟨r - (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ,
    sub_pos.2 hρ, fun z hz ↦ ?_, fun ξ hξ t ↦ ?_⟩
  · exact (hNd z hz).congr_of_eventuallyEq
      ((TauCeti.radialRetraction_eventuallyEq_id (mem_ball_zero_iff.1 hz)).fun_comp N)
  · exact ball_lyapunovPerronSolution_comp_radialRetraction_subset
      hs hu hr hN hsmall hα hN0 (hU ξ hξ) t

/-- Suppose the approximating nonlinear remainders vanish at zero and are differentiable on
the open confinement ball with uniformly continuous derivatives. Suppose the approximants and
limit share a small Lipschitz bound on the closed ball. Uniform convergence of the remainders
on the closed ball and of their derivatives on the open ball implies uniform convergence of
the local stable graph derivatives on any bounded parameter set with a strict solution reserve.
For a nontrivial filter, the corresponding regularity and vanishing of the limit follow from
these convergence hypotheses. -/
theorem tendstoUniformlyOn_fderiv_localStableGraphMap
    (hF0 : ∀ i, F i 0 = 0)
    (hFd : ∀ i z, z ∈ ball (0 : X) r → HasFDerivAt (F i) (F' i z) z)
    (hF' : ∀ i, UniformContinuousOn (F' i) (ball (0 : X) r))
    (hFN : TendstoUniformlyOn F N l (closedBall 0 r))
    (hFN' : TendstoUniformlyOn F' N' l (ball (0 : X) r))
    (hU : ∀ ξ ∈ U, ‖ξ‖ ≤ ρ)
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r) :
    TendstoUniformlyOn
      (fun i ↦ fderiv ℝ (localStableGraphMap A P (F i) r hs hu hr (hF i) hsmall))
      (fderiv ℝ (localStableGraphMap A P N r hs hu hr hN hsmall)) l U := by
  rcases l.eq_or_neBot with rfl | hl
  · simp [TendstoUniformlyOn]
  have hN0 : N 0 = 0 := by
    have hzero : Tendsto (fun _ : ι ↦ (0 : X)) l (𝓝 (N 0)) := by
      simpa only [hF0] using hFN.tendsto_at (mem_closedBall_self hr)
    exact tendsto_nhds_unique hzero tendsto_const_nhds
  have hNd : ∀ z ∈ ball (0 : X) r, HasFDerivAt N (N' z) z :=
    fun z hz ↦ hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hFN' hFd
      (fun x hx ↦ hFN.tendsto_at (ball_subset_closedBall hx)) hz
  have hN' := hFN'.uniformContinuousOn (Eventually.frequently (Eventually.of_forall hF'))
  have hα : 0 < α := lt_of_le_of_lt zero_le hsmall
  let B : ℝ := K / (1 - 2 * K * ((ε : ℝ) * 2) / α)
  let D : ℝ := (2 * K / α * B) / (1 - 2 * K * ((ε : ℝ) * 2) / α)
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
  obtain ⟨d, hd, hDe⟩ := exists_pos_mul_lt he (2 * D)
  obtain ⟨η, hη, hηd⟩ := Metric.uniformContinuousOn_iff.1 hN' d hd
  -- Uniform convergence of trajectories and of remainder derivatives controls every
  -- linearized coefficient, simultaneously in the parameter and time.
  have hsolutions := tendstoUniformly_lyapunovPerronSolution_comp_radialRetraction
    hs hu hr hN hF hsmall (fun _ ↦ hsmall) hα hFN
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
  calc
    _ = ‖fderiv ℝ (lyapunovPerronGraphMap A P Nc hs hu hα hNc hsmall) ξ -
        fderiv ℝ (lyapunovPerronGraphMap A P (Fc i) hs hu hα (hFc i) hsmall) ξ‖ := by
      rw [dist_eq_norm, localStableGraphMap_def A P N r hs hu hr hN hsmall hα,
        localStableGraphMap_def A P (F i) r hs hu hr (hF i) hsmall hα]
    _ ≤ D * (2 * d) := by convert hb using 1; dsimp [D, B]; ring
    _ < e := by simpa only [mul_left_comm, mul_assoc] using hDe

/-- Under the same local C¹ convergence and confinement hypotheses, the derivatives of the
local unstable graph maps converge uniformly on the bounded parameter set. -/
theorem tendstoUniformlyOn_fderiv_localUnstableGraphMap
    (hF0 : ∀ i, F i 0 = 0)
    (hFd : ∀ i z, z ∈ ball (0 : X) r → HasFDerivAt (F i) (F' i z) z)
    (hF' : ∀ i, UniformContinuousOn (F' i) (ball (0 : X) r))
    (hFN : TendstoUniformlyOn F N l (closedBall 0 r))
    (hFN' : TendstoUniformlyOn F' N' l (ball (0 : X) r))
    (hU : ∀ ξ ∈ U, ‖ξ‖ ≤ ρ)
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ < r) :
    TendstoUniformlyOn
      (fun i ↦ fderiv ℝ (localUnstableGraphMap A P (F i) r hs hu hr (hF i) hsmall))
      (fderiv ℝ (localUnstableGraphMap A P N r hs hu hr hN hsmall)) l U := by
  simp_rw [localUnstableGraphMap_def A P _ r hs hu hr _ hsmall]
  exact tendstoUniformlyOn_fderiv_localStableGraphMap
    (norm_exp_smul_neg_id_sub_apply_le A P hu)
    (norm_exp_smul_neg_sub_id_sub_apply_le A P hs) hr hN.neg
    (fun i ↦ (hF i).neg) hsmall
    (fun i ↦ by simpa using congrArg Neg.neg (hF0 i))
    (fun i z hz ↦ (hFd i z hz).neg)
    (fun i ↦ uniformContinuous_neg.comp_uniformContinuousOn (hF' i)) hFN.neg hFN'.neg hU hρ

end ContinuousLinearMap
