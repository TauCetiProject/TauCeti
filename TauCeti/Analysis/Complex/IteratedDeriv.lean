/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Iterated derivatives of holomorphic functions and series of one complex variable

This file records that every iterated derivative of a complex differentiable function `g : ℂ → E`
is again complex differentiable (`Differentiable.iteratedDeriv`, `DifferentiableOn.iteratedDeriv`),
that locally uniform convergence of holomorphic functions on an open set `U ⊆ ℂ` passes to every
iterated derivative (`TendstoLocallyUniformlyOn.iteratedDeriv`), and the resulting Weierstrass
M-test formulas for differentiating holomorphic series (`Complex.hasDerivAt_tsum_of_summable_norm`,
`Complex.hasSum_iteratedDeriv_of_summable_norm`). It also computes the norms of the real iterated
derivatives of the powers `z ^ m` (`TauCeti.Complex.norm_iteratedFDeriv_pow`).
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` is complex
differentiable. This is the iterated form of `Differentiable.deriv`. -/
theorem Differentiable.iteratedDeriv {g : ℂ → E} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k g) :=
  (hg.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` on an open set `U ⊆ ℂ`
is again complex differentiable on `U`. -/
theorem DifferentiableOn.iteratedDeriv {g : ℂ → E} {U : Set ℂ} (hg : DifferentiableOn ℂ g U)
    (hU : IsOpen U) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k g) U := by
  rw [iteratedDeriv_eq_iterate]
  exact ((hg.analyticOnNhd hU).iterated_deriv k).differentiableOn

/-- Locally uniform convergence of holomorphic functions on an open set `U ⊆ ℂ` implies locally
uniform convergence of every `k`-th iterated derivative to that of the limit. -/
theorem TendstoLocallyUniformlyOn.iteratedDeriv {ι : Type*} {φ : Filter ι} {F : ι → ℂ → E}
    {f : ℂ → E} {U : Set ℂ} (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => _root_.iteratedDeriv k (F n))
      (_root_.iteratedDeriv k f) φ U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    simp_rw [iteratedDeriv_succ]
    exact ih.deriv (hF.mono fun _ hn => hn.iteratedDeriv hU k) hU

namespace Complex

/-- If holomorphic functions `F i` on an open set `U ⊆ ℂ` satisfy a uniform summable norm bound
`‖F i w‖ ≤ u i`, then their sum has derivative `∑' i, deriv (F i) z` at every `z ∈ U`. -/
theorem hasDerivAt_tsum_of_summable_norm {ι : Type*} {F : ι → ℂ → E} {U : Set ℂ} {u : ι → ℝ}
    (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ i, ∀ w ∈ U, ‖F i w‖ ≤ u i) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => ∑' i, F i w) (∑' i, deriv (F i) z) z := by
  have hd := ((Complex.differentiableOn_tsum_of_summable_norm hu hF hU hF_le).differentiableAt
    (hU.mem_nhds hz)).hasDerivAt
  rwa [← (Complex.hasSum_deriv_of_summable_norm hu hF hU hF_le hz).tsum_eq] at hd

/-- If holomorphic functions `F i` on an open set `U ⊆ ℂ` satisfy a uniform summable norm bound
`‖F i w‖ ≤ u i`, then for every `k : ℕ` and `z ∈ U`, the `k`-th iterated derivatives
`iteratedDeriv k (F i) z` sum to `iteratedDeriv k (fun w => ∑' i, F i w) z`. -/
theorem hasSum_iteratedDeriv_of_summable_norm {ι : Type*} {F : ι → ℂ → E} {U : Set ℂ}
    {u : ι → ℝ} (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ i, ∀ w ∈ U, ‖F i w‖ ≤ u i) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasSum (fun i => iteratedDeriv k (F i) z) (iteratedDeriv k (fun w => ∑' i, F i w) z) := by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine ((hc.iteratedDeriv (Filter.Eventually.of_forall fun s =>
    DifferentiableOn.fun_sum fun i _ => hF i) hU k).tendsto_at hz).congr fun s => ?_
  exact iteratedDeriv_fun_sum fun i _ => ((hF i).analyticOnNhd hU z hz).contDiffAt

end Complex

namespace TauCeti.Complex

/-- The real iterated derivatives of `z ^ m` have the norms of the complex ones:
`‖D^k (z ^ m)‖ = m (m - 1) ⋯ (m - k + 1) ‖z‖ ^ (m - k)`. -/
theorem norm_iteratedFDeriv_pow (k m : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ m) z‖ = m.descFactorial k * ‖z‖ ^ (m - k) := by
  have h : ContDiffAt ℂ k (fun w : ℂ => w ^ m) z := by fun_prop
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_pow, norm_mul, norm_pow, Complex.norm_natCast]

end TauCeti.Complex
