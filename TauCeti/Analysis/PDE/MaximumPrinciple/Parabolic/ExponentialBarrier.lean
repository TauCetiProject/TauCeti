/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Topology.ContinuousOn.CompactDomination
public import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic

/-!
# Uniform decay for a moving smooth exponential barrier

For compact coefficient data, the glued profile `expNegInvGlue` admits one exponential decay
rate provided the squared-gradient coefficient is positive on its zero level. The rate is
uniform in the evaluation point and is used by expanding parabolic comparison barriers.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollaries 4.14–4.15.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

open Set Topology Filter Polynomial
open scoped ContDiff BigOperators
noncomputable section
namespace TauCeti
/-- Compact coefficient data admit a uniform decay constant when the gradient coefficient
is positive on the profile zero set. -/
public theorem exists_exponential_barrier_decay
    {X : Type u} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {q L G : X → ℝ} (hq : ContinuousOn q K) (hL : ContinuousOn L K)
    (hG : ContinuousOn G K) (hzero : ∀ x ∈ K, q x = 0 → 0 < G x) (b : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K,
      (b - L x) * deriv expNegInvGlue (q x) -
          G x * deriv (deriv expNegInvGlue) (q x) ≤
        A * expNegInvGlue (q x) := by
  let P : X → ℝ := fun x ↦ (b - L x) * q x ^ 2 -
    (1 - 2 * q x) * G x
  have hP : ContinuousOn P K := by
    have hcoef : ContinuousOn (fun x : X ↦ (1 : ℝ) - 2 * q x) K :=
      continuousOn_const.sub (continuousOn_const.mul hq)
    exact ((continuousOn_const.sub hL).mul (hq.pow 2)).sub
      (hcoef.mul hG)
  obtain ⟨A, hA, hAK⟩ := hK.exists_pos_forall_lt_mul hP (hq.pow 4)
    (fun x _ ↦ by
      dsimp only [Pi.pow_apply]
      positivity) (by
      intro x hx hqx
      have hqx0 : q x = 0 := (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hqx
      simpa [P, hqx0] using (neg_lt_zero.mpr (hzero x hx hqx0)))
  refine ⟨A, hA, ?_⟩
  intro x hx
  by_cases hqx : q x ≤ 0
  · have hz : expNegInvGlue (q x) = 0 := expNegInvGlue.zero_of_nonpos hqx
    have hdz : deriv expNegInvGlue (q x) = 0 := by simp [(expNegInvGlue.hasDerivAt _).deriv, hz]
    have hddz : deriv (deriv expNegInvGlue) (q x) = 0 := by
      simp [expNegInvGlue.deriv_deriv, hz]
    simp [hz, hdz, hddz]
  · have hqx' : 0 < q x := lt_of_not_ge hqx
    have hPineq : P x < A * q x ^ 4 := hAK x hx
    rw [(expNegInvGlue.hasDerivAt _).deriv, expNegInvGlue.deriv_deriv]
    have hψ : 0 < expNegInvGlue (q x) := expNegInvGlue.pos_of_pos hqx'
    have hq0 : q x ≠ 0 := ne_of_gt hqx'
    have hcoeff : (b - L x) * (q x)⁻¹ ^ 2 -
        G x * ((q x)⁻¹ ^ 4 - 2 * (q x)⁻¹ ^ 3) ≤ A := by
      apply (le_of_mul_le_mul_right ?_ (pow_pos hqx' 4))
      calc
        ((b - L x) * (q x)⁻¹ ^ 2 -
            G x * ((q x)⁻¹ ^ 4 - 2 * (q x)⁻¹ ^ 3)) * q x ^ 4 = P x := by
              field_simp [hq0]
              ring
        _ ≤ A * q x ^ 4 := hPineq.le
    calc
      _ = ((b - L x) * (q x)⁻¹ ^ 2 -
          G x * ((q x)⁻¹ ^ 4 - 2 * (q x)⁻¹ ^ 3)) * expNegInvGlue (q x) := by
            ring
      _ ≤ A * expNegInvGlue (q x) := mul_le_mul_of_nonneg_right hcoeff hψ.le


end TauCeti
