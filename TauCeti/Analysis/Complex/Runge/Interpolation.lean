/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Analytic.HermiteInterpolation
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Complex.Runge.Rational.Basic

/-!
# Runge approximation with finite-jet interpolation

Let `K` be a compact set filled in an arbitrary subset `Ω ⊆ ℂ` (without requiring `Ω` to be open),
let `f : ℂ → ℂ` be holomorphic on an open neighbourhood `U` of `K`, and let `S ⊆ Ω` be a finite
set with orders `m : ℂ → ℕ`. Every `ε > 0` admits a function `g` holomorphic on `Ω` satisfying
`‖f z - g z‖ < ε` on `K` and matching the finite jets `iteratedDeriv k g a = iteratedDeriv k f a`
for all `a ∈ S` and `k < m a`
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq`).

The proof factors `f - P = (∏ a ∈ S, (z - a) ^ m a) * q` via
`AnalyticOnNhd.exists_hermite_quotient`, approximates the analytic quotient `q` on `K` using
rational Runge approximation (`IsCompact.exists_rational_norm_sub_lt`), and verifies jet vanishing
for the remainder via `TauCeti.iteratedDeriv_prod_pow_sub_smul_eq_zero`.

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq`: Runge
  approximation matching prescribed finite jets at finitely many points of `Ω`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3 / §2.7.
-/

public section

open Set

namespace TauCeti

/-- **Runge approximation with finite-jet interpolation.** Let `K` be a compact set filled in
`Ω ⊆ ℂ` (without requiring `Ω` to be open), let `f : ℂ → ℂ` be holomorphic on an open neighbourhood
`U` of `K`, and let `S ⊆ Ω` be a finite set with orders `m : ℂ → ℕ`. For every `ε > 0` there is a
function `g : ℂ → ℂ` holomorphic on `Ω` such that `‖f z - g z‖ < ε` on `K` and
`iteratedDeriv k g a = iteratedDeriv k f a` for all `a ∈ S` and `k < m a`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq
    {K Ω U : Set ℂ} (hfill : IsFilledIn K Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (S : Finset ℂ) (hSΩ : (S : Set ℂ) ⊆ Ω) (m : ℂ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖f z - g z‖ < ε) ∧
      ∀ a ∈ S, ∀ k < m a, iteratedDeriv k g a = iteratedDeriv k f a := by
  obtain ⟨P, U', q, hU', hKU', hq_an, hq_eq, hP⟩ :=
    ((hf.analyticOnNhd hU).mono hKU).exists_hermite_quotient S m
  set Q : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (z - a) ^ m a
  have hQ_diff : Differentiable ℂ Q := by fun_prop
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image hQ_diff.continuous.norm.continuousOn
  set M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  obtain ⟨p_r, q_r, -, hqrΩ, hqr⟩ := hK.exists_rational_norm_sub_lt hU' hKU'
    (fun _ hx ↦ hfill.compl_inter_connectedComponentIn_nonempty hKΩ hx) hq_an.differentiableOn
    (ε := ε / (M + 1)) (by positivity)
  set r : ℂ → ℂ := fun z ↦ p_r.eval z / q_r.eval z
  set W : Set ℂ := {z : ℂ | q_r.eval z ≠ 0}
  have hW_open : IsOpen W := isOpen_ne_fun q_r.differentiable.continuous continuous_const
  have hΩW : Ω ⊆ W := fun z hz h0 ↦ (hqrΩ z h0).1 hz
  have hrW : DifferentiableOn ℂ r W :=
    p_r.differentiable.differentiableOn.div q_r.differentiable.differentiableOn fun _ hz ↦ hz
  refine ⟨fun z ↦ P.eval z + Q z * r z,
    P.differentiable.differentiableOn.add (hQ_diff.differentiableOn.mul (hrW.mono hΩW)),
    fun z hz ↦ ?_, fun a ha k hk ↦ ?_⟩
  · have hfg : f z - (P.eval z + Q z * r z) = Q z * (q z - r z) := by
      linear_combination hq_eq z (hKU' hz)
    have hQz : ‖Q z‖ ≤ M := (hM₀ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
    rw [hfg, norm_mul]
    calc ‖Q z‖ * ‖q z - r z‖ ≤ M * (ε / (M + 1)) :=
          mul_le_mul hQz (hqr z hz).le (norm_nonneg _) hM0
      _ = (M / (M + 1)) * ε := by ring
      _ < 1 * ε := mul_lt_mul_of_pos_right ((div_lt_one (by positivity)).mpr (lt_add_one M)) hε
      _ = ε := one_mul ε
  · have hra : AnalyticAt ℂ r a := hrW.analyticAt (hW_open.mem_nhds (hΩW (hSΩ ha)))
    have hvan : iteratedDeriv k (fun z ↦ Q z * r z) a = 0 := by
      simpa only [smul_eq_mul] using
        iteratedDeriv_prod_pow_sub_smul_eq_zero S m ha hra.contDiffAt hk
    rw [iteratedDeriv_fun_add (P.differentiable.analyticAt a).contDiffAt
      ((hQ_diff.analyticAt a).fun_mul hra).contDiffAt, hvan, add_zero, hP a ha k hk]

end TauCeti
