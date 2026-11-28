/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import TauCeti.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import TauCeti.Analysis.Calculus.MeanValue.Exp
import TauCeti.Analysis.Calculus.Taylor.Basic
import TauCeti.Analysis.LaplaceTransform.Watson
import TauCeti.MeasureTheory.Integral.Exp.Complex

/-!
# Laplace integrals by integration by parts

Let `q : ℝ → ℂ` be `C^∞` within `[0, ∞)` at `0` (for instance `C^∞` on `[0, ε)` for some
`ε > 0`), and let `t ↦ e^{-σt} q(t)` be integrable on `(0, ∞)` for some real `σ`. Then

`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ q^{(s)}(0) x^{-s-1}`   as `x → +∞`

(DLMF 2.3.1–2.3.2), with one-sided derivatives at `0`. This is Watson's lemma
`Asymptotics.hasAsymptoticExpansion_laplace` with the exponents `α_s = s + 1` and the Taylor
coefficients `c_s = q^{(s)}(0) / s!`, since `Γ(s + 1) = s!`.

If `q` is `C^n` on `[0, ∞)` and `‖q^{(n)}(t)‖ ≤ M e^{σt}` for `t > 0`, then `n` integrations by
parts give, for complex `s` with `Re s > max(0, σ)`, the error bound

`‖∫₀^∞ e^{-st} q(t) dt - ∑_{k<n} q^{(k)}(0) s^{-k-1}‖ ≤ M / (|s|ⁿ (Re s - σ))`

(DLMF 2.3.3, where `s = x` is real). DLMF takes `M = |q^{(n)}(0)|`, `q^{(n)}(0) ≠ 0`, and for
`σ` the number `σ_n = sup_{t>0} t⁻¹ log |q^{(n)}(t) / q^{(n)}(0)|`, the least `σ` for which the
hypothesis holds with that `M`; it also assumes `q` to be `C^∞`.

## Main results

* `TauCeti.integral_cexp_neg_mul_smul_eq_sum_add`: `n` integrations by parts in a Laplace
  integral, `L[q](s) = ∑_{k<n} s^{-k-1} q^{(k)}(0) + s^{-n} L[q^{(n)}](s)`, when the Laplace
  integrals of `q, q', …, q^{(n)}` converge at `s ≠ 0`.
* `Asymptotics.hasAsymptoticExpansion_laplace_of_contDiffWithinAt`: the expansion (DLMF 2.3.2).
* `Asymptotics.norm_integral_cexp_neg_mul_sub_sum_le`: the error bound (DLMF 2.3.3).

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/AsymptoticApproximations/Integrals/Parts.lean`
(`laplace_hasAsymptoticExpansion_of_contDiffOn`, `laplace_error_bound`), with the Laplace
integral identities of `DLMF/AlgebraicAnalytic/Transforms/Laplace.lean`
(`laplaceTransform_iteratedDeriv`). Here the integrations by parts use `TauCeti.hasLaplace_deriv`.

## References

* DLMF §2.3(i), <https://dlmf.nist.gov/2.3.i>.
-/

public section

noncomputable section

open MeasureTheory Set Filter Finset Complex
open scoped Topology ContDiff Nat

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Repeated integration by parts in a Laplace integral.** Let `q` be `C^n` on `[0, ∞)`, let
`s ≠ 0`, and let the Laplace integrands `t ↦ e^{-st} q^{(k)}(t)` be integrable on `(0, ∞)` for
every `k ≤ n` (derivatives within `[0, ∞)`). Then
`∫₀^∞ e^{-st} q(t) dt = ∑_{k<n} s^{-k-1} q^{(k)}(0) + s^{-n} ∫₀^∞ e^{-st} q^{(n)}(t) dt`. -/
theorem integral_cexp_neg_mul_smul_eq_sum_add {q : ℝ → E} {s : ℂ} {n : ℕ} (hs : s ≠ 0)
    (hq : ContDiffOn ℝ n q (Ici 0))
    (hint : ∀ k ≤ n, Integrable (fun t : ℝ => cexp (-s * t) • iteratedDerivWithin k q (Ici 0) t)
      (volume.restrict (Ioi 0))) :
    ∫ t in Ioi (0 : ℝ), cexp (-s * t) • q t =
      ∑ k ∈ range n, (s ^ (k + 1))⁻¹ • iteratedDerivWithin k q (Ici 0) 0 +
        (s ^ n)⁻¹ • ∫ t in Ioi (0 : ℝ), cexp (-s * t) • iteratedDerivWithin n q (Ici 0) t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : WithTop ℕ∞) < (n + 1 : ℕ) := mod_cast n.lt_succ_self
    rw [ih (hq.of_le hn.le) fun k hk => hint k (by omega)]
    -- one integration by parts: `L[q^{(n+1)}](s) = s L[q^{(n)}](s) - q^{(n)}(0)`
    have hL := hasLaplace_deriv
      ((hq.continuousOn_iteratedDerivWithin hn.le (uniqueDiffOn_Ici 0)) 0 self_mem_Ici)
      (fun t (ht : 0 < t) => hq.hasDerivAt_iteratedDerivWithin hn (Ici_mem_nhds ht))
      (hint n (by omega)).hasLaplace (hint (n + 1) le_rfl)
    have hs' : (s ^ (n + 1))⁻¹ * s = (s ^ n)⁻¹ := by
      rw [pow_succ, mul_inv, inv_mul_cancel_right₀ hs]
    rw [hL.integral_eq, smul_sub, smul_smul, hs', sum_range_succ]
    abel

end TauCeti

namespace Asymptotics

open TauCeti

/-- **Laplace integrals by integration by parts** (DLMF 2.3.1–2.3.2). Let `q : ℝ → ℂ` be `C^∞`
within `[0, ∞)` at `0`, and let `t ↦ e^{-σt} q(t)` be integrable on `(0, ∞)` for some real `σ`.
Then `∫₀^∞ e^{-xt} q(t) dt ∼ ∑ q^{(s)}(0) x^{-s-1}` as `x → +∞`, where `q^{(s)}(0)` is the `s`th
derivative of `q` at `0` within `[0, ∞)`, in the sense of `HasAsymptoticExpansion`: for every `N`
the remainder after `N` terms is `O(x^{-N-1})`. The hypothesis holds when `q` is `C^∞` on
`[0, ε)` for some `ε > 0`. -/
theorem hasAsymptoticExpansion_laplace_of_contDiffWithinAt {q : ℝ → ℂ} {σ : ℝ}
    (hq : ContDiffWithinAt ℝ ∞ q (Ici 0) 0)
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0)) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (x : ℂ) ^ (-((s : ℂ) + 1)))
      (fun s => iteratedDerivWithin s q (Ici 0) 0)
      fun x : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t := by
  set d : ℕ → ℂ := fun s => iteratedDerivWithin s q (Ici 0) 0
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ici 0] 0 := nhdsWithin_mono _ Ioi_subset_Ici_self
  -- Taylor's theorem: the remainder after `N` terms of the Taylor series is `O(t^N)` at `0+`
  have hT (N : ℕ) : (fun t : ℝ => q t - ∑ s ∈ range N, d s / s ! * (t : ℂ) ^ s)
      =O[𝓝[>] 0] fun t => t ^ N := by
    rcases N with _ | N
    · simpa using (hq.continuousWithinAt.tendsto.mono_left hle).isBigO_one ℝ
    refine ((taylor_isBigO (convex_Ici 0) self_mem_Ici (n := N)
      (hq.of_le (mod_cast le_top))).mono hle).congr (fun t => ?_) fun t => by simp
    simp only [taylor_within_apply, d, sub_zero, Complex.real_smul]
    push_cast
    exact congrArg (q t - ·) (sum_congr rfl fun s _ => by ring)
  refine (hasAsymptoticExpansion_laplace (α := fun s => (s : ℂ) + 1) (c := fun s => d s / s !)
    (fun s => by simp only [add_re, natCast_re, one_re]; positivity) hint fun N => ?_).congr_coeff
    fun s => ?_
  · simpa [Real.rpow_natCast, ← cpow_natCast] using hT N
  · have hs : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 s.factorial_ne_zero
    rw [Gamma_nat_eq_factorial, mul_div_cancel₀ _ hs]

/-- **The error bound of integration by parts** (DLMF 2.3.3). Let `q` be `C^n` on `[0, ∞)` with
`‖q^{(n)}(t)‖ ≤ M e^{σt}` for `t > 0` (derivatives within `[0, ∞)`). Then for `Re s > 0` and
`Re s > σ` the remainder after `n` terms of the expansion of
`Asymptotics.hasAsymptoticExpansion_laplace_of_contDiffWithinAt` is bounded by
`‖∫₀^∞ e^{-st} q(t) dt - ∑_{k<n} s^{-k-1} q^{(k)}(0)‖ ≤ M / (|s|ⁿ (Re s - σ))`. DLMF's form is the
case of real `s = x`, with `M = ‖q^{(n)}(0)‖` and `σ` the least admissible rate `σ_n`. -/
theorem norm_integral_cexp_neg_mul_sub_sum_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {q : ℝ → E} {n : ℕ} {σ M : ℝ} {s : ℂ}
    (hq : ContDiffOn ℝ n q (Ici 0))
    (hb : ∀ t ∈ Ioi (0 : ℝ), ‖iteratedDerivWithin n q (Ici 0) t‖ ≤ M * Real.exp (σ * t))
    (hs : 0 < s.re) (hσs : σ < s.re) :
    ‖(∫ t in Ioi (0 : ℝ), cexp (-s * t) • q t) -
        ∑ k ∈ range n, (s ^ (k + 1))⁻¹ • iteratedDerivWithin k q (Ici 0) 0‖ ≤
      M / (‖s‖ ^ n * (s.re - σ)) := by
  -- by continuity of `q^{(n)}` on `[0, ∞)`, the bound also holds at `t = 0`
  have hb₀ : ∀ t ∈ Ici (0 : ℝ), ‖iteratedDerivWithin n q (Ici 0) t‖ ≤ M * Real.exp (σ * t) := by
    intro t ht
    rcases (mem_Ici.1 ht).eq_or_lt with rfl | ht
    · exact ContinuousWithinAt.closure_le (by simp)
        (((hq.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0)) 0
          self_mem_Ici).mono Ioi_subset_Ici_self).norm
        (by fun_prop : Continuous fun t : ℝ => M * Real.exp (σ * t)).continuousWithinAt hb
    · exact hb t ht
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hb₀ 0 self_mem_Ici)
  -- a common rate `α` with `max σ 0 < α < Re s` for the lower derivatives
  obtain ⟨α, hσα, hα, hαs⟩ : ∃ α, σ ≤ α ∧ 0 < α ∧ α < s.re :=
    ⟨(max σ 0 + s.re) / 2, by linarith [le_max_left σ 0, le_max_right σ 0], by positivity,
      by linarith [max_lt hσs hs]⟩
  have hb' : ∀ t ∈ Ici (0 : ℝ), ‖iteratedDerivWithin n q (Ici 0) t‖ ≤
      M * Real.exp (α * (t - 0)) := fun t (ht : 0 ≤ t) => (hb₀ t ht).trans (by
        rw [sub_zero]
        gcongr)
  have hint (k : ℕ) (hk : k ≤ n) : Integrable
      (fun t : ℝ => cexp (-s * t) • iteratedDerivWithin k q (Ici 0) t)
      (volume.restrict (Ioi 0)) := by
    obtain ⟨C, hC⟩ := hq.exists_norm_iteratedDerivWithin_le_mul_exp hα hb' hk
    exact integrable_cexp_neg_mul_smul_of_norm_le_mul_exp
      (((hq.continuousOn_iteratedDerivWithin (mod_cast hk) (uniqueDiffOn_Ici 0)).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) => by
        simpa using hC t ht.le) hαs
  have hL := norm_integral_cexp_neg_mul_smul_le_of_norm_le_mul_exp (c := 0)
    (ae_restrict_of_forall_mem measurableSet_Ioi hb) hσs
  rw [mul_zero, Real.exp_zero, mul_one] at hL
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hs
  rw [integral_cexp_neg_mul_smul_eq_sum_add hs₀ hq hint, add_sub_cancel_left, norm_smul, norm_inv,
    norm_pow]
  calc (‖s‖ ^ n)⁻¹ * ‖∫ t in Ioi (0 : ℝ), cexp (-s * t) • iteratedDerivWithin n q (Ici 0) t‖
      ≤ (‖s‖ ^ n)⁻¹ * (M / (s.re - σ)) := by gcongr
    _ = M / (‖s‖ ^ n * (s.re - σ)) := by
        rw [inv_mul_eq_div, div_div, mul_comm (s.re - σ)]

end Asymptotics
