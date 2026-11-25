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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import TauCeti.Analysis.Calculus.MeanValue.Exp
import TauCeti.Analysis.Calculus.Taylor.Basic
import TauCeti.Analysis.LaplaceTransform.Watson

/-!
# Laplace integrals by integration by parts

Let `q : ℝ → ℂ` be `C^∞` on `[0, ε)` for some `ε > 0`, and let `t ↦ e^{-σt} q(t)` be integrable
on `(0, ∞)` for some real `σ`. Then

`∫₀^∞ e^{-xt} q(t) dt ∼ ∑ q^{(s)}(0) x^{-s-1}`   as `x → +∞`

(DLMF 2.3.1–2.3.2), with one-sided derivatives at `0`. This is Watson's lemma
`Asymptotics.hasAsymptoticExpansion_laplace` with the exponents `α_s = s + 1` and the Taylor
coefficients `c_s = q^{(s)}(0) / s!`, since `Γ(s + 1) = s!`.

If `q` is `C^n` on `[0, ∞)` and `‖q^{(n)}(t)‖ ≤ M e^{σt}` for `t ≥ 0`, then `n` integrations by
parts give, for `x > max(0, σ)`, the error bound

`‖∫₀^∞ e^{-xt} q(t) dt - ∑_{s<n} q^{(s)}(0) x^{-s-1}‖ ≤ M / (xⁿ (x - σ))`

(DLMF 2.3.3). DLMF takes `M = |q^{(n)}(0)|`, `q^{(n)}(0) ≠ 0`, and for `σ` the number
`σ_n = sup_{t>0} t⁻¹ log |q^{(n)}(t) / q^{(n)}(0)|`, the least `σ` for which the hypothesis
holds with that `M`; it also assumes `q` to be `C^∞`.

## Main results

* `TauCeti.integral_cexp_neg_mul_smul_eq_sum_add`: `n` integrations by parts in a Laplace
  integral, `L[q](s) = ∑_{k<n} s^{-k-1} q^{(k)}(0) + s^{-n} L[q^{(n)}](s)`, when the Laplace
  integrals of `q, q', …, q^{(n)}` converge at `s ≠ 0`.
* `TauCeti.integrable_cexp_neg_mul_smul_of_norm_le_mul_exp`,
  `TauCeti.norm_integral_cexp_neg_mul_smul_le_of_norm_le_mul_exp`: for `‖f(t)‖ ≤ M e^{σt}` and
  `Re s > σ` the Laplace integral of `f` converges and has norm at most `M / (Re s - σ)`.
* `Asymptotics.hasAsymptoticExpansion_laplace_of_contDiffOn`: the expansion (DLMF 2.3.2).
* `Asymptotics.norm_integral_cexp_neg_mul_sub_sum_le`: the error bound (DLMF 2.3.3).

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/AsymptoticApproximations/Integrals/Parts.lean`
(`laplace_hasAsymptoticExpansion_of_contDiffOn`, `laplace_error_bound`), with the Laplace
integral identities of `DLMF/AlgebraicAnalytic/Transforms/Laplace.lean`
(`laplaceTransform_iteratedDeriv`, `norm_laplaceTransform_le`). Here the integrations by parts
are `TauCeti.hasLaplace_deriv`.

## References

* DLMF §2.3(i), <https://dlmf.nist.gov/2.3.i>.
-/

public section

noncomputable section

open MeasureTheory Set Filter Finset Complex
open scoped Topology ContDiff Nat

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- At a point `t` with `‖f(t)‖ ≤ M e^{σt}`, the Laplace integrand has
`‖e^{-st} f(t)‖ ≤ M e^{-(Re s - σ)t}`. -/
theorem norm_cexp_neg_mul_smul_le_mul_exp {f : ℝ → E} {s : ℂ} {σ M t : ℝ}
    (h : ‖f t‖ ≤ M * Real.exp (σ * t)) :
    ‖cexp (-s * t) • f t‖ ≤ M * Real.exp (-(s.re - σ) * t) := by
  rw [norm_smul, Complex.norm_exp, re_mul_ofReal, neg_re]
  calc Real.exp (-s.re * t) * ‖f t‖ ≤ Real.exp (-s.re * t) * (M * Real.exp (σ * t)) := by
        gcongr
    _ = M * Real.exp (-(s.re - σ) * t) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- If `f` is a.e. strongly measurable on `(0, ∞)` with `‖f(t)‖ ≤ M e^{σt}` there and
`σ < Re s`, then the Laplace integrand `t ↦ e^{-st} f(t)` is integrable on `(0, ∞)`. -/
theorem integrable_cexp_neg_mul_smul_of_norm_le_mul_exp {f : ℝ → E} {s : ℂ} {σ M : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hb : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t)) (hs : σ < s.re) :
    Integrable (fun t : ℝ => cexp (-s * t) • f t) (volume.restrict (Ioi 0)) :=
  Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M)
    ((by fun_prop : Continuous fun t : ℝ => cexp (-s * t)).aestronglyMeasurable.smul hf)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      norm_cexp_neg_mul_smul_le_mul_exp (hb t ht))

/-- If `‖f(t)‖ ≤ M e^{σt}` on `(0, ∞)` and `σ < Re s`, then the Laplace integral of `f` at `s`
has norm at most `M / (Re s - σ)`. -/
theorem norm_integral_cexp_neg_mul_smul_le_of_norm_le_mul_exp {f : ℝ → E} {s : ℂ} {σ M : ℝ}
    (hb : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t)) (hs : σ < s.re) :
    ‖∫ t in Ioi (0 : ℝ), cexp (-s * t) • f t‖ ≤ M / (s.re - σ) := by
  have hσs : -(s.re - σ) < 0 := by linarith
  refine (norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi hσs 0).const_mul M)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      norm_cexp_neg_mul_smul_le_mul_exp (hb t ht))).trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi hσs, mul_zero, Real.exp_zero, neg_div_neg_eq,
    mul_one_div]

variable [CompleteSpace E]

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
on `[0, ε)` for some `ε > 0`, and let `t ↦ e^{-σt} q(t)` be integrable on `(0, ∞)` for some real
`σ`. Then `∫₀^∞ e^{-xt} q(t) dt ∼ ∑ q^{(s)}(0) x^{-s-1}` as `x → +∞`, where `q^{(s)}(0)` is the
`s`th derivative of `q` at `0` within `[0, ∞)`, in the sense of `HasAsymptoticExpansion`: for
every `N` the remainder after `N` terms is `O(x^{-N-1})`. -/
theorem hasAsymptoticExpansion_laplace_of_contDiffOn {q : ℝ → ℂ} {σ ε : ℝ} (hε : 0 < ε)
    (hq : ContDiffOn ℝ ∞ q (Ico 0 ε))
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0)) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (x : ℂ) ^ (-((s : ℂ) + 1)))
      (fun s => iteratedDerivWithin s q (Ici 0) 0)
      fun x : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * q t := by
  set d : ℕ → ℂ := fun s => iteratedDerivWithin s q (Ici 0) 0
  -- near `0` the sets `[0, ε)` and `[0, ∞)` agree, so they give the same derivatives at `0`
  have hd (k : ℕ) : iteratedDerivWithin k q (Ico 0 ε) 0 = d k := by
    have hset : Ico 0 ε =ᶠ[𝓝 (0 : ℝ)] Ici 0 := by
      filter_upwards [Iio_mem_nhds hε] with t ht
      exact ⟨fun (h : t ∈ Set.Ico 0 ε) => h.1, fun (h : t ∈ Set.Ici (0 : ℝ)) => ⟨h, ht⟩⟩
    simp only [d, iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_congr_set hset]
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico 0 ε] 0 := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hε]
    exact nhdsWithin_mono _ Ioo_subset_Ico_self
  -- Taylor's theorem: the remainder after `N` terms of the Taylor series is `O(t^N)` at `0+`
  have hT (N : ℕ) : (fun t : ℝ => q t - ∑ s ∈ range N, d s / s ! * (t : ℂ) ^ s)
      =O[𝓝[>] 0] fun t => t ^ N := by
    rcases N with _ | N
    · simpa using ((hq.continuousOn _ (left_mem_Ico.2 hε)).tendsto.mono_left hle).isBigO_one ℝ
    refine ((taylor_isBigO (convex_Ico 0 ε) (left_mem_Ico.2 hε) (n := N)
      (hq.of_le (mod_cast le_top))).mono hle).congr (fun t => ?_) fun t => by simp
    simp only [taylor_within_apply, hd, sub_zero, Complex.real_smul]
    push_cast
    exact congrArg (q t - ·) (sum_congr rfl fun s _ => by ring)
  refine (hasAsymptoticExpansion_laplace (α := fun s => (s : ℂ) + 1) (c := fun s => d s / s !)
    (fun s => by simp only [add_re, natCast_re, one_re]; positivity) hint fun N => ?_).congr_coeff
    fun s => ?_
  · simpa [Real.rpow_natCast, ← cpow_natCast] using hT N
  · have hs : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 s.factorial_ne_zero
    rw [Gamma_nat_eq_factorial, mul_div_cancel₀ _ hs]

/-- **The error bound of integration by parts** (DLMF 2.3.3). Let `q` be `C^n` on `[0, ∞)` with
`‖q^{(n)}(t)‖ ≤ M e^{σt}` for `t ≥ 0` (derivatives within `[0, ∞)`). Then for `x > 0` and
`x > σ` the remainder after `n` terms of the expansion of
`Asymptotics.hasAsymptoticExpansion_laplace_of_contDiffOn` is bounded by
`‖∫₀^∞ e^{-xt} q(t) dt - ∑_{s<n} q^{(s)}(0) x^{-s-1}‖ ≤ M / (xⁿ (x - σ))`. DLMF's form is the
case `M = ‖q^{(n)}(0)‖`, with `σ` the least admissible rate `σ_n`. -/
theorem norm_integral_cexp_neg_mul_sub_sum_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {q : ℝ → E} {n : ℕ} {σ M x : ℝ}
    (hq : ContDiffOn ℝ n q (Ici 0))
    (hb : ∀ t ∈ Ici (0 : ℝ), ‖iteratedDerivWithin n q (Ici 0) t‖ ≤ M * Real.exp (σ * t))
    (hx : 0 < x) (hσx : σ < x) :
    ‖(∫ t in Ioi (0 : ℝ), cexp (-(x * t)) • q t) -
        ∑ s ∈ range n, ((x : ℂ) ^ (s + 1))⁻¹ • iteratedDerivWithin s q (Ici 0) 0‖ ≤
      M / (x ^ n * (x - σ)) := by
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hb 0 self_mem_Ici)
  -- a common rate `α` with `max σ 0 < α < x` for the lower derivatives
  obtain ⟨α, hσα, hα, hαx⟩ : ∃ α, σ ≤ α ∧ 0 < α ∧ α < x :=
    ⟨(max σ 0 + x) / 2, by linarith [le_max_left σ 0, le_max_right σ 0], by positivity,
      by linarith [max_lt hσx hx]⟩
  have hb' : ∀ t ∈ Ici (0 : ℝ), ‖iteratedDerivWithin n q (Ici 0) t‖ ≤
      M * Real.exp (α * (t - 0)) := fun t (ht : 0 ≤ t) => (hb t ht).trans (by
        rw [sub_zero]
        gcongr)
  have hint (k : ℕ) (hk : k ≤ n) : Integrable
      (fun t : ℝ => cexp (-(x : ℂ) * t) • iteratedDerivWithin k q (Ici 0) t)
      (volume.restrict (Ioi 0)) := by
    obtain ⟨C, hC⟩ := hq.exists_norm_iteratedDerivWithin_le_mul_exp hα hb' hk
    refine integrable_cexp_neg_mul_smul_of_norm_le_mul_exp
      (((hq.continuousOn_iteratedDerivWithin (mod_cast hk) (uniqueDiffOn_Ici 0)).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (fun t (ht : 0 < t) => by simpa using hC t ht.le) (by simpa using hαx)
  have hL := norm_integral_cexp_neg_mul_smul_le_of_norm_le_mul_exp (s := (x : ℂ))
    (fun t (ht : 0 < t) => hb t ht.le) (by simpa using hσx)
  simp_rw [← neg_mul]
  rw [integral_cexp_neg_mul_smul_eq_sum_add (ofReal_ne_zero.2 hx.ne') hq hint,
    add_sub_cancel_left, norm_smul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg hx.le]
  calc (x ^ n)⁻¹ * ‖∫ t in Ioi (0 : ℝ), cexp (-(x : ℂ) * t) • iteratedDerivWithin n q (Ici 0) t‖
      ≤ (x ^ n)⁻¹ * (M / (x - σ)) := by
        gcongr
        simpa using hL
    _ = M / (x ^ n * (x - σ)) := by
        rw [inv_mul_eq_div, div_div, mul_comm (x - σ)]

end Asymptotics
