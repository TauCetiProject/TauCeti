/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.RightOfCurve
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion

/-!
# The prime number theorem with de la Vallée Poussin's error term

There is `c > 0` with `ψ(x) = x + O(x exp(-c √(log x)))`, where `ψ` is Chebyshev's function
`Chebyshev.psi`.

The proof applies Ingham's transfer theorem `TauCeti.LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion`
to `a = Λ`, with residue `r = 1` and width `η(t) = c / log t`. Its hypotheses on `ζ` come from the
classical bound for `ζ′/ζ + 1/(s - 1)` right of the curve `Re s = 1 - β / log (|Im s| + 2)`, in the
shape the transfer theorem consumes: `TauCeti.exists_neg_logDeriv_riemannZeta_eq_add_and_norm_le`
writes `-ζ′/ζ = G + 1/(s - 1)` with `G` holomorphic on an open set containing
`1 - c / log (|Im s| + 3) ≤ Re s` and `‖G(s)‖ ≤ C log (|Im s| + 3)` there. For
`η(t) = c / log t` the Ingham exponent is at least `√c √(log x)`
(`TauCeti.le_inghamExponent_of_mul_log_rpow_le` at `A = 1`).

## Main results

* `Chebyshev.exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log`: `|ψ(x) - x| ≤ C x exp(-c √(log x))`
  for `x ≥ 3`.
* `Chebyshev.exists_isBigO_psi_sub_id_mul_exp_neg_mul_sqrt_log`:
  `ψ(x) - x = O(x exp(-c √(log x)))`.

## References

* C.-J. de la Vallée Poussin, *Sur la fonction ζ(s) de Riemann et le nombre des nombres premiers
  inférieurs à une limite donnée*, Mém. Couronnés Acad. Roy. Belgique 59 (1899).
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §18.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Theorem 6.9.
* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd*,
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, Theorem `StrongPNT` in
  `PrimeNumberTheoremAnd/StrongPNT.lean`, which proves the `O`-form below by the same route.
-/

public section

open Complex Filter Set
open scoped ArithmeticFunction.vonMangoldt Chebyshev

namespace Chebyshev

open TauCeti

/-- **The prime number theorem with de la Vallée Poussin's error term**, explicit form: there are
`c > 0` and `C` with `|ψ(x) - x| ≤ C x exp(-c √(log x))` for every `x ≥ 3`. -/
theorem exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log :
    ∃ c > 0, ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |ψ x - x| ≤ C * x * Real.exp (-c * √(Real.log x)) := by
  obtain ⟨c, C₀, hc, U, -, hRU, G, hG, hLζ, hGb⟩ :=
    exists_neg_logDeriv_riemannZeta_eq_add_and_norm_le
  set η : ℝ → ℝ := fun t ↦ c / Real.log t
  have hlog {t : ℝ} (ht : t ∈ Ici (3 : ℝ)) : 0 < Real.log t :=
    Real.log_pos (by linarith [mem_Ici.1 ht])
  have hηc : ContinuousOn η (Ici 3) := continuousOn_const.div
    (Real.continuousOn_log.mono fun t ht ↦
      mem_compl_singleton_iff.2 (by linarith [mem_Ici.1 ht] : (0 : ℝ) < t).ne')
    fun t ht ↦ (hlog ht).ne'
  have hηa : AntitoneOn η (Ici 3) := fun s hs t _ hst ↦
    div_le_div_of_nonneg_left hc.le (hlog hs) (Real.log_le_log (by linarith [mem_Ici.1 hs]) hst)
  have hηlow (t : ℝ) (_ : 3 ≤ t) : c * Real.log t ^ (-(1 : ℝ)) ≤ η t := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
  have ha (n : ℕ) (hn : 1 ≤ n) : ‖(Λ n : ℂ)‖ ≤ 1 * Real.log (n + 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn) (by linarith))
  have hLG (s : ℂ) (hs : 1 < s.re) : LSeries (fun n ↦ (Λ n : ℂ)) s = G s + 1 / (s - 1) := by
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    have hR : 1 - η (|s.im| + 3) ≤ s.re := by
      have : 0 < η (|s.im| + 3) := div_pos hc (hlog (by simp [abs_nonneg]))
      linarith
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, ← (hLζ s hs1 hR).2,
      logDeriv_apply, neg_div]
  obtain ⟨c', hc', C', hC'⟩ := LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion hηc hηa hc hηlow ha
    hRU hG hLG (C₀ := C₀) (B' := 1) fun s hs ↦ by rw [Real.rpow_one]; exact hGb s hs
  refine ⟨c' * √c, mul_pos hc' (Real.sqrt_pos.2 hc), max C' 0, fun x hx ↦ ?_⟩
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) - 1 * x = ((ψ x - x : ℝ) : ℂ) := by
    rw [psi, ← Finset.Icc_add_one_left_eq_Ioc]
    push_cast
    ring
  have hω : √c * √(Real.log x) ≤ inghamExponent η x := by
    have := le_inghamExponent_of_mul_log_rpow_le hc.le zero_le_one hηlow (by linarith : 1 ≤ x)
    rwa [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow] at this
  have h := hC' x hx
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at h
  calc |ψ x - x| ≤ max C' 0 * x * Real.exp (-c' * inghamExponent η x) :=
        h.trans (by gcongr; exact le_max_left _ _)
    _ ≤ max C' 0 * x * Real.exp (-(c' * √c) * √(Real.log x)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hω hc'.le]

/-- **The prime number theorem with de la Vallée Poussin's error term**: there is `c > 0` with
`ψ(x) - x = O(x exp(-c √(log x)))`. -/
theorem exists_isBigO_psi_sub_id_mul_exp_neg_mul_sqrt_log :
    ∃ c > 0, (fun x ↦ ψ x - x) =O[atTop] fun x ↦ x * Real.exp (-c * √(Real.log x)) := by
  obtain ⟨c, hc, C, hC⟩ := exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log
  refine ⟨c, hc, Asymptotics.IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), ← mul_assoc]
  exact hC x hx

end Chebyshev
