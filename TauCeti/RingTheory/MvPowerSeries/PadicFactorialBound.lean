/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import TauCeti.NumberTheory.Padics.Factorial
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# p-adic norm bounds for multi-index factorials and homogeneous jets

Using Legendre's lower bound on the `p`-adic valuation of a product of factorials
(`TauCeti.div_sub_log_le_multiplicity_prod_factorial`), we bound the norm of a multi-index
factorial `∏ i, (d i)!` in any normed field `K` whose norm restricts to the `p`-adic norm on `ℕ`.
When `K` is ultrametric, this yields the norm bound for the pairing
`∑ d, coeff d Q * (∏ i, (d i)!) * coeff d G` of a homogeneous integral multivariate polynomial `Q`
of degree `l` with a power series `G` whose degree-`l` coefficients have norm at most `1`.

## Main results

* `TauCeti.norm_prod_factorial_le_of_padic_norm`: support-sharp norm bound
  `‖∏ i, (d i)!‖ ≤ p ^ (#supp(d) * (log_p |d| + 1) - |d| / (p - 1))`.
* `TauCeti.norm_prod_factorial_le_fintype`: finite-variable form using `Fintype.card σ`.
* `TauCeti.norm_sum_mul_factorial_le_of_isHomogeneous`: ultrametric jet norm bound for a
  homogeneous polynomial of degree `l` paired against a power series.

## Provenance

Adapted from `New.norm_prod_factorial_le` and `New.norm_jet_le_of_isHomogeneous` in
`grh/src/New/Derivatives/Divisibility/Count.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Finset

/-- Legendre's norm bound for a multi-index factorial `∏ i, (d i)!` in any normed field `K`
whose norm on nonzero natural numbers is `p ^ (-v_p(n))`. -/
theorem norm_prod_factorial_le_of_padic_norm {p : ℕ} [hp : Fact p.Prime] {σ K : Type*}
    [NormedField K]
    (hnorm : ∀ n : ℕ, n ≠ 0 → ‖(n : K)‖ = (p : ℝ) ^ (-(padicValNat p n : ℝ)))
    (d : σ →₀ ℕ) :
    ‖d.prod fun (_ : σ) (k : ℕ) ↦ (k.factorial : K)‖ ≤
      (p : ℝ) ^ ((d.support.card : ℝ) * (Nat.log p d.degree + 1) -
        (d.degree : ℝ) / ((p : ℝ) - 1)) := by
  have hne : (d.prod fun _ k ↦ k.factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ ↦ Nat.factorial_ne_zero _
  have hcast : (d.prod fun _ k ↦ (k.factorial : K)) = ((d.prod fun _ k ↦ k.factorial : ℕ) : K) := by
    simp [Finsupp.prod]
  rw [hcast, hnorm _ hne]
  have hleg := div_sub_log_le_multiplicity_prod_factorial p d
  rw [← Nat.padicValNat_def] at hleg
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.out.one_le) (by linarith)

/-- Finite-variable form of `TauCeti.norm_prod_factorial_le_of_padic_norm`, bounding
`d.support.card` by `Fintype.card σ`. -/
theorem norm_prod_factorial_le_fintype {p : ℕ} [hp : Fact p.Prime] {σ K : Type*}
    [Fintype σ] [NormedField K]
    (hnorm : ∀ n : ℕ, n ≠ 0 → ‖(n : K)‖ = (p : ℝ) ^ (-(padicValNat p n : ℝ)))
    (d : σ →₀ ℕ) :
    ‖d.prod fun (_ : σ) (k : ℕ) ↦ (k.factorial : K)‖ ≤
      (p : ℝ) ^ ((Fintype.card σ : ℝ) * (Nat.log p d.degree + 1) -
        (d.degree : ℝ) / ((p : ℝ) - 1)) := by
  refine (norm_prod_factorial_le_of_padic_norm hnorm d).trans ?_
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.out.one_le) ?_
  have hcard : (d.support.card : ℝ) ≤ Fintype.card σ := by
    exact_mod_cast d.support.card_le_univ
  gcongr

/-- Ultrametric norm bound for the factorial-weighted pairing (jet) of a homogeneous polynomial
`Q` of degree `l` with integral coefficients against a power series `G` whose degree-`l`
coefficients have norm at most `1`. -/
theorem norm_sum_mul_factorial_le_of_isHomogeneous {p : ℕ} [hp : Fact p.Prime] {σ K : Type*}
    [Fintype σ] [NormedField K] [IsUltrametricDist K]
    (hnorm : ∀ n : ℕ, n ≠ 0 → ‖(n : K)‖ = (p : ℝ) ^ (-(padicValNat p n : ℝ)))
    {G : MvPowerSeries σ K} {l : ℕ}
    (hG : ∀ d : σ →₀ ℕ, d.degree = l → ‖MvPowerSeries.coeff d G‖ ≤ 1)
    {Q : MvPolynomial σ K} (hQ : Q.IsHomogeneous l)
    (hQ_int : ∀ d : σ →₀ ℕ, ‖Q.coeff d‖ ≤ 1) :
    ‖∑ d ∈ Q.support, Q.coeff d * (d.prod fun (_ : σ) (k : ℕ) ↦ (k.factorial : K)) *
        MvPowerSeries.coeff d G‖ ≤
      (p : ℝ) ^ ((Fintype.card σ : ℝ) * (Nat.log p l + 1) -
        (l : ℝ) / ((p : ℝ) - 1)) := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d hd ↦ ?_
  have hdeg : d.degree = l := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (hQ.coeff_eq_zero hne)
  rw [norm_mul, norm_mul, ← hdeg]
  calc ‖Q.coeff d‖ * ‖d.prod fun _ k ↦ (k.factorial : K)‖ * ‖MvPowerSeries.coeff d G‖
      ≤ 1 * ‖d.prod fun _ k ↦ (k.factorial : K)‖ * 1 := by
        gcongr
        · exact hQ_int d
        · exact hG d hdeg
    _ = ‖d.prod fun _ k ↦ (k.factorial : K)‖ := by ring
    _ ≤ _ := norm_prod_factorial_le_fintype hnorm d

end TauCeti
