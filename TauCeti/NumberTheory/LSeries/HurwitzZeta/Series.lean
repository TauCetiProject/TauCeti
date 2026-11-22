/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# The complex-parameter Hurwitz zeta series

For a complex shift parameter `c : ℂ` and exponent `s : ℂ`, the complex Hurwitz series
`complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c))` agrees termwise with
`(n + c) ^ (-s)` for every `s : ℂ` whenever `c ∉ -ℕ` (including negative noninteger shifts on or
across the branch cut `(-∞, 0]` of the principal logarithm, as distinct from `slitPlane` or
`0 < c.re`). Note that holomorphy and meromorphic continuation in `Continuation.lean` are developed
on `{0 < c.re}`, where no base `n + c` meets the branch cut `(-∞, 0]`.

On `1 < s.re`, the series converges absolutely for every `c : ℂ`. At a nonpositive integer shift
`c = -n` (`n : ℕ`), the defining summand at index `n` is `exp (-s * log 0) = exp 0 = 1` (by Lean's
`Complex.log 0 = 0`), whereas the corresponding principal-power summand `0 ^ (-s)` is `0` for
`1 < s.re`; thus convergence on `1 < s.re` at `c ∈ -ℕ` is purely formal under totalization.

For `1 < s.re`, shifting `c ≠ 0` by `1` subtracts the initial `n = 0` term `c ^ (-s)`. Also for
`1 < s.re`: along the real interval `(0, 1]`, `complexHurwitzSeries s x` agrees with Mathlib's
circle-parametrized Hurwitz zeta function `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`; at
`c = 1` it reduces to `riemannZeta s`; and at `c = 1 / 2` the odd-integer sum yields
`((2 : ℂ) ^ s - 1) * riemannZeta s`.

## Main definitions and results

* `TauCeti.complexHurwitzSeries`: the Dirichlet-type series `∑' n : ℕ, exp (-s * log (n + c))`.
* `TauCeti.complexHurwitzSeries_eq_tsum_cpow`: termwise agreement with `∑' n : ℕ, (n + c) ^ (-s)`
  for every `s : ℂ` when `c ∉ -ℕ`.
* `TauCeti.exists_norm_complexHurwitzSeries_term_le`: compact-uniform summable majorant
  `C * (n + 1) ^ (-σ)` (`1 < σ`) on compact subsets of
  `{p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}` (combining `1 < s.re` convergence with
  `c ∉ -ℕ` termwise agreement).
* `TauCeti.summable_norm_complexHurwitzSeries_term`, `TauCeti.summable_complexHurwitzSeries_term`,
  `TauCeti.hasSum_complexHurwitzSeries_term`, `TauCeti.hasSum_complexHurwitzSeries`, and
  `TauCeti.hasSum_complexHurwitzSeries_of_re_pos`: for `1 < s.re`, formal absolute convergence and
  `HasSum` for arbitrary `c : ℂ`, and principal-power `HasSum` when `c ∉ -ℕ` (in particular
  `0 < c.re`).
* `TauCeti.complexHurwitzSeries_add_one_right`: shift identity
  `complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s)` for `1 < s.re` and
  `c ≠ 0`.
* `TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta`: agreement with `HurwitzZeta.hurwitzZeta`
  for real `x ∈ (0, 1]` and `1 < s.re`.
* `TauCeti.complexHurwitzSeries_one_right` and `TauCeti.complexHurwitzSeries_one_half_right`:
  specializations at `c = 1` and `c = 1 / 2` for `1 < s.re`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  **24** (2012), 49–84.
* F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, §25.11.
-/

public section

open Complex Set Filter
open scoped Topology

namespace TauCeti

/-- The complex-parameter Hurwitz zeta series `∑' n : ℕ, exp (-s * log (n + c))`, using the
principal complex logarithm. Whenever `c ∉ -ℕ`, every base `n + c` is nonzero and each summand
equals `(n + c) ^ (-s)` for every `s : ℂ` (including negative noninteger shifts on the branch cut
`(-∞, 0]`, whereas the analytic continuation in `Continuation.lean` stays on `0 < c.re` inside
`slitPlane`). On `1 < s.re`, the series converges absolutely for all `c : ℂ`, including formally
at `c = -n` (`n : ℕ`) under totalization: at index `n` the defining summand is
`exp (-s * log 0) = 1` (whereas the totalized principal power `0 ^ (-s)` is `0`), so values at
`c ∈ -ℕ` are totalized artifacts outside the termwise-agreement shifts `c ∉ -ℕ`. -/
noncomputable def complexHurwitzSeries (s c : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c))

/-- Defining equation for `complexHurwitzSeries`. -/
theorem complexHurwitzSeries_def (s c : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c)) := (rfl)

/-- Away from the nonpositive integers `c = -n`, every shifted base `n + c` is nonzero, so
`complexHurwitzSeries s c` coincides termwise with `∑' n : ℕ, (n + c) ^ (-s)` for every
`s : ℂ`. -/
theorem complexHurwitzSeries_eq_tsum_cpow {c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (s : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, ((n : ℂ) + c) ^ (-s) := by
  rw [complexHurwitzSeries_def]
  refine tsum_congr fun n => ?_
  have hne : (n : ℂ) + c ≠ 0 := fun h => hc n (eq_neg_of_add_eq_zero_right h)
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- On any compact subset `K` of `{p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}`
(combining `1 < s.re` convergence with `c ∉ -ℕ` termwise agreement), the defining terms
`Complex.exp (-p.1 * Complex.log (n + p.2))` admit a uniform summable bound
`C * ((n : ℝ) + 1) ^ (-σ)` with `1 < σ` and `0 ≤ C`. -/
theorem exists_norm_complexHurwitzSeries_term_le {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hK_sub : K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}) :
    ∃ σ : ℝ, 1 < σ ∧ ∃ C ≥ 0, ∀ p ∈ K, ∀ n : ℕ,
      ‖Complex.exp (-p.1 * Complex.log (n + p.2))‖ ≤ C * ((n : ℝ) + 1) ^ (-σ) := by
  obtain ⟨σ, hσ, C, hC, hle⟩ := exists_norm_natCast_add_cpow_neg_le hK hK_sub
  refine ⟨σ, hσ, C, hC, fun p hp n => ?_⟩
  have hne : (n : ℂ) + p.2 ≠ 0 := fun h => (hK_sub hp).2 n (eq_neg_of_add_eq_zero_right h)
  rw [mul_comm (-p.1), ← cpow_def_of_ne_zero hne]
  exact hle p hp n

/-- For `1 < s.re` and any `c : ℂ`, the defining terms `exp (-s * log (n + c))` are absolutely
summable. When `c ∉ -ℕ`, this is absolute convergence of `∑' n, (n + c) ^ (-s)`; at `c = -n`
(`n : ℕ`), the `n`-th summand is totalized to `exp 0 = 1` (unlike `0 ^ (-s) = 0`), so summability
holds formally there as well. -/
theorem summable_norm_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖Complex.exp (-s * Complex.log (n + c))‖) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_re_natCast_add_pos c)
  refine (summable_nat_add_iff N).mp
    (((summable_nat_add_iff N).mpr (summable_norm_natCast_add_cpow_neg hs c)).congr fun n => ?_)
  have hne : (((n + N : ℕ) : ℂ) + c) ≠ 0 := fun h0 =>
    (hN (n + N) (Nat.le_add_left N n)).ne' (by rw [h0, zero_re])
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- For `1 < s.re` and any `c : ℂ`, the defining terms of `complexHurwitzSeries s c` are
summable (formal totalized convergence at `c = -n` with `n`-th term `exp 0 = 1`; principal-power
convergence when `c ∉ -ℕ`). -/
theorem summable_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_complexHurwitzSeries_term hs c).of_norm

/-- For `1 < s.re` and any `c : ℂ`, the defining exponential-log terms sum to
`complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    HasSum (fun n : ℕ => Complex.exp (-s * Complex.log (n + c))) (complexHurwitzSeries s c) := by
  rw [complexHurwitzSeries_def]
  exact (summable_complexHurwitzSeries_term hs c).hasSum

/-- On `1 < s.re` and away from `c = -n` (`n : ℕ`), `n ↦ (n + c) ^ (-s)` has sum
`complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    HasSum (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) := by
  rw [complexHurwitzSeries_eq_tsum_cpow hc]
  exact (summable_natCast_add_cpow_neg hs c).hasSum

/-- On `1 < s.re` and `0 < c.re`, `n ↦ (n + c) ^ (-s)` has sum `complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries_of_re_pos {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    HasSum (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) :=
  hasSum_complexHurwitzSeries hs fun n h => by
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- On `1 < s.re`, shifting the complex Hurwitz parameter `c ≠ 0` by `1` removes the `n = 0` term
`c ^ (-s)`. -/
theorem complexHurwitzSeries_add_one_right {s c : ℂ} (hs : 1 < s.re) (hc : c ≠ 0) :
    complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s) := by
  rw [complexHurwitzSeries_def s c, (summable_complexHurwitzSeries_term hs c).tsum_eq_zero_add]
  have hshift : (∑' n : ℕ, Complex.exp (-s * Complex.log (((n + 1 : ℕ) : ℂ) + c))) =
      complexHurwitzSeries s (c + 1) := by
    rw [complexHurwitzSeries_def]
    refine tsum_congr fun n => ?_
    have hbase : ((n + 1 : ℕ) : ℂ) + c = (n : ℂ) + (c + 1) := by push_cast; ring
    rw [hbase]
  rw [Nat.cast_zero, zero_add, mul_comm (-s), ← cpow_def_of_ne_zero hc, hshift,
    add_sub_cancel_left]

/-- For real `x ∈ (0, 1]` and `1 < s.re`, `complexHurwitzSeries s x` agrees with Mathlib's
circle-parametrized `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`. -/
theorem complexHurwitzSeries_ofReal_eq_hurwitzZeta {s : ℂ} {x : ℝ} (hs : 1 < s.re)
    (hx : x ∈ Ioc 0 1) :
    complexHurwitzSeries s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have h1 := hasSum_complexHurwitzSeries_of_re_pos (c := (x : ℂ)) hs (by simpa using hx.1)
  have h2 := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (Ioc_subset_Icc_self hx) hs
  exact h1.unique (h2.congr_fun fun _ => by rw [cpow_neg, one_div])

/-- At `c = 1`, the complex Hurwitz series on `1 < s.re` equals `riemannZeta s`. -/
theorem complexHurwitzSeries_one_right {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  have h := complexHurwitzSeries_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

/-- At `c = 1 / 2` and `1 < s.re`, partitioning positive integers by parity yields
`complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzSeries_one_half_right {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hzeta : HasSum (fun k : ℕ => ((k : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    rw [← complexHurwitzSeries_one_right hs]
    exact hasSum_complexHurwitzSeries_of_re_pos hs (by simp)
  have heven : HasSum (fun k : ℕ => (((2 * k : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2)) :=
    ((hasSum_complexHurwitzSeries_of_re_pos hs (by norm_num)).mul_left ((2 : ℂ) ^ (-s))).congr_fun
      fun k => by
        have hmul := ofReal_mul_cpow (a := 2) zero_le_two ((k : ℂ) + 1 / 2) (-s)
        simp only [ofReal_ofNat] at hmul
        rw [← hmul]; congr 1; push_cast; ring
  have hodd : HasSum (fun k : ℕ => (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * riemannZeta s) :=
    (hzeta.mul_left ((2 : ℂ) ^ (-s))).congr_fun fun k => by
      have hmul := ofReal_mul_cpow (a := 2) zero_le_two ((k : ℂ) + 1) (-s)
      simp only [ofReal_ofNat] at hmul
      rw [← hmul]; congr 1; push_cast; ring
  have hsum : (2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2) + (2 : ℂ) ^ (-s) * riemannZeta s =
      riemannZeta s := (HasSum.even_add_odd heven hodd).unique hzeta
  have htwo : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
  calc complexHurwitzSeries s (1 / 2)
      = (2 : ℂ) ^ s * ((2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2)) := by
        rw [← mul_assoc, htwo, one_mul]
    _ = (2 : ℂ) ^ s * (riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s) := by
        rw [eq_sub_of_add_eq hsum]
    _ = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
        rw [mul_sub, ← mul_assoc, htwo]; ring

example : complexHurwitzSeries 2 (1 + I) - complexHurwitzSeries 2 (2 + I) = -I / 2 := by
  have hne : (1 + I : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hshift := complexHurwitzSeries_add_one_right (s := 2) (by norm_num) hne
  have h2I : (1 + I : ℂ) + 1 = 2 + I := by ring
  have hsq : (1 + I : ℂ) ^ (2 : ℕ) = 2 * I := by rw [sq]; ring_nf; simp
  rw [h2I] at hshift
  rw [hshift, sub_sub_cancel]
  simp only [cpow_neg, cpow_ofNat, hsq, mul_inv, inv_I]
  ring

end TauCeti

end
