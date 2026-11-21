/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# The complex-parameter Hurwitz zeta series

For a complex shift parameter `c : ℂ` and exponent `s : ℂ` with `1 < s.re`, the complex Hurwitz
series
`complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c))`
converges absolutely for every `c : ℂ`. The genuine Hurwitz domain consists of non-singular shifts
`c ∉ -ℕ` (and `0 < c.re` for the meromorphic continuation in `Continuation.lean`), where every
base `n + c` is nonzero and each summand coincides with the principal complex power
`(n + c) ^ (-s)`. At a nonpositive integer shift `c = -n` (`n : ℕ`), the defining summand at
index `n` is `exp (-s * log 0) = exp 0 = 1` (by Lean's `Complex.log 0 = 0`), whereas the
corresponding principal-power summand `0 ^ (-s)` is `0` for `1 < s.re`; thus convergence at `c ∈ -ℕ`
is purely formal under totalization and does not represent a genuine Hurwitz zeta value.

For `1 < s.re`, shifting `c ≠ 0` by `1` subtracts the initial `n = 0` term `c ^ (-s)`. Along the
real interval `(0, 1]`, `complexHurwitzSeries s x` agrees with Mathlib's circle-parametrized
Hurwitz zeta function `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`; at `c = 1` it reduces to
`riemannZeta s`, and at `c = 1 / 2` the odd-integer sum yields
`((2 : ℂ) ^ s - 1) * riemannZeta s`.

## Main definitions and results

* `TauCeti.complexHurwitzSeries`: the Dirichlet-type series `∑' n : ℕ, exp (-s * log (n + c))`.
* `TauCeti.summable_norm_complexHurwitzSeries_term`, `TauCeti.summable_complexHurwitzSeries_term`,
  `TauCeti.hasSum_complexHurwitzSeries_term`, `TauCeti.hasSum_complexHurwitzSeries`, and
  `TauCeti.hasSum_complexHurwitzSeries_of_re_pos`: formal absolute convergence and `HasSum` on
  `1 < s.re` for arbitrary `c : ℂ`, and principal-power convergence on the genuine shift domain
  `c ∉ -ℕ` (in particular `0 < c.re`).
* `TauCeti.complexHurwitzSeries_add_one_right`: shift identity
  `complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s)` for `1 < s.re` and
  `c ≠ 0`.
* `TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta`: agreement with `HurwitzZeta.hurwitzZeta`
  for real `x ∈ (0, 1]` and `1 < s.re`.
* `TauCeti.complexHurwitzSeries_one_right` and `TauCeti.complexHurwitzSeries_one_half_right`:
  specializations at `c = 1` and `c = 1 / 2`.

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
principal complex logarithm. The genuine Hurwitz domain is `1 < s.re` and `c ∉ -ℕ`, where every
base `n + c` is nonzero and each summand equals `(n + c) ^ (-s)`. On `1 < s.re`, the series also
converges formally for `c = -n` (`n : ℕ`) under totalization: at index `n` the defining summand is
`exp (-s * log 0) = 1` (whereas the totalized principal power `0 ^ (-s)` is `0`), so values at
`c ∈ -ℕ` are totalized artifacts rather than genuine Hurwitz values. -/
noncomputable def complexHurwitzSeries (s c : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c))

/-- Defining equation for `complexHurwitzSeries`. -/
theorem complexHurwitzSeries_def (s c : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c)) := (rfl)

/-- Away from the nonpositive integers `c = -n`, every shifted base `n + c` is nonzero, so
`complexHurwitzSeries s c` coincides termwise with `∑' n : ℕ, (n + c) ^ (-s)`. -/
theorem complexHurwitzSeries_eq_tsum_cpow {c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (s : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, ((n : ℂ) + c) ^ (-s) := by
  refine tsum_congr fun n => ?_
  have hne : (n : ℂ) + c ≠ 0 := fun h => hc n (eq_neg_of_add_eq_zero_right h)
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- For `1 < s.re` and any `c : ℂ`, the defining terms `exp (-s * log (n + c))` are absolutely
summable. Away from `c ∈ -ℕ` this is absolute convergence of the genuine Hurwitz series
`∑' n, (n + c) ^ (-s)`; at `c = -n` (`n : ℕ`), the `n`-th summand is totalized to `exp 0 = 1`
(unlike `0 ^ (-s) = 0`), so summability holds formally there as well. -/
theorem summable_norm_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖Complex.exp (-s * Complex.log (n + c))‖) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-c.re)
  refine (summable_nat_add_iff N).mp
    (((summable_nat_add_iff N).mpr (summable_norm_natCast_add_cpow_neg hs c)).congr fun n => ?_)
  have hne : (((n + N : ℕ) : ℂ) + c) ≠ 0 := fun h0 => by
    have hre := congrArg Complex.re h0
    simp only [add_re, natCast_re, Nat.cast_add, zero_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- For `1 < s.re` and any `c : ℂ`, the defining terms of `complexHurwitzSeries s c` are
summable (formal totalized convergence at `c = -n` with `n`-th term `exp 0 = 1`; genuine
principal-power convergence away from `c ∈ -ℕ`). -/
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
      complexHurwitzSeries s (c + 1) :=
    tsum_congr fun n => by congr 3; push_cast; ring
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

example : complexHurwitzSeries 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [complexHurwitzSeries_one_right (by norm_num), riemannZeta_two]

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
        have hmul := ofReal_mul_cpow (r := 2) zero_le_two ((k : ℂ) + 1 / 2) (-s)
        simp only [ofReal_ofNat] at hmul
        rw [← hmul]; congr 1; push_cast; ring
  have hodd : HasSum (fun k : ℕ => (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * riemannZeta s) :=
    (hzeta.mul_left ((2 : ℂ) ^ (-s))).congr_fun fun k => by
      have hmul := ofReal_mul_cpow (r := 2) zero_le_two ((k : ℂ) + 1) (-s)
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
