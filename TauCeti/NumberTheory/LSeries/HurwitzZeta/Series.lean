/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The complex-parameter Hurwitz zeta series

For a complex shift parameter `c : ℂ` and exponent `s : ℂ` with `1 < s.re`, the complex Hurwitz
series
`complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c))`
converges absolutely; away from the nonpositive integers `c = -n` (`n : ℕ`), each term coincides
with the principal complex power `(n + c) ^ (-s)`.

Shifting `c ≠ 0` by `1` subtracts the initial `n = 0` term `c ^ (-s)`. Along the real interval
`(0, 1]`, `complexHurwitzSeries s x` agrees with Mathlib's circle-parametrized Hurwitz zeta
function `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`; at `c = 1` it reduces to `riemannZeta s`,
and at `c = 1 / 2` the odd-integer sum yields `((2 : ℂ) ^ s - 1) * riemannZeta s`.

## Main definitions and results

* `TauCeti.complexHurwitzSeries`: the Dirichlet-type series `∑' n : ℕ, exp (-s * log (n + c))`.
* `TauCeti.summable_norm_complexHurwitzSeries_term` and `TauCeti.hasSum_complexHurwitzSeries`:
  absolute convergence on `1 < s.re` for arbitrary `c : ℂ` and principal-power form away from `-ℕ`.
* `TauCeti.complexHurwitzSeries_add_one_right`: shift identity
  `complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s)` for `c ≠ 0`.
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
principal complex logarithm. On `1 < s.re`, the series converges absolutely for every `c : ℂ`,
and away from `c = -n` (`n : ℕ`) each summand equals `(n + c) ^ (-s)`. -/
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

/-- For `1 < s.re` and any `c : ℂ`, the principal-power series `∑' n : ℕ, ‖(n + c) ^ (-s)‖` is
summable. -/
theorem summable_norm_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖((n : ℂ) + c) ^ (-s)‖) := by
  set N : ℕ := ⌊1 - c.re⌋₊ + 1
  have hN : (N : ℂ) + c ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have hlt : 1 - c.re < (⌊1 - c.re⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [N, add_re, natCast_re]
    push_cast
    linarith
  obtain ⟨U, hU, -, C, -, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hN (-s)
  have hp : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-s.re)) :=
    ((summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow (p := -s.re)).mpr (by linarith))).congr
      fun n => by push_cast; rw [add_comm]
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hp.mul_left C)
  have h := hbound ((N : ℂ) + c) (mem_of_mem_nhds hU) (n : ℝ) (Nat.cast_nonneg n)
  simpa only [ofReal_natCast, neg_re, Nat.cast_add, add_assoc] using h

/-- For `1 < s.re` and any `c : ℂ`, the complex Hurwitz series converges absolutely. -/
theorem summable_norm_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖Complex.exp (-s * Complex.log (n + c))‖) := by
  set N : ℕ := ⌊1 - c.re⌋₊ + 1
  refine (summable_nat_add_iff N).mp
    (((summable_nat_add_iff N).mpr (summable_norm_natCast_add_cpow_neg hs c)).congr fun n => ?_)
  have hne : (((n + N : ℕ) : ℂ) + c) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have hlt : 1 - c.re < (⌊1 - c.re⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [N, add_re, natCast_re, zero_re] at hre
    push_cast at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- For `1 < s.re` and any `c : ℂ`, the defining terms of `complexHurwitzSeries s c` are
summable. -/
theorem summable_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_complexHurwitzSeries_term hs c).of_norm

/-- For `1 < s.re` and any `c : ℂ`, `n ↦ (n + c) ^ (-s)` is summable. -/
theorem summable_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) :=
  (summable_norm_natCast_add_cpow_neg hs c).of_norm

/-- On `1 < s.re` and away from `c = -n` (`n : ℕ`), `n ↦ (n + c) ^ (-s)` has sum
`complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    HasSum (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) := by
  rw [complexHurwitzSeries_eq_tsum_cpow hc]
  exact (summable_natCast_add_cpow_neg hs c).hasSum

/-- Shifting the complex Hurwitz parameter `c ≠ 0` by `1` removes the `n = 0` term `c ^ (-s)`. -/
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
  have hne : ∀ n : ℕ, (x : ℂ) ≠ -(n : ℂ) := fun n h => by
    have hre := congrArg Complex.re h
    simp only [ofReal_re, neg_re, natCast_re] at hre
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
  have h1 := hasSum_complexHurwitzSeries hs hne
  have h2 := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (Ioc_subset_Icc_self hx) hs
  exact h1.unique (h2.congr_fun fun _ => by rw [cpow_neg, one_div])

/-- At `c = 1`, the complex Hurwitz series on `1 < s.re` equals `riemannZeta s`. -/
theorem complexHurwitzSeries_one_right {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  have h := complexHurwitzSeries_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

/-- At `(s, c) = (2, 1)`, the complex Hurwitz series evaluates to `π ^ 2 / 6`. -/
theorem complexHurwitzSeries_two_one :
    complexHurwitzSeries 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [complexHurwitzSeries_one_right (by norm_num), riemannZeta_two]

/-- At `c = 1 / 2` and `1 < s.re`, partitioning positive integers by parity yields
`complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzSeries_one_half_right {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hhalf_ne : ∀ n : ℕ, (1 / 2 : ℂ) ≠ -(n : ℂ) := fun n h => by
    have hre := congrArg Complex.re h
    simp only [one_div, inv_re, re_ofNat, normSq_ofNat, neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hone_ne : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := fun n h => by
    have hre := congrArg Complex.re h
    simp only [one_re, neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzeta : HasSum (fun k : ℕ => ((k : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    rw [← complexHurwitzSeries_one_right hs]
    exact hasSum_complexHurwitzSeries hs hone_ne
  have heven : HasSum (fun k : ℕ => (((2 * k : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2)) :=
    ((hasSum_complexHurwitzSeries hs hhalf_ne).mul_left ((2 : ℂ) ^ (-s))).congr_fun fun k => by
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

/-- Shift identity at the nonreal parameter `1 + I`:
`complexHurwitzSeries 2 (1 + I) - complexHurwitzSeries 2 (2 + I) = -I / 2`. -/
theorem complexHurwitzSeries_two_one_add_I_sub_two_add_I :
    complexHurwitzSeries 2 (1 + I) - complexHurwitzSeries 2 (2 + I) = -I / 2 := by
  have hne : (1 + I : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hshift := complexHurwitzSeries_add_one_right (s := 2) (by norm_num) hne
  have h2I : (1 + I : ℂ) + 1 = 2 + I := by ring
  have hsq : (1 + I : ℂ) ^ (2 : ℕ) = 2 * I := by rw [sq]; ring_nf; simp
  have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_cast
  rw [h2I] at hshift
  rw [hshift, sub_sub_cancel, cpow_neg, hcast, cpow_natCast, hsq, mul_inv, inv_I]
  ring

end TauCeti

end
