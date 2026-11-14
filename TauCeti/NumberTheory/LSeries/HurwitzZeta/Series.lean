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

For a complex shift parameter `c` in the slit plane `ℂ \ (-∞, 0]` (in particular on the open
right half-plane `0 < c.re`) and exponent `s : ℂ` with `1 < s.re`, the complex Hurwitz series
`complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c))`
converges absolutely, and each term coincides with the principal complex power `(n + c) ^ (-s)`.

Shifting `c` by `1` subtracts the initial `n = 0` term `c ^ (-s)`. Along the real interval
`(0, 1]`, `complexHurwitzSeries s x` agrees with Mathlib's circle-parametrized Hurwitz zeta
function `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`; at `c = 1` it reduces to `riemannZeta s`,
and at `c = 1 / 2` the odd-integer sum yields `((2 : ℂ) ^ s - 1) * riemannZeta s`.

## Main definitions and results

* `TauCeti.complexHurwitzSeries`: the Dirichlet-type series `∑' n : ℕ, exp (-s * log (n + c))`.
* `TauCeti.summable_norm_complexHurwitzSeries_term` and `TauCeti.hasSum_complexHurwitzSeries`:
  absolute convergence and principal-power form on `1 < s.re` and `c ∈ Complex.slitPlane`.
* `TauCeti.complexHurwitzSeries_add_one`: shift identity
  `complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s)`.
* `TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta`: agreement with `HurwitzZeta.hurwitzZeta`
  for real `x ∈ (0, 1]` and `1 < s.re`.
* `TauCeti.complexHurwitzSeries_one` and `TauCeti.complexHurwitzSeries_one_div_two`:
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
principal complex logarithm. On `1 < s.re` and `c ∈ Complex.slitPlane` (in particular for
`0 < c.re`), each summand equals `(n + c) ^ (-s)` and the series converges absolutely. -/
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

/-- For `1 < s.re` and `c ∈ Complex.slitPlane`, the principal-power series
`∑' n : ℕ, ‖(n + c) ^ (-s)‖` is summable. -/
theorem summable_norm_natCast_add_cpow_neg {s c : ℂ} (hs : 1 < s.re) (hc : c ∈ slitPlane) :
    Summable (fun n : ℕ => ‖((n : ℂ) + c) ^ (-s)‖) := by
  obtain ⟨U, hU, -, C, -, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hc (-s)
  have hp : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-s.re)) :=
    ((summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow (p := -s.re)).mpr (by linarith))).congr
      fun n => by push_cast; rw [add_comm]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hp.mul_left C)
  simpa only [ofReal_natCast, neg_re] using
    hbound c (mem_of_mem_nhds hU) (n : ℝ) (Nat.cast_nonneg n)

/-- For `1 < s.re` and `c ∈ Complex.slitPlane`, the complex Hurwitz series converges
absolutely. -/
theorem summable_norm_complexHurwitzSeries_term {s c : ℂ} (hs : 1 < s.re) (hc : c ∈ slitPlane) :
    Summable (fun n : ℕ => ‖Complex.exp (-s * Complex.log (n + c))‖) := by
  refine (summable_norm_natCast_add_cpow_neg hs hc).congr fun n => ?_
  have hne : (n : ℂ) + c ≠ 0 := by
    simpa using slitPlane_ne_zero (ofReal_add_mem_slitPlane hc (Nat.cast_nonneg n))
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- For `1 < s.re` and `c ∈ Complex.slitPlane`, the defining terms of `complexHurwitzSeries s c`
are summable. -/
theorem summable_complexHurwitzSeries_term {s c : ℂ} (hs : 1 < s.re) (hc : c ∈ slitPlane) :
    Summable (fun n : ℕ => Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_complexHurwitzSeries_term hs hc).of_norm

/-- For `1 < s.re` and `c ∈ Complex.slitPlane`, `n ↦ (n + c) ^ (-s)` is summable. -/
theorem summable_natCast_add_cpow_neg {s c : ℂ} (hs : 1 < s.re) (hc : c ∈ slitPlane) :
    Summable (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) :=
  (summable_norm_natCast_add_cpow_neg hs hc).of_norm

/-- On `1 < s.re` and `c ∈ Complex.slitPlane`, `n ↦ (n + c) ^ (-s)` has sum
`complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : c ∈ slitPlane) :
    HasSum (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) := by
  have hne : ∀ n : ℕ, c ≠ -(n : ℂ) := fun n h => by
    refine slitPlane_ne_zero (ofReal_add_mem_slitPlane hc (Nat.cast_nonneg n)) ?_
    simp [h]
  rw [complexHurwitzSeries_eq_tsum_cpow hne]
  exact (summable_natCast_add_cpow_neg hs hc).hasSum

/-- Shifting the complex Hurwitz parameter `c` by `1` removes the `n = 0` term `c ^ (-s)`. -/
theorem complexHurwitzSeries_add_one {s c : ℂ} (hs : 1 < s.re) (hc : c ∈ slitPlane) :
    complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s) := by
  have hc1 : c + 1 ∈ slitPlane := by
    simpa [add_comm] using ofReal_add_mem_slitPlane hc zero_le_one
  rw [← (hasSum_complexHurwitzSeries hs hc).tsum_eq,
    ← (hasSum_complexHurwitzSeries hs hc1).tsum_eq,
    (summable_natCast_add_cpow_neg hs hc).tsum_eq_zero_add]
  have hshift : (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) + c) ^ (-s)) =
      ∑' n : ℕ, ((n : ℂ) + (c + 1)) ^ (-s) :=
    tsum_congr fun n => by push_cast; ring_nf
  rw [Nat.cast_zero, zero_add, hshift, add_sub_cancel_left]

/-- For real `x ∈ (0, 1]` and `1 < s.re`, `complexHurwitzSeries s x` agrees with Mathlib's
circle-valued `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`. -/
theorem complexHurwitzSeries_ofReal_eq_hurwitzZeta {s : ℂ} {x : ℝ} (hs : 1 < s.re)
    (hx : x ∈ Ioc 0 1) :
    complexHurwitzSeries s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have h1 := hasSum_complexHurwitzSeries hs (ofReal_mem_slitPlane.mpr hx.1)
  have h2 := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (Ioc_subset_Icc_self hx) hs
  exact h1.unique (h2.congr_fun fun _ => by rw [cpow_neg, one_div])

/-- At `c = 1`, the complex Hurwitz series on `1 < s.re` equals `riemannZeta s`. -/
theorem complexHurwitzSeries_one {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  have h := complexHurwitzSeries_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

/-- At `(s, c) = (2, 1)`, the complex Hurwitz series evaluates to `π ^ 2 / 6`. -/
theorem complexHurwitzSeries_two_one :
    complexHurwitzSeries 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [complexHurwitzSeries_one (by norm_num), riemannZeta_two]

/-- At `c = 1 / 2` and `1 < s.re`, partitioning positive integers by parity yields
`complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzSeries_one_div_two {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hhalf_slit : (1 / 2 : ℂ) ∈ slitPlane := by
    simpa using ofReal_mem_slitPlane.mpr (by positivity : (0 : ℝ) < 1 / 2)
  have hzeta : HasSum (fun k : ℕ => ((k : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    rw [← complexHurwitzSeries_one hs]
    exact hasSum_complexHurwitzSeries hs (by simp)
  have heven : HasSum (fun k : ℕ => (((2 * k : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2)) :=
    ((hasSum_complexHurwitzSeries hs hhalf_slit).mul_left ((2 : ℂ) ^ (-s))).congr_fun fun k => by
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
  have hslit : (1 + I : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp))
  have hshift := complexHurwitzSeries_add_one (s := 2) (by norm_num) hslit
  have h2I : (1 + I : ℂ) + 1 = 2 + I := by ring
  have hsq : (1 + I : ℂ) ^ (2 : ℕ) = 2 * I := by rw [sq]; ring_nf; simp
  have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_cast
  rw [h2I] at hshift
  rw [hshift, sub_sub_cancel, cpow_neg, hcast, cpow_natCast, hsq, mul_inv, inv_I]
  ring

end TauCeti

end
