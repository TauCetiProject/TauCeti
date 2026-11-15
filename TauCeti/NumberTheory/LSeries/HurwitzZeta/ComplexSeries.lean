/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The complex-parameter Hurwitz zeta series

For a complex shift parameter `c` in the open right half-plane `0 < c.re` and complex exponent `s`
with `1 < s.re`, the Hurwitz zeta series

`complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c))`

converges absolutely using the principal complex logarithm `Complex.log`. Restricting `c` to the
open right half-plane keeps every translated base `n + c` away from the nonpositive real branch cut
and bounds its argument in `(-π/2, π/2)`, giving a uniform `p`-series majorant via
`TauCeti.exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow`.

Unlike Mathlib's periodic function `HurwitzZeta.hurwitzZeta : UnitAddCircle → ℂ → ℂ`, the
unperiodized series satisfies the shift identity
`complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s)`. Comparing `HasSum`
presentations with `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re` shows that it agrees with
`HurwitzZeta.hurwitzZeta c s` precisely for real parameters `c ∈ (0, 1]`; in particular, at `c = 1`
the circle parameter is `0 : UnitAddCircle` and the series reduces to `riemannZeta s`. Partitioning
residue classes modulo `N ≥ 1` expresses `ZMod.LFunction` and `DirichletCharacter.LFunction` as
finite linear combinations over `a ∈ [1, N]` of Hurwitz values at `a / N`.

## Main definitions and results

* `TauCeti.complexHurwitzSeries`: the unperiodized complex-parameter Hurwitz series
  `∑' n : ℕ, exp (-s * log (n + c))`.
* `TauCeti.summable_norm_exp_neg_mul_log_nat_add`, `TauCeti.hasSum_complexHurwitzSeries`: absolute
  convergence and `(n + c) ^ (-s)` series representation on `1 < s.re`, `0 < c.re`.
* `TauCeti.complexHurwitzSeries_add_one`, `TauCeti.complexHurwitzSeries_add_natCast`: shift
  identities in the parameter `c`.
* `TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta`, `TauCeti.complexHurwitzSeries_one`,
  `TauCeti.complexHurwitzSeries_one_half`: comparison with `HurwitzZeta.hurwitzZeta` on `(0, 1]`
  and specializations to `riemannZeta`.
* `ZMod.LFunction_eq_sum_Icc_hurwitzZeta`, `ZMod.LFunction_eq_sum_Icc_complexHurwitzSeries`,
  `DirichletCharacter.LFunction_eq_sum_Icc_hurwitzZeta`,
  `DirichletCharacter.LFunction_eq_sum_Icc_complexHurwitzSeries`: finite Hurwitz decomposition of
  congruence and Dirichlet `L`-functions over positive residue representatives `1, …, N`.

## References

* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I. Zeta integrals*, Forum Math. 24
  (2012), 1–48, §1.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  24 (2012), 49–84, §9.
* NIST Digital Library of Mathematical Functions, §25.11, <https://dlmf.nist.gov/25.11>.
-/

public section

open Complex Filter Real Set Topology
open scoped BigOperators

namespace TauCeti

/-- The complex-parameter Hurwitz zeta series `∑' n : ℕ, exp (-s * log (n + c))`, using the
principal branch `Complex.log` for each translated base `n + c`. It converges absolutely on the
product of half-planes `1 < s.re` and `0 < c.re`. -/
noncomputable def complexHurwitzSeries (s c : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c))

/-- Unfolding lemma for `complexHurwitzSeries`. -/
theorem complexHurwitzSeries_def (s c : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c)) := (rfl)

/-- On the right half-plane `0 < c.re`, the principal exponential term `exp (-s * log (n + c))`
coincides with the complex power `(n + c) ^ (-s)`. -/
theorem exp_neg_mul_log_nat_add_eq_cpow (s : ℂ) {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    Complex.exp (-s * Complex.log ((n : ℂ) + c)) = ((n : ℂ) + c) ^ (-s) := by
  have hne : (n : ℂ) + c ≠ 0 := by
    intro h
    have hre : 0 < ((n : ℂ) + c).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [h, zero_re] at hre
    exact lt_irrefl 0 hre
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- On `0 < c.re`, `complexHurwitzSeries s c` equals `∑' n : ℕ, (n + c) ^ (-s)`. -/
theorem complexHurwitzSeries_eq_tsum_cpow (s : ℂ) {c : ℂ} (hc : 0 < c.re) :
    complexHurwitzSeries s c = ∑' n : ℕ, ((n : ℂ) + c) ^ (-s) := by
  rw [complexHurwitzSeries_def]
  exact tsum_congr fun n ↦ exp_neg_mul_log_nat_add_eq_cpow s hc n

/-- The complex-parameter Hurwitz series converges absolutely for `1 < s.re` and `0 < c.re`. -/
theorem summable_norm_exp_neg_mul_log_nat_add {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    Summable fun n : ℕ ↦ ‖Complex.exp (-s * Complex.log ((n : ℂ) + c))‖ := by
  obtain ⟨U, hU, -, C, -, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow (Or.inl hc) (-s)
  have hp : Summable fun n : ℕ ↦ C * (1 + (n : ℝ)) ^ (-s.re) := by
    refine Summable.mul_left C ?_
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow (p := -s.re).mpr (by linarith))
    exact h.congr fun n ↦ by push_cast; ring_nf
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hp
  rw [exp_neg_mul_log_nat_add_eq_cpow s hc n]
  simpa [neg_re] using hbound c (mem_of_mem_nhds hU) n (Nat.cast_nonneg n)

/-- Summability of the defining Hurwitz terms on `1 < s.re` and `0 < c.re`. -/
theorem summable_exp_neg_mul_log_nat_add {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    Summable fun n : ℕ ↦ Complex.exp (-s * Complex.log ((n : ℂ) + c)) :=
  (summable_norm_exp_neg_mul_log_nat_add hs hc).of_norm

/-- Summability of `n ↦ (n + c) ^ (-s)` on `1 < s.re` and `0 < c.re`. -/
theorem summable_cpow_nat_add_neg {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    Summable fun n : ℕ ↦ ((n : ℂ) + c) ^ (-s) :=
  (summable_exp_neg_mul_log_nat_add hs hc).congr fun n ↦ exp_neg_mul_log_nat_add_eq_cpow s hc n

/-- `HasSum` presentation of `complexHurwitzSeries s c` as `∑ (n + c) ^ (-s)` on `1 < s.re`,
`0 < c.re`. -/
theorem hasSum_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    HasSum (fun n : ℕ ↦ ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) := by
  rw [complexHurwitzSeries_eq_tsum_cpow s hc]
  exact (summable_cpow_nat_add_neg hs hc).hasSum

/-- Separating the `n = 0` term from `complexHurwitzSeries s c` shifts `c` to `c + 1`. -/
theorem complexHurwitzSeries_eq_add_complexHurwitzSeries_add_one {s c : ℂ}
    (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzSeries s c = c ^ (-s) + complexHurwitzSeries s (c + 1) := by
  have hc1 : 0 < (c + 1).re := by simp [add_re]; linarith
  rw [complexHurwitzSeries_eq_tsum_cpow s hc, complexHurwitzSeries_eq_tsum_cpow s hc1,
    (summable_cpow_nat_add_neg hs hc).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add]
  congr 1
  refine tsum_congr fun n ↦ ?_
  congr 1
  push_cast
  ring

/-- The shift identity `ζ_H(s, c + 1) = ζ_H(s, c) - c ^ (-s)` on `1 < s.re`, `0 < c.re`. -/
theorem complexHurwitzSeries_add_one {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s) := by
  rw [complexHurwitzSeries_eq_add_complexHurwitzSeries_add_one hs hc]
  ring

/-- Iterated `N`-step parameter shift for `complexHurwitzSeries`. -/
theorem complexHurwitzSeries_add_natCast {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) (N : ℕ) :
    complexHurwitzSeries s c =
      (∑ k ∈ Finset.range N, ((k : ℂ) + c) ^ (-s)) + complexHurwitzSeries s (c + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hcN : 0 < (c + (N : ℂ)).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hsucc : c + ((N + 1 : ℕ) : ℂ) = c + (N : ℂ) + 1 := by push_cast; ring
    have hcomm : (N : ℂ) + c = c + (N : ℂ) := add_comm _ _
    rw [ih, hsucc, complexHurwitzSeries_eq_add_complexHurwitzSeries_add_one hs hcN,
      Finset.sum_range_succ, hcomm]
    ring

/-! ### Comparison with circle-valued Hurwitz and Riemann zeta functions -/

/-- For real `c ∈ (0, 1]` and `1 < s.re`, the complex Hurwitz series agrees with Mathlib's
circle-valued `HurwitzZeta.hurwitzZeta c s`. The lower endpoint `0` is excluded because the
unperiodized `n = 0` term uses `log 0 = 0`, whereas `HurwitzZeta.hurwitzZeta 0 s` omits `n = 0`. -/
theorem complexHurwitzSeries_ofReal_eq_hurwitzZeta {s : ℂ} {c : ℝ}
    (hs : 1 < s.re) (hc : c ∈ Ioc (0 : ℝ) 1) :
    complexHurwitzSeries s c = HurwitzZeta.hurwitzZeta c s := by
  have hc_re : 0 < (c : ℂ).re := by simpa using hc.1
  refine (hasSum_complexHurwitzSeries hs hc_re).unique ?_
  refine (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨hc.1.le, hc.2⟩ hs).congr_fun fun n ↦ ?_
  rw [one_div, cpow_neg]

/-- At `c = 1` and `1 < s.re`, `complexHurwitzSeries s 1` equals `riemannZeta s`. -/
theorem complexHurwitzSeries_one {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  have h := complexHurwitzSeries_ofReal_eq_hurwitzZeta (c := 1) hs
    (mem_Ioc.mpr ⟨zero_lt_one, le_rfl⟩)
  rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h
  simpa using h

/-- Special value check: `complexHurwitzSeries 2 1 = π ^ 2 / 6`. -/
theorem complexHurwitzSeries_two_one :
    complexHurwitzSeries 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [complexHurwitzSeries_one (by norm_num), riemannZeta_two]

/-- Complex-parameter shift check: `ζ_H(2, 1 + i) - ζ_H(2, 2 + i) = -i / 2`. -/
theorem complexHurwitzSeries_two_one_add_I_sub :
    complexHurwitzSeries 2 (1 + I) - complexHurwitzSeries 2 (2 + I) = -I / 2 := by
  have hc : 0 < (1 + I).re := by simp
  have h2 : (2 : ℂ) + I = (1 + I) + 1 := by ring
  rw [h2, complexHurwitzSeries_eq_add_complexHurwitzSeries_add_one (by norm_num) hc,
    add_sub_cancel_right]
  have hcpow : (1 + I) ^ (-2 : ℂ) = ((1 + I) ^ (2 : ℕ))⁻¹ := by
    rw [← cpow_natCast, Nat.cast_two, cpow_neg]
  rw [hcpow]
  have hsq : (1 + I) ^ (2 : ℕ) = 2 * I := by
    calc (1 + I) ^ (2 : ℕ) = 1 + 2 * I + I ^ 2 := by ring
      _ = 2 * I := by simp
  rw [hsq]
  field_simp [I_ne_zero]
  simp

end TauCeti

/-! ### Congruence and Dirichlet `L`-function Hurwitz decomposition -/

namespace ZMod

/-- Every congruence `L`-function `ZMod.LFunction Φ s` modulo `N ≥ 1` decomposes over the positive
residue representatives `a ∈ [1, N]` as `N ^ (-s) * ∑_{a = 1}^N Φ(a) ζ_H(a / N, s)`, including the
endpoint `a = N` where `a / N = 1 ≡ 0 (mod 1)`. -/
theorem LFunction_eq_sum_Icc_hurwitzZeta {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * HurwitzZeta.hurwitzZeta ((a : ℝ) / (N : ℝ)) s := by
  have hN : 0 < N := NeZero.pos N
  rw [ZMod.LFunction]
  congr 1
  symm
  refine Finset.sum_bij (fun a _ ↦ (a : ZMod N)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ h
    rw [Finset.mem_Icc] at ha₁ ha₂
    rcases eq_or_lt_of_le ha₁.2 with rfl | ha₁_lt <;>
      rcases eq_or_lt_of_le ha₂.2 with rfl | ha₂_lt
    · rfl
    · rw [natCast_self] at h
      have hv := congrArg ZMod.val h.symm
      rw [val_zero, val_natCast_of_lt ha₂_lt] at hv
      omega
    · rw [natCast_self] at h
      have hv := congrArg ZMod.val h
      rw [val_zero, val_natCast_of_lt ha₁_lt] at hv
      omega
    · have hv := congrArg ZMod.val h
      rwa [val_natCast_of_lt ha₁_lt, val_natCast_of_lt ha₂_lt] at hv
  · intro j _
    by_cases hj : j.val = 0
    · refine ⟨N, Finset.mem_Icc.mpr ⟨hN, le_rfl⟩, ?_⟩
      rw [natCast_self]
      exact (ZMod.val_eq_zero j).mp hj |>.symm
    · refine ⟨j.val, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hj, (val_lt j).le⟩, ?_⟩
      exact natCast_zmod_val j
  · intro a _
    rw [toAddCircle_natCast]

/-- On the convergence half-plane `1 < s.re`, `ZMod.LFunction Φ s` is a finite linear combination
of the unperiodized complex Hurwitz series at the rational shifts `a / N` for `1 ≤ a ≤ N`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzSeries {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : 1 < s.re) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) * ∑ a ∈ Finset.Icc 1 N,
        Φ a * TauCeti.complexHurwitzSeries s ((a : ℂ) / N) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [LFunction_eq_sum_Icc_hurwitzZeta]
  congr 1
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.mem_Icc] at ha
  have ha_mem : (a : ℝ) / (N : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨div_pos (Nat.cast_pos.mpr ha.1) hN, (div_le_one hN).mpr (by exact_mod_cast ha.2)⟩
  have hcast : (((a : ℝ) / (N : ℝ) : ℝ) : ℂ) = (a : ℂ) / N := by push_cast; rfl
  rw [← hcast, TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta hs ha_mem]

end ZMod

namespace DirichletCharacter

/-- Every Dirichlet `L`-function `χ.LFunction s` modulo `N ≥ 1` (primitive or imprimitive,
including principal characters) decomposes over `a ∈ [1, N]` into circle-Hurwitz zeta values. -/
theorem LFunction_eq_sum_Icc_hurwitzZeta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ.LFunction s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, χ a * HurwitzZeta.hurwitzZeta ((a : ℝ) / (N : ℝ)) s :=
  ZMod.LFunction_eq_sum_Icc_hurwitzZeta χ s

/-- On `1 < s.re`, `χ.LFunction s = N ^ (-s) * ∑_{a = 1}^N χ(a) ζ_H(s, a / N)` in terms of the
complex-parameter Hurwitz series. -/
theorem LFunction_eq_sum_Icc_complexHurwitzSeries {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s =
      (N : ℂ) ^ (-s) * ∑ a ∈ Finset.Icc 1 N,
        χ a * TauCeti.complexHurwitzSeries s ((a : ℂ) / N) :=
  ZMod.LFunction_eq_sum_Icc_complexHurwitzSeries χ hs

end DirichletCharacter

namespace TauCeti

/-- At `c = 1 / 2` and `1 < s.re`, `complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s`,
obtained from the modulus-`2` Hurwitz decomposition of `riemannZeta`. -/
theorem complexHurwitzSeries_one_half {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hZ := ZMod.LFunction_eq_sum_Icc_complexHurwitzSeries (N := 2) (fun _ ↦ (1 : ℂ)) hs
  have hL : ZMod.LFunction (fun _ : ZMod 2 ↦ (1 : ℂ)) s = riemannZeta s := by
    rw [ZMod.LFunction_eq_LSeries _ hs, ← LSeries_one_eq_riemannZeta hs]
    rfl
  have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [hL, hIcc, Finset.sum_pair (by decide)] at hZ
  simp only [one_mul, Nat.cast_one, Nat.cast_ofNat] at hZ
  have hdiv2 : ((2 : ℂ) / 2) = 1 := by norm_num
  rw [hdiv2, complexHurwitzSeries_one hs] at hZ
  have h2ne : (2 : ℂ) ^ s ≠ 0 := by
    rw [cpow_def_of_ne_zero two_ne_zero]
    exact Complex.exp_ne_zero _
  have hmul : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ h2ne]
  have hZ' := congrArg ((2 : ℂ) ^ s * ·) hZ
  rw [← mul_assoc, hmul, one_mul] at hZ'
  linear_combination -hZ'

end TauCeti
