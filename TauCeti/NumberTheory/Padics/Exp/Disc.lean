/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.Exp.Basic
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.UltrametricSubst
import Mathlib.Algebra.CharP.Algebra

/-!
# The exponential and the logarithm on the `p`-adic disc

Let `L` be a normed field that is a normed algebra over `ℚ_[p]`, for instance `ℂ_[p]` or a
finite extension of `ℚ_[p]`. Its norm is ultrametric, and Mathlib's exponential series converges
on the open disc `‖x‖ < r₀` of radius `r₀ = p ^ (-1 / (p - 1))`, which is
`TauCeti.amiceRadius p 0` (see `TauCeti.NumberTheory.Padics.Exp.Basic`). For complete `L`, on this
disc the exponential turns sums into products and preserves norms, `‖exp x - 1‖ = ‖x‖`
(`TauCeti.PadicExp.norm_exp_sub_one`), and Mathlib's logarithm series inverts it on the disc of
radius `r₀` about `1`. Hence the exponential maps the first disc bijectively onto the second: it
maps into the second disc by `TauCeti.PadicExp.norm_exp_sub_one`, it is injective by
`TauCeti.PadicExp.injOn_exp` (or via `TauCeti.log_exp_of_norm_lt`), and it is onto because
`TauCeti.norm_log_of_norm_sub_one_lt` puts `log y` in the first disc and
`TauCeti.exp_log_of_norm_sub_one_lt` gives `exp (log y) = y`.

The key estimate is the sharp factorial bound `r₀ ^ (n - 1) ≤ ‖n!‖` for `n ≥ 1`
(`TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial`): by Legendre's formula
`(p - 1) v_p(n!) = n - s_p(n)`, where the digit sum `s_p(n)` is at least one. Hence the
term `xⁿ / n!` has norm at most `‖x‖ (‖x‖ / r₀) ^ (n - 1)`, which is strictly smaller than `‖x‖`
for `n ≥ 2` and `x ≠ 0`. The bound is attained at every power of `p`, so the exponent `n - 1`
cannot be lowered; it is sharper than the bound `r₀ ^ n ≤ ‖n!‖` of
`TauCeti.amiceRadius_pow_le_norm_factorial`. Since `‖n‖ ≥ ‖n!‖`, the terms `zⁿ / n` of the
logarithm series obey the same bound. The two inverse identities evaluate the formal identities
`log (exp X) = X` and `exp (log (1 + X)) = 1 + X` through
`PowerSeries.eq_of_hasSum_of_subst_eq_X`.

The disc is open. At `p = 2` the point `2` has norm `r₀ = 1 / 2`, and the series diverges there.
Odd primes `p` lie strictly inside their disc (`TauCeti.inv_lt_amiceRadius_zero_iff`). The radius
of the inverse identity `exp (log y) = y` cannot be enlarged to the disc of convergence of the
logarithm: at `p = 2`, `y = -1` has `‖y - 1‖ = r₀` and `log (-1) = 0`.

Over `ℚ_[p]` itself, where nonzero norms are integral powers of `p`, the open disc is the closed
disc `‖x‖ ≤ p ^ (-i)` of the least depth `i` with `1 < (p - 1) i`
(`TauCeti.zpow_neg_lt_amiceRadius_zero`). The statements here hold in every normed field over
`ℚ_[p]`, including `ℂ_[p]`, which is not a finite extension of `ℚ_[p]`.

## Main results

* `TauCeti.norm_pow_div_natCast_le`: `‖zⁿ / n‖ ≤ ‖z‖ (‖z‖ / r₀) ^ (n - 1)` for `n ≠ 0`, the bound
  for the logarithm series.
* `TauCeti.hasSum_log_of_norm_sub_one_lt`: for `‖y - 1‖ < r₀`,
  `log y = ∑ (-1) ^ (n + 1) (y - 1) ^ n / n`.
* `TauCeti.norm_log_of_norm_sub_one_lt`: `‖log y‖ = ‖y - 1‖`.
* `TauCeti.log_exp_of_norm_lt`, `TauCeti.exp_log_of_norm_sub_one_lt`: the exponential and the
  logarithm are inverse.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Chapter IV, §1.
-/

public section

open NormedSpace
open scoped Nat

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]

/-- **The terms of the logarithm series on the disc of radius `r₀`.** For `n ≠ 0`,
`‖zⁿ / n‖ ≤ ‖z‖ (‖z‖ / r₀) ^ (n - 1)`. -/
theorem norm_pow_div_natCast_le (z : L) {n : ℕ} (hn : n ≠ 0) :
    ‖z ^ n / (n : L)‖ ≤ ‖z‖ * (‖z‖ / amiceRadius p 0) ^ (n - 1) :=
  norm_pow_div_le_of_le_norm z hn (amiceRadius_zero_pow_sub_one_le_norm_natCast hn)

variable [CompleteSpace L]

omit [CompleteSpace L] in
/-- A convergent series `∑ tₙ` with `t₀ = 0` and `t₁ = z ≠ 0`, whose later terms satisfy
`‖tₙ‖ ≤ ‖z‖ (‖z‖ / r₀) ^ (n - 1)` with `‖z‖ < r₀`, has sum of norm `‖z‖`: every term of degree at
least two is strictly smaller than `z`. -/
private theorem norm_eq_of_hasSum {t : ℕ → L} {s z : L} (hs : HasSum t s) (h0 : t 0 = 0)
    (h1 : t 1 = z) (hz : ‖z‖ < amiceRadius p 0)
    (ht : ∀ n, ‖t (n + 2)‖ ≤ ‖z‖ * (‖z‖ / amiceRadius p 0) ^ (n + 1)) : ‖s‖ = ‖z‖ := by
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  have hr := amiceRadius_pos (p := p) 0
  have hq : ‖z‖ / amiceRadius p 0 < 1 := (div_lt_one hr).mpr hz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [norm_zero, norm_eq_zero]
    refine hs.unique (hasSum_zero.congr_fun fun n ↦ ?_)
    rcases n with _ | _ | n
    · exact h0
    · exact h1
    · exact norm_le_zero_iff.mp (by simpa using ht n)
  -- The tail `∑_{n ≥ 2} tₙ` is `s - z`, and it is strictly smaller than `z`.
  have htail := (hasSum_nat_add_iff' (f := t) 2).mpr hs
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1, zero_add] at htail
  have hT : ‖s - z‖ ≤ ‖z‖ * (‖z‖ / amiceRadius p 0) := by
    rw [← htail.tsum_eq]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦ ?_
    exact (ht n).trans (mul_le_mul_of_nonneg_left
      (pow_le_of_le_one (by positivity) hq.le (by omega)) (norm_nonneg z))
  have hlt : ‖s - z‖ < ‖z‖ := hT.trans_lt (mul_lt_of_lt_one_right (norm_pos_iff.mpr hz0) hq)
  rw [← sub_add_cancel s z, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
    max_eq_left hlt.le]

/-- The coefficients of `exp - 1` give the series of `exp x - 1` on the disc. -/
private theorem hasSum_exp_sub_one {x : L} (hx : ‖x‖ < amiceRadius p 0) :
    HasSum (fun n ↦ if n = 0 then 0 else x ^ n / (n ! : L)) (exp x - 1) := by
  convert (TauCeti.PadicExp.hasSum_exp hx).sub (hasSum_ite_eq 0 (1 : L)) using 1
  funext n
  split_ifs with hn <;> simp [hn]

omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L] in
/-- The sign of a term of the logarithm series does not change its norm. -/
private theorem norm_neg_one_pow_mul_div (n : ℕ) (z c : L) :
    ‖(-1) ^ (n + 1) * z ^ n / c‖ = ‖z ^ n / c‖ := by
  simp [mul_div_assoc]

/-- **The logarithm series on the disc of radius `r₀` about `1`.** For `‖y - 1‖ < r₀`,
`log y = ∑ (-1) ^ (n + 1) (y - 1) ^ n / n`. -/
theorem hasSum_log_of_norm_sub_one_lt {y : L} (hy : ‖y - 1‖ < amiceRadius p 0) :
    HasSum (fun n : ℕ ↦ (-1) ^ (n + 1) * (y - 1) ^ n / (n : L)) (log y) := by
  have hr := amiceRadius_pos (p := p) 0
  have hq0 : 0 ≤ ‖y - 1‖ / amiceRadius p 0 := by positivity
  have hq : ‖y - 1‖ / amiceRadius p 0 < 1 := (div_lt_one hr).mpr hy
  -- The terms are bounded by the geometric sequence `r₀ (‖y - 1‖ / r₀) ^ n`.
  have hsum : Summable fun n : ℕ ↦ (-1) ^ (n + 1) * (y - 1) ^ n / (n : L) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq).mul_left
      (amiceRadius p 0)) fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using hr.le
    rw [norm_neg_one_pow_mul_div]
    refine (norm_pow_div_natCast_le (p := p) (y - 1) hn).trans_eq ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, _root_.pow_succ', ← mul_assoc, mul_div_cancel₀ _ hr.ne']
  convert hsum.hasSum using 1
  rw [log_eq_tsum ℚ_[p]]
  refine tsum_congr fun n ↦ ?_
  simp only [Algebra.smul_def, map_div₀, map_pow, map_neg, map_one, map_natCast,
    div_mul_eq_mul_div]

/-- **The `p`-adic logarithm preserves norms on the disc of radius `r₀` about `1`.** For
`‖y - 1‖ < r₀`, `‖log y‖ = ‖y - 1‖`. -/
theorem norm_log_of_norm_sub_one_lt {y : L} (hy : ‖y - 1‖ < amiceRadius p 0) :
    ‖log y‖ = ‖y - 1‖ :=
  norm_eq_of_hasSum (hasSum_log_of_norm_sub_one_lt hy) (by simp) (by simp) hy fun n ↦ by
    rw [norm_neg_one_pow_mul_div]
    simpa using norm_pow_div_natCast_le (p := p) (y - 1) (n := n + 2) (by omega)

omit [CompleteSpace L] in
/-- The coefficients of the formal series `exp - 1` satisfy `‖cₙ‖ r₀ ^ (n - 1) ≤ 1`. -/
private theorem norm_coeff_exp_sub_one_mul_le [CharZero L] (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.exp L - 1)‖ * amiceRadius p 0 ^ (n - 1) ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hf := amiceRadius_zero_pow_sub_one_le_norm_factorial (p := p) (L := L) hn
  rw [PowerSeries.coeff_exp_sub_one_of_ne_zero hn, norm_inv, ← div_eq_inv_mul]
  exact div_le_one_of_le₀ hf (norm_nonneg _)

omit [CompleteSpace L] in
/-- The coefficients of the formal logarithm series satisfy `‖cₙ‖ r₀ ^ (n - 1) ≤ 1`. -/
private theorem norm_coeff_log_mul_le [CharZero L] (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.log L)‖ * amiceRadius p 0 ^ (n - 1) ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hf := amiceRadius_zero_pow_sub_one_le_norm_natCast (p := p) (L := L) hn
  rw [PowerSeries.coeff_log_eq_neg_one_pow_div]
  simpa [div_eq_inv_mul] using div_le_one_of_le₀ hf (norm_nonneg _)

/-- The series of `exp x - 1` on the disc, with the coefficients of the formal series `exp - 1`. -/
private theorem hasSum_coeff_exp_sub_one_mul_pow [CharZero L] {x : L}
    (hx : ‖x‖ < amiceRadius p 0) :
    HasSum (fun n ↦ PowerSeries.coeff n (PowerSeries.exp L - 1) * x ^ n) (exp x - 1) :=
  (hasSum_exp_sub_one hx).congr_fun fun n ↦ PowerSeries.coeff_exp_sub_one_mul_pow n x

/-- The series of `log y` on the disc about `1`, with the coefficients of the formal logarithm. -/
private theorem hasSum_coeff_log_mul_pow [CharZero L] {y : L}
    (hy : ‖y - 1‖ < amiceRadius p 0) :
    HasSum (fun n ↦ PowerSeries.coeff n (PowerSeries.log L) * (y - 1) ^ n) (log y) := by
  refine (hasSum_log_of_norm_sub_one_lt hy).congr_fun fun n ↦ ?_
  rw [PowerSeries.coeff_log_eq_neg_one_pow_div, div_mul_eq_mul_div]

/-- **The logarithm inverts the exponential on its disc.** For `‖x‖ < r₀`, `log (exp x) = x`. -/
theorem log_exp_of_norm_lt {x : L} (hx : ‖x‖ < amiceRadius p 0) : log (exp x) = x := by
  -- The formal series live over the `ℚ`-algebra structure of the characteristic-zero field `L`.
  have := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  have hy : ‖exp x - 1‖ < amiceRadius p 0 := by rwa [TauCeti.PadicExp.norm_exp_sub_one hx]
  refine PowerSeries.eq_of_hasSum_of_subst_eq_X (f := PowerSeries.log L)
    (g := PowerSeries.exp L - 1) (by simp) (PowerSeries.subst_log_exp_sub_one L)
    norm_coeff_log_mul_le norm_coeff_exp_sub_one_mul_le hx (hasSum_coeff_exp_sub_one_mul_pow hx)
    (by simpa using hasSum_coeff_log_mul_pow (p := p) (y := exp x) (by simpa using hy))

/-- **The exponential inverts the logarithm on the disc of radius `r₀` about `1`.** For
`‖y - 1‖ < r₀`, `exp (log y) = y`. -/
theorem exp_log_of_norm_sub_one_lt {y : L} (hy : ‖y - 1‖ < amiceRadius p 0) :
    exp (log y) = y := by
  have := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  have hl : ‖log y‖ < amiceRadius p 0 := by rwa [norm_log_of_norm_sub_one_lt hy]
  have hfg : (PowerSeries.exp L - 1).subst (PowerSeries.log L) = PowerSeries.X := by
    rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, PowerSeries.subst_exp_log,
      PowerSeries.subst_one, add_sub_cancel_left]
  exact sub_left_injective <| PowerSeries.eq_of_hasSum_of_subst_eq_X (by simp) hfg
    norm_coeff_exp_sub_one_mul_le norm_coeff_log_mul_le hy (hasSum_coeff_log_mul_pow hy)
    (hasSum_coeff_exp_sub_one_mul_pow hl)

end TauCeti
