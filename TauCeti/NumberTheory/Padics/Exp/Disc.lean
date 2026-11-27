/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.NumberTheory.Padics.AddChar
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Normed.Algebra.Logarithm.Basic
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.Polynomial.Ultra
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.UltrametricSubst

/-!
# The exponential and the logarithm on the `p`-adic disc

Let `A` be a complete ultrametric normed algebra over `ℚ_[p]`: its norm is submultiplicative but
need not be multiplicative, and `A` need not be a field or even commutative. Examples are `ℂ_[p]`
and the finite extensions of `ℚ_[p]`, but also Banach algebras such as affinoid algebras and
algebras of continuous functions on a compact space with the supremum norm. Mathlib's exponential
series converges on the open disc `‖x‖ < r₀` of radius `r₀ = p ^ (-1 / (p - 1))`, which is
`TauCeti.amiceRadius p 0`, and Mathlib's logarithm series converges on the open unit disc
`‖y - 1‖ < 1` about `1`. On the disc of radius `r₀` the exponential preserves norms,
`‖exp x - 1‖ = ‖x‖`, the logarithm preserves norms, `‖log y‖ = ‖y - 1‖`, and the two are inverse to
each other. Hence the exponential maps the first disc bijectively onto the disc of radius `r₀` about
`1`: it maps into it by `TauCeti.norm_exp_sub_one_of_norm_lt`, it is injective by
`TauCeti.injOn_exp_ball` (via `TauCeti.log_exp_of_norm_lt`), and it is onto because
`TauCeti.norm_log_of_norm_sub_one_lt` puts `log y` in the first disc and
`TauCeti.exp_log_of_norm_sub_one_lt` gives `exp (log y) = y`.

On these discs, the exponential turns sums of commuting elements into products and the logarithm
turns products of commuting elements into sums. For `‖t‖ < r₀`, the continuous additive character
`x ↦ (1 + t) ^ x` of `ℤ_p` (Mathlib's `PadicInt.addChar_of_value_at_one`) is then
`x ↦ exp (x log (1 + t))`: both sides are continuous in `x` and equal `(1 + t) ^ n` at natural
numbers `n`, which are dense in `ℤ_p`. In particular `‖(1 + t) ^ x - 1‖ = ‖x‖ ‖t‖` in every such
`A`.

The key estimate is the sharp factorial bound `r₀ ^ (n - 1) ≤ ‖n!‖` for `n ≥ 1`
(`TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial`): by Legendre's formula
`(p - 1) v_p(n!) = n - s_p(n)`, where the digit sum `s_p(n)` is at least one. With the
submultiplicativity of the norm, the term `xⁿ / n!` has norm at most `‖x‖ (‖x‖ / r₀) ^ (n - 1)`,
which is strictly smaller than `‖x‖` for `n ≥ 2` and `x ≠ 0`. The ultrametric inequality then
gives the norm identities without any multiplicativity of the norm. The bound is attained at every
power of `p`, so the exponent `n - 1` cannot be lowered; it is sharper than the bound
`r₀ ^ n ≤ ‖n!‖` of `TauCeti.amiceRadius_pow_le_norm_factorial`. Since `‖n‖ ≥ ‖n!‖`, the terms
`zⁿ / n` of the logarithm series obey the same bound. The convergence of the logarithm series on
`‖z‖ < 1` (`NormedSpace.hasSum_log_of_norm_sub_one_lt_one`) and `exp (n • x) = exp x ^ n` need no
ultrametric hypothesis on `A`. The two inverse
identities evaluate the formal identities `log (exp X) = X` and `exp (log (1 + X)) = 1 + X`
through `PowerSeries.eq_of_hasSum_of_subst_eq_X`.

The disc is open. At `p = 2` the point `2` has norm `r₀ = 1 / 2`, and the series diverges there.
Odd primes `p` lie strictly inside their disc (`TauCeti.inv_lt_amiceRadius_zero_iff`). The radius
of the inverse identity `exp (log y) = y` cannot be enlarged to the disc of convergence of the
logarithm: at `p = 2`, `y = -1` has `‖y - 1‖ = r₀` and `log (-1) = 0`.

Over `ℚ_[p]` itself, where nonzero norms are integral powers of `p`, the open disc is the closed
disc `‖x‖ ≤ p ^ (-i)` of the least depth `i` with `1 < (p - 1) i`
(`TauCeti.zpow_neg_lt_amiceRadius_zero`).

## Main results

* `TauCeti.norm_inv_factorial_smul_pow_le`: `‖xⁿ / n!‖ ≤ ‖x‖ (‖x‖ / r₀) ^ (n - 1)` for `n ≠ 0`.
* `TauCeti.ofReal_amiceRadius_zero_le_radius_expSeries`: the exponential series converges on
  the disc of radius `r₀`.
* `TauCeti.expSeries_hasSum_exp_of_norm_lt`: on that disc, `exp x = ∑ xⁿ / n!`.
* `TauCeti.exp_add_of_commute_of_norm_lt`, `TauCeti.exp_sum_of_commute_of_norm_lt`: the
  functional equation for commuting elements, with the commutative forms
  `TauCeti.exp_add_of_norm_lt`, `TauCeti.exp_sum_of_norm_lt`.
* `TauCeti.exp_nsmul_of_norm_lt`, `TauCeti.exp_zsmul_of_norm_lt`: `exp (n • x) = exp x ^ n`.
* `TauCeti.norm_exp_sub_one_of_norm_lt`: `‖exp x - 1‖ = ‖x‖`.
* `TauCeti.norm_exp_of_norm_lt`: `‖exp x‖ = 1`.
* `TauCeti.norm_neg_one_pow_div_natCast_smul_pow_le`: the corresponding bound for the logarithm
  series.
* `TauCeti.norm_log_of_norm_sub_one_lt`: `‖log y‖ = ‖y - 1‖`.
* `TauCeti.log_exp_of_norm_lt`, `TauCeti.exp_log_of_norm_sub_one_lt`: the exponential and the
  logarithm are inverse.
* `TauCeti.injOn_exp_ball`: the exponential is injective on the disc.
* `TauCeti.log_mul_of_commute_of_norm_sub_one_lt`, `TauCeti.log_mul_of_norm_sub_one_lt`:
  `log (y * w) = log y + log w` for commuting `y` and `w`.
* `TauCeti.addChar_of_value_at_one_eq_exp_smul_log`: `(1 + t) ^ x = exp (x log (1 + t))`.
* `TauCeti.norm_addChar_of_value_at_one_sub_one`: `‖(1 + t) ^ x - 1‖ = ‖x‖ ‖t‖`.
* `TauCeti.norm_sum_intCast_mul_log_lt`, `Finset.exp_sum_intCast_mul_log`: for units `αⱼ` in
  the disc about `1` and integers `nⱼ`, `∑ⱼ nⱼ log αⱼ` lies in the disc and
  `exp (∑ⱼ nⱼ log αⱼ) = ∏ⱼ αⱼ ^ nⱼ`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Chapter IV, §1.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Series 320 (2007), §8.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.6.
-/

public section

open NormedSpace Filter Topology
open scoped Nat

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The exponential series converges on the disc of radius `r₀ = p ^ (-1 / (p - 1))`** in
every normed algebra over `ℚ_[p]`. -/
theorem ofReal_amiceRadius_zero_le_radius_expSeries {L : Type*} [NormedRing L]
    [NormedAlgebra ℚ_[p] L] :
    ENNReal.ofReal (amiceRadius p 0) ≤ (expSeries ℚ_[p] L).radius := by
  have hr := amiceRadius_pos (p := p) 0
  rw [ENNReal.ofReal_eq_coe_nnreal hr.le]
  refine FormalMultilinearSeries.le_radius_of_bound _
    (max ‖expSeries ℚ_[p] L 0‖ (amiceRadius p 0)) fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine le_max_of_le_right ?_
  rw [expSeries_eq_ofScalars, NNReal.coe_mk]
  refine (mul_le_mul_of_nonneg_right (FormalMultilinearSeries.ofScalars_norm_le _ _ _
    (Nat.pos_of_ne_zero hn)) (by positivity)).trans ?_
  -- `‖n!⁻¹‖ r₀ⁿ ≤ r₀ⁿ / r₀ ^ (n - 1) = r₀`
  have hf := amiceRadius_zero_pow_sub_one_le_norm_factorial (p := p) (L := ℚ_[p]) hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hf
  rw [norm_inv, inv_mul_le_iff₀ ((pow_pos hr m).trans_le hf), _root_.pow_succ]
  exact mul_le_mul_of_nonneg_right hf hr.le

/-- The coefficients of the formal series `exp - 1` over `ℚ_[p]` satisfy
`‖cₙ‖ r₀ ^ (n - 1) ≤ 1`. -/
private theorem norm_coeff_exp_sub_one_mul_le (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.exp ℚ_[p] - 1)‖ * amiceRadius p 0 ^ (n - 1) ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hf := amiceRadius_zero_pow_sub_one_le_norm_factorial (p := p) (L := ℚ_[p]) hn
  rw [PowerSeries.coeff_exp_sub_one_of_ne_zero hn, norm_inv, ← div_eq_inv_mul]
  exact div_le_one_of_le₀ hf (norm_nonneg _)

/-- The coefficients of the formal logarithm series over `ℚ_[p]` satisfy
`‖cₙ‖ r₀ ^ (n - 1) ≤ 1`. -/
private theorem norm_coeff_log_mul_le (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.log ℚ_[p])‖ * amiceRadius p 0 ^ (n - 1) ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hf := amiceRadius_zero_pow_sub_one_le_norm_natCast (p := p) (L := ℚ_[p]) hn
  rw [PowerSeries.coeff_log_eq_neg_one_pow_div]
  simpa [div_eq_inv_mul] using div_le_one_of_le₀ hf (norm_nonneg _)

section NormedRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]

/-- If `‖c‖ r₀ ^ (n - 1) ≤ 1`, then `‖c • xⁿ‖ ≤ ‖x‖ (‖x‖ / r₀) ^ (n - 1)` for `n ≠ 0`. -/
private theorem norm_smul_pow_le_of_norm_mul_le (x : A) {c : ℚ_[p]} {n : ℕ} (hn : n ≠ 0)
    (hc : ‖c‖ * amiceRadius p 0 ^ (n - 1) ≤ 1) :
    ‖c • x ^ n‖ ≤ ‖x‖ * (‖x‖ / amiceRadius p 0) ^ (n - 1) := by
  have hr := amiceRadius_pos (p := p) 0
  refine (norm_smul_pow_le_mul_div_pow hr hn
    (norm_mul_pow_le_of_norm_mul_pow_sub_one_le hr.le (absurd · hn) hc) x).trans_eq ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, _root_.pow_succ]
  field_simp

/-- **The terms of the exponential series on its disc.** For `n ≠ 0`,
`‖xⁿ / n!‖ ≤ ‖x‖ (‖x‖ / r₀) ^ (n - 1)`. When `‖x‖ < r₀` the terms decay geometrically, and every
term of degree at least two is strictly smaller than a nonzero `x`. -/
theorem norm_inv_factorial_smul_pow_le (x : A) {n : ℕ} (hn : n ≠ 0) :
    ‖(n ! : ℚ_[p])⁻¹ • x ^ n‖ ≤ ‖x‖ * (‖x‖ / amiceRadius p 0) ^ (n - 1) := by
  have hc := norm_coeff_exp_sub_one_mul_le (p := p) n
  rw [PowerSeries.coeff_exp_sub_one_of_ne_zero hn] at hc
  exact norm_smul_pow_le_of_norm_mul_le x hn hc

/-- **The terms of the logarithm series on the disc of radius `r₀`.** For `n ≠ 0`,
`‖(-1) ^ (n + 1) zⁿ / n‖ ≤ ‖z‖ (‖z‖ / r₀) ^ (n - 1)`. -/
theorem norm_neg_one_pow_div_natCast_smul_pow_le (z : A) {n : ℕ} (hn : n ≠ 0) :
    ‖((-1) ^ (n + 1) / n : ℚ_[p]) • z ^ n‖ ≤ ‖z‖ * (‖z‖ / amiceRadius p 0) ^ (n - 1) := by
  have hc := norm_coeff_log_mul_le (p := p) n
  rw [PowerSeries.coeff_log_eq_neg_one_pow_div] at hc
  exact norm_smul_pow_le_of_norm_mul_le z hn hc

/-- A point of the disc `‖x‖ < r₀` lies in the ball of convergence of the exponential series. -/
private theorem mem_eball_radius_expSeries {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    x ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius := by
  refine lt_of_lt_of_le ?_ ofReal_amiceRadius_zero_le_radius_expSeries
  rw [edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff (amiceRadius_pos 0)).mpr hx

/-- For `‖x‖ < r₀` and every natural number `n`, `‖n • x‖ < r₀`. -/
private theorem norm_nsmul_lt_amiceRadius {x : A} (hx : ‖x‖ < amiceRadius p 0) (n : ℕ) :
    ‖n • x‖ < amiceRadius p 0 := by
  rw [← Nat.cast_smul_eq_nsmul ℚ_[p]]
  exact (norm_smul_le _ _).trans_lt <| (mul_le_of_le_one_left (norm_nonneg _)
    (IsUltrametricDist.norm_natCast_le_one ℚ_[p] n)).trans_lt hx

variable [CompleteSpace A]

/-- **The exponential as a series on its disc.** For `‖x‖ < r₀`, `exp x = ∑ xⁿ / n!`. -/
theorem expSeries_hasSum_exp_of_norm_lt {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    HasSum (fun n ↦ (n ! : ℚ_[p])⁻¹ • x ^ n) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball' x (mem_eball_radius_expSeries hx)

/-- **The functional equation of the `p`-adic exponential for commuting elements.** If `x` and `y`
commute and `‖x‖, ‖y‖ < r₀`, then `exp (x + y) = exp x * exp y`. -/
theorem exp_add_of_commute_of_norm_lt {x y : A} (hxy : Commute x y)
    (hx : ‖x‖ < amiceRadius p 0) (hy : ‖y‖ < amiceRadius p 0) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℚ_[p]) hxy (mem_eball_radius_expSeries hx)
    (mem_eball_radius_expSeries hy)

/-- The series of `exp x - 1` on the disc, with the coefficients of the formal series `exp - 1`. -/
private theorem hasSum_exp_sub_one {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    HasSum (fun n ↦ PowerSeries.coeff n (PowerSeries.exp ℚ_[p] - 1) • x ^ n) (exp x - 1) := by
  convert (expSeries_hasSum_exp_of_norm_lt hx).sub (hasSum_ite_eq 0 (1 : A)) using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, PowerSeries.coeff_exp_sub_one_of_ne_zero hn]

/-- For `‖x‖ < r₀` and every natural number `n`, `exp (n • x) = exp x ^ n`. -/
theorem exp_nsmul_of_norm_lt (n : ℕ) {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih =>
    rw [succ_nsmul, pow_succ, exp_add_of_commute_of_norm_lt ((Commute.refl x).smul_left n)
      (norm_nsmul_lt_amiceRadius hx n) hx, ih]

variable [IsUltrametricDist A]

omit [NormedAlgebra ℚ_[p] A] [CompleteSpace A] in
/-- A convergent series `∑ tₙ` with `t₀ = 0` and `t₁ = z`, whose later terms satisfy
`‖tₙ‖ ≤ ‖z‖ (‖z‖ / r₀) ^ (n - 1)` with `‖z‖ < r₀`, has sum of norm `‖z‖`: every term of degree at
least two is strictly smaller than a nonzero `z`. -/
private theorem norm_eq_of_hasSum {t : ℕ → A} {s z : A} (hs : HasSum t s) (h0 : t 0 = 0)
    (h1 : t 1 = z) (hz : ‖z‖ < amiceRadius p 0)
    (ht : ∀ n, ‖t (n + 2)‖ ≤ ‖z‖ * (‖z‖ / amiceRadius p 0) ^ (n + 1)) : ‖s‖ = ‖z‖ := by
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

/-- **The `p`-adic exponential preserves norms on its disc.** For `‖x‖ < r₀`,
`‖exp x - 1‖ = ‖x‖`: every term `xⁿ / n!` of degree `n ≥ 2` is strictly smaller than `x`. -/
theorem norm_exp_sub_one_of_norm_lt {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    ‖exp x - 1‖ = ‖x‖ :=
  norm_eq_of_hasSum (hasSum_exp_sub_one hx) (by simp)
    (by simp [PowerSeries.coeff_exp_sub_one_of_ne_zero]) hx fun n ↦ by
      simpa using norm_smul_pow_le_of_norm_mul_le x (n := n + 2) (by omega)
        (norm_coeff_exp_sub_one_mul_le (n + 2))

/-- For `‖x‖ < r₀`, the exponential `exp x` has norm one. -/
theorem norm_exp_of_norm_lt [NormOneClass A] {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    ‖exp x‖ = 1 := by
  refine norm_eq_one_of_norm_one_sub_lt_one ?_
  rw [norm_sub_rev, norm_exp_sub_one_of_norm_lt hx]
  exact hx.trans (amiceRadius_lt_one 0)

/-- The series of `log y` on the open unit disc about `1`, with the coefficients of the formal
logarithm. -/
private theorem hasSum_coeff_log_smul_pow {y : A} (hy : ‖y - 1‖ < 1) :
    HasSum (fun n ↦ PowerSeries.coeff n (PowerSeries.log ℚ_[p]) • (y - 1) ^ n) (log y) := by
  simpa only [PowerSeries.coeff_log_eq_neg_one_pow_div] using
    hasSum_log_of_norm_sub_one_lt_one ℚ_[p] hy

/-- **The `p`-adic logarithm preserves norms on the disc of radius `r₀` about `1`.** For
`‖y - 1‖ < r₀`, `‖log y‖ = ‖y - 1‖`. -/
theorem norm_log_of_norm_sub_one_lt {y : A} (hy : ‖y - 1‖ < amiceRadius p 0) :
    ‖log y‖ = ‖y - 1‖ :=
  norm_eq_of_hasSum (hasSum_log_of_norm_sub_one_lt_one ℚ_[p] (hy.trans (amiceRadius_lt_one 0)))
    (by simp) (by simp) hy fun n ↦ by
      simpa using norm_neg_one_pow_div_natCast_smul_pow_le (p := p) (y - 1) (n := n + 2) (by omega)

/-- **The logarithm inverts the exponential on its disc.** For `‖x‖ < r₀`, `log (exp x) = x`. -/
theorem log_exp_of_norm_lt {x : A} (hx : ‖x‖ < amiceRadius p 0) : log (exp x) = x := by
  have hy : ‖exp x - 1‖ < 1 := by
    rw [norm_exp_sub_one_of_norm_lt hx]
    exact hx.trans (amiceRadius_lt_one 0)
  exact PowerSeries.eq_of_hasSum_of_subst_eq_X (by simp)
    (PowerSeries.subst_log_exp_sub_one ℚ_[p])
    norm_coeff_log_mul_le norm_coeff_exp_sub_one_mul_le hx (hasSum_exp_sub_one hx)
    (hasSum_coeff_log_smul_pow (p := p) hy)

/-- **The exponential inverts the logarithm on the disc of radius `r₀` about `1`.** For
`‖y - 1‖ < r₀`, `exp (log y) = y`. -/
theorem exp_log_of_norm_sub_one_lt {y : A} (hy : ‖y - 1‖ < amiceRadius p 0) :
    exp (log y) = y := by
  have hl : ‖log y‖ < amiceRadius p 0 := by rwa [norm_log_of_norm_sub_one_lt hy]
  have hfg : (PowerSeries.exp ℚ_[p] - 1).subst (PowerSeries.log ℚ_[p]) = PowerSeries.X := by
    rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, PowerSeries.subst_exp_log,
      PowerSeries.subst_one, add_sub_cancel_left]
  exact sub_left_injective <| PowerSeries.eq_of_hasSum_of_subst_eq_X (by simp) hfg
    norm_coeff_exp_sub_one_mul_le norm_coeff_log_mul_le hy
    (hasSum_coeff_log_smul_pow (p := p) (hy.trans (amiceRadius_lt_one 0))) (hasSum_exp_sub_one hl)

/-- **Integer combinations of logarithms stay in the disc.** If `0 < r ≤ r₀` and
`‖αⱼ - 1‖ < r` for every `j ∈ s`, then `‖∑ⱼ nⱼ log αⱼ‖ < r` for all integers `nⱼ`. -/
theorem norm_sum_intCast_mul_log_lt {ι : Type*} {s : Finset ι} {α : ι → A} {r : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ amiceRadius p 0) (hα : ∀ j ∈ s, ‖α j - 1‖ < r) (n : ι → ℤ) :
    ‖∑ j ∈ s, (n j : A) * log (α j)‖ < r := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using hr
  obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    fun j ↦ (n j : A) * log (α j)
  rw [← zsmul_eq_mul] at hle
  refine (hle.trans (IsUltrametricDist.norm_zsmul_le _ _)).trans_lt ?_
  rw [norm_log_of_norm_sub_one_lt ((hα j hj).trans_le hr₀)]
  exact hα j hj

/-- **The `p`-adic exponential is injective on its disc** `‖x‖ < r₀`: the logarithm is a left
inverse there. -/
theorem injOn_exp_ball : Set.InjOn (exp : A → A) (Metric.ball 0 (amiceRadius p 0)) :=
  fun x hx y hy hxy ↦ by
    rw [mem_ball_zero_iff] at hx hy
    rw [← log_exp_of_norm_lt hx, hxy, log_exp_of_norm_lt hy]

open scoped Function in
/-- The functional equation for finite sums of pairwise commuting elements: if the `f i` commute
pairwise and `‖f i‖ < r₀` for every `i ∈ s`, then `exp (∑ i ∈ s, f i)` is the product of the
`exp (f i)`. -/
theorem exp_sum_of_commute_of_norm_lt {ι : Type*} (s : Finset ι) {f : ι → A}
    (h : (s : Set ι).Pairwise (Commute on f)) (hf : ∀ i ∈ s, ‖f i‖ < amiceRadius p 0) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i ↦ exp (f i)) (h.mono' fun _ _ hij ↦ Commute.exp hij) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [exp_zero]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ‖f i‖ < amiceRadius p 0 := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hsum : ‖∑ i ∈ s, f i‖ < amiceRadius p 0 := by
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simpa using amiceRadius_pos (p := p) 0
      obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      exact hle.trans_lt (hs i hi)
    have hcomm : Commute (f a) (∑ i ∈ s, f i) := Commute.sum_right _ _ _ fun i hi ↦
      h.forall₂ (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.sum_insert ha,
      exp_add_of_commute_of_norm_lt hcomm (hf a (Finset.mem_insert_self a s)) hsum,
      ih (h.mono <| Finset.subset_insert _ _) hs]

/-- **The logarithm turns products of commuting elements into sums on the disc of radius `r₀`
about `1`.** If `y` and `w` commute, `‖y - 1‖ < r₀` and `‖w - 1‖ < r₀`, then
`log (y * w) = log y + log w`. -/
theorem log_mul_of_commute_of_norm_sub_one_lt {y w : A} (hyw : Commute y w)
    (hy : ‖y - 1‖ < amiceRadius p 0) (hw : ‖w - 1‖ < amiceRadius p 0) :
    log (y * w) = log y + log w := by
  have hy' : ‖log y‖ < amiceRadius p 0 := by rwa [norm_log_of_norm_sub_one_lt hy]
  have hw' : ‖log w‖ < amiceRadius p 0 := by rwa [norm_log_of_norm_sub_one_lt hw]
  rw [← exp_log_of_norm_sub_one_lt hy, ← exp_log_of_norm_sub_one_lt hw,
    ← exp_add_of_commute_of_norm_lt hyw.log hy' hw', log_exp_of_norm_lt
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hy' hw')),
    log_exp_of_norm_lt hy', log_exp_of_norm_lt hw']

/-- For `‖t‖ < r₀`, the logarithm preserves the norm: `‖log (1 + t)‖ = ‖t‖`. -/
private theorem norm_log_one_add_of_norm_lt {t : A} (ht : ‖t‖ < amiceRadius p 0) :
    ‖log (1 + t)‖ = ‖t‖ := by
  rw [norm_log_of_norm_sub_one_lt (by simpa using ht), add_sub_cancel_left]

/-- For `‖t‖ < r₀` and `x ∈ ℤ_p`, `x • log (1 + t)` lies in the disc of radius `r₀`. -/
private theorem norm_coe_smul_log_one_add_lt {t : A} (ht : ‖t‖ < amiceRadius p 0) (x : ℤ_[p]) :
    ‖(x : ℚ_[p]) • log (1 + t)‖ < amiceRadius p 0 :=
  (norm_smul_le _ _).trans_lt <| (mul_le_of_le_one_left (norm_nonneg _) x.norm_le_one).trans_lt <|
    (norm_log_one_add_of_norm_lt ht).trans_lt ht

/-- **The binomial power as an exponential.** In a complete ultrametric normed algebra over
`ℚ_[p]`, for `‖t‖ < r₀` and `x ∈ ℤ_p`, the continuous additive character
`x ↦ (1 + t) ^ x` (`PadicInt.addChar_of_value_at_one`) is `x ↦ exp (x log (1 + t))`. -/
theorem addChar_of_value_at_one_eq_exp_smul_log [Algebra ℤ_[p] A] [IsBoundedSMul ℤ_[p] A] {t : A}
    (ht : ‖t‖ < amiceRadius p 0) (x : ℤ_[p]) :
    PadicInt.addChar_of_value_at_one t
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (ht.trans (amiceRadius_lt_one 0))) x =
      exp ((x : ℚ_[p]) • log (1 + t)) := by
  have hL : ‖log (1 + t)‖ < amiceRadius p 0 := (norm_log_one_add_of_norm_lt ht).trans_lt ht
  -- Both sides are continuous in `x` and agree with `(1 + t) ^ n` at natural numbers `n`.
  have hcont : Continuous fun x : ℤ_[p] ↦ exp ((x : ℚ_[p]) • log (1 + t)) :=
    (continuousOn_exp (𝕂 := ℚ_[p])).comp_continuous
      (continuous_subtypeVal.smul continuous_const) fun x ↦
      mem_eball_radius_expSeries (norm_coe_smul_log_one_add_lt ht x)
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    (PadicInt.continuous_addChar_of_value_at_one _) hcont (funext fun n ↦ ?_)) x
  simp only [Function.comp_apply, PadicInt.coe_natCast, Nat.cast_smul_eq_nsmul]
  rw [← nsmul_one, AddChar.map_nsmul_eq_pow, PadicInt.addChar_of_value_at_one_def,
    exp_nsmul_of_norm_lt n hL, exp_log_of_norm_sub_one_lt (by simpa using ht), add_comm]

/-- In every complete ultrametric normed algebra over `ℚ_[p]`, the binomial power satisfies
`‖(1 + t) ^ x - 1‖ = ‖x‖ ‖t‖` for `‖t‖ < r₀` and `x ∈ ℤ_p`. -/
theorem norm_addChar_of_value_at_one_sub_one [Algebra ℤ_[p] A] [IsBoundedSMul ℤ_[p] A] {t : A}
    (ht : ‖t‖ < amiceRadius p 0) (x : ℤ_[p]) :
    ‖PadicInt.addChar_of_value_at_one t
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (ht.trans (amiceRadius_lt_one 0))) x - 1‖ =
      ‖x‖ * ‖t‖ := by
  rw [addChar_of_value_at_one_eq_exp_smul_log ht x,
    norm_exp_sub_one_of_norm_lt (norm_coe_smul_log_one_add_lt ht x), norm_smul,
    norm_log_one_add_of_norm_lt ht, PadicInt.norm_def]

end NormedRing

section NormedCommRing

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

/-- **The functional equation of the `p`-adic exponential.** For `‖x‖, ‖y‖ < r₀`,
`exp (x + y) = exp x * exp y`. -/
theorem exp_add_of_norm_lt {x y : A} (hx : ‖x‖ < amiceRadius p 0)
    (hy : ‖y‖ < amiceRadius p 0) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_norm_lt (Commute.all x y) hx hy

variable [IsUltrametricDist A]

/-- The functional equation for finite sums: if `‖f i‖ < r₀` for every `i ∈ s`, then
`exp (∑ i ∈ s, f i) = ∏ i ∈ s, exp (f i)`. -/
theorem exp_sum_of_norm_lt {ι : Type*} (s : Finset ι) {f : ι → A}
    (hf : ∀ i ∈ s, ‖f i‖ < amiceRadius p 0) : exp (∑ i ∈ s, f i) = ∏ i ∈ s, exp (f i) := by
  rw [exp_sum_of_commute_of_norm_lt s (fun _ _ _ _ _ ↦ Commute.all _ _) hf,
    Finset.noncommProd_eq_prod]

/-- **The logarithm turns products into sums on the disc of radius `r₀` about `1`.** For
`‖y - 1‖ < r₀` and `‖w - 1‖ < r₀`, `log (y * w) = log y + log w`. -/
theorem log_mul_of_norm_sub_one_lt {y w : A} (hy : ‖y - 1‖ < amiceRadius p 0)
    (hw : ‖w - 1‖ < amiceRadius p 0) : log (y * w) = log y + log w :=
  log_mul_of_commute_of_norm_sub_one_lt (Commute.all y w) hy hw

end NormedCommRing

/-- For `‖x‖ < r₀` and every integer `n`, `exp (n • x) = exp x ^ n`, in every complete normed
division ring over `ℚ_[p]`. -/
theorem exp_zsmul_of_norm_lt {L : Type*} [NormedDivisionRing L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] (n : ℤ) {x : L} (hx : ‖x‖ < amiceRadius p 0) : exp (n • x) = exp x ^ n := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using exp_nsmul_of_norm_lt n hx
  · rw [neg_smul, natCast_zsmul, exp_neg_of_mem_ball ℚ_[p]
      (mem_eball_radius_expSeries (norm_nsmul_lt_amiceRadius hx n)),
      exp_nsmul_of_norm_lt n hx, zpow_neg, zpow_natCast]

/-- **Integer combinations of logarithms of units near `1`.** If `‖αⱼ - 1‖ < r₀` for every
`j ∈ s`, then `exp (∑ⱼ nⱼ log αⱼ) = ∏ⱼ αⱼ ^ nⱼ` for all integers `nⱼ`. -/
theorem _root_.Finset.exp_sum_intCast_mul_log {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] {ι : Type*} (s : Finset ι) {α : ι → L}
    (hα : ∀ j ∈ s, ‖α j - 1‖ < amiceRadius p 0) (n : ι → ℤ) :
    exp (∑ j ∈ s, (n j : L) * log (α j)) = ∏ j ∈ s, α j ^ n j := by
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  have hlog (j : ι) (hj : j ∈ s) : ‖log (α j)‖ < amiceRadius p 0 :=
    (norm_log_of_norm_sub_one_lt (hα j hj)).trans_lt (hα j hj)
  simp_rw [← zsmul_eq_mul]
  rw [exp_sum_of_norm_lt (p := p) s fun j hj ↦
    (IsUltrametricDist.norm_zsmul_le _ _).trans_lt (hlog j hj)]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [exp_zsmul_of_norm_lt _ (hlog j hj), exp_log_of_norm_sub_one_lt (hα j hj)]

end TauCeti
