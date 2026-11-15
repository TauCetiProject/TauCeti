/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Factorial

/-!
# The `p`-adic exponential on its disc of convergence

In a normed field `L` over `ℚ_[p]`, every natural number has the same norm as in `ℚ_[p]`
(`TauCeti.norm_natCast_eq_norm_padic`), so Legendre's formula bounds the factorial denominators of
the exponential series `NormedSpace.expSeries L L` away from zero:
`‖(n ! : L)⁻¹‖ ≤ p ^ ((n - 1) / (p - 1))`, with equality along prime powers `n = p ^ k`
(`Padic.rpow_neg_pred_div_le_norm_factorial`, `Padic.norm_factorial_pow`).

Consequently `NormedSpace.expSeries L L` has exact radius of convergence
`ρ = p ^ (-1 / (p - 1))` (`TauCeti.PadicExp.radius_expSeries`). At every point `x : L` outside the
open disc `{x : L | ‖x‖ < ρ}`, including the boundary circle `‖x‖ = ρ`, the prime-power terms
`x ^ (p ^ k) / (p ^ k)!` have norm at least `ρ`, so the exponential series diverges and
`NormedSpace.exp x` takes its default value `0` (`TauCeti.PadicExp.not_summable_pow_div_factorial`,
`TauCeti.PadicExp.exp_eq_zero_of_le_norm`). For `p = 2` the point `2` itself has norm `1 / 2 = ρ`
and lies on this boundary (`TauCeti.PadicExp.norm_two_eq`), whereas for odd primes `p ≠ 2` the
prime `p` lies strictly inside the disc (`TauCeti.PadicExp.norm_natCast_prime_lt_iff`).

When `L` is complete (including infinite extensions and completions such as `ℂ_[p]`), the open
disc `{x : L | ‖x‖ < ρ}` is an additive subgroup on which `NormedSpace.exp` is analytic, turns
sums into products (`TauCeti.PadicExp.exp_add`, `TauCeti.PadicExp.exp_sum`), takes values on the
unit sphere (`TauCeti.PadicExp.norm_exp`), and satisfies the ultrametric isometry
`‖exp x - 1‖ = ‖x‖` (`TauCeti.PadicExp.norm_exp_sub_one`) and `‖exp x - exp y‖ = ‖x - y‖`
(`TauCeti.PadicExp.norm_exp_sub_exp`), making `exp` injective on the disc
(`TauCeti.PadicExp.injOn_exp`).

## Main results

* `TauCeti.PadicExp.nontriviallyNormedField`: every normed field over `ℚ_[p]` is nontrivially
  normed.
* `TauCeti.PadicExp.norm_pow_div_factorial_mul_pow_le_one`,
  `TauCeti.PadicExp.norm_pow_div_factorial_le`: norm bounds on `x ^ n / n !` from Legendre's
  formula.
* `TauCeti.PadicExp.le_radius_expSeries`, `TauCeti.PadicExp.radius_expSeries`: the radius of
  convergence of `NormedSpace.expSeries L L` is `ENNReal.ofReal (p ^ (-1 / (p - 1)))`.
* `TauCeti.PadicExp.not_summable_pow_div_factorial`, `TauCeti.PadicExp.exp_eq_zero_of_le_norm`,
  `TauCeti.PadicExp.eventuallyEq_zero_exp_of_le_norm`: divergence of the exponential series and
  local vanishing of `NormedSpace.exp` for `ρ ≤ ‖x‖`.
* `TauCeti.PadicExp.hasStrictDerivAt_exp`, `TauCeti.PadicExp.hasDerivAt_exp`,
  `TauCeti.PadicExp.deriv_exp`: global derivative of `NormedSpace.exp` on a complete nontrivially
  normed field over `ℚ_[p]`.
* `TauCeti.PadicExp.exp_add`, `TauCeti.PadicExp.exp_nsmul`, `TauCeti.PadicExp.exp_zsmul`,
  `TauCeti.PadicExp.exp_sum`: homomorphism properties of `NormedSpace.exp` on `{x : L | ‖x‖ < ρ}`.
* `TauCeti.PadicExp.norm_exp_sub_one`, `TauCeti.PadicExp.norm_exp`,
  `TauCeti.PadicExp.norm_exp_sub_exp`, `TauCeti.PadicExp.injOn_exp`,
  `TauCeti.PadicExp.exp_eq_one_iff`: ultrametric isometry and injectivity of `NormedSpace.exp`.

## References

* [A. Brumer, *On the units of algebraic number fields*]: Mathematika 14 (1967), 121–124.
* [A. M. Robert, *A Course in p-adic Analysis*]: Graduate Texts in Mathematics 198, Springer,
  2000, Chapter 5, §5.4.
* Ported and generalised from `Mathlib/NumberTheory/Transcendental/Baker/Padic/Exp.lean` on the
  `baker-padic` branch of `mkaratarakis/mathlib4` (commit `65cdef5722`, by Michail Karatarakis),
  which treated the special case `L = ℂ_[p]` and the lower bound on the radius.
-/

public section

open Filter Nat NormedSpace
open scoped Topology NNReal ENNReal

namespace TauCeti.PadicExp

section TermBounds

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every normed field over `ℚ_[p]` is nontrivially normed. The body is exposed so that the
underlying `NormedField L` structure reduces definitionally to the ambient instance. -/
@[expose, instance_reducible]
def nontriviallyNormedField (p : ℕ) [hp : Fact p.Prime] (L : Type*) [NormedField L]
    [NormedAlgebra ℚ_[p] L] : NontriviallyNormedField L where
  __ := ‹NormedField L›
  non_trivial := ⟨(p : L)⁻¹, by
    rw [norm_inv, TauCeti.norm_natCast_eq_norm_padic (p := p), Padic.norm_p, inv_inv]
    exact_mod_cast hp.out.one_lt⟩

/-- In a seminormed `ℚ_[p]`-algebra `L` with `‖1‖ = 1`, the prime `p` lies strictly inside the
disc of radius `p ^ (-1 / (p - 1))` if and only if `p ≠ 2`. -/
theorem norm_natCast_prime_lt_iff {L : Type*} [SeminormedRing L] [NormOneClass L]
    [NormedAlgebra ℚ_[p] L] :
    ‖(p : L)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ↔ p ≠ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by positivity
  rw [TauCeti.norm_natCast_eq_norm_padic (p := p), Padic.norm_p, ← Real.rpow_neg_one,
    Real.rpow_lt_rpow_left_iff hp1, neg_lt_neg_iff, inv_lt_one_iff₀]
  refine ⟨fun h => ?_, fun h => Or.inr ?_⟩
  · rcases h with h | h
    · linarith
    · rintro rfl
      norm_num at h
  · have hp3 : 3 ≤ p := lt_of_le_of_ne hp.out.two_le (Ne.symm h)
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith

/-- In a seminormed `ℚ_[2]`-algebra `L` with `‖1‖ = 1`, the element `2` lies on the boundary
circle of radius `2 ^ (-1 / (2 - 1)) = 1 / 2`. -/
theorem norm_two_eq {L : Type*} [SeminormedRing L] [NormOneClass L] [NormedAlgebra ℚ_[2] L] :
    ‖(2 : L)‖ = (2 : ℝ) ^ (-((2 : ℝ) - 1)⁻¹) := by
  have h := TauCeti.norm_natCast_eq_norm_padic (p := 2) (K := L) 2
  have hp2 : ‖((2 : ℕ) : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p (p := 2)
  rw [Nat.cast_two] at h
  rw [h, hp2]
  norm_num

variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]

/-- **Sharpened Legendre bound on `(n !)⁻¹`.** In a normed field `L` over `ℚ_[p]`,
`‖(n ! : L)⁻¹‖ ≤ (p ^ (1 / (p - 1))) ^ (n - 1)` for every `n : ℕ`. -/
theorem norm_factorial_inv_le (n : ℕ) :
    ‖(n ! : L)⁻¹‖ ≤ ((p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (n - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpos : 0 < ‖(n ! : ℚ_[p])‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [norm_inv, TauCeti.norm_natCast_eq_norm_padic (p := p), ← Real.rpow_natCast,
    ← Real.rpow_mul hp0.le, inv_mul_eq_div, inv_le_comm₀ hpos (by positivity),
    ← Real.rpow_neg hp0.le]
  exact Padic.rpow_neg_pred_div_le_norm_factorial n

/-- **Legendre's bound in exponential-series form.** With `ρ = p ^ (-1 / (p - 1))`,
`‖(n ! : L)⁻¹‖ * ρ ^ n ≤ 1` for every `n : ℕ`. -/
theorem norm_factorial_inv_mul_pow_le (n : ℕ) :
    ‖(n ! : L)⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ n ≤ 1 := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpos : 0 < ‖(n ! : ℚ_[p])‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [norm_inv, TauCeti.norm_natCast_eq_norm_padic (p := p), ← Real.rpow_natCast,
    ← Real.rpow_mul hp0, inv_mul_le_one₀ hpos, neg_mul, inv_mul_eq_div]
  exact Padic.rpow_neg_div_le_norm_factorial n

/-- Along prime powers `n = p ^ k`, the product `‖((p ^ k)! : L)⁻¹‖ * ρ ^ (p ^ k)` is constantly
equal to `ρ = p ^ (-1 / (p - 1))`. -/
theorem norm_factorial_pow_inv_mul_pow (k : ℕ) :
    ‖((p ^ k)! : L)⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (p ^ k) =
      (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_inv, TauCeti.norm_natCast_eq_norm_padic (p := p), Padic.norm_factorial_pow,
    ← Real.rpow_neg hp0.le, neg_neg, ← Real.rpow_natCast ((p : ℝ) ^ _) (p ^ k),
    ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
  congr 1
  rw [Nat.cast_pow]
  field_simp [sub_ne_zero.mpr (by exact_mod_cast hp.out.ne_one : (p : ℝ) ≠ 1)]
  ring

/-- For `0 ≤ r` and `‖x‖ * r ≤ p ^ (-1 / (p - 1))`, the `n`-th rescaled exponential coefficient
satisfies `‖x ^ n / n !‖ * r ^ n ≤ 1`. -/
theorem norm_pow_div_factorial_mul_pow_le_one {x : L} {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ * r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    ‖x ^ n / (n ! : L)‖ * r ^ n ≤ 1 := by
  calc ‖x ^ n / (n ! : L)‖ * r ^ n
      = ‖(n ! : L)⁻¹‖ * (‖x‖ * r) ^ n := by
        rw [div_eq_mul_inv, norm_mul, norm_pow, mul_pow]
        ring
    _ ≤ ‖(n ! : L)⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (norm_nonneg x) hr) hx n)
          (norm_nonneg _)
    _ ≤ 1 := norm_factorial_inv_mul_pow_le n

/-- On the closed disc `‖x‖ ≤ p ^ (-1 / (p - 1))`, every term `x ^ n / n !` has norm at most `1`. -/
theorem norm_pow_div_factorial_le_one {x : L} (hx : ‖x‖ ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    ‖x ^ n / (n ! : L)‖ ≤ 1 := by
  simpa only [mul_one, one_pow] using
    norm_pow_div_factorial_mul_pow_le_one zero_le_one (by simpa only [mul_one] using hx) n

/-- For `1 ≤ n`, `‖x ^ n / n !‖ ≤ ‖x‖ * (‖x‖ * p ^ (1 / (p - 1))) ^ (n - 1)`. -/
theorem norm_pow_div_factorial_le (x : L) {n : ℕ} (hn : 1 ≤ n) :
    ‖x ^ n / (n ! : L)‖ ≤ ‖x‖ * (‖x‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (n - 1) := by
  calc ‖x ^ n / (n ! : L)‖
      = ‖x‖ ^ n * ‖(n ! : L)⁻¹‖ := by rw [div_eq_mul_inv, norm_mul, norm_pow]
    _ ≤ ‖x‖ ^ n * ((p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (n - 1) := by
        gcongr
        exact norm_factorial_inv_le n
    _ = ‖x‖ * (‖x‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (n - 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_add_of_le' hn
        rw [Nat.add_sub_cancel, mul_pow, pow_add, pow_one]
        ring

/-- Outside the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, every prime-power term
`x ^ (p ^ k) / (p ^ k)!` has norm at least `p ^ (-1 / (p - 1))`. -/
theorem le_norm_pow_div_factorial_pow {x : L}
    (hx : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖) (k : ℕ) :
    (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x ^ (p ^ k) / ((p ^ k)! : L)‖ := by
  calc (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)
      = ‖((p ^ k)! : L)⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (p ^ k) :=
        (norm_factorial_pow_inv_mul_pow k).symm
    _ ≤ ‖((p ^ k)! : L)⁻¹‖ * ‖x‖ ^ (p ^ k) := by gcongr
    _ = ‖x ^ (p ^ k) / ((p ^ k)! : L)‖ := by
        rw [div_eq_mul_inv, norm_mul, norm_pow, mul_comm]

/-- Outside the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, the exponential series at `x`
is not summable. -/
theorem not_summable_pow_div_factorial {x : L}
    (hx : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖) :
    ¬ Summable fun n : ℕ => x ^ n / (n ! : L) := by
  intro hsum
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hρ : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by positivity
  have hsub : StrictMono (fun k : ℕ => p ^ k) := pow_right_strictMono₀ hp.out.one_lt
  have htend : Tendsto (fun k : ℕ => ‖x ^ (p ^ k) / ((p ^ k)! : L)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero] using
      hsum.tendsto_atTop_zero.norm.comp hsub.tendsto_atTop
  have hle : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ 0 :=
    ge_of_tendsto' htend (le_norm_pow_div_factorial_pow hx)
  exact hρ.not_ge hle

/-- Outside the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, `NormedSpace.exp x = 0`. -/
theorem exp_eq_zero_of_le_norm {x : L}
    (hx : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖) : NormedSpace.exp x = 0 := by
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  rw [NormedSpace.exp_eq_tsum_div]
  exact tsum_eq_zero_of_not_summable (not_summable_pow_div_factorial hx)

/-- Outside the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, `NormedSpace.exp` vanishes in a
neighbourhood of `x`. -/
theorem eventuallyEq_zero_exp_of_le_norm {x : L}
    (hx : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖) :
    (NormedSpace.exp : L → L) =ᶠ[𝓝 x] 0 := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hρ : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hρ] with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hlt : ‖z - x‖ < ‖x‖ := hz.trans_le hx
  have hnorm : ‖z‖ = ‖x‖ := by
    have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rwa [sub_add_cancel, max_eq_right hlt.le] at heq
  exact exp_eq_zero_of_le_norm (hx.trans_eq hnorm.symm)

end TermBounds

section Summable

/-- Whenever the exponential series at `x : L` is summable, `‖NormedSpace.exp x - 1‖ = ‖x‖`. -/
theorem norm_exp_sub_one_of_summable (p : ℕ) [hp : Fact p.Prime] {L : Type*} [NormedField L]
    [NormedAlgebra ℚ_[p] L] {x : L} (hsum : Summable fun n : ℕ => x ^ n / (n ! : L)) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    lt_of_not_ge fun hx => not_summable_pow_div_factorial hx hsum
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set q := ‖x‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, ← lt_div_iff₀ (by positivity), one_div, ← Real.rpow_neg hp0.le]
    exact hx
  have hhas : HasSum (fun n : ℕ => x ^ n / (n ! : L)) (NormedSpace.exp x) := by
    rw [NormedSpace.exp_eq_tsum_div]
    exact hsum.hasSum
  have htail : HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2)! : L))
      (NormedSpace.exp x - (1 + x)) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ n / (n ! : L)) 2).mpr hhas
    simpa [Finset.sum_range_succ] using h
  have hbound : ‖NormedSpace.exp x - (1 + x)‖ ≤ ‖x‖ * q := by
    rw [← htail.tsum_eq]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n => ?_
    calc ‖x ^ (n + 2) / ((n + 2)! : L)‖
        ≤ ‖x‖ * q ^ (n + 1) := norm_pow_div_factorial_le x (by omega)
      _ ≤ ‖x‖ * q ^ 1 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le (by omega)) (norm_nonneg x)
      _ = ‖x‖ * q := by rw [pow_one]
  have hlt : ‖NormedSpace.exp x - (1 + x)‖ < ‖x‖ :=
    hbound.trans_lt (mul_lt_of_lt_one_right (norm_pos_iff.mpr hx0) hq1)
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  have hsub : NormedSpace.exp x - (1 + x) + x = NormedSpace.exp x - 1 := by ring
  rwa [hsub, max_eq_right hlt.le] at heq

/-- In a normed field `L` over `ℚ_[p]`, `NormedSpace.exp x = 1` if and only if `x = 0`. -/
theorem exp_eq_one_iff (p : ℕ) [Fact p.Prime] {L : Type*} [NormedField L]
    [NormedAlgebra ℚ_[p] L] {x : L} : NormedSpace.exp x = 1 ↔ x = 0 := by
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hsum : Summable fun n : ℕ => x ^ n / (n ! : L) := by
    by_contra hns
    have h0 : NormedSpace.exp x = 0 := by
      rw [NormedSpace.exp_eq_tsum_div]
      exact tsum_eq_zero_of_not_summable hns
    exact one_ne_zero (h.symm.trans h0)
  have hnorm := norm_exp_sub_one_of_summable p hsum
  rw [h, sub_self, norm_zero] at hnorm
  exact norm_eq_zero.mp hnorm.symm

end Summable

section Radius

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]

/-- **The radius of the `p`-adic exponential series** is at least `p ^ (-1 / (p - 1))`. -/
theorem le_radius_expSeries :
    ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ≤ (NormedSpace.expSeries L L).radius := by
  have hρ : 0 ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by positivity
  rw [ENNReal.ofReal]
  refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun n => ?_
  rw [Real.coe_toNNReal _ hρ, expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm]
  exact norm_factorial_inv_mul_pow_le n

/-- The radius of `NormedSpace.expSeries L L` is at most `p ^ (-1 / (p - 1))`. -/
theorem radius_expSeries_le :
    (NormedSpace.expSeries L L).radius ≤ ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) := by
  by_contra! hlt
  obtain ⟨r, hρr, hrrad⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hρ0 : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hρle : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ (r : ℝ) :=
    ((ENNReal.ofReal_lt_coe_iff hρ0.le).mp hρr).le
  have hsum := (NormedSpace.expSeries L L).summable_norm_mul_pow hrrad
  have hsub : StrictMono (fun k : ℕ => p ^ k) := pow_right_strictMono₀ hp.out.one_lt
  have htend : Tendsto (fun k : ℕ => ‖NormedSpace.expSeries L L (p ^ k)‖ * (r : ℝ) ^ (p ^ k))
      atTop (𝓝 0) := hsum.tendsto_atTop_zero.comp hsub.tendsto_atTop
  have hge : ∀ k : ℕ, (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤
      ‖NormedSpace.expSeries L L (p ^ k)‖ * (r : ℝ) ^ (p ^ k) := fun k => by
    rw [expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm]
    calc (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)
        = ‖((p ^ k)! : L)⁻¹‖ * ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ^ (p ^ k) :=
          (norm_factorial_pow_inv_mul_pow k).symm
      _ ≤ ‖((p ^ k)! : L)⁻¹‖ * (r : ℝ) ^ (p ^ k) := by gcongr
  exact hρ0.not_ge (ge_of_tendsto' htend hge)

/-- **Exact radius of the `p`-adic exponential series.** In any nontrivially normed field `L` over
`ℚ_[p]`, `(NormedSpace.expSeries L L).radius = ENNReal.ofReal (p ^ (-1 / (p - 1)))`. -/
theorem radius_expSeries :
    (NormedSpace.expSeries L L).radius = ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :=
  le_antisymm radius_expSeries_le le_radius_expSeries

/-- A point `x : L` lies in the extended-real ball of convergence of `NormedSpace.expSeries L L`
if and only if `‖x‖ < p ^ (-1 / (p - 1))`. -/
theorem mem_eball_expSeries_iff {x : L} :
    x ∈ Metric.eball (0 : L) (NormedSpace.expSeries L L).radius ↔
      ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  rw [radius_expSeries (p := p), Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm,
    ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]

end Radius

section Analytic

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L]
  [NormedAlgebra ℚ_[p] L] [CompleteSpace L]

/-- On the open ball of radius `p ^ (-1 / (p - 1))`, `NormedSpace.exp` is represented by
`NormedSpace.expSeries L L`. -/
theorem hasFPowerSeriesOnBall_exp :
    HasFPowerSeriesOnBall (NormedSpace.exp : L → L) (NormedSpace.expSeries L L) 0
      (ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))) := by
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  have hpos : 0 < (NormedSpace.expSeries L L).radius := by
    rw [radius_expSeries (p := p), ENNReal.ofReal_pos]
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  simpa only [radius_expSeries (p := p)] using
    NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos (𝕂 := L) (𝔸 := L) hpos

end Analytic

section Deriv

/-- In a complete nontrivially normed field `L` over `ℚ_[p]`, `NormedSpace.exp` has strict
derivative `NormedSpace.exp x` at every `x : L` (agreeing with `0` outside the clopen disc of
convergence). -/
theorem hasStrictDerivAt_exp (p : ℕ) [Fact p.Prime] {L : Type*} [NontriviallyNormedField L]
    [NormedAlgebra ℚ_[p] L] [CompleteSpace L] (x : L) :
    HasStrictDerivAt NormedSpace.exp (NormedSpace.exp x) x := by
  rcases lt_or_ge ‖x‖ ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) with hx | hx
  · have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
    exact _root_.hasStrictDerivAt_exp_of_mem_ball ((mem_eball_expSeries_iff (p := p)).mpr hx)
  · rw [exp_eq_zero_of_le_norm hx]
    exact (hasStrictDerivAt_const x (0 : L)).congr_of_eventuallyEq
      (eventuallyEq_zero_exp_of_le_norm hx).symm

/-- In a complete nontrivially normed field `L` over `ℚ_[p]`, `NormedSpace.exp` has derivative
`NormedSpace.exp x` at every `x : L`. -/
theorem hasDerivAt_exp (p : ℕ) [Fact p.Prime] {L : Type*} [NontriviallyNormedField L]
    [NormedAlgebra ℚ_[p] L] [CompleteSpace L] (x : L) :
    HasDerivAt NormedSpace.exp (NormedSpace.exp x) x :=
  (hasStrictDerivAt_exp p x).hasDerivAt

/-- In a complete nontrivially normed field `L` over `ℚ_[p]`,
`deriv NormedSpace.exp x = NormedSpace.exp x` for every `x : L`. -/
theorem deriv_exp (p : ℕ) [Fact p.Prime] {L : Type*} [NontriviallyNormedField L]
    [NormedAlgebra ℚ_[p] L] [CompleteSpace L] (x : L) :
    deriv (NormedSpace.exp : L → L) x = NormedSpace.exp x :=
  (hasDerivAt_exp p x).deriv

end Deriv

section DiscProperties

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NormedField L]
  [NormedAlgebra ℚ_[p] L] [CompleteSpace L]

/-- On `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, the exponential series `∑ x ^ n / n !` sums to
`NormedSpace.exp x`. -/
theorem hasSum_expSeries_div {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun n : ℕ => x ^ n / (n ! : L)) (NormedSpace.exp x) := by
  let : NontriviallyNormedField L := nontriviallyNormedField p L
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  exact NormedSpace.expSeries_div_hasSum_exp_of_mem_ball L x
    ((mem_eball_expSeries_iff (p := p)).mpr hx)

/-- In a complete normed field `L` over `ℚ_[p]`, the exponential series `∑ x ^ n / n !` is
summable if and only if `‖x‖ < p ^ (-1 / (p - 1))`. -/
theorem summable_pow_div_factorial_iff {x : L} :
    Summable (fun n : ℕ => x ^ n / (n ! : L)) ↔ ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
  ⟨fun h => lt_of_not_ge fun hx => not_summable_pow_div_factorial hx h,
    fun hx => (hasSum_expSeries_div hx).summable⟩

/-- **The functional equation of the `p`-adic exponential** on `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`.
-/
theorem exp_add {x y : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y := by
  let : NontriviallyNormedField L := nontriviallyNormedField p L
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  exact NormedSpace.exp_add_of_mem_ball ((mem_eball_expSeries_iff (p := p)).mpr hx)
    ((mem_eball_expSeries_iff (p := p)).mpr hy)

/-- On `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, `NormedSpace.exp x` is nonzero. -/
theorem exp_ne_zero {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp x ≠ 0 := by
  let : NontriviallyNormedField L := nontriviallyNormedField p L
  have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
  exact (NormedSpace.isUnit_exp_of_mem_ball ((mem_eball_expSeries_iff (p := p)).mpr hx)).ne_zero

/-- In a complete normed field `L` over `ℚ_[p]`, `NormedSpace.exp x = 0` if and only if `x` lies
outside the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`. -/
theorem exp_eq_zero_iff {x : L} :
    NormedSpace.exp x = 0 ↔ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖ :=
  ⟨fun h => le_of_not_gt fun hx => exp_ne_zero hx h, exp_eq_zero_of_le_norm⟩

/-- On `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, `NormedSpace.exp (n • x) = NormedSpace.exp x ^ n`. -/
theorem exp_nsmul {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  induction n with
  | zero => simp
  | succ n ih =>
    have hnx : ‖n • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rw [nsmul_eq_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg x)
        (IsUltrametricDist.norm_natCast_le_one L n)).trans_lt hx
    rw [succ_nsmul, exp_add hnx hx, ih, pow_succ]

/-- On `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, `NormedSpace.exp (z • x) = NormedSpace.exp x ^ z`
for every `z : ℤ`. -/
theorem exp_zsmul {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (z : ℤ) :
    NormedSpace.exp (z • x) = NormedSpace.exp x ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [natCast_zsmul, zpow_natCast, exp_nsmul hx n]
  · let : NontriviallyNormedField L := nontriviallyNormedField p L
    have : CharZero L := (RingHom.charZero_iff (algebraMap ℚ_[p] L).injective).mp inferInstance
    have hnx : ‖n • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
      rw [nsmul_eq_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg x)
        (IsUltrametricDist.norm_natCast_le_one L n)).trans_lt hx
    rw [neg_smul, natCast_zsmul, zpow_neg, zpow_natCast,
      NormedSpace.exp_neg_of_mem_ball L ((mem_eball_expSeries_iff (p := p)).mpr hnx),
      exp_nsmul hx n]

/-- **The exponential of a finite sum** in `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}` is the product of
the exponentials. -/
theorem exp_sum {ι : Type*} (s : Finset ι) {f : ι → L}
    (hf : ∀ i ∈ s, ‖f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (∑ i ∈ s, f i) = ∏ i ∈ s, NormedSpace.exp (f i) := by
  classical
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hρ : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ‖f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hsum : ‖∑ i ∈ s, f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simpa using hρ
      · obtain ⟨j, hj, hjmax⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
        exact hjmax.trans_lt (hs j hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      exp_add (hf a (Finset.mem_insert_self a s)) hsum, ih hs]

/-- **Ultrametric isometry at the origin.** For `‖x‖ < p ^ (-1 / (p - 1))`,
`‖NormedSpace.exp x - 1‖ = ‖x‖`. -/
theorem norm_exp_sub_one {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ :=
  norm_exp_sub_one_of_summable p (hasSum_expSeries_div hx).summable

/-- On `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`, `NormedSpace.exp` takes values of norm `1`. -/
theorem norm_exp {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x‖ = 1 := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hρ1 : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (inv_nonneg.mpr (sub_nonneg.mpr hp1)))
  have hlt : ‖NormedSpace.exp x - 1‖ < ‖(1 : L)‖ := by
    rw [norm_exp_sub_one hx, norm_one]
    exact hx.trans_le hρ1
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rwa [sub_add_cancel, max_eq_right hlt.le, norm_one] at heq

/-- **Ultrametric isometry on the disc.** For `‖x‖, ‖y‖ < p ^ (-1 / (p - 1))`,
`‖NormedSpace.exp x - NormedSpace.exp y‖ = ‖x - y‖`. -/
theorem norm_exp_sub_exp {x y : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ = ‖x - y‖ := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hsub : ‖x - y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_lt (max_lt hx (by rwa [norm_neg]))
  have hfac : NormedSpace.exp x - NormedSpace.exp y =
      NormedSpace.exp y * (NormedSpace.exp (x - y) - 1) := by
    rw [mul_sub, mul_one, ← exp_add hy hsub, add_sub_cancel]
  rw [hfac, norm_mul, norm_exp hy, one_mul, norm_exp_sub_one hsub]

/-- **`NormedSpace.exp` is injective** on `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`. -/
theorem injOn_exp :
    Set.InjOn (NormedSpace.exp : L → L) {x | ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)} := by
  intro x hx y hy hxy
  have h := norm_exp_sub_exp hx hy
  rw [hxy, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)

end DiscProperties

end TauCeti.PadicExp
