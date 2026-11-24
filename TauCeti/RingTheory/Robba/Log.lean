/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.Robba.OpenDisc
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The logarithm `log (1 + t)` in the Robba ring

Over a complete ultrametric normed field `K` of characteristic zero, the logarithm series

`log (1 + t) = ∑_{n ≥ 1} (-1)ⁿ⁺¹ tⁿ / n`,

Mathlib's `PowerSeries.log K`, converges on the whole open unit disc `|t| < 1`
(`PowerSeries.onOpenDisc_log`). Through the inclusion `TauCeti.RobbaRing.ofOnOpenDisc` of the power
series on the open unit disc it is an element `TauCeti.RobbaRing.log K` of the Robba ring, lying in
every annular subalgebra `TauCeti.RobbaRing.annulus K r` and with no terms of nonpositive degree.
Once the Robba variable is the cyclotomic coordinate `π = [ε] - 1`, this element is Fontaine's
period `t = log (1 + π)`.

When some positive integer `q` has `‖q‖ < 1`, for instance `q = p` in an extension of `ℚ_p`, the
coefficient `± 1 / qᵏ` of `t^(qᵏ)` has norm `‖q‖⁻ᵏ`, so `log (1 + t)` does not have bounded
coefficients: it is not in the bounded Robba ring, although it converges on the full open disc.

Over a normed `ℚ_p`-algebra `K`, `log (1 + t)` is the limit of the polynomials
`((1 + t) ^ (p ^ m) - 1) / p ^ m` in every Gauss norm `|·|_ρ` with `0 ≤ ρ < 1`. The coefficient of
`t ^ (j + 1)` in `((1 + t) ^ N - 1) / N` is `C(N, j + 1) / N = C(N - 1, j) / (j + 1)`, and the
binomial congruence `‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖`
(`TauCeti.norm_natCast_choose_pred_sub_neg_one_pow_le`) bounds its distance to the coefficient
`(-1)ʲ / (j + 1)` of `log (1 + t)` by `(j + 1)² ‖N‖`.

## Main definitions

* `TauCeti.RobbaRing.log`: the element `log (1 + t)` of the Robba ring.

## Main results

* `TauCeti.RobbaRing.coe_log_natCast`, `TauCeti.RobbaRing.coe_log_of_nonpos`: its coefficients
  are `(-1)ⁿ⁺¹ / n` in degree `n ≥ 1` and zero in degrees `n ≤ 0`.
* `TauCeti.RobbaRing.log_mem_annulus`: it lies in every annular subalgebra.
* `TauCeti.RobbaRing.log_notMem_bounded`: it is not in the bounded Robba ring when some positive
  integer has norm less than `1`.
* `TauCeti.norm_natCast_choose_pred_sub_neg_one_pow_le`: the binomial congruence
  `‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖` in a normed `ℚ_p`-algebra.
* `TauCeti.RobbaRing.tendsto_laurentGaussNorm_one_add_pow_sub_log`: over a normed `ℚ_p`-algebra,
  `((1 + t) ^ (p ^ m) - 1) / p ^ m → log (1 + t)` in every Gauss norm `|·|_ρ`, `0 ≤ ρ < 1`.

## References

* L. Berger, *An introduction to the theory of p-adic representations*, in *Geometric aspects of
  Dwork theory*, de Gruyter (2004), §§IV.2 and V.1.1.
* L. Berger, *Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002).
-/

public section

open Filter Topology
open scoped PowerSeries

namespace TauCeti

/-! ### A binomial congruence -/

section Binomial

variable {K : Type*} [NormedField K]

/-- In a normed `ℚ_p`-algebra the norm of a natural number is its `p`-adic norm. -/
private theorem norm_natCast_eq_padic (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K] (n : ℕ) :
    ‖(n : K)‖ = ‖(n : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap']

/-- In a normed `ℚ_p`-algebra a nonzero natural number is nonzero. -/
private theorem natCast_ne_zero_of_padic (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K] {n : ℕ}
    (hn : n ≠ 0) : (n : K) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_natCast_eq_padic p, norm_ne_zero_iff]
  exact_mod_cast hn

/-- In a normed `ℚ_p`-algebra, `‖1 / n‖ ≤ n`. -/
private theorem norm_inv_natCast_le (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K] (n : ℕ) :
    ‖(n : K)⁻¹‖ ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [norm_inv, norm_natCast_eq_padic p]
  exact inv_le_of_inv_le₀ (by positivity) (Padic.inv_natCast_le_norm_natCast n)

/-- **`C(N - 1, j) ≡ (-1)ʲ` modulo `(j + 1) N`.** In a normed `ℚ_p`-algebra the binomial
coefficient `C(N - 1, j) = ∏_{1 ≤ i ≤ j} (N - i) / i` is close to `(-1)ʲ`:
`‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖`. -/
theorem norm_natCast_choose_pred_sub_neg_one_pow_le (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] {N : ℕ} (hN : N ≠ 0) (j : ℕ) :
    ‖((N - 1).choose j : K) - (-1) ^ j‖ ≤ (j + 1) * ‖(N : K)‖ := by
  have : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have hsub (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
    simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : ((j + 1 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_padic p j.succ_ne_zero
    set x : K := N / (j + 1 : ℕ) with hx_def
    -- The recursion `C(N - 1, j + 1) = -C(N - 1, j) (1 - N / (j + 1))`.
    have hrec : ((N - 1).choose (j + 1) : K) = -((N - 1).choose j : K) * (1 - x) := by
      rcases le_or_gt j (N - 1) with h | h
      · have h' := congrArg (Nat.cast : ℕ → K) (Nat.choose_succ_right_eq (N - 1) j)
        push_cast [Nat.cast_sub h, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hN)] at h'
        rw [hx_def, eq_comm, ← sub_eq_zero]
        have : ((N - 1).choose (j + 1) : K) = (N - 1).choose j * (N - 1 - j) / (j + 1 : ℕ) := by
          rw [eq_div_iff hj, ← h']
          push_cast
          ring
        rw [this]
        field_simp
        push_cast
        ring
      · simp [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (h.trans (Nat.lt_succ_self j))]
    by_cases hbig : 1 ≤ (j + 1 + 1) * ‖(N : K)‖
    · -- Both terms are integers, so the difference has norm at most `1`.
      have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) + 1) * ‖(N : K)‖ := by push_cast; linarith
      refine (hsub _ _).trans (max_le ((IsUltrametricDist.norm_natCast_le_one K _).trans h1) ?_)
      simpa using h1
    · push Not at hbig
      have hx : ‖x‖ ≤ (j + 1) * ‖(N : K)‖ := by
        rw [hx_def, div_eq_mul_inv, norm_mul, mul_comm]
        gcongr
        exact_mod_cast norm_inv_natCast_le p (j + 1)
      have hx1 : ‖1 - x‖ ≤ 1 :=
        (hsub _ _).trans (max_le norm_one.le (hx.trans (by nlinarith [norm_nonneg (N : K)])))
      have hsplit : ((N - 1).choose (j + 1) : K) - (-1) ^ (j + 1) =
          -((((N - 1).choose j : K) - (-1) ^ j) * (1 - x) - (-1) ^ j * x) := by
        rw [hrec]
        ring
      rw [hsplit, norm_neg]
      refine (hsub _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc _ ≤ ((j + 1) * ‖(N : K)‖) * 1 :=
              mul_le_mul ih hx1 (norm_nonneg _) (by positivity)
          _ ≤ _ := by push_cast; nlinarith [norm_nonneg (N : K)]
      · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        refine hx.trans ?_
        push_cast
        nlinarith [norm_nonneg (N : K)]

/-- **The coefficients of `((1 + t) ^ N - 1) / N` approximate those of `log (1 + t)`.** In a normed
`ℚ_p`-algebra, `‖C(N, j + 1) / N - (-1)ʲ / (j + 1)‖ ≤ (j + 1)² ‖N‖`. -/
theorem norm_natCast_choose_succ_div_sub_le (p : ℕ) [Fact p.Prime] [NormedAlgebra ℚ_[p] K] {N : ℕ}
    (hN : N ≠ 0) (j : ℕ) :
    ‖(N.choose (j + 1) : K) / N - (-1) ^ j / (j + 1)‖ ≤ (j + 1) ^ 2 * ‖(N : K)‖ := by
  have hN' : (N : K) ≠ 0 := natCast_ne_zero_of_padic p hN
  have hj : ((j + 1 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_padic p j.succ_ne_zero
  -- `C(N, j + 1) / N = C(N - 1, j) / (j + 1)`.
  have hsucc := congrArg (Nat.cast : ℕ → K) (Nat.add_one_mul_choose_eq (N - 1) j)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN)] at hsucc
  push_cast at hsucc hj
  have heq : (N.choose (j + 1) : K) / N - (-1) ^ j / (j + 1) =
      (((N - 1).choose j : K) - (-1) ^ j) * ((j + 1 : ℕ) : K)⁻¹ := by
    push_cast
    field_simp
    linear_combination -hsucc
  rw [heq, norm_mul]
  calc _ ≤ ((j + 1) * ‖(N : K)‖) * (j + 1 : ℕ) :=
        mul_le_mul (norm_natCast_choose_pred_sub_neg_one_pow_le p hN j)
          (norm_inv_natCast_le p _) (norm_nonneg _) (by positivity)
    _ = _ := by push_cast; ring

end Binomial

namespace RobbaRing

open IsConvolutionRing

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- `(1 + t) ^ N` is the image of the polynomial `(1 + X) ^ N`, whose coefficients are binomial
coefficients. -/
private theorem one_add_monomial_pow (N : ℕ) : (1 + monomial 1 1 : RobbaRing K) ^ N =
    ofOnOpenDisc K (PowerSeries.OnOpenDisc.polynomialHom ((1 + Polynomial.X) ^ N)) := by
  simp

variable [CharZero K]

/-- **The logarithm `log (1 + t) = ∑_{n ≥ 1} (-1)ⁿ⁺¹ tⁿ / n`** as an element of the Robba ring:
the image of the power series `PowerSeries.log K`, which converges on the open unit disc
(`PowerSeries.onOpenDisc_log`). With the cyclotomic variable `π` in place of `t` it is Fontaine's
period `t = log (1 + π)`. -/
noncomputable def log : RobbaRing K :=
  ofOnOpenDisc K
    ⟨PowerSeries.log K, PowerSeries.OnOpenDisc.mem_subring.2 PowerSeries.onOpenDisc_log⟩

/-- The coefficient of `tⁿ` in `log (1 + t)` is `(-1)ⁿ⁺¹ / n`; for `n = 0` both sides are `0`. -/
@[simp]
theorem coe_log_natCast (n : ℕ) : (log K : ℤ → K) n = (-1) ^ (n + 1) / n := by
  simp only [log, coe_ofOnOpenDisc_natCast]
  exact PowerSeries.coeff_log_eq_neg_one_pow_div n

/-- `log (1 + t)` has no terms of nonpositive degree. -/
theorem coe_log_of_nonpos {n : ℤ} (hn : n ≤ 0) : (log K : ℤ → K) n = 0 := by
  rcases hn.lt_or_eq with hn | rfl
  · exact coe_ofOnOpenDisc_of_neg K _ hn
  · simpa using coe_log_natCast K 0

/-- The constant term of `log (1 + t)` is `0`. -/
@[simp]
theorem coe_log_zero : (log K : ℤ → K) 0 = 0 :=
  coe_log_of_nonpos K le_rfl

/-- The linear coefficient of `log (1 + t)` is `1`. -/
@[simp]
theorem coe_log_one : (log K : ℤ → K) 1 = 1 := by
  simpa using coe_log_natCast K 1

/-- **`log (1 + t)` converges on the whole open unit disc**, so it lies in every annular subalgebra
`r < |t| < 1` of the Robba ring. -/
theorem log_mem_annulus (r : ℝ) : log K ∈ annulus K r :=
  ofOnOpenDisc_mem_annulus K _ r

/-- **`log (1 + t)` is not in the bounded Robba ring** as soon as some positive integer `q` has
`‖q‖ < 1`, for instance `q = p` over an extension of `ℚ_p`: the coefficient of `t^(qᵏ)` has norm
`‖q‖⁻ᵏ`. -/
theorem log_notMem_bounded {q : ℕ} (hq₀ : q ≠ 0) (hq₁ : ‖(q : K)‖ < 1) :
    log K ∉ bounded K := by
  intro h
  obtain ⟨B, hB⟩ := mem_bounded.1 h
  have hq : 0 < ‖(q : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hq₀)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B ((one_lt_inv₀ hq).2 hq₁)
  have : ‖(log K : ℤ → K) ((q ^ k : ℕ) : ℤ)‖ ≤ B := hB ⟨_, rfl⟩
  rw [coe_log_natCast] at this
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Nat.cast_pow] at this
  rw [one_div, ← inv_pow] at this
  exact absurd hk (not_lt.2 this)

/-! ### `log (1 + t)` as a limit of polynomials -/

variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- **`log (1 + t) = lim ((1 + t) ^ (p ^ m) - 1) / p ^ m`.** Over a complete normed `ℚ_p`-algebra
`K`, the polynomials `((1 + t) ^ (p ^ m) - 1) / p ^ m` converge to `log (1 + t)` in every Gauss
norm `|·|_ρ` with `0 ≤ ρ < 1`, the seminorms of the open unit disc. In fact
`|((1 + t) ^ (p ^ m) - 1) / p ^ m - log (1 + t)|_ρ ≤ C_ρ p⁻ᵐ` with `C_ρ = sup_n n² ρⁿ`. -/
theorem tendsto_laurentGaussNorm_one_add_pow_sub_log {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    Tendsto (fun m : ℕ ↦ laurentGaussNorm ρ
      ((((p : K) ^ m)⁻¹ • ((1 + monomial 1 1 : RobbaRing K) ^ p ^ m - 1) - log K :
        RobbaRing K) : ℤ → K)) atTop (𝓝 0) := by
  -- A bound `C` for `n² ρⁿ`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ n : ℕ, (n : ℝ) ^ 2 * ρ ^ n ≤ C := by
    obtain ⟨C, hC⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
      (by rwa [abs_of_nonneg hρ₀])).bddAbove_range
    exact ⟨C, fun n ↦ hC ⟨n, rfl⟩⟩
  have hC₀ : 0 ≤ C := by simpa using hC 0
  have hp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap', Padic.norm_p]
  have hp₁ : ‖(p : K)‖ < 1 :=
    hp ▸ inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  refine squeeze_zero (fun _ ↦ laurentGaussNorm_nonneg _ _) (fun m ↦ ?_)
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp₁).const_mul C)
  -- The coefficient bound `‖dₙ‖ ρⁿ ≤ C ‖p‖ᵐ`.
  refine laurentGaussNorm_le fun n ↦ ?_
  simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    coe_one]
  rcases lt_or_ge 0 n with hn | hn
  · -- In degree `j + 1` the coefficient is `C(N, j + 1) / N - (-1) ʲ / (j + 1)`, `N = p ^ m`.
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
    have hcoeff := norm_natCast_choose_succ_div_sub_le p (K := K)
      (pow_ne_zero m (Fact.out : p.Prime).ne_zero) j
    rw [one_add_monomial_pow, coe_ofOnOpenDisc_natCast, PowerSeries.OnOpenDisc.coe_polynomialHom,
      Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, coe_log_natCast,
      Pi.single_eq_of_ne (by omega), sub_zero, zpow_natCast]
    calc _ = ‖(((p ^ m).choose (j + 1) : ℕ) : K) / ((p ^ m : ℕ) : K) - (-1) ^ j / (j + 1)‖ *
          ρ ^ (j + 1) := by
          congr 2
          push_cast
          ring
      _ ≤ ((j + 1) ^ 2 * ‖((p ^ m : ℕ) : K)‖) * ρ ^ (j + 1) := by gcongr
      _ = ((j + 1 : ℕ) : ℝ) ^ 2 * ρ ^ (j + 1) * ‖(p : K)‖ ^ m := by
          push_cast
          rw [norm_pow]
          ring
      _ ≤ C * ‖(p : K)‖ ^ m := by gcongr; exact hC (j + 1)
  · -- In degrees `n ≤ 0` the coefficient vanishes.
    rcases hn.lt_or_eq with hn | rfl
    · rw [one_add_monomial_pow, coe_ofOnOpenDisc_of_neg K _ hn, coe_log_of_nonpos K hn.le,
        Pi.single_eq_of_ne hn.ne, sub_self, mul_zero, sub_zero, norm_zero, zero_mul]
      positivity
    · rw [← Nat.cast_zero, one_add_monomial_pow, coe_ofOnOpenDisc_natCast, coe_log_natCast]
      simp only [PowerSeries.OnOpenDisc.coe_polynomialHom, Polynomial.coeff_coe,
        Polynomial.coeff_one_add_X_pow, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero,
        Pi.single_eq_same, sub_self, mul_zero, div_zero, norm_zero, zero_mul]
      positivity

end RobbaRing

end TauCeti
