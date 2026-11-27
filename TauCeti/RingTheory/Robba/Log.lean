/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Topology
public import TauCeti.RingTheory.Robba.OpenDisc
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Choose
import TauCeti.RingTheory.PowerSeries.TateAlgebra

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
binomial estimate `‖C(N - 1, j) - (-1)ʲ‖ ≤ (j + 1) ‖N‖` of `TauCeti.NumberTheory.Padics.Choose`
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
* `TauCeti.RobbaRing.tendsto_laurentGaussNorm_one_add_pow_sub_log`: over a normed `ℚ_p`-algebra,
  `((1 + t) ^ (p ^ m) - 1) / p ^ m → log (1 + t)` in every Gauss norm `|·|_ρ`, `0 ≤ ρ < 1`.
* `TauCeti.RobbaRing.tendsto_onOpenDisc_one_add_pow_sub_log`: the same limit in the topology of
  the power series on the open unit disc.

## References

* L. Berger, *An introduction to the theory of p-adic representations*, in *Geometric aspects of
  Dwork theory*, de Gruyter (2004), §§IV.2 and V.1.1.
* L. Berger, *Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002).
-/

public section

open Filter Topology
open scoped PowerSeries

namespace TauCeti

namespace RobbaRing

open IsConvolutionRing

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable [CharZero K]

/-- **The logarithm `log (1 + t) = ∑_{n ≥ 1} (-1)ⁿ⁺¹ tⁿ / n`** as an element of the Robba ring:
the image of the power series `PowerSeries.log K`, which converges on the open unit disc
(`PowerSeries.onOpenDisc_log`). With the cyclotomic variable `π` in place of `t` it is Fontaine's
period `t = log (1 + π)`. -/
noncomputable def log : RobbaRing K :=
  ofOnOpenDisc K
    ⟨PowerSeries.log K, PowerSeries.OnOpenDisc.mem_subring.2 PowerSeries.onOpenDisc_log⟩

/-- `log (1 + t)` is the image of the power series `PowerSeries.log K` on the open unit disc. -/
theorem log_def : log K =
    ofOnOpenDisc K
      ⟨PowerSeries.log K, PowerSeries.OnOpenDisc.mem_subring.2 PowerSeries.onOpenDisc_log⟩ :=
  (rfl)

/-- The coefficient of `tⁿ` in `log (1 + t)` is `(-1)ⁿ⁺¹ / n`; for `n = 0` both sides are `0`. -/
@[simp]
theorem coe_log_natCast (n : ℕ) : (log K : ℤ → K) n = (-1) ^ (n + 1) / n := by
  simp only [log, coe_ofOnOpenDisc_natCast]
  exact PowerSeries.coeff_log_eq_neg_one_pow_div n

/-- `log (1 + t)` has no terms of nonpositive degree. -/
@[simp]
theorem coe_log_of_nonpos {n : ℤ} (hn : n ≤ 0) : (log K : ℤ → K) n = 0 := by
  rcases hn.lt_or_eq with hn | rfl
  · exact coe_ofOnOpenDisc_of_neg K _ hn
  · simpa using coe_log_natCast K 0

/-- The constant term of `log (1 + t)` is `0`. -/
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
norm `|·|_ρ` with `0 ≤ ρ < 1`, the seminorms of the open unit disc. -/
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
  have hp₁ : ‖(p : K)‖ < 1 :=
    norm_natCast_p (p := p) (K := K) ▸
      inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
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
    rw [coe_one_add_monomial_pow_natCast, coe_log_natCast, Pi.single_eq_of_ne (by omega), sub_zero,
      zpow_natCast]
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
    have hCp : 0 ≤ C * ‖(p : K)‖ ^ m := by positivity
    rcases hn.lt_or_eq with hn | rfl
    · simpa [coe_one_add_monomial_pow_of_neg K _ hn, coe_log_of_nonpos K hn.le,
        Pi.single_eq_of_ne hn.ne] using hCp
    · have h0 : (((1 + monomial 1 1) ^ p ^ m : RobbaRing K) : ℤ → K) 0 = 1 := by
        simpa using coe_one_add_monomial_pow_natCast K (p ^ m) 0
      simp [h0, hCp]

/-- **`log (1 + X) = lim ((1 + X) ^ (p ^ m) - 1) / p ^ m` on the open unit disc.** Over a complete
normed `ℚ_p`-algebra `K`, the polynomials `((1 + X) ^ (p ^ m) - 1) / p ^ m` converge to the power
series `log (1 + X)` in the topology of the open unit disc. This is
`TauCeti.RobbaRing.tendsto_laurentGaussNorm_one_add_pow_sub_log` transported along the Gauss-norm
preserving inclusion `TauCeti.RobbaRing.ofOnOpenDisc`. -/
theorem tendsto_onOpenDisc_one_add_pow_sub_log :
    Tendsto (fun m : ℕ ↦ ((p : K) ^ m)⁻¹ •
        PowerSeries.OnOpenDisc.polynomialHom (R₀ := 1) ((1 + Polynomial.X) ^ p ^ m - 1)) atTop
      (𝓝 ⟨PowerSeries.log K, PowerSeries.OnOpenDisc.mem_subring.2 PowerSeries.onOpenDisc_log⟩) := by
  refine PowerSeries.OnOpenDisc.tendsto_iff.2 fun r ↦ ?_
  have : Fact (0 < (r : ℝ)) := ⟨r.property.1⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine (tendsto_laurentGaussNorm_one_add_pow_sub_log (p := p) K r.property.1.le
    r.property.2).congr fun m ↦ ?_
  rw [← map_sub, PowerSeries.norm_eq_gaussNorm, PowerSeries.OnOpenDisc.coe_restrict,
    ← laurentGaussNorm_ofOnOpenDisc, map_sub, map_smul, ofOnOpenDisc_polynomialHom, ← log_def]
  simp

end RobbaRing

end TauCeti
