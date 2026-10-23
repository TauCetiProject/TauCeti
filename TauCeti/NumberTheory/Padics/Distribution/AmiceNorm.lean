/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.NumberTheory.Padics.Measure.MahlerDuality
public import TauCeti.RingTheory.PowerSeries.OpenDisc
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The dual stage norms and the disc norms of Amice transforms

A locally analytic distribution `μ` on `ℤ_p` is recorded by its moments
`bₙ = μ (x ↦ (x choose n))`, the coefficients of its Amice transform `F = ∑ bₙ Tⁿ`. Restricted to
the functions analytic on the discs of radius `p⁻ʰ`, `μ` has the dual stage norm

`D_h(F) = supₙ ‖bₙ‖ ‖⌊n / pʰ⌋!‖`,

computed in `ℚ_p`: Amice's basis of that stage consists of the polynomials
`⌊n / pʰ⌋! (x choose n)`. On the analytic side, `F` has the Gauss norm
`S_h(F) = supₙ ‖bₙ‖ r_hⁿ` at the radius

`r_h = p ^ (-1 / ((p - 1) pʰ))`,

which is the `pʰ`-th root of the radius `p ^ (-1 / (p - 1))` of convergence of the `p`-adic
exponential. Legendre's formula `(p - 1) v_p(m!) = m - s_p(m)` compares the two weights:
`r_hⁿ ≤ ‖⌊n / pʰ⌋!‖ ≤ p r_{h+1}ⁿ`. Hence

`S_h(F) ≤ D_h(F) ≤ p S_{h+1}(F)`,

each inequality holding as soon as its right-hand side is a supremum of a bounded family.

Since `r_h` increases to `1`, every `D_h(F)` is finite exactly when every `S_h(F)` is finite,
exactly when `F` converges on the open unit disc, that is, is restricted at every radius
`0 < ρ < 1` (`PowerSeries.OnOpenDisc`). By Amice's theorem these are the coefficient conditions
for `F` to be the Amice transform of a distribution. A bound at a single level does not
suffice: the moments `1 / n!` of the exponential series have finite level-zero norm but infinite
level-one norm. The series `log (1 + T)`, with coefficients `(-1) ^ (n + 1) / n`, lies on the
open unit disc (`PowerSeries.onOpenDisc_log`), but its coefficients are unbounded, so it is not
the Amice transform of a measure. Informally, it is the transform of the derivative at zero, a
distribution that is not a measure.

The supremum `amiceDualNorm` is a real `iSup`, so its value is meaningful only for bounded
families; every statement assumes the relevant boundedness. The disc norm `S_h` is Mathlib's
`PowerSeries.gaussNorm` at the radius `TauCeti.amiceRadius p h`.

## Main definitions

* `TauCeti.amiceRadius p h`: the radius `p ^ (-1 / ((p - 1) pʰ))`.
* `TauCeti.amiceDualNorm p h F`: the dual stage norm `supₙ ‖coeff n F‖ ‖⌊n / pʰ⌋!‖`, with the
  basic API `TauCeti.le_amiceDualNorm` and `TauCeti.amiceDualNorm_le`.

## Main results

* `TauCeti.amiceRadius_pow_le_norm_factorial`,
  `TauCeti.norm_factorial_le_mul_amiceRadius_succ_pow`: `r_hⁿ ≤ ‖⌊n / pʰ⌋!‖ ≤ p r_{h+1}ⁿ`.
* `TauCeti.gaussNorm_amiceRadius_le_amiceDualNorm`: `S_h(F) ≤ D_h(F)`.
* `TauCeti.amiceDualNorm_le_mul_gaussNorm_amiceRadius_succ`: `D_h(F) ≤ p S_{h+1}(F)`.
* `TauCeti.onOpenDisc_iff_forall_hasGaussNorm_amiceRadius` and
  `TauCeti.onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial`: all disc norms,
  equivalently all dual stage norms, are finite exactly when the series lies on the open unit
  disc.
* `TauCeti.bddAbove_norm_coeff_mul_norm_factorial_zero_exp` and
  `TauCeti.not_bddAbove_norm_coeff_mul_norm_factorial_one_exp`: the exponential series has finite
  dual stage norm at level zero but not at level one.
* `TauCeti.not_bddAbove_norm_coeff_log` and `TauCeti.log_notMem_range_amiceTransform`: the
  coefficients of `log (1 + T)` are unbounded in `ℚ_p`, so it is not the Amice transform of a
  measure.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3,
  Theorem 3.43.
-/

public section

open Filter Topology Nat

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The radii `r_h` -/

/-- The radius `r_h = p ^ (-1 / ((p - 1) pʰ))` attached to the analytic level `h`: the `pʰ`-th
root of the radius of convergence `p ^ (-1 / (p - 1))` of the `p`-adic exponential. The Gauss
norm of an Amice transform at this radius is comparable with its dual stage norm at level `h`. -/
noncomputable def amiceRadius (h : ℕ) : ℝ :=
  (p : ℝ) ^ (-(1 / (((p : ℝ) - 1) * (p : ℝ) ^ h)))

omit hp in
/-- The closed form of the radius `r_h`. -/
theorem amiceRadius_def (h : ℕ) :
    amiceRadius p h = (p : ℝ) ^ (-(1 / (((p : ℝ) - 1) * (p : ℝ) ^ h))) :=
  (rfl)

variable {p}

private theorem one_lt_natCast : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

private theorem natCast_pos : (0 : ℝ) < p := zero_lt_one.trans (one_lt_natCast (p := p))

private theorem sub_one_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (one_lt_natCast (p := p))

/-- The radii `r_h` are positive. -/
theorem amiceRadius_pos (h : ℕ) : 0 < amiceRadius p h :=
  Real.rpow_pos_of_pos natCast_pos _

/-- The radii `r_h` are smaller than `1`. -/
theorem amiceRadius_lt_one (h : ℕ) : amiceRadius p h < 1 := by
  refine Real.rpow_lt_one_of_one_lt_of_neg one_lt_natCast (neg_neg_of_pos ?_)
  have := sub_one_pos (p := p)
  have := natCast_pos (p := p)
  positivity

omit hp in
/-- The `n`-th power of `r_h` is `p ^ (-n / ((p - 1) pʰ))`. -/
theorem amiceRadius_pow (h n : ℕ) :
    amiceRadius p h ^ n = (p : ℝ) ^ (-((n : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ h))) := by
  rw [amiceRadius_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The radii `r_h` increase strictly with the level `h`. -/
theorem strictMono_amiceRadius : StrictMono (amiceRadius p) := by
  refine strictMono_nat_of_lt_succ fun h ↦ Real.rpow_lt_rpow_of_exponent_lt one_lt_natCast ?_
  have := sub_one_pos (p := p)
  have := natCast_pos (p := p)
  rw [neg_lt_neg_iff, pow_succ]
  gcongr
  exact lt_mul_of_one_lt_right (by positivity) one_lt_natCast

/-- The radii `r_h` tend to `1`. -/
theorem tendsto_amiceRadius : Tendsto (amiceRadius p) atTop (𝓝 1) := by
  have hexp : Tendsto (fun h : ℕ ↦ -(1 / (((p : ℝ) - 1) * (p : ℝ) ^ h))) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_atTop_of_one_lt (one_lt_natCast (p := p))).const_mul_atTop
      (sub_one_pos (p := p))).inv_tendsto_atTop.neg
  have hlim := (Real.continuousAt_const_rpow (natCast_pos (p := p)).ne').tendsto.comp hexp
  rw [Real.rpow_zero] at hlim
  exact hlim

/-! ### The weights `‖⌊n / pʰ⌋!‖` -/

/-- The norm in `ℚ_p` of a nonzero natural number `m` is `p ^ (-v_p(m))`, as a real power. -/
private theorem norm_natCast_eq_rpow {m : ℕ} (hm : m ≠ 0) :
    ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℝ)) := by
  rw [Padic.norm_natCast_eq_zpow hm, ← Real.rpow_intCast]
  simp

/-- **Lower weight bound.** `r_hⁿ ≤ ‖⌊n / pʰ⌋!‖`: the weight `r_hⁿ` of the Gauss norm at the
radius `r_h` is at most the weight of the dual stage norm at level `h`. -/
theorem amiceRadius_pow_le_norm_factorial (h n : ℕ) :
    amiceRadius p h ^ n ≤ ‖((n / p ^ h)! : ℚ_[p])‖ := by
  -- Legendre's formula gives `(p - 1) v_p(m!) ≤ m`, and `m pʰ ≤ n` for `m = ⌊n / pʰ⌋`.
  rw [amiceRadius_pow, norm_natCast_eq_rpow (factorial_ne_zero _)]
  refine Real.rpow_le_rpow_of_exponent_le one_lt_natCast.le (neg_le_neg ?_)
  have hsub := sub_one_pos (p := p)
  have := natCast_pos (p := p)
  rw [le_div_iff₀ (by positivity)]
  have hleg : (p - 1) * padicValNat p (n / p ^ h)! ≤ n / p ^ h := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hle : (p - 1) * padicValNat p (n / p ^ h)! * p ^ h ≤ n :=
    (Nat.mul_le_mul_right _ hleg).trans (Nat.div_mul_le_self n _)
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  calc (padicValNat p (n / p ^ h)! : ℝ) * (((p : ℝ) - 1) * (p : ℝ) ^ h)
      = (((p - 1) * padicValNat p (n / p ^ h)! * p ^ h : ℕ) : ℝ) := by
        push_cast [hcast]; ring
    _ ≤ n := by exact_mod_cast hle

/-- **Upper weight bound.** `‖⌊n / pʰ⌋!‖ ≤ p r_{h+1}ⁿ`: the weight of the dual stage norm at
level `h` is at most `p` times the weight `r_{h+1}ⁿ` of the Gauss norm at the radius `r_{h+1}`. -/
theorem norm_factorial_le_mul_amiceRadius_succ_pow (h n : ℕ) :
    ‖((n / p ^ h)! : ℚ_[p])‖ ≤ p * amiceRadius p (h + 1) ^ n := by
  rw [amiceRadius_pow, norm_natCast_eq_rpow (factorial_ne_zero _)]
  have hp0 := natCast_pos (p := p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  -- Compare both sides through `k = ⌊n / p^(h+1)⌋`.
  set k := n / p ^ (h + 1)
  -- `v_p(⌊n / pʰ⌋!) ≥ ⌊⌊n / pʰ⌋ / p⌋ = k`
  have hk : k ≤ padicValNat p (n / p ^ h)! := by
    rw [← padicValNat_mul_div_factorial, padicValNat_factorial_mul, Nat.div_div_eq_div_mul,
      ← pow_succ]
    exact Nat.le_add_left _ _
  have hkv : (k : ℝ) ≤ padicValNat p (n / p ^ h)! := by exact_mod_cast hk
  -- `n < p^(h+1) (k + 1)`
  have hn : (n : ℝ) < (p : ℝ) ^ (h + 1) * (k + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ n (pow_pos hp.out.pos _)
  have hP : (0 : ℝ) < (p : ℝ) ^ (h + 1) := by positivity
  have hdiv : (n : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ (h + 1)) ≤ k + 1 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p - 2) hP.le)
      (by positivity : (0 : ℝ) ≤ k + 1)]
  calc (p : ℝ) ^ (-(padicValNat p (n / p ^ h)! : ℝ))
      ≤ (p : ℝ) ^ (1 + -((n : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ (h + 1)))) :=
        Real.rpow_le_rpow_of_exponent_le one_lt_natCast.le (by linarith)
    _ = p * (p : ℝ) ^ (-((n : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ (h + 1)))) := by
        rw [Real.rpow_add hp0, Real.rpow_one]

/-! ### The dual stage norm and its comparison with the disc norms -/

variable (p) {K : Type*} [NormedRing K]

/-- The dual stage norm `D_h(F) = supₙ ‖coeff n F‖ ‖⌊n / pʰ⌋!‖` of a power series `F`, the
factorials being taken in `ℚ_p`. When `F` is the Amice transform of a distribution, Amice's basis
theorem identifies it with the norm of the distribution on the functions analytic on the discs of
radius `p⁻ʰ`. As a real
supremum it is meaningful only when the family is bounded above. -/
noncomputable def amiceDualNorm (h : ℕ) (F : PowerSeries K) : ℝ :=
  ⨆ n, ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖

variable {p} in
/-- The dual stage norm is the supremum of the terms `‖coeff n F‖ ‖⌊n / pʰ⌋!‖`. -/
theorem amiceDualNorm_def (h : ℕ) (F : PowerSeries K) :
    amiceDualNorm p h F = ⨆ n, ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ :=
  (rfl)

variable {p} {F : PowerSeries K}

/-- The lower weight bound, multiplied by the norm of a coefficient: the term of the Gauss norm at
the radius `r_h` is at most the term of the dual stage norm at level `h`. -/
theorem norm_coeff_mul_amiceRadius_pow_le (F : PowerSeries K) (h n : ℕ) :
    ‖F.coeff n‖ * amiceRadius p h ^ n ≤ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ :=
  mul_le_mul_of_nonneg_left (amiceRadius_pow_le_norm_factorial h n) (norm_nonneg _)

/-- The upper weight bound, multiplied by the norm of a coefficient: the term of the dual stage
norm at level `h` is at most `p` times the term of the Gauss norm at the radius `r_{h+1}`. -/
theorem norm_coeff_mul_norm_factorial_le (F : PowerSeries K) (h n : ℕ) :
    ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤ p * (‖F.coeff n‖ * amiceRadius p (h + 1) ^ n) :=
  (mul_le_mul_of_nonneg_left (norm_factorial_le_mul_amiceRadius_succ_pow h n)
    (norm_nonneg _)).trans_eq (mul_left_comm _ _ _)

/-- Each term of a bounded family is at most the dual stage norm. -/
theorem le_amiceDualNorm {h : ℕ}
    (hF : BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖)) (n : ℕ) :
    ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤ amiceDualNorm p h F :=
  le_ciSup hF n

/-- A common bound on the terms bounds the dual stage norm. -/
theorem amiceDualNorm_le {h : ℕ} {C : ℝ}
    (hC : ∀ n, ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤ C) : amiceDualNorm p h F ≤ C :=
  ciSup_le hC

/-- The dual stage norm is nonnegative. -/
theorem amiceDualNorm_nonneg (h : ℕ) (F : PowerSeries K) : 0 ≤ amiceDualNorm p h F :=
  Real.iSup_nonneg fun _ ↦ by positivity

/-- A bounded dual stage norm at level `h` bounds the Gauss norm at the radius `r_h`. -/
theorem hasGaussNorm_amiceRadius_of_bddAbove {h : ℕ}
    (hF : BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖)) :
    F.HasGaussNorm norm (amiceRadius p h) := by
  obtain ⟨B, hB⟩ := hF
  exact ⟨B, Set.forall_mem_range.mpr fun n ↦
    (hB ⟨n, rfl⟩).trans' (norm_coeff_mul_amiceRadius_pow_le F h n)⟩

/-- A bounded Gauss norm at the radius `r_{h+1}` bounds the dual stage norm at level `h`. -/
theorem bddAbove_norm_coeff_mul_norm_factorial_of_hasGaussNorm {h : ℕ}
    (hF : F.HasGaussNorm norm (amiceRadius p (h + 1))) :
    BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖) := by
  obtain ⟨B, hB⟩ := hF
  have := natCast_pos (p := p)
  exact ⟨p * B, Set.forall_mem_range.mpr fun n ↦ (norm_coeff_mul_norm_factorial_le F h n).trans
    (mul_le_mul_of_nonneg_left (hB ⟨n, rfl⟩) (by positivity))⟩

/-- **`S_h ≤ D_h`.** The Gauss norm at the radius `r_h` is at most the dual stage norm at level
`h`, provided the latter is the supremum of a bounded family. -/
theorem gaussNorm_amiceRadius_le_amiceDualNorm {h : ℕ}
    (hF : BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖)) :
    F.gaussNorm norm (amiceRadius p h) ≤ amiceDualNorm p h F := by
  rw [PowerSeries.gaussNorm_eq]
  exact ciSup_le fun n ↦ (norm_coeff_mul_amiceRadius_pow_le F h n).trans (le_amiceDualNorm hF n)

/-- **`D_h ≤ p S_{h+1}`.** The dual stage norm at level `h` is at most `p` times the Gauss norm at
the radius `r_{h+1}`, provided the latter is the supremum of a bounded family. -/
theorem amiceDualNorm_le_mul_gaussNorm_amiceRadius_succ {h : ℕ}
    (hF : F.HasGaussNorm norm (amiceRadius p (h + 1))) :
    amiceDualNorm p h F ≤ p * F.gaussNorm norm (amiceRadius p (h + 1)) :=
  amiceDualNorm_le fun n ↦ (norm_coeff_mul_norm_factorial_le F h n).trans
    (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm _ _ _ hF n) natCast_pos.le)

/-! ### Finiteness at every level -/

/-- A series lies on the open unit disc exactly when it is restricted at every radius `r_h`. -/
theorem onOpenDisc_iff_forall_isRestricted_amiceRadius :
    F.OnOpenDisc 1 ↔ ∀ h, F.IsRestricted (amiceRadius p h) :=
  PowerSeries.onOpenDisc_iff_of_tendsto
    (fun h ↦ (abs_of_pos (amiceRadius_pos h)).trans_lt (amiceRadius_lt_one h)) tendsto_amiceRadius

/-- **All disc norms are finite exactly on the open unit disc.** A series has a finite Gauss norm
at every radius `r_h` exactly when it is restricted at every radius `0 < ρ < 1`. -/
theorem onOpenDisc_iff_forall_hasGaussNorm_amiceRadius :
    F.OnOpenDisc 1 ↔ ∀ h, F.HasGaussNorm norm (amiceRadius p h) := by
  rw [onOpenDisc_iff_forall_isRestricted_amiceRadius (p := p)]
  refine ⟨fun hF h ↦ TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (hF h), fun hF h ↦ ?_⟩
  exact (hF (h + 1)).isRestricted_of_abs_lt
    ((abs_of_pos (amiceRadius_pos h)).trans_lt (strictMono_amiceRadius h.lt_succ_self))

/-- **All dual stage norms are finite exactly on the open unit disc.** The families
`‖coeff n F‖ ‖⌊n / pʰ⌋!‖` are bounded for every level `h` exactly when `F` is restricted at every
radius `0 < ρ < 1`. -/
theorem onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial :
    F.OnOpenDisc 1 ↔
      ∀ h, BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖) := by
  rw [onOpenDisc_iff_forall_hasGaussNorm_amiceRadius (p := p)]
  exact ⟨fun hF h ↦ bddAbove_norm_coeff_mul_norm_factorial_of_hasGaussNorm (hF (h + 1)),
    fun hF h ↦ hasGaussNorm_amiceRadius_of_bddAbove (hF h)⟩

/-! ### Examples: the exponential and the logarithm -/

/-- A family taking every value `pᵏ` is unbounded. -/
private theorem not_bddAbove_range_of_eq_pow {f : ℕ → ℝ} (g : ℕ → ℕ)
    (hf : ∀ k, f (g k) = (p : ℝ) ^ k) : ¬ BddAbove (Set.range f) := by
  refine fun hB ↦ not_bddAbove_of_tendsto_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_natCast (p := p))) (hB.mono ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨g k, hf k⟩

/-- The moments `1 / n!` of the exponential series have a finite dual stage norm at level zero:
every term `‖1 / n!‖ ‖n!‖` is `1`. -/
theorem bddAbove_norm_coeff_mul_norm_factorial_zero_exp :
    BddAbove (Set.range fun n ↦
      ‖(PowerSeries.exp ℚ_[p]).coeff n‖ * ‖((n / p ^ 0)! : ℚ_[p])‖) :=
  ⟨1, Set.forall_mem_range.mpr fun n ↦ by simp [PowerSeries.coeff_exp, factorial_ne_zero]⟩

/-- **A bound at one level does not suffice.** The moments `1 / n!` of the exponential series have
an infinite dual stage norm at level one: the term at `n = p k` is `‖k!‖ / ‖(p k)!‖ = pᵏ`. -/
theorem not_bddAbove_norm_coeff_mul_norm_factorial_one_exp :
    ¬ BddAbove (Set.range fun n ↦
      ‖(PowerSeries.exp ℚ_[p]).coeff n‖ * ‖((n / p ^ 1)! : ℚ_[p])‖) :=
  not_bddAbove_range_of_eq_pow (p := p) (p * ·) fun k ↦ by
    have hk : ‖(k ! : ℚ_[p])‖ ≠ 0 := by simp [factorial_ne_zero]
    simp [PowerSeries.coeff_exp, Nat.mul_div_cancel_left _ hp.out.pos, Padic.norm_factorial_mul]
    field_simp

/-- The exponential series does not lie on the open unit disc of `ℚ_p`: its dual stage norm at
level one is infinite. -/
theorem not_onOpenDisc_exp : ¬ (PowerSeries.exp ℚ_[p]).OnOpenDisc 1 := fun h ↦
  not_bddAbove_norm_coeff_mul_norm_factorial_one_exp
    ((onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial (p := p)).mp h 1)

/-- The coefficients of `log (1 + T)` are unbounded in `ℚ_p`: the coefficient of `T ^ (p ^ k)`
has norm `pᵏ`. By contrast, `log (1 + T)` lies on the open unit disc
(`PowerSeries.onOpenDisc_log`). -/
theorem not_bddAbove_norm_coeff_log :
    ¬ BddAbove (Set.range fun n ↦ ‖(PowerSeries.log ℚ_[p]).coeff n‖) :=
  not_bddAbove_range_of_eq_pow (p := p) (p ^ ·) fun k ↦ by
    simp [PowerSeries.coeff_log, hp.out.ne_zero]

/-- **`log (1 + T)` is not the Amice transform of a measure.** The series `log (1 + T)` is not the
Amice transform of a bounded measure on `ℤ_p` with values in `ℚ_p`, its coefficients being
unbounded. Informally, it is the transform of the derivative at zero, which is therefore a
distribution but not a measure. -/
theorem log_notMem_range_amiceTransform :
    PowerSeries.log ℚ_[p] ∉
      LinearMap.range (AbstractMeasure.amiceTransform (p := p) (R := ℚ_[p])) := fun h ↦
  not_bddAbove_norm_coeff_log ((AbstractMeasure.mem_range_amiceTransform_iff _).mp h)

end TauCeti
