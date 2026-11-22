/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative bounds for rescaled p-adic exponential series

Over any seminormed commutative `ℚ_[p]`-algebra `A` with `‖(1 : A)‖ = 1` and `[Algebra ℚ A]`, the
coefficients of `exp(xX)` satisfy

`‖[Xⁿ] exp(xX)‖ cⁿ ≤ (p ^ (1 / (p - 1)) * ‖x‖ * c)ⁿ`.

Over any normed field `K` extending `ℚ_[p]` isometrically, this series is restricted at a
nonnegative radius `c` if and only if `‖x‖ * c < p ^ (-1 / (p - 1))`. Its Gauss norm is `1` on
that disc, and the Gauss norm of `exp(xX) - 1` is at most `p ^ (1 / (p - 1)) * ‖x‖ * c`. The
strict radius condition includes the dyadic case: there it reads `‖x‖ * c < 1 / 2`. At the
critical radius the weighted coefficients in degrees `p ^ k` have constant positive norm, proving
failure of restrictedness. Both series nevertheless have a Gauss norm, i.e. bounded weighted
coefficients, there: the exponential has one exactly on the closed disc
`‖x‖ * c ≤ p ^ (-1 / (p - 1))`.

For `x = log u`, these estimates give discs of radius greater than one for normal series
interpolating powers of sufficiently deep units. A quantitative Gauss norm, rather than just
convergence at integral arguments, is needed in interpolation estimates for these series.
Neither completeness nor finite dimension over `ℚ_[p]` is needed for the coefficient bounds.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58,
  Chapter IV, §1.
-/

public section

namespace PowerSeries

open Filter Topology
open TauCeti.PowerSeries

section SeminormedCommRing

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*}
  [SeminormedCommRing A] [NormOneClass A] [Algebra ℚ A] [NormedAlgebra ℚ_[p] A]

/-- A geometric majorant for the weighted coefficients of a rescaled p-adic exponential.
The norm on the coefficient algebra restricts to the usual norm on `ℚ_[p]`. -/
theorem norm_coeff_rescale_exp_mul_pow_le (x : A) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ‖coeff n (rescale x (exp A))‖ * c ^ n ≤
      ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c) ^ n := by
  have hfac := inv_anti₀
    (Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos : (0 : ℝ) < p) _)
    (Padic.rpow_neg_div_le_norm_factorial (p := p) n)
  have hbound : ‖(n.factorial : ℚ_[p])‖⁻¹ ≤ ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹)) ^ n := by
    simpa only [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p), inv_inv, div_eq_mul_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p), mul_comm] using hfac
  have hnorm : ‖algebraMap ℚ_[p] A (algebraMap ℚ ℚ_[p] (1 / (n.factorial : ℚ)))‖ =
      ‖(n.factorial : ℚ_[p])‖⁻¹ := by
    rw [norm_algebraMap']
    simp
  rw [coeff_rescale, coeff_exp, ← RingHom.map_rat_algebraMap (algebraMap ℚ_[p] A)]
  calc
    ‖x ^ n * algebraMap ℚ_[p] A (algebraMap ℚ ℚ_[p] (1 / (n.factorial : ℚ)))‖ * c ^ n
        ≤ (‖x‖ ^ n * ‖(n.factorial : ℚ_[p])‖⁻¹) * c ^ n := by
          gcongr
          exact (norm_mul_le _ _).trans <|
            mul_le_mul (norm_pow_le _ _) hnorm.le (norm_nonneg _) (by positivity)
    _ ≤ (‖x‖ ^ n * ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹)) ^ n) * c ^ n := by gcongr
    _ = ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c) ^ n := by simp only [mul_pow]; ring

/-- The rescaled exponential is restricted on every closed disc strictly inside the p-adic
exponential disc. In particular the condition is strict also for `p = 2`. -/
theorem isRestricted_rescale_exp {A : Type*} [NormedCommRing A] [NormOneClass A] [Algebra ℚ A]
    [NormedAlgebra ℚ_[p] A] {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp A)).IsRestricted c := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hlt : (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c < 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at hxc
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne'] using
      mul_lt_mul_of_pos_left hxc hpos
  rw [isRestricted_iff']
  exact squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc n))
    (norm_coeff_rescale_exp_mul_pow_le x hc)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt)

omit [NormOneClass A] [Algebra ℚ A] [NormedAlgebra ℚ_[p] A] in
/-- The closed p-adic exponential disc condition, rewritten as a geometric ratio at most one. -/
private theorem rpow_inv_mul_norm_mul_le_one {x : A} {c : ℝ}
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c ≤ 1 := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at hxc
  simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne'] using
    mul_le_mul_of_nonneg_left hxc hpos.le

/-- On the closed exponential disc, the weighted coefficients of `exp(xX)` are at most one. -/
theorem norm_coeff_rescale_exp_mul_pow_le_one {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (n : ℕ) :
    ‖coeff n (rescale x (exp A))‖ * c ^ n ≤ 1 :=
  (norm_coeff_rescale_exp_mul_pow_le x hc n).trans
    (pow_le_one₀ (by positivity) (rpow_inv_mul_norm_mul_le_one hxc))

/-- On the closed exponential disc, the weighted coefficients of `exp(xX) - 1` are at most the
geometric ratio. -/
private theorem norm_coeff_rescale_exp_sub_one_mul_pow_le {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (n : ℕ) :
    ‖coeff n (rescale x (exp A) - 1)‖ * c ^ n ≤ (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [coeff_zero_eq_constantCoeff, map_sub, constantCoeff_rescale, constantCoeff_exp,
      constantCoeff_one, sub_self, norm_zero, pow_zero, mul_one]
    positivity
  · simpa [coeff_one, hn] using (norm_coeff_rescale_exp_mul_pow_le x hc n).trans
      (pow_le_pow_of_le_one (by positivity) (rpow_inv_mul_norm_mul_le_one hxc)
        (Nat.one_le_iff_ne_zero.mpr hn))

/-- The rescaled exponential has a Gauss norm on the closed p-adic exponential disc, including
its boundary, where it is not restricted. -/
theorem hasGaussNorm_rescale_exp {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp A)).HasGaussNorm norm c :=
  ⟨1, Set.forall_mem_range.mpr (norm_coeff_rescale_exp_mul_pow_le_one hc hxc)⟩

/-- The Gauss norm of `exp(xX)` is exactly one as long as the coefficient majorant has ratio
at most one. This bound also applies at the boundary, without asserting restrictedness there. -/
theorem gaussNorm_rescale_exp {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp A)).gaussNorm norm c = 1 := by
  have h := gaussNorm_eq_of_forall_le (s := 0) (a := rescale x (exp A)) (c := c)
    (v := norm) fun n ↦ (norm_coeff_rescale_exp_mul_pow_le_one hc hxc n).trans (by simp)
  simpa using h

/-- On the closed p-adic exponential disc, including its boundary, `exp(xX) - 1` has a Gauss norm.
-/
theorem hasGaussNorm_rescale_exp_sub_one {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp A) - 1).HasGaussNorm norm c :=
  ⟨_, Set.forall_mem_range.mpr (norm_coeff_rescale_exp_sub_one_mul_pow_le hc hxc)⟩

/-- On a disc in the p-adic exponential range, subtracting the constant term leaves Gauss norm
at most the geometric ratio. This is a uniform estimate for the distance from `exp(xX)` to `1`.
-/
theorem gaussNorm_rescale_exp_sub_one_le {x : A} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp A) - 1).gaussNorm norm c ≤
      (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c := by
  rw [gaussNorm_eq]
  exact ciSup_le (norm_coeff_rescale_exp_sub_one_mul_pow_le hc hxc)

end SeminormedCommRing

section NormedField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*}
  [NormedField K] [Algebra ℚ K] [NormedAlgebra ℚ_[p] K]

/-- Along the degrees `p ^ k`, the weighted coefficients of the exponential at its critical
radius have constant positive norm. This is the obstruction to convergence at the boundary. -/
theorem norm_coeff_exp_mul_pow_prime_pow (k : ℕ) :
    ‖coeff (p ^ k) (exp K)‖ *
        ((p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) ^ (p ^ k) =
      (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
  simpa [coeff_exp] using TauCeti.norm_inv_factorial_pow_prime_mul_rpow (p := p) (D := K) k

/-- The exact criterion for a rescaled p-adic exponential to be restricted at a real radius.
The boundary is excluded for every prime, including `2`. The case `x = 0` is included. -/
theorem isRestricted_rescale_exp_iff {x : K} {c : ℝ} (hc : 0 ≤ c) :
    (rescale x (exp K)).IsRestricted c ↔
      ‖x‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
  refine ⟨fun hf ↦ ?_, isRestricted_rescale_exp hc⟩
  by_contra hlt
  have hle := not_lt.mp hlt
  have hρ : 0 < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hbound (k : ℕ) : (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) ≤
      ‖coeff (p ^ k) (rescale x (exp K))‖ * c ^ (p ^ k) := by
    calc
      _ = ‖coeff (p ^ k) (exp K)‖ *
          ((p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) ^ (p ^ k) :=
        (norm_coeff_exp_mul_pow_prime_pow (K := K) k).symm
      _ ≤ ‖coeff (p ^ k) (exp K)‖ * (‖x‖ * c) ^ (p ^ k) := by gcongr
      _ = _ := by simp [coeff_rescale, norm_mul, norm_pow, mul_pow, mul_comm, mul_assoc]
  have hlim := ((isRestricted_iff' c _).mp hf).comp
    (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hρ)).exists
  exact (not_lt_of_ge (hbound k)) hk

/-- The exact criterion for a rescaled p-adic exponential to have a Gauss norm at a real radius.
Unlike restrictedness, the boundary is included. The case `x = 0` is included. -/
theorem hasGaussNorm_rescale_exp_iff {x : K} {c : ℝ} (hc : 0 ≤ c) :
    (rescale x (exp K)).HasGaussNorm norm c ↔
      ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
  refine ⟨fun hf ↦ le_of_not_gt fun hlt ↦ ?_, hasGaussNorm_rescale_exp hc⟩
  have hρ : 0 < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hx : 0 < ‖x‖ := pos_of_mul_pos_left (hρ.trans hlt) hc
  have hr : 0 ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) / ‖x‖ := (div_pos hρ hx).le
  have hf' := hf.isRestricted_of_abs_lt (by
    rw [abs_of_nonneg hr]
    exact (div_lt_iff₀' hx).mpr hlt)
  have hlt' := (isRestricted_rescale_exp_iff (p := p) hr).mp hf'
  rw [mul_div_cancel₀ _ hx.ne'] at hlt'
  exact (lt_irrefl _) hlt'

end NormedField

end PowerSeries
