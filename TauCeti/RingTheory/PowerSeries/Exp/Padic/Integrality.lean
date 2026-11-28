/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Subst
public import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Divisibility of `exp(G) - 1`, integral logarithms and prime-to-`p` roots

Let `K` be a normed field extending `ℚ_[p]` isometrically, and write `exp(G)` for the substitution
`(PowerSeries.exp K).subst G` of a power series `G` without constant term. A number `c` divides a
coefficient `a` when `‖a‖ ≤ ‖c‖`, and a series is integral when its coefficients have norm at most
`1`. The condition `v_p(c) ≥ 1 / (p - 1)` reads `‖c‖ ≤ p ^ (-1 / (p - 1))`.

* **Divisibility of `exp(G) - 1`.** If `c` divides the coefficients of `G` below a degree `l`, so
  does it divide those of `exp(G) - 1`. The terms are `G ^ j / j!`, and
  `‖c‖ ^ j / ‖j!‖ ≤ ‖c‖` for `j ≥ 1` by Legendre's bound `v_p(j!) ≤ (j - 1) / (p - 1)`.
* **Integral logarithms.** If `c ≠ 0` and `exp(c G) = 1 + c H` with `H` integral, then `G` is
  integral: `c G = log(1 + c H)` has terms `± (c H) ^ j / j`, and `‖c‖ ^ j / ‖j‖ ≤ ‖c‖`.
* **Prime-to-`p` roots.** If `f` has constant coefficient of norm one and `f ^ m` is integral for
  some `m` with `‖m‖ = 1`, then `f` is integral: the coefficient of degree `n` of `f ^ m` is
  `m f(0) ^ (m - 1)` times that of `f`, plus a polynomial in the coefficients of lower degree.
  For `f = exp(G)` this applies to every `m` not divisible by `p`.

For the exponential, the last two hold also for the integral series `F.subst T` in a series `T`
without constant term (the ring `𝒪[[T]]`): if `exp(c G) = 1 + c H₀(T)`, then `G = G₀(T)` with
`G₀ = log(1 + c H₀) / c` integral, and if `exp(G) ^ m = F(T)`, then `exp(G) = f₀(T)` with
`f₀ = exp(log(F) / m)` integral.

## Main results

* `PowerSeries.norm_coeff_subst_exp_sub_one_mul_prod_le`: the weighted coefficientwise bound for
  `exp(B) - 1`, `B` a multivariate series.
* `PowerSeries.norm_coeff_subst_exp_sub_one_le`: `c` divides `exp(G) - 1` below the degree `l`
  if it divides `G` there.
* `PowerSeries.norm_coeff_le_one_of_subst_exp_smul_eq`,
  `PowerSeries.exists_eq_subst_of_subst_exp_smul_eq`: `exp(c G) = 1 + c H` with `H` integral
  (in `T`) forces `G` integral (in `T`).
* `PowerSeries.norm_coeff_le_one_of_norm_coeff_pow_le_one`: over an ultrametric field, `f` with
  `‖f(0)‖ = 1` is integral in the degrees at most `n` when `f ^ m` is, for `‖m‖ = 1`.
* `PowerSeries.exists_subst_exp_eq_subst_of_pow_eq_subst`: `exp(G)` is integral in `T` when
  `exp(G) ^ m` is, for `m` prime to `p`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58,
  Chapter IV, §1.
* The statements follow the formal proof in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `Lib/General/Algebra/SeriesBounds.lean` (`New.norm_coeff_expSubst_sub_one_le`,
  `New.IsSeriesGenerator.mem_of_expSubst_smul_eq`,
  `New.IsSeriesGenerator.expSubst_mem_of_pow_mem`).
-/

public section

namespace PowerSeries

open Nat

/-! ### Coefficient bounds in one variable -/

section OneVariable

variable {R : Type*} [SeminormedCommRing R]

/-- A coefficient bound in degrees at most `n` of a series in one variable, read as the weighted
bound at radius one of `MvPowerSeries.norm_coeff_subst_mul_prod_le` below the index `n`. -/
private theorem norm_coeff_mul_prod_le_of_le {g : R⟦X⟧} {n : ℕ} {r : ℝ}
    (hg : ∀ k ≤ n, ‖coeff k g‖ ≤ r) :
    ∀ m ≤ Finsupp.single () n,
      ‖MvPowerSeries.coeff m g‖ * m.prod (fun _ e ↦ (1 : ℝ) ^ e) ≤ r := by
  intro m hm
  have hmn : m () ≤ n := by simpa using hm ()
  rw [← coeff_def (s := m) rfl]
  simpa [Finsupp.prod] using hg _ hmn

variable [IsUltrametricDist R]

/-- The ultrametric substitution bound in one variable: if `‖coeff k g‖ ≤ ρ` for `k ≤ n` and
`‖coeff j f‖ ρ ^ j ≤ s` for all `j`, then `‖coeff n (f (g))‖ ≤ s`. -/
private theorem norm_coeff_subst_le {g : R⟦X⟧} (hg : constantCoeff g = 0) {n : ℕ} {ρ s : ℝ}
    (hgn : ∀ k ≤ n, ‖coeff k g‖ ≤ ρ) {f : R⟦X⟧} (hf : ∀ j, ‖coeff j f‖ * ρ ^ j ≤ s) :
    ‖coeff n (f.subst g)‖ ≤ s := by
  simpa [Finsupp.prod, coeff_def] using norm_coeff_subst_mul_prod_le (c := fun _ : Unit ↦ 1)
    (fun _ ↦ zero_le_one) (HasSubst.of_constantCoeff_zero' hg)
    (norm_coeff_mul_prod_le_of_le hgn) hf

/-- Powers of a series that is integral in degrees at most `n` are integral there. -/
private theorem norm_coeff_pow_le_one [NormOneClass R] {g : R⟦X⟧} {n : ℕ}
    (hg : ∀ k ≤ n, ‖coeff k g‖ ≤ 1) (j : ℕ) : ‖coeff n (g ^ j)‖ ≤ 1 := by
  simpa [Finsupp.prod, coeff_def] using MvPowerSeries.norm_coeff_pow_mul_prod_le
    (c := fun _ : Unit ↦ 1) (fun _ ↦ zero_le_one) (norm_coeff_mul_prod_le_of_le hg) j

end OneVariable

/-- `‖1 / n‖ ≤ ‖1 / n!‖` over an ultrametric field of characteristic zero, since `n!` is `n` times
an integer. -/
private theorem norm_inv_natCast_le_norm_inv_factorial {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CharZero K] (n : ℕ) : ‖(n : K)⁻¹‖ ≤ ‖((n ! : ℕ) : K)⁻¹‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [norm_inv, norm_inv, ← Nat.mul_factorial_pred hn, Nat.cast_mul, norm_mul]
  refine inv_anti₀ (mul_pos (norm_pos_iff.2 (Nat.cast_ne_zero.2 hn))
    (norm_pos_iff.2 (Nat.cast_ne_zero.2 (factorial_ne_zero _))))
    (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _))

/-! ### Divisibility of `exp(G) - 1` and integral logarithms -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

/-- For `0 ≤ r ≤ p ^ (-1 / (p - 1))` and `n ≠ 0`, `‖1 / n!‖ r ^ n ≤ r`: this is
`v_p(n!) ≤ (n - 1) / (p - 1)`, in the form
`TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial`. -/
private theorem norm_inv_factorial_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {n : ℕ} (hn : n ≠ 0) :
    ‖((n ! : ℕ) : K)⁻¹‖ * r ^ n ≤ r := by
  have hfac : r ^ (n - 1) ≤ ‖((n ! : ℕ) : K)‖ :=
    (pow_le_pow_left₀ hr0 (hr.trans_eq (by simp [TauCeti.amiceRadius_def])) _).trans
      (TauCeti.amiceRadius_zero_pow_sub_one_le_norm_factorial (p := p) hn)
  have hpos : 0 < ‖((n ! : ℕ) : K)‖ := by
    rw [TauCeti.norm_natCast_eq_norm_padic (p := p), norm_pos_iff]
    exact_mod_cast factorial_ne_zero n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [norm_inv, pow_succ, ← mul_assoc]
  exact mul_le_of_le_one_left hr0 (inv_mul_le_one_of_le₀ hfac hpos.le)

variable [Algebra ℚ K] {σ : Type*} {c : σ → ℝ}

/-- **Divisibility of `exp(B) - 1`, coefficientwise.** Let `B` have no constant term, and let
`r ≤ p ^ (-1 / (p - 1))` bound the weighted coefficients `‖coeff m B‖ * ∏ᵢ cᵢ ^ mᵢ` for `m ≤ n`.
Then `r` bounds the weighted coefficient of `exp(B) - 1` at `n`. -/
theorem norm_coeff_subst_exp_sub_one_mul_prod_le (hc : 0 ≤ c) {B : MvPowerSeries σ K}
    (hB : MvPowerSeries.constantCoeff B = 0) {r : ℝ} (hr : r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹))
    {n : σ →₀ ℕ} (hBn : ∀ m ≤ n, ‖MvPowerSeries.coeff m B‖ * m.prod (c · ^ ·) ≤ r) :
    ‖MvPowerSeries.coeff n ((exp K).subst B - 1)‖ * n.prod (c · ^ ·) ≤ r := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hsub : HasSubst B := .of_constantCoeff_zero hB
  have hr0 : 0 ≤ r := by simpa [hB] using hBn 0 (_root_.zero_le)
  rw [← subst_one (R := K) B, ← subst_sub hsub]
  refine norm_coeff_subst_mul_prod_le hc hsub hBn fun j ↦ ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simpa using hr0
  · rw [coeff_exp_sub_one_of_ne_zero hj]
    exact norm_inv_factorial_mul_pow_le hr0 hr hj

/-- **Divisibility of `exp(G) - 1`.** If `G` has no constant term, `r ≤ p ^ (-1 / (p - 1))` and
`‖coeff k G‖ ≤ r` in the degrees `k < l`, then `‖coeff k (exp(G) - 1)‖ ≤ r` there. With `r = ‖c‖`:
if `c` divides the coefficients of `G` below `l`, it divides those of `exp(G) - 1`. -/
theorem norm_coeff_subst_exp_sub_one_le {G : K⟦X⟧} (hG : constantCoeff G = 0) {r : ℝ}
    (hr : r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {l : ℕ} (hGl : ∀ k < l, ‖coeff k G‖ ≤ r) :
    ∀ k < l, ‖coeff k ((exp K).subst G - 1)‖ ≤ r := fun k hk ↦ by
  simpa [Finsupp.prod, coeff_def] using norm_coeff_subst_exp_sub_one_mul_prod_le
    (c := fun _ : Unit ↦ 1) (fun _ ↦ zero_le_one) hG hr
    (norm_coeff_mul_prod_le_of_le fun i hi ↦ hGl i (hi.trans_lt hk))

/-- **Integral logarithms, coefficientwise.** Let `a ≠ 0` with `‖a‖ ≤ p ^ (-1 / (p - 1))`, and
let `G` have no constant term. If `exp(a G) = 1 + a H` and `H` is integral in the degrees at most
`n`, then the coefficient of `G` of degree `n` is integral. -/
theorem norm_coeff_le_one_of_subst_exp_smul_eq {a : K} (ha0 : a ≠ 0)
    (ha : ‖a‖ ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {G H : K⟦X⟧} (hG : constantCoeff G = 0)
    (h : (exp K).subst (a • G) = 1 + a • H) {n : ℕ} (hH : ∀ k ≤ n, ‖coeff k H‖ ≤ 1) :
    ‖coeff n G‖ ≤ 1 := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have : CharZero K := algebraRat.charZero K
  have haG : constantCoeff (a • G) = 0 := by simp [hG]
  have haH : constantCoeff (a • H) = 0 := by
    have h0 := congrArg constantCoeff h
    rw [constantCoeff_subst_exp haG, map_add, map_one, left_eq_add] at h0
    exact h0
  -- `a G = log (exp (a G)) = log (1 + a H)`.
  have hlog : a • G = (log K).subst (a • H) := by
    rw [← logOf_subst_exp haG, h, logOf_eq, add_sub_cancel_left]
  have key : ‖coeff n (a • G)‖ ≤ ‖a‖ := by
    rw [hlog]
    refine norm_coeff_subst_le haH (ρ := ‖a‖) (fun k hk ↦ ?_) fun j ↦ ?_
    · rw [coeff_smul, smul_eq_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg a) (hH k hk)
    · rcases eq_or_ne j 0 with rfl | hj
      · simp
      rw [coeff_log_eq_neg_one_pow_div, div_eq_mul_inv, norm_mul, norm_pow, norm_neg, norm_one,
        one_pow, one_mul]
      exact (mul_le_mul_of_nonneg_right (norm_inv_natCast_le_norm_inv_factorial j)
        (by positivity)).trans (norm_inv_factorial_mul_pow_le (norm_nonneg a) ha hj)
  rw [coeff_smul, smul_eq_mul, norm_mul] at key
  exact le_of_mul_le_mul_left (by rwa [mul_one]) (norm_pos_iff.2 ha0)

end Padic

/-! ### Prime-to-`p` roots -/

section Root

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- For `n ≠ 0`, the coefficient of degree `n` of `f ^ m` is that of `t ^ m`, where `t` is the
truncation of `f` below `n`, plus `m f(0) ^ (m - 1)` times the coefficient of degree `n` of `f`. -/
private theorem coeff_pow_eq_coeff_trunc_pow_add {R : Type*} [CommRing R] (f : R⟦X⟧) {n : ℕ}
    (hn : n ≠ 0) (m : ℕ) :
    coeff n (f ^ m) = coeff n (((trunc n f : Polynomial R) : R⟦X⟧) ^ m) +
      m * constantCoeff f ^ (m - 1) * coeff n f := by
  set t : R⟦X⟧ := ((trunc n f : Polynomial R) : R⟦X⟧)
  set q : R⟦X⟧ := mk fun i ↦ coeff (i + n) f
  have hft : f - t = X ^ n * q := sub_eq_of_eq_add (eq_X_pow_mul_shift_add_trunc n f)
  have ht0 : constantCoeff t = constantCoeff f := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_coe_trunc_of_lt (Nat.pos_of_ne_zero hn)]
  -- `f ^ m - t ^ m = (∑ fⁱ t^(m - 1 - i)) (f - t)`, whose constant factor is `m f(0) ^ (m - 1)`.
  rw [← sub_eq_iff_eq_add', ← map_sub, ← (Commute.all f t).geom_sum₂_mul, hft, mul_left_comm,
    coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul,
    map_sum, map_pow, ht0, geom_sum₂_self]
  simp [q]

/-- **Prime-to-`p` roots, coefficientwise.** Over an ultrametric field, let `f` have constant
coefficient of norm one and let `‖m‖ = 1`. If `f ^ m` is integral in the degrees at most `n`, then
the coefficient of `f` of degree `n` is integral. -/
theorem norm_coeff_le_one_of_norm_coeff_pow_le_one {f : K⟦X⟧} (hf : ‖constantCoeff f‖ = 1)
    {m : ℕ} (hm : ‖(m : K)‖ = 1) {n : ℕ} (h : ∀ k ≤ n, ‖coeff k (f ^ m)‖ ≤ 1) :
    ‖coeff n f‖ ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hf]
  have ht : ∀ k ≤ n, ‖coeff k ((trunc n f : Polynomial K) : K⟦X⟧)‖ ≤ 1 := fun k _ ↦ by
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hkn
    · exact ih k hkn fun i hi ↦ h i (hi.trans hkn.le)
    · simp
  have hcoeff : ‖(m : K) * constantCoeff f ^ (m - 1) * coeff n f‖ = ‖coeff n f‖ := by
    rw [norm_mul, norm_mul, norm_pow, hm, hf, one_pow, one_mul, one_mul]
  rw [← hcoeff, eq_sub_of_add_eq' (coeff_pow_eq_coeff_trunc_pow_add f hn m).symm]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h n le_rfl) ?_)
  rw [norm_neg]
  exact norm_coeff_pow_le_one ht m

end Root

/-! ### Integral series in a series `T` without constant term -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NormedField K] [Algebra ℚ K]
  [NormedAlgebra ℚ_[p] K]

/-- **Integral logarithms in `T`.** Let `a ≠ 0` with `‖a‖ ≤ p ^ (-1 / (p - 1))`, let `G` and `T`
have no constant term, and let `exp(a G) = 1 + a H₀(T)` with `H₀` integral. Then `G = G₀(T)` for
an integral `G₀`, namely `G₀ = log(1 + a H₀) / a`. -/
theorem exists_eq_subst_of_subst_exp_smul_eq {a : K} (ha0 : a ≠ 0)
    (ha : ‖a‖ ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) {T : K⟦X⟧} (hT0 : constantCoeff T = 0)
    {G H₀ : K⟦X⟧} (hG : constantCoeff G = 0) (hH₀ : ∀ k, ‖coeff k H₀‖ ≤ 1)
    (h : (exp K).subst (a • G) = 1 + a • H₀.subst T) :
    ∃ G₀ : K⟦X⟧, (∀ k, ‖coeff k G₀‖ ≤ 1) ∧ G = G₀.subst T := by
  have hT : HasSubst T := .of_constantCoeff_zero' hT0
  have hH₀0 : constantCoeff H₀ = 0 := by
    have h0 := congrArg constantCoeff h
    simpa [hG, constantCoeff_subst_of_constantCoeff_zero' hT0, ha0] using h0
  have h1 : constantCoeff (1 + a • H₀) = 1 := by simp [hH₀0]
  set G₀ := a⁻¹ • logOf (1 + a • H₀)
  have hG₀ : constantCoeff G₀ = 0 := by simp [G₀, constantCoeff_logOf h1]
  have hexp : (exp K).subst (a • G₀) = 1 + a • H₀ := by
    rw [smul_inv_smul₀ ha0, subst_exp_logOf h1]
  refine ⟨G₀, fun k ↦ norm_coeff_le_one_of_subst_exp_smul_eq ha0 ha hG₀ hexp fun j _ ↦ hH₀ j,
    smul_right_injective _ ha0 ((subst_exp_inj (by simp [hG]) ?_).1 ?_)⟩
  · simp [constantCoeff_subst_of_constantCoeff_zero' hT0, hG₀]
  · have haG₀ : HasSubst (a • G₀) := .of_constantCoeff_zero' (by simp [hG₀])
    beta_reduce
    rw [h, ← subst_smul hT a G₀, ← subst_comp_subst_apply haG₀ hT, hexp, subst_add hT,
      subst_one, subst_smul hT]

/-- **Prime-to-`p` roots of exponentials in `T`.** Let `G` and `T` have no constant term and `m`
be prime to `p`. If `exp(G) ^ m = F(T)` with `F` integral, then `exp(G) = f₀(T)` for an integral
`f₀`, namely `f₀ = exp(log(F) / m)`. For `T = X`: if `exp(G) ^ m` is integral, so is `exp(G)`. -/
theorem exists_subst_exp_eq_subst_of_pow_eq_subst {T : K⟦X⟧} (hT0 : constantCoeff T = 0)
    {G : K⟦X⟧} (hG : constantCoeff G = 0) {m : ℕ} (hm : ¬p ∣ m) {F : K⟦X⟧}
    (hF : ∀ k, ‖coeff k F‖ ≤ 1) (h : (exp K).subst G ^ m = F.subst T) :
    ∃ f₀ : K⟦X⟧, (∀ k, ‖coeff k f₀‖ ≤ 1) ∧ (exp K).subst G = f₀.subst T := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hT : HasSubst T := .of_constantCoeff_zero' hT0
  have hm' : ‖(m : K)‖ = 1 := by
    rwa [TauCeti.norm_natCast_eq_norm_padic (p := p), Padic.norm_natCast_eq_one_iff,
      Nat.Prime.coprime_iff_not_dvd hp.out]
  have hm0 : (m : K) ≠ 0 := by rw [← norm_ne_zero_iff, hm']; exact one_ne_zero
  have hF1 : constantCoeff F = 1 := by
    simpa [hG, constantCoeff_subst_of_constantCoeff_zero' hT0] using (congrArg constantCoeff h).symm
  have hL0 : constantCoeff ((m : K)⁻¹ • logOf F) = 0 := by simp [constantCoeff_logOf hF1]
  have hf₀ : constantCoeff ((exp K).subst ((m : K)⁻¹ • logOf F)) = 1 := constantCoeff_subst_exp hL0
  have hpow : (exp K).subst ((m : K)⁻¹ • logOf F) ^ m = F := by
    rw [← logOf_inj (by simp [hf₀]) hF1, logOf_pow hf₀, logOf_subst_exp hL0,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hm0, one_smul]
  -- `log (F (T)) = log (exp (G) ^ m) = m G`.
  have hlogT : (logOf F).subst T = m • G := by
    rw [logOf_eq, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (by simp [hF1])) hT,
      subst_sub hT, subst_one, ← logOf_eq, ← h, logOf_pow (constantCoeff_subst_exp hG),
      logOf_subst_exp hG]
  refine ⟨_, fun k ↦ norm_coeff_le_one_of_norm_coeff_pow_le_one (by simp [hf₀]) hm'
    fun j _ ↦ hpow ▸ hF j, ?_⟩
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hL0) hT, subst_smul hT, hlogT,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hm0, one_smul]

end Padic

end PowerSeries
