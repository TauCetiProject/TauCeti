/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.LFunctions.Mertens
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.SumPrimePow

/-!
# Mertens's second and third theorems over the rationals

This file develops Mertens's second and third theorems for rational primes, with uniform error
bounds valid on the entire half-line `x ≥ 2`, together with the von Mangoldt prime-power form and
two-sided partial Euler-product estimates with finitely many primes omitted.

Specializing the number-field Mertens theorem of `TauCeti/NumberTheory/LFunctions/Mertens.lean` to
`ℚ`, where `dedekindZeta_residue ℚ = 1` (`TauCeti.dedekindZeta_residue_rat`) and height-one primes
of `𝓞 ℚ` correspond bijectively to `Nat.Primes` via absolute norm, identifies `mertensConstant ℚ`
with the classical Meissel–Mertens constant
`B = γ + ∑_p (log (1 - p⁻¹) + p⁻¹)` (`TauCeti.meisselMertensConstant`), strictly smaller than
Euler's constant `γ`. Upgrading the asymptotic error `O(1 / log x)` to `[2, ∞)` yields uniform
estimates for the inclusive sum `∑_{p ≤ x} p⁻¹`, the strict-cutoff sum `∑_{p < x} p⁻¹`, and the
interval sum `∑_{y < p ≤ x} p⁻¹ = log (log x / log y) + O(1 / log y)`.

Adding the convergent quadratic remainder `∑_p (-log (1 - p⁻¹) - p⁻¹)` and bounding its prime tail
by `O(1 / x)` gives the logarithmic Euler-product expansion
`∑_{p ≤ x} -log (1 - p⁻¹) = log log x + γ + O(1 / log x)` uniformly for `x ≥ 2`. Expanding each
logarithmic factor over prime powers and bounding the omitted powers `p ^ k > x` by `O(1 / √x)`
yields Mertens's second theorem in von Mangoldt form:
`∑_{2 ≤ n ≤ x} Λ(n) / (n log n) = log log x + γ + O(1 / log x)` uniformly for `x ≥ 2`.

Exponentiating the logarithmic Euler-product estimate via `|exp t - 1| ≤ |t| exp |t|` produces
Mertens's third theorem with sharp `O(1)` additive remainder,
`∏_{p ≤ x} (1 - p⁻¹)⁻¹ = e^γ log x + O(1)` for `x ≥ 2`, its reciprocal form
`∏_{p ≤ x} (1 - p⁻¹) = e^(-γ) / log x + O(1 / log² x)`, and positive two-sided `1 / log y`
bounds when any finite set of primes is removed from the product.

## Main definitions

* `TauCeti.meisselMertensConstant`: the Meissel–Mertens constant
  `γ + ∑' p : Nat.Primes, (log (1 - p⁻¹) + p⁻¹)`.

## Main results

* `TauCeti.mertensConstant_rat`: `LFunctions.mertensConstant ℚ = meisselMertensConstant`.
* `TauCeti.meisselMertensConstant_lt_eulerMascheroniConstant`:
  `meisselMertensConstant < Real.eulerMascheroniConstant`.
* `TauCeti.exists_abs_sum_primesLE_inv_sub_log_log_sub_le`: Mertens's second theorem uniformly on
  `x ≥ 2`, `|∑_{p ≤ x} p⁻¹ - log log x - B| ≤ C / log x`.
* `TauCeti.exists_abs_sum_sdiff_primesLE_inv_sub_log_div_le`: uniform interval estimate
  `|∑_{y < p ≤ x} p⁻¹ - log (log x / log y)| ≤ C / log y` for `2 ≤ y ≤ x`.
* `TauCeti.exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le`: uniform logarithmic
  Euler product `|∑_{p ≤ x} -log (1 - p⁻¹) - log log x - γ| ≤ C / log x` for `x ≥ 2`.
* `TauCeti.exists_abs_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub_le`: Mertens's second theorem
  in von Mangoldt form, `|∑_{2 ≤ n ≤ x} Λ(n) / (n log n) - log log x - γ| ≤ C / log x` for `x ≥ 2`.
* `TauCeti.exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le`: Mertens's third theorem
  with bounded additive remainder, `|∏_{p ≤ x} (1 - p⁻¹)⁻¹ - e^γ log x| ≤ C` for `x ≥ 2`.
* `TauCeti.exists_pos_prod_primesLE_filter_notMem_one_sub_inv_bounds`: two-sided `1 / log y`
  comparison for `∏_{p ≤ y, p ∉ T} (1 - p⁻¹)` on `y ≥ 2` for any finite set `T`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874), 46–62.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society (2019), Theorem 3.4 and Exercise 5.4.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., §22.8.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.1.
-/

public section

open Asymptotics Filter Finset IsDedekindDomain
open scoped ArithmeticFunction NumberField Topology

namespace TauCeti

/-! ### Rational prime-ideal transport -/

/-- The image of `primesLE ℚ x` under absolute norm is `Nat.primesLE ⌊x⌋₊`. -/
theorem image_absNorm_primesLE_rat (x : ℝ) :
    (primesLE ℚ x).image (fun v ↦ Ideal.absNorm v.asIdeal) = Nat.primesLE ⌊x⌋₊ := by
  ext p
  simp only [mem_image, mem_normLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hv
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hv ⊢
    exact ⟨Nat.le_floor hv, Rat.HeightOneSpectrum.prime_natGenerator v⟩
  · rintro ⟨hple, hp⟩
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    have hx0 : 0 ≤ x := by
      by_contra hlt
      have hfl : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hlt)
      have hp2 := hp.two_le
      omega
    exact ⟨v, hv.symm ▸ (Nat.cast_le.mpr hple).trans (Nat.floor_le hx0), hv⟩

/-- A summatory function over the height-one primes of `𝓞 ℚ` depending only on the absolute norm
equals the corresponding finite sum over `Nat.primesLE ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [primeSummatory_apply, ← image_absNorm_primesLE_rat,
    sum_image fun _ _ _ _ h ↦ Rat.HeightOneSpectrum.absNorm_asIdeal_injective h]

/-- An unconditional series over the height-one primes of `𝓞 ℚ` depending only on the absolute norm
equals the corresponding series over `Nat.Primes`. -/
theorem tsum_heightOneSpectrum_rat_eq_tsum_primes {α : Type*} [AddCommMonoid α]
    [TopologicalSpace α] (f : ℕ → α) :
    (∑' v : HeightOneSpectrum (𝓞 ℚ), f (Ideal.absNorm v.asIdeal)) =
      ∑' p : Nat.Primes, f p := by
  refine (tsum_congr fun v ↦ ?_).trans
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tsum_eq (fun p : Nat.Primes ↦ f p))
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal, Rat.HeightOneSpectrum.primesEquiv]
  rfl

/-! ### The Meissel–Mertens constant and prime logarithmic remainders -/

/-- The prime series `∑_p (log (1 - p⁻¹) + p⁻¹)` is summable. -/
theorem summable_prime_log_one_sub_inv_add_inv :
    Summable (fun p : Nat.Primes ↦ Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹) := by
  have hsq : Summable (fun p : Nat.Primes ↦ (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr one_lt_two).subtype _
  have hneg : Summable (fun p : Nat.Primes ↦
      -Real.log (1 - ((p : ℕ) : ℝ)⁻¹) - ((p : ℕ) : ℝ)⁻¹) :=
    hsq.of_nonneg_of_le
      (fun p ↦ (Real.neg_log_one_sub_inv_sub_inv_pos (mod_cast p.2.one_lt)).le)
      (fun p ↦ Real.neg_log_one_sub_inv_sub_inv_le (mod_cast p.2.two_le))
  exact hneg.neg.congr fun _ ↦ by ring

/-- For `x > 0`, the tail of the positive quadratic Euler-product remainders
`-log (1 - p⁻¹) - p⁻¹` over primes `p > x` is at most `4 / x`. -/
theorem tsum_prime_neg_log_one_sub_inv_sub_inv_gt_le {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0) ≤
      4 / x := by
  have hsq := summable_prime_inv_sq_gt x
  have hnonneg : ∀ n : ℕ,
      0 ≤ (if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0) := by
    intro n
    split_ifs with hn
    · exact (Real.neg_log_one_sub_inv_sub_inv_pos (mod_cast hn.1.one_lt)).le
    · exact le_rfl
  have hle : ∀ n : ℕ,
      (if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0) ≤
        if n.Prime ∧ x < (n : ℝ) then ((n : ℝ) ^ 2)⁻¹ else 0 := by
    intro n
    split_ifs with hn
    · exact Real.neg_log_one_sub_inv_sub_inv_le (mod_cast hn.1.two_le)
    · exact le_rfl
  exact ((hsq.of_nonneg_of_le hnonneg hle).tsum_le_tsum hle hsq).trans
    (tsum_prime_inv_sq_gt_le hx)

/-- **The Meissel–Mertens constant**: `B = γ + ∑_p (log (1 - p⁻¹) + p⁻¹)`, the constant term in
Mertens's second theorem `∑_{p ≤ x} p⁻¹ = log log x + B + O(1 / log x)`. -/
noncomputable def meisselMertensConstant : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' p : Nat.Primes, (Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹)

/-- Explicit series formula for `meisselMertensConstant`. -/
theorem meisselMertensConstant_def :
    meisselMertensConstant =
      Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹) :=
  (rfl)

/-- Over `ℚ`, the number-field Mertens constant `LFunctions.mertensConstant ℚ` equals the
Meissel–Mertens constant. -/
@[simp]
theorem mertensConstant_rat : LFunctions.mertensConstant ℚ = meisselMertensConstant := by
  rw [LFunctions.mertensConstant_eq, dedekindZeta_residue_rat, Real.log_one, add_zero,
    meisselMertensConstant_def,
    tsum_heightOneSpectrum_rat_eq_tsum_primes (fun n ↦ Real.log (1 - (n : ℝ)⁻¹) + (n : ℝ)⁻¹)]

/-- Upper bound `meisselMertensConstant ≤ γ + 1 / 2 - log 2`. -/
theorem meisselMertensConstant_le_add_half_sub_log_two :
    meisselMertensConstant ≤ Real.eulerMascheroniConstant + 1 / 2 - Real.log 2 := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  rw [meisselMertensConstant_def,
    summable_prime_log_one_sub_inv_add_inv.tsum_eq_add_tsum_ite p2]
  have hrest : (∑' p : Nat.Primes,
      if p = p2 then 0 else Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹) ≤ 0 :=
    tsum_nonpos fun p ↦ by
      split_ifs
      · exact le_rfl
      · linarith [Real.neg_log_one_sub_inv_sub_inv_pos (x := (p : ℕ)) (mod_cast p.2.one_lt)]
  have hp2 : Real.log (1 - ((p2 : ℕ) : ℝ)⁻¹) + ((p2 : ℕ) : ℝ)⁻¹ = 1 / 2 - Real.log 2 := by
    have hsub : 1 - ((p2 : ℕ) : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num [p2]
    have hinv : ((p2 : ℕ) : ℝ)⁻¹ = 1 / 2 := by norm_num [p2]
    rw [hsub, hinv, Real.log_inv]
    ring
  linarith

/-- The Meissel–Mertens constant is strictly smaller than Euler's constant `γ`. -/
theorem meisselMertensConstant_lt_eulerMascheroniConstant :
    meisselMertensConstant < Real.eulerMascheroniConstant := by
  linarith [meisselMertensConstant_le_add_half_sub_log_two, Real.log_two_gt_d9]

/-! ### Mertens's second theorem over the rationals -/

/-- **Mertens's second theorem, asymptotic form.** The reciprocal-prime partial sum satisfies
`∑_{p ≤ x} p⁻¹ = log log x + B + O(1 / log x)` as `x → ∞`, with `B = meisselMertensConstant`. -/
theorem isBigO_sum_primesLE_inv_sub_log_log_sub_meisselMertensConstant :
    (fun x : ℝ ↦
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) - meisselMertensConstant)
      =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  refine (LFunctions.isBigO_primeSummatory_inv_absNorm_sub_log_log_sub_mertensConstant ℚ).congr_left
    fun x ↦ ?_
  rw [primeSummatory_rat_eq_sum_primesLE (fun n ↦ (n : ℝ)⁻¹), mertensConstant_rat]

/-- **Mertens's second theorem, limit form.** As `x → ∞`,
`∑_{p ≤ x} p⁻¹ - log log x` converges to `meisselMertensConstant`. -/
theorem tendsto_sum_primesLE_inv_sub_log_log :
    Tendsto (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x))
      atTop (𝓝 meisselMertensConstant) := by
  rw [← mertensConstant_rat]
  refine (LFunctions.tendsto_primeSummatory_inv_absNorm_sub_log_log ℚ).congr fun x ↦ ?_
  rw [primeSummatory_rat_eq_sum_primesLE (fun n ↦ (n : ℝ)⁻¹)]

/-- An `=O[atTop] (log x)⁻¹` bound on a function bounded on compact subsets of `[2, ∞)` upgrades
to a uniform bound on `[2, ∞)`. -/
private theorem exists_abs_le_div_log_of_isBigO {f : ℝ → ℝ}
    (hO : f =O[atTop] fun x ↦ (Real.log x)⁻¹)
    (hbdd : ∀ b : ℝ, ∃ B : ℝ, ∀ x ∈ Set.Icc 2 b, |f x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |f x| ≤ C / Real.log x := by
  have hmul : (fun x : ℝ ↦ f x * Real.log x) =O[atTop] fun _ ↦ (1 : ℝ) := by
    refine (hO.mul (isBigO_refl Real.log atTop)).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact inv_mul_cancel₀ (Real.log_pos hx).ne'
  have hprin := hmul.isBigO_principal_Ici (a := 2) zero_lt_one (fun _ _ ↦ by simp) fun b ↦ by
    obtain ⟨B, hB⟩ := hbdd b
    refine ⟨max B 0 * max (Real.log b) 0, fun x hx ↦ ?_⟩
    have hlog0 : 0 ≤ Real.log x := (Real.log_pos (one_lt_two.trans_le hx.1)).le
    have hlogb : Real.log x ≤ max (Real.log b) 0 :=
      (Real.log_le_log (by linarith [hx.1]) hx.2).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0]
    exact mul_le_mul ((hB x hx).trans (le_max_left _ _)) hlogb hlog0 (le_max_right _ _)
  obtain ⟨C, hC0, hC⟩ := hprin.exists_nonneg
  refine ⟨C, hC0, fun x hx ↦ ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  have h := isBigOWith_principal.mp hC x hx
  rw [Real.norm_eq_abs, norm_one, mul_one, abs_mul, abs_of_pos hlog] at h
  exact (le_div_iff₀ hlog).mpr h

/-- **Mertens's second theorem, uniform on `[2, ∞)`.** There is an absolute constant `C` such that
for every real `x ≥ 2`,
`|∑_{p ≤ x} p⁻¹ - log log x - meisselMertensConstant| ≤ C / log x`. -/
theorem exists_abs_sum_primesLE_inv_sub_log_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) - meisselMertensConstant| ≤
        C / Real.log x := by
  obtain ⟨C, -, hC⟩ :=
    exists_abs_le_div_log_of_isBigO
      isBigO_sum_primesLE_inv_sub_log_log_sub_meisselMertensConstant fun b ↦ by
      refine ⟨(∑ p ∈ Nat.primesLE ⌊b⌋₊, (p : ℝ)⁻¹) +
          (|Real.log (Real.log 2)| + |Real.log (Real.log (max b 2))|) + |meisselMertensConstant|,
        fun x hx ↦ ?_⟩
      have hsum_nonneg : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ :=
        sum_nonneg fun _ _ ↦ by positivity
      have hsum_le : (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) ≤ ∑ p ∈ Nat.primesLE ⌊b⌋₊, (p : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hx.2)) fun _ _ _ ↦ by
          positivity
      have hll_lo : Real.log (Real.log 2) ≤ Real.log (Real.log x) :=
        Real.log_le_log (Real.log_pos one_lt_two) (Real.log_le_log zero_lt_two hx.1)
      have hll_hi : Real.log (Real.log x) ≤ Real.log (Real.log (max b 2)) :=
        Real.log_le_log (Real.log_pos (one_lt_two.trans_le hx.1))
          (Real.log_le_log (by linarith [hx.1]) (hx.2.trans (le_max_left _ _)))
      have hll_abs : |Real.log (Real.log x)| ≤
          |Real.log (Real.log 2)| + |Real.log (Real.log (max b 2))| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (Real.log (Real.log 2)), abs_nonneg (Real.log (Real.log (max b 2)))]
        · linarith [le_abs_self (Real.log (Real.log (max b 2))), abs_nonneg (Real.log (Real.log 2))]
      refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans ?_) le_rfl)
      rw [abs_of_nonneg hsum_nonneg]
      exact add_le_add hsum_le hll_abs
  exact ⟨C, hC⟩

/-- For `x ≥ 1`, the inclusive reciprocal-prime sum `∑_{p ≤ x} p⁻¹` exceeds the strict-cutoff sum
`∑_{p < x} p⁻¹` by a nonnegative amount bounded by `1 / log x`. -/
private theorem sum_primesLE_inv_sub_sum_primesBelow_ceil_inv_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹) ∧
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹) ≤
        1 / Real.log x := by
  rcases hx.eq_or_lt with rfl | hx
  · have hle1 : Nat.primesLE 1 = ∅ := by decide
    have hlt1 : Nat.primesBelow 1 = ∅ := by decide
    simp [hle1, hlt1]
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsub : Nat.primesBelow ⌈x⌉₊ ⊆ Nat.primesLE ⌊x⌋₊ := fun p hp ↦ by
    rw [Nat.mem_primesBelow, Nat.lt_ceil] at hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hp.1.le, hp.2⟩
  have hsdiff : Nat.primesLE ⌊x⌋₊ \ Nat.primesBelow ⌈x⌉₊ ⊆ {⌊x⌋₊} := fun p hp ↦ by
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesBelow, Nat.lt_ceil, not_and_or] at hp
    rcases hp with ⟨⟨hple, hp_prime⟩, hnot⟩
    have hxle : x ≤ (p : ℝ) := not_lt.mp (hnot.resolve_right (not_not.mpr hp_prime))
    have hpeq : (p : ℝ) = x := le_antisymm ((Nat.le_floor_iff hx0.le).mp hple) hxle
    rw [mem_singleton, ← hpeq, Nat.floor_natCast]
  refine ⟨sub_nonneg.mpr (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity), ?_⟩
  rw [← sum_sdiff_eq_sub hsub]
  rcases (Nat.primesLE ⌊x⌋₊ \ Nat.primesBelow ⌈x⌉₊).eq_empty_or_nonempty with hemp | ⟨q, hq⟩
  · rw [hemp, sum_empty]
    exact div_nonneg zero_le_one hlog.le
  · have hq_eq : q = ⌊x⌋₊ := mem_singleton.mp (hsdiff hq)
    have hx_eq : (q : ℝ) = x := by
      rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesBelow, Nat.lt_ceil] at hq
      have hnot : ¬((q : ℝ) < x) := fun hlt ↦ hq.2 ⟨hlt, hq.1.2⟩
      exact le_antisymm ((Nat.le_floor_iff hx0.le).mp hq.1.1) (not_lt.mp hnot)
    calc ∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹
        ≤ ∑ p ∈ ({⌊x⌋₊} : Finset ℕ), (p : ℝ)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg hsdiff fun _ _ _ ↦ by positivity
      _ = x⁻¹ := by rw [sum_singleton, ← hq_eq, hx_eq]
      _ ≤ 1 / Real.log x := by
          rw [one_div]
          exact inv_anti₀ hlog (Real.log_le_self hx0.le)

/-- **Mertens's second theorem with strict cutoff.** Replacing the inclusive prime carrier
`Nat.primesLE ⌊x⌋₊` (`p ≤ x`) by the strict carrier `Nat.primesBelow ⌈x⌉₊` (`p < x`) preserves the
uniform `O(1 / log x)` remainder on `x ≥ 2`. -/
theorem exists_abs_sum_primesBelow_ceil_inv_sub_log_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹) - Real.log (Real.log x) - meisselMertensConstant| ≤
        C / Real.log x := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primesLE_inv_sub_log_log_sub_le
  refine ⟨1 + C, fun x hx ↦ ?_⟩
  obtain ⟨hdiff_nonneg, hdiff_le⟩ :=
    sum_primesLE_inv_sub_sum_primesBelow_ceil_inv_bounds (one_le_two.trans hx)
  have h2 : |(∑ p ∈ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹) - (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹)| ≤
      1 / Real.log x := by
    rw [abs_sub_comm, abs_of_nonneg hdiff_nonneg]
    exact hdiff_le
  have hsplit : (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹) - Real.log (Real.log x) -
      meisselMertensConstant =
      ((∑ p ∈ Nat.primesBelow ⌈x⌉₊, (p : ℝ)⁻¹) - (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹)) +
        ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) -
          meisselMertensConstant) := by
    ring
  rw [hsplit, add_div]
  exact (abs_add_le _ _).trans (add_le_add h2 (hC x hx))

/-- **Uniform reciprocal-prime sum over an interval.** There is an absolute constant `C` such that
for all reals `2 ≤ y ≤ x`,
`|∑_{y < p ≤ x} p⁻¹ - log (log x / log y)| ≤ C / log y`. -/
theorem exists_abs_sum_sdiff_primesLE_inv_sub_log_div_le :
    ∃ C : ℝ, ∀ y x : ℝ, 2 ≤ y → y ≤ x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊y⌋₊, (p : ℝ)⁻¹) -
          Real.log (Real.log x / Real.log y)| ≤ C / Real.log y := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primesLE_inv_sub_log_log_sub_le
  have hC0 : 0 ≤ C := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hm := (le_div_iff₀ hlog2).mp ((abs_nonneg _).trans (hC 2 le_rfl))
    linarith
  refine ⟨2 * C, fun y x hy hyx ↦ ?_⟩
  have hx : 2 ≤ x := hy.trans hyx
  have hlogy : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  have hlogx : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ := Nat.primesLE_mono (Nat.floor_mono hyx)
  have hlog_div : Real.log (Real.log x / Real.log y) =
      Real.log (Real.log x) - Real.log (Real.log y) :=
    Real.log_div hlogx.ne' hlogy.ne'
  have hsplit : (∑ p ∈ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊y⌋₊, (p : ℝ)⁻¹) -
      Real.log (Real.log x / Real.log y) =
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) -
          meisselMertensConstant) -
        ((∑ p ∈ Nat.primesLE ⌊y⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log y) -
          meisselMertensConstant) := by
    rw [sum_sdiff_eq_sub hsub, hlog_div]
    ring
  have hcx : C / Real.log x ≤ C / Real.log y :=
    div_le_div_of_nonneg_left hC0 hlogy (Real.log_le_log (by linarith) hyx)
  rw [hsplit, two_mul, add_div]
  exact (abs_sub _ _).trans (add_le_add (hC x hx |>.trans hcx) (hC y hy))

/-! ### Logarithmic Euler product and von Mangoldt form -/

/-- Decomposition of the total prime logarithmic remainder into its cutoff sum up to `x` and its
tail over primes `p > x`. -/
private theorem sum_primesLE_neg_log_one_sub_inv_sub_inv_add_tail (x : ℝ) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (-Real.log (1 - (p : ℝ)⁻¹) - (p : ℝ)⁻¹)) +
      (∑' n : ℕ, if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0) =
      -∑' p : Nat.Primes, (Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹) := by
  let r : ℕ → ℝ := fun n ↦ if n.Prime then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0
  have hr_sum : Summable r :=
    (Real.summable_nat_pow_inv.mpr one_lt_two).of_nonneg_of_le
      (fun n ↦ by
        simp only [r]
        split_ifs with hn
        · exact (Real.neg_log_one_sub_inv_sub_inv_pos (mod_cast hn.one_lt)).le
        · exact le_rfl)
      (fun n ↦ by
        simp only [r]
        split_ifs with hn
        · exact Real.neg_log_one_sub_inv_sub_inv_le (mod_cast hn.two_le)
        · positivity)
  have hsplit := hr_sum.sum_add_tsum_nat_add (⌊x⌋₊ + 1)
  have hfin : ∑ n ∈ range (⌊x⌋₊ + 1), r n =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (-Real.log (1 - (p : ℝ)⁻¹) - (p : ℝ)⁻¹) := by
    rw [Nat.primesLE_eq_filter_range, sum_filter]
  have htail : (∑' k : ℕ, r (k + (⌊x⌋₊ + 1))) =
      ∑' n : ℕ, if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0 := by
    have hind : (fun n : ℕ ↦
        if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0) =
        fun n ↦ if ⌊x⌋₊ + 1 ≤ n then r n else 0 := by
      ext n
      by_cases hn : n.Prime
      · have hiff : x < (n : ℝ) ↔ ⌊x⌋₊ + 1 ≤ n := by
          rcases le_or_gt 0 x with hx | hx
          · rw [← not_le, ← Nat.le_floor_iff hx]
            omega
          · simp [Nat.floor_of_nonpos hx.le, hn.one_le, hx.trans_le (Nat.cast_nonneg n)]
        simp [r, hn, hiff]
      · simp [r, hn]
    rw [hind]
    have h0 := (hr_sum.indicator {n : ℕ | ⌊x⌋₊ + 1 ≤ n}).sum_add_tsum_nat_add (⌊x⌋₊ + 1)
    have hrange0 : ∑ n ∈ range (⌊x⌋₊ + 1),
        ({n : ℕ | ⌊x⌋₊ + 1 ≤ n}.indicator r n) = 0 :=
      sum_eq_zero fun n hn ↦ Set.indicator_of_notMem
        (by simp only [Set.mem_ofPred_eq, not_le]; exact mem_range.mp hn) _
    rw [hrange0, zero_add] at h0
    refine (tsum_congr fun k ↦ ?_).trans (h0.trans (tsum_congr fun n ↦ ?_))
    · exact (Set.indicator_of_mem (Set.mem_ofPred.mpr (Nat.le_add_left _ _)) r).symm
    · simp [Set.indicator_apply]
  have htot : (∑' n : ℕ, r n) =
      -∑' p : Nat.Primes, (Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹) := by
    rw [← tsum_neg]
    have hsub := tsum_subtype {n : ℕ | n.Prime} (fun n : ℕ ↦ -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹)
    refine (tsum_congr fun n ↦ ?_).trans (hsub.symm.trans (tsum_congr fun p ↦ by ring))
    simp [r, Set.indicator_apply]
  rw [← hfin, htail.symm, hsplit, htot]

/-- **Logarithmic Euler-product form of Mertens's theorem, uniform on `[2, ∞)`.** There is an
absolute constant `C` such that for every real `x ≥ 2`,
`|∑_{p ≤ x} -log (1 - p⁻¹) - log log x - γ| ≤ C / log x`. -/
theorem exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
          Real.log (Real.log x) - Real.eulerMascheroniConstant| ≤ C / Real.log x := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primesLE_inv_sub_log_log_sub_le
  refine ⟨C + 4, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  set T := ∑' n : ℕ, if n.Prime ∧ x < (n : ℝ) then -Real.log (1 - (n : ℝ)⁻¹) - (n : ℝ)⁻¹ else 0
  have hT0 : 0 ≤ T := tsum_nonneg fun n ↦ by
    split_ifs with hn
    · exact (Real.neg_log_one_sub_inv_sub_inv_pos (mod_cast hn.1.one_lt)).le
    · exact le_rfl
  have hTle : T ≤ 4 / Real.log x :=
    (tsum_prime_neg_log_one_sub_inv_sub_inv_gt_le hx0).trans
      (div_le_div_of_nonneg_left (by norm_num) hlog (Real.log_le_self hx0.le))
  have hrel := sum_primesLE_neg_log_one_sub_inv_sub_inv_add_tail x
  rw [sum_sub_distrib] at hrel
  have hident : (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
      Real.log (Real.log x) - Real.eulerMascheroniConstant =
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) - meisselMertensConstant) -
        T := by
    rw [meisselMertensConstant_def]
    linarith
  rw [hident, add_div]
  refine (abs_sub _ _).trans (add_le_add (hC x hx) ?_)
  rwa [abs_of_nonneg hT0]

/-- **Logarithmic Euler-product form of Mertens's theorem, asymptotic form:**
`∑_{p ≤ x} -log (1 - p⁻¹) - log log x - γ = O(1 / log x)` as `x → ∞`. -/
theorem isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
        Real.log (Real.log x) - Real.eulerMascheroniConstant)
      =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr hlog.le), ← div_eq_mul_inv]
  exact hC x hx

/-- **Logarithmic Euler-product form of Mertens's theorem, limit form:**
`∑_{p ≤ x} -log (1 - p⁻¹) - log log x → γ` as `x → ∞`. -/
theorem tendsto_sum_primesLE_neg_log_one_sub_inv_sub_log_log :
    Tendsto (fun x : ℝ ↦
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) - Real.log (Real.log x))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := (isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub.trans_tendsto
    (Real.tendsto_log_atTop.inv_tendsto_atTop)).add_const Real.eulerMascheroniConstant
  simpa using h

/-- Exact prime-power regrouping of the weighted von Mangoldt sum:
`∑_{2 ≤ n ≤ N} Λ(n) / (n log n) = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} 1 / (k p ^ k)`. -/
theorem sum_Icc_vonMangoldt_div_mul_log_eq (N : ℕ) :
    ∑ n ∈ Icc 2 N, Λ n / (n * Real.log n) =
      ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
  have h12 : ∑ n ∈ Icc 2 N, Λ n / (n * Real.log n) =
      ∑ n ∈ Icc 1 N, Λ n / (n * Real.log n) := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · rw [← insert_Icc_add_one_left_eq_Icc (Nat.one_le_iff_ne_zero.mpr hN),
        sum_insert (by simp)]
      simp
  rw [h12, Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log
    (fun n hn ↦ by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div])]
  refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
  have hp_prime := Nat.prime_of_mem_primesLE hp
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1
  have hlogp : Real.log p ≠ 0 := (Real.log_pos (mod_cast hp_prime.one_lt)).ne'
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
    ArithmeticFunction.vonMangoldt_apply_prime hp_prime, Nat.cast_pow, Real.log_pow]
  field_simp [hlogp]

/-- For every `p, N : ℕ`, the difference between `-log (1 - p⁻¹)` and the truncated harmonic
power sum `∑_{1 ≤ k ≤ log_p N} 1 / (k p ^ k)` is nonnegative and bounded by
`2 / p ^ (log_p N + 1)`. -/
private theorem neg_log_one_sub_inv_sub_sum_Icc_le (p N : ℕ) :
    0 ≤ -Real.log (1 - (p : ℝ)⁻¹) - ∑ k ∈ Icc 1 (p.log N), 1 / ((k : ℝ) * (p : ℝ) ^ k) ∧
      -Real.log (1 - (p : ℝ)⁻¹) - ∑ k ∈ Icc 1 (p.log N), 1 / ((k : ℝ) * (p : ℝ) ^ k) ≤
        2 * ((p : ℝ) ^ (p.log N + 1))⁻¹ := by
  rcases lt_or_ge p 2 with hp | hp
  · interval_cases p <;> simp
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp
  have habs : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hhas := Real.hasSum_pow_div_natCast habs
  have hsplit := hhas.summable.sum_add_tsum_nat_add (p.log N + 1)
  have hfin : ∑ k ∈ range (p.log N + 1), ((p : ℝ)⁻¹) ^ k / (k : ℝ) =
      ∑ k ∈ Icc 1 (p.log N), 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le _),
      sum_insert (by simp)]
    simp only [Nat.cast_zero, div_zero, zero_add]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [inv_pow]
    ring
  rw [← hhas.tsum_eq, ← hsplit, hfin, add_sub_cancel_left]
  refine ⟨tsum_nonneg fun m ↦ by positivity, ?_⟩
  have hshift := hhas.summable.comp_injective (add_left_injective (p.log N + 1))
  have hdom : ∀ m : ℕ,
      ((p : ℝ)⁻¹) ^ (m + (p.log N + 1)) / ((m + (p.log N + 1) : ℕ) : ℝ) ≤
        ((p : ℝ) ^ (p.log N + 1))⁻¹ * (1 / 2 : ℝ) ^ m := by
    intro m
    have hm1 : (1 : ℝ) ≤ ((m + (p.log N + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hpow : ((p : ℝ)⁻¹) ^ m ≤ (1 / 2 : ℝ) ^ m := by
      rw [one_div]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ zero_lt_two hp2) m
    calc ((p : ℝ)⁻¹) ^ (m + (p.log N + 1)) / ((m + (p.log N + 1) : ℕ) : ℝ)
        ≤ ((p : ℝ)⁻¹) ^ (m + (p.log N + 1)) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hm1
      _ = ((p : ℝ) ^ (p.log N + 1))⁻¹ * ((p : ℝ)⁻¹) ^ m := by
          rw [div_one, add_comm m, pow_add _ (p.log N + 1) m, inv_pow]
      _ ≤ ((p : ℝ) ^ (p.log N + 1))⁻¹ * (1 / 2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hgeom : Summable (fun m : ℕ ↦ ((p : ℝ) ^ (p.log N + 1))⁻¹ * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
  calc (∑' m : ℕ, ((p : ℝ)⁻¹) ^ (m + (p.log N + 1)) / ((m + (p.log N + 1) : ℕ) : ℝ))
      ≤ ∑' m : ℕ, ((p : ℝ) ^ (p.log N + 1))⁻¹ * (1 / 2 : ℝ) ^ m :=
        hshift.tsum_le_tsum hdom hgeom
    _ = ((p : ℝ) ^ (p.log N + 1))⁻¹ * ∑' m : ℕ, (1 / 2 : ℝ) ^ m := tsum_mul_left
    _ = 2 * ((p : ℝ) ^ (p.log N + 1))⁻¹ := by rw [tsum_geometric_two]; ring

/-- The weighted von Mangoldt sum never exceeds the logarithmic Euler-product sum up to `x`. -/
theorem sum_Icc_vonMangoldt_div_mul_log_le_sum_primesLE_neg_log_one_sub_inv (x : ℝ) :
    ∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n) ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹) := by
  rw [sum_Icc_vonMangoldt_div_mul_log_eq]
  exact sum_le_sum fun p _ ↦ sub_nonneg.mp (neg_log_one_sub_inv_sub_sum_Icc_le p ⌊x⌋₊).1

/-- Quantitative refinement of `Nat.tendsto_sum_primesLE_inv_pow_log_succ`: for every real `x`,
the reciprocals of the first omitted prime powers `p ^ (log_p ⌊x⌋₊ + 1)` sum to at most
`5 / √x`. -/
theorem sum_primesLE_inv_pow_log_succ_le (x : ℝ) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹) ≤ 5 / Real.sqrt x := by
  rcases lt_or_ge x 2 with hx | hx
  · have hemp : Nat.primesLE ⌊x⌋₊ = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp ↦ by
      have hp2 := (Nat.prime_of_mem_primesLE hp).two_le
      have hple := Nat.le_of_mem_primesLE hp
      have hx0 : 0 ≤ x := by
        by_contra hlt
        have hfl : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hlt)
        omega
      have h2f : (2 : ℝ) ≤ ⌊x⌋₊ := mod_cast hp2.trans hple
      linarith [Nat.floor_le hx0]
    rw [hemp, sum_empty]
    positivity
  have hx0 : 0 < x := by linarith
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  set P_le := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ℝ) ≤ Real.sqrt x)
  set P_gt := (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ ¬((p : ℝ) ≤ Real.sqrt x))
  have h1 : (∑ p ∈ P_le, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹) ≤ 1 / Real.sqrt x := by
    have hterm : ∀ p ∈ P_le, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹ ≤ x⁻¹ := fun p hp ↦ by
      have hlt := Nat.lt_pow_succ_log_self (Nat.one_lt_of_mem_primesLE (mem_filter.mp hp).1) ⌊x⌋₊
      have hxlt : x < (p : ℝ) ^ (p.log ⌊x⌋₊ + 1) :=
        (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast Nat.succ_le_of_lt hlt)
      exact inv_anti₀ hx0 hxlt.le
    have hcard : (P_le.card : ℝ) ≤ Real.sqrt x := by
      have hsub : P_le ⊆ Icc 1 ⌊Real.sqrt x⌋₊ := fun p hp ↦
        mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).one_le,
          Nat.le_floor (mem_filter.mp hp).2⟩
      exact (Nat.cast_le.mpr (card_le_card hsub)).trans (by simp [Nat.floor_le hsq.le])
    calc (∑ p ∈ P_le, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹)
        ≤ ∑ _p ∈ P_le, x⁻¹ := sum_le_sum hterm
      _ = (P_le.card : ℝ) * x⁻¹ := by simp [nsmul_eq_mul]
      _ ≤ Real.sqrt x * x⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / Real.sqrt x := by
          have hsq2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
          field_simp [hsq.ne', hx0.ne']
          linarith
  have h2 : (∑ p ∈ P_gt, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹) ≤ 4 / Real.sqrt x := by
    have hterm : ∀ p ∈ P_gt, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹ ≤
        if p.Prime ∧ Real.sqrt x < (p : ℝ) then ((p : ℝ) ^ 2)⁻¹ else 0 := fun p hp ↦ by
      obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      have hp_prime := Nat.prime_of_mem_primesLE hp1
      have hp0 : (0 : ℝ) < p := mod_cast hp_prime.pos
      have hlt : Real.sqrt x < (p : ℝ) := not_le.mp hp2
      have hlog1 : 1 ≤ p.log ⌊x⌋₊ := Nat.log_pos hp_prime.one_lt (Nat.le_of_mem_primesLE hp1)
      simp only [hp_prime, hlt, and_self, ↓reduceIte]
      exact inv_anti₀ (pow_pos hp0 2) (pow_le_pow_right₀ (mod_cast hp_prime.one_le) (by omega))
    exact (sum_le_sum hterm).trans
      (((summable_prime_inv_sq_gt (Real.sqrt x)).sum_le_tsum P_gt
        fun n _ ↦ by split_ifs <;> positivity).trans (tsum_prime_inv_sq_gt_le hsq))
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE ⌊x⌋₊) (fun p : ℕ ↦ (p : ℝ) ≤ Real.sqrt x)]
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- For every real `x`, the prime-power excess between the logarithmic Euler-product sum and the
weighted von Mangoldt sum is at most `10 / √x`. -/
theorem sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_le (x : ℝ) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
        (∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n)) ≤ 10 / Real.sqrt x := by
  rw [sum_Icc_vonMangoldt_div_mul_log_eq, ← sum_sub_distrib]
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (-Real.log (1 - (p : ℝ)⁻¹) - ∑ k ∈ Icc 1 (p.log ⌊x⌋₊), 1 / ((k : ℝ) * (p : ℝ) ^ k))
      ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, 2 * ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹ :=
        sum_le_sum fun p _ ↦ (neg_log_one_sub_inv_sub_sum_Icc_le p ⌊x⌋₊).2
    _ = 2 * ∑ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹ := (mul_sum _ _ _).symm
    _ ≤ 2 * (5 / Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_inv_pow_log_succ_le x) zero_le_two
    _ = 10 / Real.sqrt x := by ring

/-- **Mertens's second theorem in von Mangoldt form, uniform on `[2, ∞)`.** There is an absolute
constant `C` such that for every real `x ≥ 2`,
`|∑_{2 ≤ n ≤ x} Λ(n) / (n log n) - log log x - γ| ≤ C / log x`. -/
theorem exists_abs_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n) -
          Real.log (Real.log x) - Real.eulerMascheroniConstant| ≤ C / Real.log x := by
  obtain ⟨C, hC⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  refine ⟨C + 20, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hlog_le_sq : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have h10 : 10 / Real.sqrt x ≤ 20 / Real.log x := by
    rw [div_le_div_iff₀ hsq hlog]
    linarith
  set D := (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
    (∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n))
  have hD0 : 0 ≤ D :=
    sub_nonneg.mpr (sum_Icc_vonMangoldt_div_mul_log_le_sum_primesLE_neg_log_one_sub_inv x)
  have hDle : D ≤ 20 / Real.log x :=
    (sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_le x).trans h10
  have hsplit : ∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n) -
      Real.log (Real.log x) - Real.eulerMascheroniConstant =
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
        Real.log (Real.log x) - Real.eulerMascheroniConstant) - D := by
    simp only [D]
    ring
  rw [hsplit, add_div]
  refine (abs_sub _ _).trans (add_le_add (hC x hx) ?_)
  rwa [abs_of_nonneg hD0]

/-- **Mertens's second theorem in von Mangoldt form, asymptotic form:**
`∑_{2 ≤ n ≤ x} Λ(n) / (n log n) - log log x - γ = O(1 / log x)` as `x → ∞`. -/
theorem isBigO_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub :
    (fun x : ℝ ↦ ∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n) -
        Real.log (Real.log x) - Real.eulerMascheroniConstant)
      =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_abs_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub_le
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr hlog.le), ← div_eq_mul_inv]
  exact hC x hx

/-- **Mertens's second theorem in von Mangoldt form, limit form:**
`∑_{2 ≤ n ≤ x} Λ(n) / (n log n) - log log x → γ` as `x → ∞`. -/
theorem tendsto_sum_Icc_vonMangoldt_div_mul_log_sub_log_log :
    Tendsto (fun x : ℝ ↦ ∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n) - Real.log (Real.log x))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := (isBigO_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub.trans_tendsto
    (Real.tendsto_log_atTop.inv_tendsto_atTop)).add_const Real.eulerMascheroniConstant
  simpa using h

/-! ### Mertens's third theorem and Euler-product bounds -/

/-- The partial Euler product `∏_{p ≤ N} (1 - p⁻¹)⁻¹` equals `exp (∑_{p ≤ N} -log (1 - p⁻¹))`. -/
theorem prod_primesLE_one_sub_inv_inv_eq_exp_sum (N : ℕ) :
    (∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹) =
      Real.exp (∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹)) := by
  rw [Real.exp_sum]
  refine prod_congr rfl fun p hp ↦ ?_
  have hp1 : (1 : ℝ) < p := mod_cast (Nat.one_lt_of_mem_primesLE hp)
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  rw [Real.exp_neg, Real.exp_log hpos]

/-- The partial product `∏_{p ≤ N} (1 - p⁻¹)` equals `exp (-(∑_{p ≤ N} -log (1 - p⁻¹)))`. -/
theorem prod_primesLE_one_sub_inv_eq_exp_neg_sum (N : ℕ) :
    (∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)) =
      Real.exp (-(∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹))) := by
  rw [Real.exp_neg, ← prod_primesLE_one_sub_inv_inv_eq_exp_sum, ← prod_inv_distrib]
  simp

/-- **Mertens's third theorem with bounded additive remainder.** There is an absolute constant `C`
such that for every real `x ≥ 2`,
`|∏_{p ≤ x} (1 - p⁻¹)⁻¹ - e^γ log x| ≤ C`. -/
theorem exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) -
          Real.exp Real.eulerMascheroniConstant * Real.log x| ≤ C := by
  obtain ⟨K, hK⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  set M := max K 0
  refine ⟨Real.exp Real.eulerMascheroniConstant * M * Real.exp (M / Real.log 2), fun x hx ↦ ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  set E := (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
    Real.log (Real.log x) - Real.eulerMascheroniConstant
  have hE : |E| ≤ M / Real.log x :=
    (hK x hx).trans (div_le_div_of_nonneg_right (le_max_left _ _) hlog.le)
  have hE2 : |E| ≤ M / Real.log 2 :=
    hE.trans (div_le_div_of_nonneg_left (le_max_right _ _) hlog2 (Real.log_le_log zero_lt_two hx))
  have hprod : (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) =
      Real.exp Real.eulerMascheroniConstant * Real.log x * Real.exp E := by
    rw [prod_primesLE_one_sub_inv_inv_eq_exp_sum,
      ← Real.exp_log hlog, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [E]
    ring
  rw [hprod, ← mul_sub_one, abs_mul, abs_of_pos (mul_pos (Real.exp_pos _) hlog)]
  calc Real.exp Real.eulerMascheroniConstant * Real.log x * |Real.exp E - 1|
      ≤ Real.exp Real.eulerMascheroniConstant * Real.log x * (|E| * Real.exp |E|) :=
        mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_mul_exp_abs E) (by positivity)
    _ ≤ Real.exp Real.eulerMascheroniConstant * Real.log x *
          (M / Real.log x * Real.exp (M / Real.log 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hE (Real.exp_le_exp.mpr hE2) (by positivity)
            (div_nonneg (le_max_right _ _) hlog.le))
          (by positivity)
    _ = Real.exp Real.eulerMascheroniConstant * M * Real.exp (M / Real.log 2) := by
        field_simp [hlog.ne']

/-- **Mertens's third theorem, big-O form:**
`∏_{p ≤ x} (1 - p⁻¹)⁻¹ - e^γ log x = O(1)` as `x → ∞`. -/
theorem isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log :
    (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) -
        Real.exp Real.eulerMascheroniConstant * Real.log x)
      =O[atTop] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

/-- **Mertens's third theorem, asymptotic ratio form.** As `x → ∞`,
`(∏_{p ≤ x} (1 - p⁻¹)⁻¹) / log x` tends to `e^γ`. -/
theorem tendsto_prod_primesLE_one_sub_inv_inv_div_log :
    Tendsto (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) / Real.log x)
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have hinv : Tendsto (fun x : ℝ ↦ (1 : ℝ) * (Real.log x)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).congr fun _ ↦ (one_mul _).symm
  have h0 := (isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log.mul
    (isBigO_refl (fun x : ℝ ↦ (Real.log x)⁻¹) atTop)).trans_tendsto hinv
  have h := h0.add_const (Real.exp Real.eulerMascheroniConstant)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [sub_mul, mul_assoc, mul_inv_cancel₀ hlog, mul_one, sub_add_cancel, div_eq_mul_inv]

/-- **Reciprocal form of Mertens's third theorem, uniform on `[2, ∞)`.** There is an absolute
constant `C` such that for every real `x ≥ 2`,
`|∏_{p ≤ x} (1 - p⁻¹) - e^(-γ) / log x| ≤ C / log² x`. -/
theorem exists_abs_prod_primesLE_one_sub_inv_sub_exp_neg_div_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
          Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤ C / Real.log x ^ 2 := by
  obtain ⟨K, hK⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  set M := max K 0
  refine ⟨Real.exp (-Real.eulerMascheroniConstant) * M * Real.exp (M / Real.log 2), fun x hx ↦ ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  set E := (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
    Real.log (Real.log x) - Real.eulerMascheroniConstant
  have hE : |-E| ≤ M / Real.log x := by
    rw [abs_neg]
    exact (hK x hx).trans (div_le_div_of_nonneg_right (le_max_left _ _) hlog.le)
  have hE2 : |-E| ≤ M / Real.log 2 :=
    hE.trans (div_le_div_of_nonneg_left (le_max_right _ _) hlog2 (Real.log_le_log zero_lt_two hx))
  have hprod : (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) =
      Real.exp (-Real.eulerMascheroniConstant) / Real.log x * Real.exp (-E) := by
    rw [prod_primesLE_one_sub_inv_eq_exp_neg_sum, div_eq_mul_inv, ← Real.exp_log hlog,
      ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [E]
    ring
  rw [hprod, ← mul_sub_one, abs_mul, abs_of_pos (div_pos (Real.exp_pos _) hlog)]
  calc Real.exp (-Real.eulerMascheroniConstant) / Real.log x * |Real.exp (-E) - 1|
      ≤ Real.exp (-Real.eulerMascheroniConstant) / Real.log x * (|-E| * Real.exp |-E|) :=
        mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_mul_exp_abs (-E)) (by positivity)
    _ ≤ Real.exp (-Real.eulerMascheroniConstant) / Real.log x *
          (M / Real.log x * Real.exp (M / Real.log 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hE (Real.exp_le_exp.mpr hE2) (by positivity)
            (div_nonneg (le_max_right _ _) hlog.le))
          (by positivity)
    _ = Real.exp (-Real.eulerMascheroniConstant) * M * Real.exp (M / Real.log 2) /
          Real.log x ^ 2 := by
        field_simp [hlog.ne']

/-- **Reciprocal form of Mertens's third theorem, big-O form:**
`∏_{p ≤ x} (1 - p⁻¹) - e^(-γ) / log x = O(1 / log² x)` as `x → ∞`. -/
theorem isBigO_prod_primesLE_one_sub_inv_sub_exp_neg_div_log :
    (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
        Real.exp (-Real.eulerMascheroniConstant) / Real.log x)
      =O[atTop] fun x ↦ (Real.log x ^ 2)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_abs_prod_primesLE_one_sub_inv_sub_exp_neg_div_log_le
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), ← div_eq_mul_inv]
  exact hC x hx

/-- **Reciprocal form of Mertens's third theorem, asymptotic ratio form.** As `x → ∞`,
`(∏_{p ≤ x} (1 - p⁻¹)) * log x` tends to `e^(-γ)`. -/
theorem tendsto_prod_primesLE_one_sub_inv_mul_log :
    Tendsto (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) * Real.log x)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := tendsto_prod_primesLE_one_sub_inv_inv_div_log.inv₀ (Real.exp_pos _).ne'
  rw [← Real.exp_neg] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x _
  rw [inv_div, div_eq_mul_inv, ← prod_inv_distrib, mul_comm]
  simp

private theorem one_sub_natCast_inv_nonneg (p : ℕ) : 0 ≤ 1 - (p : ℝ)⁻¹ := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (mod_cast Nat.one_le_iff_ne_zero.mpr hp))

private theorem prod_one_sub_inv_nonneg (s : Finset ℕ) :
    0 ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) :=
  prod_nonneg fun p _ ↦ one_sub_natCast_inv_nonneg p

private theorem prod_one_sub_inv_le_one (s : Finset ℕ) :
    (∏ p ∈ s, (1 - (p : ℝ)⁻¹)) ≤ 1 :=
  prod_le_one₀ (fun p _ ↦ one_sub_natCast_inv_nonneg p) (fun _ _ ↦ sub_le_self 1 (by positivity))

private theorem prod_filter_prime_one_sub_inv_le (T : Finset ℕ) (n : ℕ) :
    (∏ p ∈ T with p.Prime, (1 - (p : ℝ)⁻¹)) ≤
      ∏ p ∈ Nat.primesLE n with p ∈ T, (1 - (p : ℝ)⁻¹) := by
  have hsub : filter (· ∈ T) (Nat.primesLE n) ⊆ filter Nat.Prime T := fun p hp ↦
    mem_filter.mpr ⟨(mem_filter.mp hp).2, Nat.prime_of_mem_primesLE (mem_filter.mp hp).1⟩
  rw [← prod_sdiff hsub]
  exact mul_le_of_le_one_left (prod_one_sub_inv_nonneg _) (prod_one_sub_inv_le_one _)

/-- **Universal lower bound for partial Euler products with omitted primes.** There is an absolute
positive constant `c₁ > 0` such that for every finite set `T : Finset ℕ` and every real `y ≥ 2`,
`c₁ / log y ≤ ∏_{p ≤ y, p ∉ T} (1 - p⁻¹)`. -/
theorem exists_pos_div_log_le_prod_primesLE_filter_notMem_one_sub_inv :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (T : Finset ℕ) (y : ℝ), 2 ≤ y →
      c₁ / Real.log y ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹) := by
  obtain ⟨K, hK⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  set B := max K 0 / Real.log 2
  refine ⟨Real.exp (-Real.eulerMascheroniConstant - B), Real.exp_pos _, fun T y hy ↦ ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  set S := ∑ p ∈ Nat.primesLE ⌊y⌋₊, -Real.log (1 - (p : ℝ)⁻¹)
  have hSle : S ≤ Real.log (Real.log y) + Real.eulerMascheroniConstant + B := by
    have h1 : S - Real.log (Real.log y) - Real.eulerMascheroniConstant ≤ max K 0 / Real.log y :=
      (le_abs_self _).trans
        ((hK y hy).trans (div_le_div_of_nonneg_right (le_max_left _ _) hlog.le))
    have h2 : max K 0 / Real.log y ≤ B :=
      div_le_div_of_nonneg_left (le_max_right _ _) hlog2 (Real.log_le_log zero_lt_two hy)
    linarith
  have hfull : Real.exp (-Real.eulerMascheroniConstant - B) / Real.log y ≤
      ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹) := by
    rw [prod_primesLE_one_sub_inv_eq_exp_neg_sum, div_eq_mul_inv, ← Real.exp_log hlog,
      ← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  refine hfull.trans ?_
  rw [← prod_filter_mul_prod_filter_not (Nat.primesLE ⌊y⌋₊) (· ∈ T)]
  exact mul_le_of_le_one_left (prod_one_sub_inv_nonneg _) (prod_one_sub_inv_le_one _)

/-- **Two-sided `1 / log y` comparison for partial Euler products with omitted primes.** For every
finite set `T : Finset ℕ`, there exist positive constants `c₁, c₂ > 0` such that for all `y ≥ 2`,
`c₁ / log y ≤ ∏_{p ≤ y, p ∉ T} (1 - p⁻¹) ≤ c₂ / log y`. -/
theorem exists_pos_prod_primesLE_filter_notMem_one_sub_inv_bounds (T : Finset ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ y : ℝ, 2 ≤ y →
      c₁ / Real.log y ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)) ∧
        (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)) ≤ c₂ / Real.log y := by
  obtain ⟨c₁, hc₁, hlo⟩ := exists_pos_div_log_le_prod_primesLE_filter_notMem_one_sub_inv
  obtain ⟨K, hK⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  set B := max K 0 / Real.log 2
  set P := ∏ p ∈ T with p.Prime, (1 - (p : ℝ)⁻¹)
  have hPpos : 0 < P := prod_pos fun p hp ↦
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast (mem_filter.mp hp).2.one_lt))
  refine ⟨c₁, Real.exp (-Real.eulerMascheroniConstant + B) / P, hc₁,
    div_pos (Real.exp_pos _) hPpos, fun y hy ↦ ⟨hlo T y hy, ?_⟩⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  set S := ∑ p ∈ Nat.primesLE ⌊y⌋₊, -Real.log (1 - (p : ℝ)⁻¹)
  have hSge : Real.log (Real.log y) + Real.eulerMascheroniConstant - B ≤ S := by
    have h1 : -(max K 0 / Real.log y) ≤
        S - Real.log (Real.log y) - Real.eulerMascheroniConstant :=
      (neg_le_neg ((hK y hy).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hlog.le))).trans (neg_abs_le _)
    have h2 : max K 0 / Real.log y ≤ B :=
      div_le_div_of_nonneg_left (le_max_right _ _) hlog2 (Real.log_le_log zero_lt_two hy)
    linarith
  have hfull : (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)) ≤
      Real.exp (-Real.eulerMascheroniConstant + B) / Real.log y := by
    rw [prod_primesLE_one_sub_inv_eq_exp_neg_sum, div_eq_mul_inv, ← Real.exp_log hlog,
      ← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hmul : P * (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)) ≤
      Real.exp (-Real.eulerMascheroniConstant + B) / Real.log y :=
    (mul_le_mul_of_nonneg_right (prod_filter_prime_one_sub_inv_le T ⌊y⌋₊)
      (prod_one_sub_inv_nonneg _)).trans
      ((prod_filter_mul_prod_filter_not (Nat.primesLE ⌊y⌋₊) (· ∈ T) _).trans_le hfull)
  rw [div_div, mul_comm P (Real.log y), ← div_div, le_div_iff₀' hPpos]
  exact hmul

/-- **Two-sided `1 / log y` comparison for the full partial Euler product.** There exist positive
constants `c₁, c₂ > 0` such that for all `y ≥ 2`,
`c₁ / log y ≤ ∏_{p ≤ y} (1 - p⁻¹) ≤ c₂ / log y`. -/
theorem exists_pos_prod_primesLE_one_sub_inv_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ y : ℝ, 2 ≤ y →
      c₁ / Real.log y ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)) ∧
        (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)) ≤ c₂ / Real.log y := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := exists_pos_prod_primesLE_filter_notMem_one_sub_inv_bounds ∅
  refine ⟨c₁, c₂, hc₁, hc₂, fun y hy ↦ ?_⟩
  simpa using h y hy

end TauCeti
