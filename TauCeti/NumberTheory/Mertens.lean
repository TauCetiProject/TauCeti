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
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Rat
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
Mertens's third theorem with bounded `O(1)` additive remainder,
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
* `TauCeti.exists_pos_prod_primesLE_filter_notMem_one_sub_inv_bounds` and
  `TauCeti.exists_pos_prod_primesLE_filter_notMem_one_sub_inv_inv_bounds`: two-sided `1 / log y`
  comparison for `∏_{p ≤ y, p ∉ T} (1 - p⁻¹)` and `log y` comparison for its reciprocal on
  `y ≥ 2` for any finite set `T`.
* `TauCeti.hasSum_vonMangoldt_nonprime_div_mul_log`,
  `TauCeti.summable_vonMangoldt_nonprime_div_mul_log`, and
  `TauCeti.tsum_vonMangoldt_nonprime_div_mul_log`: the higher-prime-power series
  `∑_{¬n.Prime} Λ(n) / (n log n)` sums to `γ - meisselMertensConstant`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874), 46–62.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society (2019), Theorem 3.4 and Exercise 5.4.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., §22.8.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.1.
-/

public section

open Asymptotics Filter Finset
open scoped ArithmeticFunction Topology

namespace TauCeti

/-! ### The Meissel–Mertens constant and prime logarithmic remainders -/

/-- The prime series `∑_p (log (1 - p⁻¹) + p⁻¹)` is summable. -/
theorem summable_prime_log_one_sub_inv_add_inv :
    Summable (fun p : Nat.Primes ↦ Real.log (1 - ((p : ℕ) : ℝ)⁻¹) + ((p : ℕ) : ℝ)⁻¹) := by
  have hsq : Summable (fun p : Nat.Primes ↦ (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr one_lt_two).subtype _
  have hneg : Summable (fun p : Nat.Primes ↦
      -Real.log (1 - ((p : ℕ) : ℝ)⁻¹) - ((p : ℕ) : ℝ)⁻¹) :=
    hsq.of_nonneg_of_le
      (fun p ↦ (Real.neg_log_one_sub_inv_sub_inv_pos (mod_cast p.property.one_lt)).le)
      (fun p ↦ Real.neg_log_one_sub_inv_sub_inv_le (mod_cast p.property.two_le))
  exact hneg.neg.congr fun _ ↦ by ring

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
      · linarith [Real.neg_log_one_sub_inv_sub_inv_pos (x := (p : ℕ)) (mod_cast p.property.one_lt)]
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

/-- Upgrade an eventual `O(1 / log x)` estimate for a nonnegative prime sum to a uniform bound on
`[2, ∞)`. -/
private theorem exists_abs_sum_primesLE_sub_log_log_sub_le_of_isBigO {f : ℕ → ℝ} {A : ℝ}
    (hf : ∀ p : ℕ, p.Prime → 0 ≤ f p)
    (hO : (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, f p) - Real.log (Real.log x) - A)
      =O[atTop] fun x ↦ (Real.log x)⁻¹) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, f p) - Real.log (Real.log x) - A| ≤ C / Real.log x := by
  obtain ⟨C, -, hC⟩ := hO.exists_norm_le_div_log one_lt_two fun b ↦ by
    refine ⟨(∑ p ∈ Nat.primesLE ⌊b⌋₊, f p) +
        (|Real.log (Real.log 2)| + |Real.log (Real.log (max b 2))|) + |A|,
      fun x hx ↦ ?_⟩
    rw [Real.norm_eq_abs]
    have hsum_nonneg : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p :=
      sum_nonneg fun p hp ↦ hf p (Nat.prime_of_mem_primesLE hp)
    have hsum_le : (∑ p ∈ Nat.primesLE ⌊x⌋₊, f p) ≤ ∑ p ∈ Nat.primesLE ⌊b⌋₊, f p :=
      sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hx.2)) fun p hp _ ↦
        hf p (Nat.prime_of_mem_primesLE hp)
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
  exact ⟨C, by simpa only [Real.norm_eq_abs] using hC⟩

/-- **Mertens's second theorem, uniform on `[2, ∞)`.** There is an absolute constant `C` such that
for every real `x ≥ 2`,
`|∑_{p ≤ x} p⁻¹ - log log x - meisselMertensConstant| ≤ C / log x`. -/
theorem exists_abs_sum_primesLE_inv_sub_log_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) - meisselMertensConstant| ≤
        C / Real.log x :=
  exists_abs_sum_primesLE_sub_log_log_sub_le_of_isBigO (fun _ _ ↦ by positivity)
    isBigO_sum_primesLE_inv_sub_log_log_sub_meisselMertensConstant

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

/-- **Logarithmic Euler-product form of Mertens's theorem, asymptotic form:**
`∑_{p ≤ x} -log (1 - p⁻¹) - log log x - γ = O(1 / log x)` as `x → ∞`. -/
theorem isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
        Real.log (Real.log x) - Real.eulerMascheroniConstant)
      =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  refine (LFunctions.isBigO_primeSummatory_neg_log_one_sub_inv_absNorm_sub_log_log_sub ℚ).congr_left
    fun x ↦ ?_
  rw [primeSummatory_rat_eq_sum_primesLE (fun n ↦ -Real.log (1 - (n : ℝ)⁻¹)),
    dedekindZeta_residue_rat, Real.log_one, add_zero]

/-- **Logarithmic Euler-product form of Mertens's theorem, uniform on `[2, ∞)`.** There is an
absolute constant `C` such that for every real `x ≥ 2`,
`|∑_{p ≤ x} -log (1 - p⁻¹) - log log x - γ| ≤ C / log x`. -/
theorem exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
          Real.log (Real.log x) - Real.eulerMascheroniConstant| ≤ C / Real.log x :=
  exists_abs_sum_primesLE_sub_log_log_sub_le_of_isBigO
    (fun p _ ↦ Real.neg_log_one_sub_nonneg (by positivity) (Nat.cast_inv_le_one p))
    isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub

/-- **Logarithmic Euler-product form of Mertens's theorem, limit form:**
`∑_{p ≤ x} -log (1 - p⁻¹) - log log x → γ` as `x → ∞`. -/
theorem tendsto_sum_primesLE_neg_log_one_sub_inv_sub_log_log :
    Tendsto (fun x : ℝ ↦
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) - Real.log (Real.log x))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := (isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub.trans_tendsto
    (Real.tendsto_log_atTop.inv_tendsto_atTop)).add_const Real.eulerMascheroniConstant
  simpa using h

private theorem sum_Icc_two_vonMangoldt_div_mul_log (N : ℕ) :
    ∑ n ∈ Icc 2 N, Λ n / ((n : ℝ) * Real.log n) =
      ∑ n ∈ Icc 1 N, Λ n / ((n : ℝ) * Real.log n) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [← insert_Icc_add_one_left_eq_Icc (Nat.one_le_iff_ne_zero.mpr hN), sum_insert (by simp)]
    simp

/-- At any prime power `p ^ k` (including `k = 0`, where both sides vanish by division by zero),
`Λ(p ^ k) / (p ^ k * log (p ^ k)) = (p⁻¹) ^ k / k`. -/
theorem vonMangoldt_div_mul_log_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Λ (p ^ k) / (((p ^ k : ℕ) : ℝ) * Real.log ((p ^ k : ℕ) : ℝ)) =
      ((p : ℝ)⁻¹) ^ k / (k : ℝ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hp0 : (p : ℝ) ≠ 0 := mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := mod_cast hk
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (mod_cast hp.one_lt)).ne'
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp,
    Nat.cast_pow, Real.log_pow, inv_pow]
  field_simp

/-- Exact prime-power regrouping of the weighted von Mangoldt sum:
`∑_{2 ≤ n ≤ N} Λ(n) / (n log n) = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} 1 / (k p ^ k)`. -/
theorem sum_Icc_vonMangoldt_div_mul_log_eq (N : ℕ) :
    ∑ n ∈ Icc 2 N, Λ n / (n * Real.log n) =
      ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
  rw [sum_Icc_two_vonMangoldt_div_mul_log, Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log
    (fun n hn ↦ by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div])]
  refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k _ ↦ ?_
  rw [vonMangoldt_div_mul_log_prime_pow (Nat.prime_of_mem_primesLE hp), inv_pow,
    div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_inv, mul_comm]

/-- The weighted von Mangoldt sum never exceeds the logarithmic Euler-product sum up to `x`. -/
theorem sum_Icc_vonMangoldt_div_mul_log_le_sum_primesLE_neg_log_one_sub_inv (x : ℝ) :
    ∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n) ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹) := by
  rw [sum_Icc_vonMangoldt_div_mul_log_eq]
  exact sum_le_sum fun p hp ↦
    sub_nonneg.mp (Real.neg_log_one_sub_inv_sub_sum_Icc_nonneg
      (mod_cast Nat.one_lt_of_mem_primesLE hp) _)

/-- For every real `x`, the prime-power excess between the logarithmic Euler-product sum and the
weighted von Mangoldt sum is at most `10 / √x`. -/
theorem sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_le (x : ℝ) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
        (∑ n ∈ Icc 2 ⌊x⌋₊, Λ n / (n * Real.log n)) ≤ 10 / Real.sqrt x := by
  rw [sum_Icc_vonMangoldt_div_mul_log_eq, ← sum_sub_distrib]
  calc ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (-Real.log (1 - (p : ℝ)⁻¹) - ∑ k ∈ Icc 1 (p.log ⌊x⌋₊), 1 / ((k : ℝ) * (p : ℝ) ^ k))
      ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, 2 * ((p : ℝ) ^ (p.log ⌊x⌋₊ + 1))⁻¹ :=
        sum_le_sum fun p hp ↦
          Real.neg_log_one_sub_inv_sub_sum_Icc_le (mod_cast Nat.two_le_of_mem_primesLE hp) _
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

/-- **Mertens's third theorem, big-O form:**
`∏_{p ≤ x} (1 - p⁻¹)⁻¹ - e^γ log x = O(1)` as `x → ∞`. -/
theorem isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log :
    (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) -
        Real.exp Real.eulerMascheroniConstant * Real.log x)
      =O[atTop] fun _ ↦ (1 : ℝ) := by
  refine (LFunctions.isBigO_prod_one_sub_inv_absNorm_sub_mul_log ℚ).congr_left fun x ↦ ?_
  rw [finprod_heightOneSpectrum_rat_ite_absNorm_le_eq_prod_primesLE (fun n ↦ (1 - (n : ℝ)⁻¹)⁻¹),
    dedekindZeta_residue_rat, mul_one]

/-- **Mertens's third theorem with bounded additive remainder.** There is an absolute constant `C`
such that for every real `x ≥ 2`,
`|∏_{p ≤ x} (1 - p⁻¹)⁻¹ - e^γ log x| ≤ C`. -/
theorem exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) -
          Real.exp Real.eulerMascheroniConstant * Real.log x| ≤ C := by
  have hIci := isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log.isBigO_principal_Ici
    (a := 2) (c := 1) one_pos (fun _ _ ↦ by simp) fun b ↦ ?_
  · obtain ⟨C, hC⟩ := Asymptotics.isBigO_principal.mp hIci
    exact ⟨C, fun x hx ↦ by simpa only [Real.norm_eq_abs, norm_one, mul_one] using hC x hx⟩
  · refine ⟨(∏ p ∈ Nat.primesLE ⌊b⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) +
        Real.exp Real.eulerMascheroniConstant * Real.log (max b 2), fun x hx ↦ ?_⟩
    rw [Real.norm_eq_abs]
    have hprod_nonneg : 0 ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ :=
      prod_nonneg fun p _ ↦ inv_nonneg.mpr (sub_nonneg.mpr (Nat.cast_inv_le_one p))
    have hprod_le : (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) ≤
        ∏ p ∈ Nat.primesLE ⌊b⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ :=
      prod_le_prod_of_subset_of_one_le₀ (Nat.primesLE_mono (Nat.floor_mono hx.2))
        (fun p _ ↦ inv_nonneg.mpr (sub_nonneg.mpr (Nat.cast_inv_le_one p)))
        fun p hp _ ↦ by
          have hp1 : (1 : ℝ) < p := mod_cast Nat.one_lt_of_mem_primesLE hp
          exact (one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))).mpr
            (sub_le_self 1 (by positivity))
    have hlog_nonneg : 0 ≤ Real.exp Real.eulerMascheroniConstant * Real.log x :=
      mul_nonneg (Real.exp_pos _).le (Real.log_pos (one_lt_two.trans_le hx.1)).le
    have hlog_le : Real.exp Real.eulerMascheroniConstant * Real.log x ≤
        Real.exp Real.eulerMascheroniConstant * Real.log (max b 2) :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith [hx.1]) (hx.2.trans (le_max_left _ _)))
        (Real.exp_pos _).le
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rwa [abs_of_nonneg hprod_nonneg]
    · rwa [abs_of_nonneg hlog_nonneg]

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

/-- Two-sided `log x` comparison for the full reciprocal Euler product on `[2, ∞)`, derived from
`exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le`. -/
private theorem exists_pos_prod_primesLE_one_sub_inv_inv_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x : ℝ, 2 ≤ x →
      c₁ * Real.log x ≤ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) ∧
        (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) ≤ c₂ * Real.log x := by
  obtain ⟨C, hC⟩ := exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le
  set K := max C 0
  set eg := Real.exp Real.eulerMascheroniConstant
  have heg : 0 < eg := Real.exp_pos _
  set B := max 2 (Real.exp (2 * K / eg))
  have hB2 : 2 ≤ B := le_max_left _ _
  have hlogB : 0 < Real.log B := Real.log_pos (one_lt_two.trans_le hB2)
  refine ⟨min (eg / 2) (1 / Real.log B), eg + K / Real.log 2,
    lt_min (half_pos heg) (div_pos one_pos hlogB), by positivity, fun x hx ↦ ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  have hCx := abs_le.mp ((hC x hx).trans (le_max_left C 0))
  constructor
  · rcases le_or_gt B x with hBx | hxB
    · have hlog_ge : 2 * K / eg ≤ Real.log x := by
        calc 2 * K / eg = Real.log (Real.exp (2 * K / eg)) := (Real.log_exp _).symm
          _ ≤ Real.log B := Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
          _ ≤ Real.log x := Real.log_le_log (by linarith) hBx
      have hK_le : K ≤ eg * Real.log x / 2 := by
        have := (div_le_iff₀ heg).mp hlog_ge
        linarith
      calc min (eg / 2) (1 / Real.log B) * Real.log x
          ≤ (eg / 2) * Real.log x := mul_le_mul_of_nonneg_right (min_le_left _ _) hlog.le
        _ = eg * Real.log x - eg * Real.log x / 2 := by ring
        _ ≤ eg * Real.log x - K := by linarith
        _ ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := by linarith [hCx.1]
    · have hprod_ge_one : (1 : ℝ) ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ :=
        one_le_prod₀ fun p hp ↦ by
          have hp1 : (1 : ℝ) < p := mod_cast Nat.one_lt_of_mem_primesLE hp
          exact (one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))).mpr
            (sub_le_self 1 (by positivity))
      calc min (eg / 2) (1 / Real.log B) * Real.log x
          ≤ (1 / Real.log B) * Real.log x := mul_le_mul_of_nonneg_right (min_le_right _ _) hlog.le
        _ ≤ (1 / Real.log B) * Real.log B :=
            mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hxB.le) (by positivity)
        _ = 1 := by field_simp [hlogB.ne']
        _ ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := hprod_ge_one
  · calc (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹)
        ≤ eg * Real.log x + K := by linarith [hCx.2]
      _ = eg * Real.log x + (K / Real.log x) * Real.log x := by field_simp [hlog.ne']
      _ ≤ eg * Real.log x + (K / Real.log 2) * Real.log x := by gcongr
      _ = (eg + K / Real.log 2) * Real.log x := by ring

/-- **Reciprocal form of Mertens's third theorem, uniform on `[2, ∞)`.** There is an absolute
constant `C` such that for every real `x ≥ 2`,
`|∏_{p ≤ x} (1 - p⁻¹) - e^(-γ) / log x| ≤ C / log² x`. -/
theorem exists_abs_prod_primesLE_one_sub_inv_sub_exp_neg_div_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) -
          Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤ C / Real.log x ^ 2 := by
  obtain ⟨C, hC⟩ := exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_mul_log_le
  obtain ⟨c₁, _, hc₁, _, hB⟩ := exists_pos_prod_primesLE_one_sub_inv_inv_bounds
  refine ⟨max C 0 / (c₁ * Real.exp Real.eulerMascheroniConstant), fun x hx ↦ ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  set P := ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹
  have hP_ge : c₁ * Real.log x ≤ P := (hB x hx).1
  have hP_pos : 0 < P := (mul_pos hc₁ hlog).trans_le hP_ge
  have heg_pos : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have hinv : (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) = P⁻¹ := by
    simp [P, prod_inv_distrib]
  have hid : P⁻¹ - Real.exp (-Real.eulerMascheroniConstant) / Real.log x =
      (Real.exp Real.eulerMascheroniConstant * Real.log x - P) /
        (P * (Real.exp Real.eulerMascheroniConstant * Real.log x)) := by
    rw [Real.exp_neg]
    field_simp [hP_pos.ne', hlog.ne', heg_pos.ne']
  rw [hinv, hid, abs_div, abs_of_pos (mul_pos hP_pos (mul_pos heg_pos hlog)), abs_sub_comm]
  calc |P - Real.exp Real.eulerMascheroniConstant * Real.log x| /
        (P * (Real.exp Real.eulerMascheroniConstant * Real.log x))
      ≤ max C 0 / (c₁ * Real.log x * (Real.exp Real.eulerMascheroniConstant * Real.log x)) := by
        gcongr
        exact (hC x hx).trans (le_max_left C 0)
    _ = max C 0 / (c₁ * Real.exp Real.eulerMascheroniConstant) / Real.log x ^ 2 := by
        ring

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

private theorem prod_filter_prime_one_sub_inv_le (T : Finset ℕ) (n : ℕ) :
    (∏ p ∈ T with p.Prime, (1 - (p : ℝ)⁻¹)) ≤
      ∏ p ∈ Nat.primesLE n with p ∈ T, (1 - (p : ℝ)⁻¹) := by
  have hsub : filter (· ∈ T) (Nat.primesLE n) ⊆ filter Nat.Prime T := fun p hp ↦
    mem_filter.mpr ⟨(mem_filter.mp hp).2, Nat.prime_of_mem_primesLE (mem_filter.mp hp).1⟩
  exact prod_le_prod_of_subset_of_le_one₀ hsub
    (fun p _ ↦ sub_nonneg.mpr (Nat.cast_inv_le_one p)) (fun _ _ _ ↦ sub_le_self 1 (by positivity))

/-- **Universal lower bound for partial Euler products with omitted primes.** There is an absolute
positive constant `c₁ > 0` such that for every finite set `T : Finset ℕ` and every real `y ≥ 2`,
`c₁ / log y ≤ ∏_{p ≤ y, p ∉ T} (1 - p⁻¹)`. -/
theorem exists_pos_div_log_le_prod_primesLE_filter_notMem_one_sub_inv :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (T : Finset ℕ) (y : ℝ), 2 ≤ y →
      c₁ / Real.log y ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹) := by
  obtain ⟨_, c₂, _, hc₂, hB⟩ := exists_pos_prod_primesLE_one_sub_inv_inv_bounds
  refine ⟨c₂⁻¹, inv_pos.mpr hc₂, fun T y hy ↦ ?_⟩
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹) := prod_pos fun p hp ↦
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast Nat.one_lt_of_mem_primesLE hp))
  have hfull : c₂⁻¹ / Real.log y ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹) := by
    have hle : (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹))⁻¹ ≤ c₂ * Real.log y := by
      simpa [prod_inv_distrib] using (hB y hy).2
    calc c₂⁻¹ / Real.log y = (c₂ * Real.log y)⁻¹ := by rw [div_eq_inv_mul, mul_inv, mul_comm]
      _ ≤ ((∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹))⁻¹)⁻¹ :=
          inv_anti₀ (inv_pos.mpr hprod_pos) hle
      _ = ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹) := inv_inv _
  exact hfull.trans (prod_le_prod_of_subset_of_le_one₀ (filter_subset _ _)
    (fun p _ ↦ sub_nonneg.mpr (Nat.cast_inv_le_one p)) (fun _ _ _ ↦ sub_le_self 1 (by positivity)))

/-- **Two-sided `1 / log y` comparison for partial Euler products with omitted primes.** For every
finite set `T : Finset ℕ`, there exist positive constants `c₁, c₂ > 0` such that for all `y ≥ 2`,
`c₁ / log y ≤ ∏_{p ≤ y, p ∉ T} (1 - p⁻¹) ≤ c₂ / log y`. -/
theorem exists_pos_prod_primesLE_filter_notMem_one_sub_inv_bounds (T : Finset ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ y : ℝ, 2 ≤ y →
      c₁ / Real.log y ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)) ∧
        (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)) ≤ c₂ / Real.log y := by
  obtain ⟨c₁, hc₁, hlo⟩ := exists_pos_div_log_le_prod_primesLE_filter_notMem_one_sub_inv
  obtain ⟨c₁', _, hc₁', _, hB⟩ := exists_pos_prod_primesLE_one_sub_inv_inv_bounds
  set P := ∏ p ∈ T with p.Prime, (1 - (p : ℝ)⁻¹)
  have hPpos : 0 < P := prod_pos fun p hp ↦
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast (mem_filter.mp hp).2.one_lt))
  refine ⟨c₁, c₁'⁻¹ / P, hc₁, div_pos (inv_pos.mpr hc₁') hPpos, fun y hy ↦ ⟨hlo T y hy, ?_⟩⟩
  have hlog : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  have hfull : (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)) ≤ c₁'⁻¹ / Real.log y := by
    have hle : c₁' * Real.log y ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹))⁻¹ := by
      simpa [prod_inv_distrib] using (hB y hy).1
    calc (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹))
        = ((∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹))⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ (c₁' * Real.log y)⁻¹ := inv_anti₀ (mul_pos hc₁' hlog) hle
      _ = c₁'⁻¹ / Real.log y := by rw [mul_inv, div_eq_inv_mul, mul_comm]
  have hmul : P * (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)) ≤ c₁'⁻¹ / Real.log y :=
    (mul_le_mul_of_nonneg_right (prod_filter_prime_one_sub_inv_le T ⌊y⌋₊)
      (prod_nonneg fun p _ ↦ sub_nonneg.mpr (Nat.cast_inv_le_one p))).trans
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

/-- **Two-sided `log y` comparison for reciprocal partial Euler products with omitted primes.**
For every finite set `T : Finset ℕ`, there exist positive constants `c₁, c₂ > 0` such that for
all `y ≥ 2`,
`c₁ * log y ≤ ∏_{p ≤ y, p ∉ T} (1 - p⁻¹)⁻¹ ≤ c₂ * log y`. -/
theorem exists_pos_prod_primesLE_filter_notMem_one_sub_inv_inv_bounds (T : Finset ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ y : ℝ, 2 ≤ y →
      c₁ * Real.log y ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)⁻¹) ∧
        (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹)⁻¹) ≤ c₂ * Real.log y := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := exists_pos_prod_primesLE_filter_notMem_one_sub_inv_bounds T
  refine ⟨c₂⁻¹, c₁⁻¹, inv_pos.mpr hc₂, inv_pos.mpr hc₁, fun y hy ↦ ?_⟩
  obtain ⟨hlo, hhi⟩ := h y hy
  have hlogy : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹) :=
    (div_pos hc₁ hlogy).trans_le hlo
  rw [prod_inv_distrib]
  constructor
  · calc c₂⁻¹ * Real.log y = (c₂ / Real.log y)⁻¹ := by rw [inv_div, div_eq_inv_mul]
      _ ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹))⁻¹ := inv_anti₀ hprod_pos hhi
  · calc (∏ p ∈ Nat.primesLE ⌊y⌋₊ with p ∉ T, (1 - (p : ℝ)⁻¹))⁻¹
        ≤ (c₁ / Real.log y)⁻¹ := inv_anti₀ (div_pos hc₁ hlogy) hlo
      _ = c₁⁻¹ * Real.log y := by rw [inv_div, div_eq_inv_mul]

/-! ### Series of higher-prime-power reciprocals -/

/-- **Exact sum of the non-prime von Mangoldt reciprocal series.** Summing `Λ(n) / (n log n)` over
non-prime `n : ℕ` (that is, `1 / (k p ^ k)` over prime powers `p ^ k` with `k ≥ 2`) converges to
`γ - meisselMertensConstant`. -/
theorem hasSum_vonMangoldt_nonprime_div_mul_log :
    HasSum (fun n : ℕ ↦ if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n))
      (Real.eulerMascheroniConstant - meisselMertensConstant) := by
  set f : ℕ → ℝ := fun n ↦ if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n)
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    simp only [f]
    split_ifs
    · exact le_rfl
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (mod_cast Nat.pos_of_ne_zero hn0)))
  rw [hasSum_iff_tendsto_nat_of_nonneg hf_nonneg, ← tendsto_add_atTop_iff_nat 1]
  have hpart (N : ℕ) : ∑ n ∈ range (N + 1), f n =
      (∑ n ∈ Icc 2 N, Λ n / ((n : ℝ) * Real.log n)) -
        ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
    have hrange : ∑ n ∈ range (N + 1), f n = ∑ n ∈ Icc 1 N, f n := by
      refine (sum_subset (fun n hn ↦ mem_range.mpr (by
        rw [mem_Icc] at hn; lia)) fun n hnR hn ↦ ?_).symm
      rw [mem_range] at hnR
      have hn0 : n = 0 := by simp only [mem_Icc, not_and, not_le] at hn; lia
      simp [f, hn0]
    have hprime_sum : ∑ n ∈ Icc 1 N with n.Prime, Λ n / ((n : ℝ) * Real.log n) =
        ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
      rw [← Nat.primesLE_eq_filter_Icc_one]
      refine sum_congr rfl fun p hp ↦ ?_
      simpa using vonMangoldt_div_mul_log_prime_pow (Nat.prime_of_mem_primesLE hp) 1
    rw [hrange, sum_Icc_two_vonMangoldt_div_mul_log,
      ← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime f,
      ← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
        (fun n ↦ Λ n / ((n : ℝ) * Real.log n)), hprime_sum]
    have h1 : ∑ n ∈ Icc 1 N with n.Prime, f n = 0 :=
      sum_eq_zero fun n hn ↦ ite_eq_left (mem_filter.mp hn).2
    have h2 : ∑ n ∈ Icc 1 N with ¬n.Prime, f n =
        ∑ n ∈ Icc 1 N with ¬n.Prime, Λ n / ((n : ℝ) * Real.log n) :=
      sum_congr rfl fun n hn ↦ ite_eq_right (mem_filter.mp hn).2
    rw [h1, h2]
    ring
  have hlim := (tendsto_sum_Icc_vonMangoldt_div_mul_log_sub_log_log.comp
    tendsto_natCast_atTop_atTop).sub
    (tendsto_sum_primesLE_inv_sub_log_log.comp tendsto_natCast_atTop_atTop)
  refine hlim.congr fun N ↦ ?_
  simp only [Function.comp_apply, Nat.floor_natCast, hpart]
  ring

/-- The non-prime von Mangoldt reciprocal series `∑_{¬n.Prime} Λ(n) / (n log n)` is summable. -/
theorem summable_vonMangoldt_nonprime_div_mul_log :
    Summable fun n : ℕ ↦ if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n) :=
  hasSum_vonMangoldt_nonprime_div_mul_log.summable

/-- Closed form of the non-prime von Mangoldt reciprocal series:
`∑'_{¬n.Prime} Λ(n) / (n log n) = γ - meisselMertensConstant`. -/
theorem tsum_vonMangoldt_nonprime_div_mul_log :
    (∑' n : ℕ, if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n)) =
      Real.eulerMascheroniConstant - meisselMertensConstant :=
  hasSum_vonMangoldt_nonprime_div_mul_log.tsum_eq

end TauCeti
