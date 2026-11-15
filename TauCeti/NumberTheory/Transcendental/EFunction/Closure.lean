/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.Height.Denominator
public import TauCeti.NumberTheory.LcmUpto
public import TauCeti.NumberTheory.Transcendental.EFunction.Basic

/-!
# Closure properties and examples of Siegel's E-functions and G-functions

Siegel's E-functions and G-functions each form a differential subalgebra of formal power series
stable under algebraic rescaling and Galois conjugation:

* **Linear and ring closure**: zero, single-term sequences, finitely supported algebraic sequences,
  polynomials with `ℚ`-algebraic coefficients, constant sequences (`e^z` as an E-function and
  `(1 - z)⁻¹` as a G-function), addition, finite sums, negation, subtraction, algebraic scalar
  multiplication, Hurwitz convolution `hurwitzMul` (pointwise multiplication of `eFun`), and Cauchy
  convolution (ordinary multiplication of `PowerSeries.mk`).
* **Analytic and arithmetic symmetries**: index shifts `n ↦ a (n + k)` (differentiation of `eFun`),
  prepending a constant `0 ↦ c, n + 1 ↦ a n` (termwise integration `c + ∫₀ᶻ f(t) dt` of `eFun` or
  multiplication of `PowerSeries.mk` by `X`), rescaling `n ↦ c ^ n * a n` (`z ↦ c z`) for algebraic
  `c`, and Galois conjugation under ring endomorphisms of `ℂ` or automorphisms in
  `Gal(algebraicClosure ℚ ℂ/ℚ)`.
* **Canonical examples and sharpness counterexamples**:
  * `(z - 1) e^z` (`aₙ = n - 1`) is an E-function;
  * `-log(1 - z) = ∑_{n ≥ 1} zⁿ / n` (`a₀ = 0`, `aₙ = 1 / n`) is a G-function, with common
    denominators `Nat.lcmUpto n` bounded geometrically via Chebyshev's `ψ`-estimate;
  * `aₙ = n!` is not an E-function (its `ePowerSeries` is `(1 - X)⁻¹`, which is not entire);
  * `e^(z²)` (`a_{2k} = (2k)! / k!`, `a_{2k+1} = 0`) is entire and D-finite with integer
    coefficients, yet is **not** an E-function because `a_{2k} ≥ k ^ k` grows super-geometrically;
  * `∑ zⁿ / n! = e^z` (`aₙ = 1 / n!`) is **not** a G-function because any common denominator `dₙ`
    must be divisible by `n!`, violating the geometric denominator bound.

## Main results

* `TauCeti.IsGFunction.zero`, `TauCeti.IsGFunction.one`, `TauCeti.IsGFunction.single`,
  `TauCeti.IsGFunction.of_eventually_eq_zero`, `TauCeti.IsGFunction.add`, `TauCeti.IsGFunction.neg`,
  `TauCeti.IsGFunction.sub`, `TauCeti.IsGFunction.smul`, `TauCeti.IsGFunction.mul`,
  `TauCeti.IsGFunction.hurwitzMul`, `TauCeti.IsGFunction.shift`, `TauCeti.IsGFunction.cons_zero`,
  `TauCeti.IsGFunction.rescale`, `TauCeti.IsGFunction.comp_ringHom`,
  `TauCeti.IsGFunction.galoisConj`, together with the corresponding `TauCeti.IsEFunction.*` API.
* `TauCeti.isEFunction_natCast`, `TauCeti.isEFunction_natCast_sub_one`: `z e^z` and `(z - 1) e^z`
  are E-functions.
* `TauCeti.isGFunction_inv_natCast`: `-log(1 - z) = ∑_{n ≥ 1} zⁿ / n` is a G-function.
* `TauCeti.not_isEFunction_factorial`, `TauCeti.not_isEFunction_exp_sq`,
  `TauCeti.not_isGFunction_inv_factorial`: sharpness of the geometric growth conditions on
  coefficients and common denominators.

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuß. Akad. Wiss.
  Phys.-Math. Kl. **1929**, no. 1.
* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1, §4.1.
* A. B. Shidlovskii, *Transcendental Numbers*, de Gruyter Studies in Mathematics **12**, 1989,
  Chapter 3, §1.
-/

public section

open Finset Polynomial PowerSeries

namespace TauCeti

/-! ### Closure properties of G-functions and E-functions -/

section Closure

/-- Arithmetic denominator helper for a single `ℚ`-algebraic complex number `c`: its natural
denominator `b = Algebra.natDenominator c` satisfies `1 ≤ b` and clears `c` into an algebraic
integer `(b : ℂ) * c`. -/
private theorem one_le_and_isIntegral_natDenominator {c : ℂ} (hc : IsAlgebraic ℚ c) :
    1 ≤ Algebra.natDenominator c ∧ IsIntegral ℤ ((Algebra.natDenominator c : ℂ) * c) :=
  ⟨Nat.pos_of_ne_zero (Algebra.natDenominator_ne_zero_of_isAlgebraic_rat hc),
    by simpa only [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul c⟩

/-- The zero sequence is a G-function. -/
theorem IsGFunction.zero : IsGFunction 0 :=
  IsGFunction.of_house_le (fun _ ↦ isAlgebraic_zero)
    (by
      have h0 : PowerSeries.mk (0 : ℕ → ℂ) = 0 := by ext; simp
      rw [h0]
      exact PowerSeries.isDFinite_zero)
    ⟨1, zero_lt_one, fun n ↦ by simp⟩
    ⟨1, zero_lt_one, fun _ ↦ 1, fun n ↦ ⟨le_rfl, by simp, fun _ _ ↦ by simp [isIntegral_zero]⟩⟩

/-- The zero sequence is an E-function. -/
theorem IsEFunction.zero : IsEFunction 0 :=
  isGFunction_iff_isEFunction.mp .zero

/-- A sequence supported at a single index `k` with `ℚ`-algebraic value `c` is a G-function. -/
theorem IsGFunction.single (k : ℕ) {c : ℂ} (hc : IsAlgebraic ℚ c) :
    IsGFunction (Pi.single k c) := by
  obtain ⟨hb1, hbc⟩ := one_le_and_isIntegral_natDenominator hc
  set b := Algebra.natDenominator c
  refine IsGFunction.of_house_le
    (fun n ↦ by
      rcases eq_or_ne n k with rfl | hnk
      · simpa using hc
      · simp [Pi.single_eq_of_ne hnk, isAlgebraic_zero])
    (?_)
    ⟨max 1 (house c), by positivity, fun n ↦ ?_⟩
    ⟨b, Nat.cast_pos.mpr hb1, fun _ ↦ b, fun n ↦ ⟨hb1, ?_, fun m _ ↦ ?_⟩⟩
  · have hmk : PowerSeries.mk (Pi.single k c) = ((Polynomial.monomial k c : ℂ[X]) : ℂ⟦X⟧) := by
      ext n
      simp [Pi.single_apply, PowerSeries.coeff_monomial]
    rw [hmk]
    exact PowerSeries.isDFinite_polynomial (algebraicClosure ℚ ℂ) _
  · rcases eq_or_ne n k with rfl | hnk
    · simp only [Pi.single_eq_same]
      exact (le_max_right 1 (house c)).trans
        (le_self_pow₀ (le_max_left 1 (house c)) (Nat.succ_ne_zero n))
    · simp only [Pi.single_eq_of_ne hnk, house_zero]
      positivity
  · exact le_self_pow₀ (by exact_mod_cast hb1) (Nat.succ_ne_zero n)
  · rcases eq_or_ne m k with rfl | hmk
    · simpa using hbc
    · simp [Pi.single_eq_of_ne hmk, isIntegral_zero]

/-- A sequence supported at a single index `k` with `ℚ`-algebraic value `c` is an E-function. -/
theorem IsEFunction.single (k : ℕ) {c : ℂ} (hc : IsAlgebraic ℚ c) :
    IsEFunction (Pi.single k c) :=
  isGFunction_iff_isEFunction.mp (.single k hc)

/-- Constant-one data `fun _ ↦ 1` define an E-function (`eFun (fun _ ↦ 1) = Complex.exp`). -/
theorem IsEFunction.one : IsEFunction fun _ ↦ (1 : ℂ) :=
  IsEFunction.of_house_le (fun _ ↦ isAlgebraic_one)
    (by rw [ePowerSeries_one]; exact PowerSeries.isDFinite_exp)
    ⟨1, zero_lt_one, fun n ↦ by simp⟩
    ⟨1, zero_lt_one, fun _ ↦ 1, fun n ↦ ⟨le_rfl, by simp, fun _ _ ↦ by simp [isIntegral_one]⟩⟩

/-- Constant-one data `fun _ ↦ 1` define a G-function (the geometric series `(1 - X)⁻¹`). -/
theorem IsGFunction.one : IsGFunction fun _ ↦ (1 : ℂ) :=
  isGFunction_iff_isEFunction.mpr .one

/-- G-functions are closed under addition. -/
theorem IsGFunction.add {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction (a + b) := by
  obtain ⟨C₁, hC₁, hh₁⟩ := ha.exists_house_le
  obtain ⟨C₂, hC₂, hh₂⟩ := hb.exists_house_le
  obtain ⟨D₁, hD₁, d₁, hd₁⟩ := ha.den_le
  obtain ⟨D₂, hD₂, d₂, hd₂⟩ := hb.den_le
  refine IsGFunction.of_house_le
    (fun n ↦ ((ha.isAlgebraic n).isIntegral.add (hb.isAlgebraic n).isIntegral).isAlgebraic)
    (by
      have hmk : PowerSeries.mk (a + b) = PowerSeries.mk a + PowerSeries.mk b := by ext; simp
      rw [hmk]
      exact ha.isDFinite.add hb.isDFinite)
    ⟨2 * max C₁ C₂, by positivity, fun n ↦ ?_⟩
    ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun n ↦ d₁ n * d₂ n, fun n ↦ ?_⟩
  · calc house (a n + b n) ≤ house (a n) + house (b n) :=
          house_add_le (ha.isAlgebraic n) (hb.isAlgebraic n)
      _ ≤ C₁ ^ (n + 1) + C₂ ^ (n + 1) := add_le_add (hh₁ n) (hh₂ n)
      _ ≤ max C₁ C₂ ^ (n + 1) + max C₁ C₂ ^ (n + 1) :=
          add_le_add (pow_le_pow_left₀ hC₁.le (le_max_left _ _) _)
            (pow_le_pow_left₀ hC₂.le (le_max_right _ _) _)
      _ = 2 * max C₁ C₂ ^ (n + 1) := (two_mul _).symm
      _ ≤ 2 ^ (n + 1) * max C₁ C₂ ^ (n + 1) := by
          gcongr
          exact le_self_pow₀ (by norm_num) (Nat.succ_ne_zero n)
      _ = (2 * max C₁ C₂) ^ (n + 1) := (mul_pow _ _ _).symm
  · refine ⟨Nat.mul_le_mul (hd₁ n).1 (hd₂ n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, mul_pow]
      exact mul_le_mul (hd₁ n).2.1 (hd₂ n).2.1 (Nat.cast_nonneg _) (by positivity)
    · simp only [Pi.add_apply, Nat.cast_mul, mul_add]
      have h1 : ((d₁ n : ℂ) * d₂ n) * a m = (d₂ n : ℂ) * ((d₁ n : ℂ) * a m) := by ring
      have h2 : ((d₁ n : ℂ) * d₂ n) * b m = (d₁ n : ℂ) * ((d₂ n : ℂ) * b m) := by ring
      rw [h1, h2]
      exact ((isIntegral_natCast (d₂ n)).mul ((hd₁ n).2.2 m hm)).add
        ((isIntegral_natCast (d₁ n)).mul ((hd₂ n).2.2 m hm))

/-- E-functions are closed under addition. -/
theorem IsEFunction.add {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction (a + b) :=
  isGFunction_iff_isEFunction.mp
    ((isGFunction_iff_isEFunction.mpr ha).add (isGFunction_iff_isEFunction.mpr hb))

/-- G-functions are closed under finite sums. -/
theorem IsGFunction.sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℂ}
    (hf : ∀ i ∈ s, IsGFunction (f i)) : IsGFunction (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using IsGFunction.zero
  | cons i s _ ih =>
    rw [Finset.sum_cons]
    exact (hf i (mem_cons_self i s)).add (ih fun j hj ↦ hf j (mem_cons_of_mem hj))

/-- E-functions are closed under finite sums. -/
theorem IsEFunction.sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℂ}
    (hf : ∀ i ∈ s, IsEFunction (f i)) : IsEFunction (∑ i ∈ s, f i) :=
  isGFunction_iff_isEFunction.mp
    (IsGFunction.sum s fun i hi ↦ isGFunction_iff_isEFunction.mpr (hf i hi))

/-- Every finitely supported sequence of `ℚ`-algebraic numbers is a G-function. -/
theorem IsGFunction.of_eventually_eq_zero {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    {N : ℕ} (hN : ∀ n ≥ N, a n = 0) : IsGFunction a := by
  have ha : a = ∑ k ∈ range N, Pi.single k (a k) := by
    ext n
    rw [Finset.sum_apply]
    by_cases hn : n < N
    · rw [Finset.sum_eq_single n]
      · simp
      · intro k _ hkn
        exact Pi.single_eq_of_ne (Ne.symm hkn) _
      · intro hn'
        exact absurd (mem_range.mpr hn) hn'
    · rw [hN n (Nat.le_of_not_lt hn), Finset.sum_eq_zero]
      intro k hk
      have hlt : k < N := mem_range.mp hk
      exact Pi.single_eq_of_ne (by omega) _
  rw [ha]
  exact IsGFunction.sum (range N) fun k _ ↦ IsGFunction.single k (halg k)

/-- Every finitely supported sequence of `ℚ`-algebraic numbers is an E-function. -/
theorem IsEFunction.of_eventually_eq_zero {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    {N : ℕ} (hN : ∀ n ≥ N, a n = 0) : IsEFunction a :=
  isGFunction_iff_isEFunction.mp (.of_eventually_eq_zero halg hN)

/-- The coefficient sequence `P.coeff` of a polynomial `P ∈ ℂ[X]` with `ℚ`-algebraic coefficients
is a G-function. -/
theorem IsGFunction.coeff_polynomial {P : ℂ[X]} (hP : ∀ n, IsAlgebraic ℚ (P.coeff n)) :
    IsGFunction (fun n ↦ P.coeff n) :=
  .of_eventually_eq_zero hP fun _ hn ↦
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hn)

/-- For a polynomial `P ∈ ℂ[X]` with `ℚ`-algebraic coefficients, `fun n ↦ P.coeff n * n!` is an
E-function (whose analytic sum `eFun` equals `z ↦ P.eval z`). -/
theorem IsEFunction.mul_factorial_coeff_polynomial {P : ℂ[X]}
    (hP : ∀ n, IsAlgebraic ℚ (P.coeff n)) :
    IsEFunction fun n ↦ P.coeff n * n.factorial :=
  .of_eventually_eq_zero
    (fun n ↦ ((hP n).isIntegral.mul (isAlgebraic_natCast n.factorial).isIntegral).isAlgebraic)
    fun n (hn : P.natDegree + 1 ≤ n) ↦ by
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hn)]

/-- G-functions are closed under negation. -/
theorem IsGFunction.neg {a : ℕ → ℂ} (ha : IsGFunction a) : IsGFunction (-a) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine IsGFunction.of_house_le
    (fun n ↦ (ha.isAlgebraic n).isIntegral.neg.isAlgebraic)
    (by
      have hmk : PowerSeries.mk (-a) = -PowerSeries.mk a := by ext; simp
      rw [hmk]
      exact ha.isDFinite.neg)
    ⟨C, hC, fun n ↦ by simpa only [Pi.neg_apply, house_neg] using hh n⟩
    ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
  simpa only [Pi.neg_apply, mul_neg] using ((hd n).2.2 m hm).neg

/-- E-functions are closed under negation. -/
theorem IsEFunction.neg {a : ℕ → ℂ} (ha : IsEFunction a) : IsEFunction (-a) :=
  isGFunction_iff_isEFunction.mp (isGFunction_iff_isEFunction.mpr ha).neg

/-- G-functions are closed under subtraction. -/
theorem IsGFunction.sub {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- E-functions are closed under subtraction. -/
theorem IsEFunction.sub {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- Multiplying every coefficient of a G-function by an algebraic scalar `c` gives a G-function. -/
theorem IsGFunction.smul {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction (c • a) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  obtain ⟨hb1, hbc⟩ := one_le_and_isIntegral_natDenominator hc
  set b := Algebra.natDenominator c
  refine IsGFunction.of_house_le
    (fun n ↦ (hc.isIntegral.mul (ha.isAlgebraic n).isIntegral).isAlgebraic)
    (by
      have hmk : PowerSeries.mk (c • a) = ((Polynomial.C c : ℂ[X]) : ℂ⟦X⟧) * PowerSeries.mk a := by
        ext n
        simp
      rw [hmk]
      exact (PowerSeries.isDFinite_polynomial (algebraicClosure ℚ ℂ) _).mul ha.isDFinite)
    ⟨max 1 (house c) * C, by positivity, fun n ↦ ?_⟩
    ⟨b * D, by positivity, fun n ↦ b * d n, fun n ↦ ?_⟩
  · calc house (c * a n) ≤ house c * house (a n) := house_mul_le hc (ha.isAlgebraic n)
      _ ≤ max 1 (house c) ^ (n + 1) * C ^ (n + 1) :=
          mul_le_mul
            ((le_max_right 1 (house c)).trans
              (le_self_pow₀ (le_max_left 1 (house c)) (Nat.succ_ne_zero n)))
            (hh n) (house_nonneg _) (by positivity)
      _ = (max 1 (house c) * C) ^ (n + 1) := (mul_pow _ _ _).symm
  · refine ⟨Nat.mul_le_mul hb1 (hd n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, mul_pow]
      exact mul_le_mul (le_self_pow₀ (by exact_mod_cast hb1) (Nat.succ_ne_zero n))
        (hd n).2.1 (Nat.cast_nonneg _) (by positivity)
    · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      have hmul : ((b : ℂ) * d n) * (c * a m) = ((b : ℂ) * c) * ((d n : ℂ) * a m) := by ring
      rw [hmul]
      exact hbc.mul ((hd n).2.2 m hm)

/-- Multiplying every coefficient of an E-function by an algebraic scalar `c` gives an
E-function. -/
theorem IsEFunction.smul {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction (c • a) :=
  isGFunction_iff_isEFunction.mp ((isGFunction_iff_isEFunction.mpr ha).smul hc)

/-- Constant algebraic data `fun _ ↦ c` define a G-function. -/
theorem IsGFunction.const {c : ℂ} (hc : IsAlgebraic ℚ c) : IsGFunction fun _ ↦ c := by
  simpa only [Pi.smul_def, smul_eq_mul, mul_one] using IsGFunction.one.smul hc

/-- Constant algebraic data `fun _ ↦ c` define an E-function (`c * exp z`). -/
theorem IsEFunction.const {c : ℂ} (hc : IsAlgebraic ℚ c) : IsEFunction fun _ ↦ c :=
  isGFunction_iff_isEFunction.mp (.const hc)

/-- Common house bound on a convolution summand `a k` and `b (n - k)` for `k ≤ n`. -/
private theorem house_mul_conv_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hh₁ : ∀ k, house (a k) ≤ C₁ ^ (k + 1)) (hh₂ : ∀ k, house (b k) ≤ C₂ ^ (k + 1))
    {n k : ℕ} (hkn : k ≤ n) :
    house (a k) * house (b (n - k)) ≤ max 1 (max C₁ C₂) ^ (n + 2) := by
  set C := max 1 (max C₁ C₂)
  have h1 : house (a k) ≤ C ^ (k + 1) :=
    (hh₁ k).trans (pow_le_pow_left₀ hC₁.le ((le_max_left C₁ C₂).trans (le_max_right _ _)) _)
  have h2 : house (b (n - k)) ≤ C ^ (n - k + 1) :=
    (hh₂ (n - k)).trans (pow_le_pow_left₀ hC₂.le ((le_max_right C₁ C₂).trans (le_max_right _ _)) _)
  calc house (a k) * house (b (n - k)) ≤ C ^ (k + 1) * C ^ (n - k + 1) :=
        mul_le_mul h1 h2 (house_nonneg _) (by positivity)
    _ = C ^ (n + 2) := by rw [← pow_add, show (k + 1) + (n - k + 1) = n + 2 by omega]

/-- **Hurwitz product of E-functions.** If `a` and `b` are E-functions, then `hurwitzMul a b` is an
E-function (corresponding to the pointwise product `eFun a * eFun b`). -/
theorem IsEFunction.hurwitzMul {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction (TauCeti.hurwitzMul a b) := by
  obtain ⟨C₁, hC₁, hh₁⟩ := ha.exists_house_le
  obtain ⟨C₂, hC₂, hh₂⟩ := hb.exists_house_le
  obtain ⟨D₁, hD₁, d₁, hd₁⟩ := ha.den_le
  obtain ⟨D₂, hD₂, d₂, hd₂⟩ := hb.den_le
  set C := max 1 (max C₁ C₂)
  have hterm_alg : ∀ n k, IsAlgebraic ℚ ((n.choose k : ℂ) * a k * b (n - k)) := fun n k ↦
    (((isAlgebraic_natCast _).isIntegral.mul (ha.isAlgebraic k).isIntegral).mul
      (hb.isAlgebraic (n - k)).isIntegral).isAlgebraic
  refine IsEFunction.of_house_le
    (fun n ↦ by
      rw [hurwitzMul_apply]
      exact (Subalgebra.sum_mem (integralClosure ℚ ℂ) fun k _ ↦
        (hterm_alg n k).isIntegral).isAlgebraic)
    (by rw [ePowerSeries_hurwitzMul]; exact ha.isDFinite.mul hb.isDFinite)
    ⟨2 * C ^ 2, by positivity, fun n ↦ ?_⟩
    ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun n ↦ d₁ n * d₂ n, fun n ↦ ?_⟩
  · rw [hurwitzMul_apply]
    refine (house_sum_le_sum_house (range (n + 1)) fun k _ ↦ hterm_alg n k).trans ?_
    calc ∑ k ∈ range (n + 1), house ((n.choose k : ℂ) * a k * b (n - k))
        ≤ ∑ k ∈ range (n + 1), (n.choose k : ℝ) * C ^ (n + 2) := by
          refine sum_le_sum fun k hk ↦ ?_
          have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
          rw [mul_assoc]
          refine (house_mul_le (isAlgebraic_natCast _)
            (((ha.isAlgebraic k).isIntegral.mul
              (hb.isAlgebraic (n - k)).isIntegral).isAlgebraic)).trans ?_
          rw [house_natCast]
          gcongr
          exact (house_mul_le (ha.isAlgebraic k) (hb.isAlgebraic (n - k))).trans
            (house_mul_conv_le hC₁ hC₂ hh₁ hh₂ hkn)
      _ = 2 ^ n * C ^ (n + 2) := by
          rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ 2 ^ (n + 1) * (C ^ 2) ^ (n + 1) := by
          rw [← pow_mul]
          exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
            (pow_le_pow_right₀ (le_max_left _ _) (by omega)) (by positivity) (by positivity)
      _ = (2 * C ^ 2) ^ (n + 1) := (mul_pow _ _ _).symm
  · refine ⟨Nat.mul_le_mul (hd₁ n).1 (hd₂ n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, mul_pow]
      exact mul_le_mul (hd₁ n).2.1 (hd₂ n).2.1 (Nat.cast_nonneg _) (by positivity)
    · rw [hurwitzMul_apply, mul_sum]
      refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun k hk ↦ ?_
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hrew : ((d₁ n * d₂ n : ℕ) : ℂ) * ((m.choose k : ℂ) * a k * b (m - k)) =
          (m.choose k : ℂ) * ((d₁ n : ℂ) * a k) * ((d₂ n : ℂ) * b (m - k)) := by
        push_cast; ring
      rw [hrew]
      exact ((isIntegral_natCast (m.choose k)).mul ((hd₁ n).2.2 k (hkm.trans hm))).mul
        ((hd₂ n).2.2 (m - k) ((Nat.sub_le m k).trans hm))

/-- G-functions are closed under Hurwitz convolution. -/
theorem IsGFunction.hurwitzMul {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction (TauCeti.hurwitzMul a b) :=
  isGFunction_iff_isEFunction.mpr
    ((isGFunction_iff_isEFunction.mp ha).hurwitzMul (isGFunction_iff_isEFunction.mp hb))

/-- **Cauchy product of G-functions.** If `a` and `b` are G-functions, then their Cauchy
convolution `n ↦ ∑ k ∈ range (n + 1), a k * b (n - k)` (the coefficient sequence of
`PowerSeries.mk a * PowerSeries.mk b`) is a G-function. -/
theorem IsGFunction.mul {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction fun n ↦ ∑ k ∈ range (n + 1), a k * b (n - k) := by
  obtain ⟨C₁, hC₁, hh₁⟩ := ha.exists_house_le
  obtain ⟨C₂, hC₂, hh₂⟩ := hb.exists_house_le
  obtain ⟨D₁, hD₁, d₁, hd₁⟩ := ha.den_le
  obtain ⟨D₂, hD₂, d₂, hd₂⟩ := hb.den_le
  set C := max 1 (max C₁ C₂)
  have hterm_alg : ∀ n k, IsAlgebraic ℚ (a k * b (n - k)) := fun n k ↦
    ((ha.isAlgebraic k).isIntegral.mul (hb.isAlgebraic (n - k)).isIntegral).isAlgebraic
  refine IsGFunction.of_house_le
    (fun n ↦ (Subalgebra.sum_mem (integralClosure ℚ ℂ) fun k _ ↦
      (hterm_alg n k).isIntegral).isAlgebraic)
    (?_)
    ⟨2 * C ^ 2, by positivity, fun n ↦ ?_⟩
    ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun n ↦ d₁ n * d₂ n, fun n ↦ ?_⟩
  · have hmk : (PowerSeries.mk fun n ↦ ∑ k ∈ range (n + 1), a k * b (n - k)) =
        PowerSeries.mk a * PowerSeries.mk b := by
      ext n
      simp only [coeff_mk, PowerSeries.coeff_mul]
      exact (Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ a i * b j) n).symm
    rw [hmk]
    exact ha.isDFinite.mul hb.isDFinite
  · refine (house_sum_le_sum_house (range (n + 1)) fun k _ ↦ hterm_alg n k).trans ?_
    calc ∑ k ∈ range (n + 1), house (a k * b (n - k))
        ≤ ∑ _ ∈ range (n + 1), C ^ (n + 2) :=
          sum_le_sum fun k hk ↦ (house_mul_le (ha.isAlgebraic k) (hb.isAlgebraic (n - k))).trans
            (house_mul_conv_le hC₁ hC₂ hh₁ hh₂ (Nat.lt_succ_iff.mp (mem_range.mp hk)))
      _ = ((n + 1 : ℕ) : ℝ) * C ^ (n + 2) := by simp
      _ ≤ 2 ^ (n + 1) * (C ^ 2) ^ (n + 1) := by
          rw [← pow_mul]
          refine mul_le_mul ?_ (pow_le_pow_right₀ (le_max_left _ _) (by omega))
            (by positivity) (by positivity)
          exact_mod_cast (Nat.lt_two_pow_self (n := n + 1)).le
      _ = (2 * C ^ 2) ^ (n + 1) := (mul_pow _ _ _).symm
  · refine ⟨Nat.mul_le_mul (hd₁ n).1 (hd₂ n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, mul_pow]
      exact mul_le_mul (hd₁ n).2.1 (hd₂ n).2.1 (Nat.cast_nonneg _) (by positivity)
    · rw [mul_sum]
      refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun k hk ↦ ?_
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have hrew : ((d₁ n * d₂ n : ℕ) : ℂ) * (a k * b (m - k)) =
          ((d₁ n : ℂ) * a k) * ((d₂ n : ℂ) * b (m - k)) := by push_cast; ring
      rw [hrew]
      exact ((hd₁ n).2.2 k (hkm.trans hm)).mul ((hd₂ n).2.2 (m - k) ((Nat.sub_le m k).trans hm))

/-- E-functions are closed under Cauchy convolution. -/
theorem IsEFunction.cauchyMul {a b : ℕ → ℂ} (ha : IsEFunction a) (hb : IsEFunction b) :
    IsEFunction fun n ↦ ∑ k ∈ range (n + 1), a k * b (n - k) :=
  isGFunction_iff_isEFunction.mp
    ((isGFunction_iff_isEFunction.mpr ha).mul (isGFunction_iff_isEFunction.mpr hb))

/-- **Differentiation / index shift of E-functions.** Shifting `a` by `k` steps preserves
`IsEFunction` (and corresponds to the `k`-th derivative `iteratedDeriv k (eFun a)`). -/
theorem IsEFunction.shift {a : ℕ → ℂ} (ha : IsEFunction a) (k : ℕ) :
    IsEFunction fun n ↦ a (n + k) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  refine IsEFunction.of_house_le
    (fun n ↦ ha.isAlgebraic (n + k))
    (by rw [← iterate_derivative_ePowerSeries]; exact ha.isDFinite.iterate_derivative k)
    ⟨max 1 C ^ (k + 1), by positivity, fun n ↦ ?_⟩
    ⟨max 1 D ^ (k + 1), by positivity, fun n ↦ d (n + k), fun n ↦ ?_⟩
  · calc house (a (n + k)) ≤ C ^ (n + k + 1) := hh (n + k)
      _ ≤ max 1 C ^ (n + k + 1) := pow_le_pow_left₀ hC.le (le_max_right _ _) _
      _ ≤ max 1 C ^ ((k + 1) * (n + 1)) :=
          pow_le_pow_right₀ (le_max_left _ _) (by nlinarith)
      _ = (max 1 C ^ (k + 1)) ^ (n + 1) := pow_mul _ _ _
  · refine ⟨(hd (n + k)).1, ?_, fun m hm ↦ (hd (n + k)).2.2 (m + k) (Nat.add_le_add_right hm k)⟩
    calc (d (n + k) : ℝ) ≤ D ^ (n + k + 1) := (hd (n + k)).2.1
      _ ≤ max 1 D ^ (n + k + 1) := pow_le_pow_left₀ hD.le (le_max_right _ _) _
      _ ≤ max 1 D ^ ((k + 1) * (n + 1)) :=
          pow_le_pow_right₀ (le_max_left _ _) (by nlinarith)
      _ = (max 1 D ^ (k + 1)) ^ (n + 1) := pow_mul _ _ _

/-- Single-step shift `n ↦ a (n + 1)` of an E-function (corresponding to `deriv (eFun a)`). -/
theorem IsEFunction.shift_one {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ a (n + 1) :=
  ha.shift 1

/-- Shifting `a` by `k` steps preserves `IsGFunction`. -/
theorem IsGFunction.shift {a : ℕ → ℂ} (ha : IsGFunction a) (k : ℕ) :
    IsGFunction fun n ↦ a (n + k) :=
  isGFunction_iff_isEFunction.mpr ((isGFunction_iff_isEFunction.mp ha).shift k)

/-- Single-step shift `n ↦ a (n + 1)` of a G-function. -/
theorem IsGFunction.shift_one {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction fun n ↦ a (n + 1) :=
  ha.shift 1

/-- Prepending an algebraic constant `c` at `n = 0` (`n + 1 ↦ a n`) preserves `IsGFunction`,
corresponding to `C c + X * PowerSeries.mk a`. -/
theorem IsGFunction.cons_zero {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction fun n ↦ if n = 0 then c else a (n - 1) := by
  have hdecomp : (fun n ↦ if n = 0 then c else a (n - 1)) =
      Pi.single 0 c +
        fun n ↦ ∑ k ∈ range (n + 1), (Pi.single 1 (1 : ℂ) : ℕ → ℂ) k * a (n - k) := by
    ext (_ | n)
    · simp
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
        Pi.add_apply, Pi.single_eq_of_ne (Nat.succ_ne_zero n), zero_add]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro k _ hk1
        simp [Pi.single_eq_of_ne hk1]
      · intro hmem
        exact absurd (mem_range.mpr (by omega)) hmem
  rw [hdecomp]
  exact (IsGFunction.single 0 hc).add ((IsGFunction.single 1 isAlgebraic_one).mul ha)

/-- **Integration of E-functions.** Prepending an algebraic constant `c` at `n = 0` (`n + 1 ↦ a n`)
preserves `IsEFunction`; its formal series `ePowerSeries` has constant term `c` and derivative
`ePowerSeries a`. -/
theorem IsEFunction.integrate {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ if n = 0 then c else a (n - 1) :=
  isGFunction_iff_isEFunction.mp ((isGFunction_iff_isEFunction.mpr ha).cons_zero hc)

/-- **Algebraic rescaling of G-functions.** Multiplying `a n` by `c ^ n` for `ℚ`-algebraic `c`
(substituting `X ↦ c X`) preserves `IsGFunction`. -/
theorem IsGFunction.rescale {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction fun n ↦ c ^ n * a n := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  obtain ⟨hb1, hbc⟩ := one_le_and_isIntegral_natDenominator hc
  set b := Algebra.natDenominator c
  refine IsGFunction.of_house_le
    (fun n ↦ ((hc.isIntegral.pow n).mul (ha.isAlgebraic n).isIntegral).isAlgebraic)
    (by
      let c₀ : algebraicClosure ℚ ℂ := ⟨c, mem_algebraicClosure_iff.mpr hc⟩
      have hmk : (PowerSeries.mk fun n ↦ c ^ n * a n) =
          PowerSeries.rescale (algebraMap (algebraicClosure ℚ ℂ) ℂ c₀) (PowerSeries.mk a) := by
        ext n
        simp [coeff_rescale, c₀]
      rw [hmk]
      exact ha.isDFinite.rescale c₀)
    ⟨max 1 (house c) * C, by positivity, fun n ↦ ?_⟩
    ⟨b * D, by positivity, fun n ↦ b ^ n * d n, fun n ↦ ?_⟩
  · calc house (c ^ n * a n) ≤ house (c ^ n) * house (a n) :=
          house_mul_le (hc.isIntegral.pow n).isAlgebraic (ha.isAlgebraic n)
      _ = house c ^ n * house (a n) := by rw [house_pow]
      _ ≤ max 1 (house c) ^ (n + 1) * C ^ (n + 1) := by
          refine mul_le_mul ?_ (hh n) (house_nonneg _) (by positivity)
          exact (pow_le_pow_left₀ (house_nonneg c) (le_max_right _ _) n).trans
            (pow_le_pow_right₀ (le_max_left _ _) (Nat.le_succ n))
      _ = (max 1 (house c) * C) ^ (n + 1) := (mul_pow _ _ _).symm
  · refine ⟨Nat.mul_le_mul (Nat.one_le_pow n b hb1) (hd n).1, ?_, fun m hm ↦ ?_⟩
    · rw [Nat.cast_mul, Nat.cast_pow, mul_pow]
      refine mul_le_mul ?_ (hd n).2.1 (by positivity) (by positivity)
      exact pow_le_pow_right₀ (by exact_mod_cast hb1) (Nat.le_succ n)
    · have hrew : ((b ^ n * d n : ℕ) : ℂ) * (c ^ m * a m) =
          (b : ℂ) ^ (n - m) * ((b : ℂ) * c) ^ m * ((d n : ℂ) * a m) := by
        push_cast
        calc (b : ℂ) ^ n * (d n : ℂ) * (c ^ m * a m)
            = (b : ℂ) ^ (n - m + m) * c ^ m * ((d n : ℂ) * a m) := by
              rw [Nat.sub_add_cancel hm]; ring
          _ = (b : ℂ) ^ (n - m) * ((b : ℂ) * c) ^ m * ((d n : ℂ) * a m) := by
              rw [pow_add, mul_pow]; ring
      rw [hrew]
      exact (((isIntegral_natCast b).pow _).mul (hbc.pow m)).mul ((hd n).2.2 m hm)

/-- **Algebraic rescaling of E-functions.** Multiplying `a n` by `c ^ n` for `ℚ`-algebraic `c`
(substituting `z ↦ c z` in `eFun a`) preserves `IsEFunction`. -/
theorem IsEFunction.rescale {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction fun n ↦ c ^ n * a n :=
  isGFunction_iff_isEFunction.mp ((isGFunction_iff_isEFunction.mpr ha).rescale hc)

/-- Every geometric sequence `n ↦ c ^ n` with `ℚ`-algebraic ratio `c` is a G-function. -/
theorem IsGFunction.geom {c : ℂ} (hc : IsAlgebraic ℚ c) : IsGFunction fun n ↦ c ^ n := by
  simpa using IsGFunction.one.rescale hc

/-- Applying any ring endomorphism `σ : ℂ →+* ℂ` (for example `Complex.conjAe.toRingHom`)
coefficientwise preserves `IsGFunction`. -/
theorem IsGFunction.comp_ringHom (σ : ℂ →+* ℂ) {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction (σ ∘ a) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  let σ₀ : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
    { toFun := fun x ↦
        ⟨σ (x : ℂ), mem_algebraicClosure_iff.mpr ((mem_algebraicClosure_iff.mp x.2).algHom
          σ.toRatAlgHom)⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y ↦ Subtype.ext (map_mul σ (x : ℂ) (y : ℂ))
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y ↦ Subtype.ext (map_add σ (x : ℂ) (y : ℂ)) }
  refine IsGFunction.of_house_le
    (fun n ↦ (ha.isAlgebraic n).algHom σ.toRatAlgHom)
    (?_)
    ⟨C, hC, fun n ↦ by simpa only [Function.comp_apply, house_map] using hh n⟩
    ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
  · have hmk : PowerSeries.mk (σ ∘ a) = PowerSeries.map σ (PowerSeries.mk a) := by
      ext n
      simp
    rw [hmk]
    exact ha.isDFinite.map σ₀ σ fun _ ↦ rfl
  · have hmap : (d n : ℂ) * σ (a m) = σ ((d n : ℂ) * a m) := by simp
    rw [Function.comp_apply, hmap]
    exact ((hd n).2.2 m hm).map σ.toIntAlgHom

/-- Applying any ring endomorphism `σ : ℂ →+* ℂ` coefficientwise preserves `IsEFunction`. -/
theorem IsEFunction.comp_ringHom (σ : ℂ →+* ℂ) {a : ℕ → ℂ} (ha : IsEFunction a) :
    IsEFunction (σ ∘ a) :=
  isGFunction_iff_isEFunction.mp ((isGFunction_iff_isEFunction.mpr ha).comp_ringHom σ)

/-- **Galois conjugation of G-functions.** Any Galois automorphism
`τ ∈ Gal(algebraicClosure ℚ ℂ/ℚ)` acts on the coefficients of a G-function `a` and produces
another G-function `f^τ`. -/
theorem IsGFunction.galoisConj (τ : Gal(algebraicClosure ℚ ℂ/ℚ)) {a : ℕ → ℂ}
    (ha : IsGFunction a) :
    IsGFunction fun n ↦
      (τ ⟨a n, mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩ : ℂ) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := ha.den_le
  set a₀ : ℕ → algebraicClosure ℚ ℂ := fun n ↦
    ⟨a n, mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩
  set ι : algebraicClosure ℚ ℂ →+* ℂ := algebraMap (algebraicClosure ℚ ℂ) ℂ
  have hdf₀ : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a₀) := by
    obtain ⟨r, q, hq, hrec⟩ := PowerSeries.isDFinite_iff_pRecursive.mp ha.isDFinite
    refine PowerSeries.isDFinite_iff_pRecursive.mpr ⟨r, q, hq, fun n ↦ ?_⟩
    refine ι.injective ?_
    simpa only [map_sum, map_zero, Algebra.smul_def, Algebra.algebraMap_self, map_mul,
      RingHom.id_apply, coeff_mk, ι, a₀, IntermediateField.algebraMap_apply] using hrec n
  refine IsGFunction.of_house_le
    (fun n ↦ mem_algebraicClosure_iff.mp (τ (a₀ n)).2)
    (?_)
    ⟨C, hC, fun n ↦ ?_⟩
    ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
  · have hmk : (PowerSeries.mk fun n ↦ (τ (a₀ n) : ℂ)) =
        PowerSeries.map (ι.comp τ.toRingHom) (PowerSeries.mk a₀) := by
      ext n
      simp [ι]
    rw [hmk]
    exact hdf₀.map τ.toRingHom (ι.comp τ.toRingHom) fun _ ↦ rfl
  · have hhouse : house (τ (a₀ n) : ℂ) = house (a n) := by
      calc house (ι (τ (a₀ n))) = house (τ.toRingHom (a₀ n)) := house_map ι _
        _ = house (a₀ n) := house_map τ.toRingHom (a₀ n)
        _ = house (ι (a₀ n)) := (house_map ι (a₀ n)).symm
        _ = house (a n) := rfl
    exact hhouse ▸ hh n
  · have hint₀ : IsIntegral ℤ ((d n : algebraicClosure ℚ ℂ) * a₀ m) := by
      rw [← isIntegral_algHom_iff (ι.toIntAlgHom) ι.injective]
      exact (hd n).2.2 m hm
    have hint_τ : IsIntegral ℤ (τ ((d n : algebraicClosure ℚ ℂ) * a₀ m)) :=
      hint₀.map (τ.toAlgHom.restrictScalars ℤ)
    have hint_ℂ := hint_τ.map ι.toIntAlgHom
    simpa only [map_mul, map_natCast, RingHom.toIntAlgHom_apply, ι, a₀,
      IntermediateField.algebraMap_apply] using hint_ℂ

/-- **Galois conjugation of E-functions.** Any `τ ∈ Gal(algebraicClosure ℚ ℂ/ℚ)` acts on the
coefficients of an E-function `a` and produces another E-function `f^τ`. -/
theorem IsEFunction.galoisConj (τ : Gal(algebraicClosure ℚ ℂ/ℚ)) {a : ℕ → ℂ}
    (ha : IsEFunction a) :
    IsEFunction fun n ↦
      (τ ⟨a n, mem_algebraicClosure_iff.mpr (ha.isAlgebraic n)⟩ : ℂ) :=
  isGFunction_iff_isEFunction.mp ((isGFunction_iff_isEFunction.mpr ha).galoisConj τ)

end Closure

/-! ### Positive examples: `z e^z`, `(z - 1) e^z`, and `-log(1 - z)` -/

section PositiveExamples

/-- The sequence `n ↦ (n : ℂ)` is the Hurwitz product of `Pi.single 1 1` and `fun _ ↦ 1`. -/
private theorem hurwitzMul_single_one_const_one :
    TauCeti.hurwitzMul (Pi.single 1 (1 : ℂ)) (fun _ ↦ 1) = fun (n : ℕ) ↦ (n : ℂ) := by
  ext (_ | n)
  · simp
  · rw [hurwitzMul_apply, Finset.sum_eq_single 1]
    · simp
    · intro k _ hk1
      simp [Pi.single_eq_of_ne hk1]
    · intro hmem
      exact absurd (mem_range.mpr (by omega)) hmem

/-- The sequence `n ↦ (n : ℂ)` defines an E-function. -/
theorem isEFunction_natCast : IsEFunction fun (n : ℕ) ↦ (n : ℂ) := by
  rw [← hurwitzMul_single_one_const_one]
  exact (IsEFunction.single 1 isAlgebraic_one).hurwitzMul .one

/-- Analytic evaluation of the E-function `n ↦ (n : ℂ)` gives `z ↦ z * Complex.exp z`. -/
@[simp]
theorem eFun_natCast (z : ℂ) : eFun (fun (n : ℕ) ↦ (n : ℂ)) z = z * Complex.exp z := by
  rw [← hurwitzMul_single_one_const_one,
    eFun_hurwitzMul (IsEFunction.single 1 isAlgebraic_one).isEntire_ePowerSeries
      IsEFunction.one.isEntire_ePowerSeries]
  simp

/-- The sequence `n ↦ (n : ℂ) - 1` defines an E-function. -/
theorem isEFunction_natCast_sub_one : IsEFunction fun (n : ℕ) ↦ (n : ℂ) - 1 :=
  isEFunction_natCast.sub .one

/-- Analytic evaluation of `n ↦ (n : ℂ) - 1` gives `(z - 1) * Complex.exp z`. -/
theorem eFun_natCast_sub_one (z : ℂ) :
    eFun (fun (n : ℕ) ↦ (n : ℂ) - 1) z = (z - 1) * Complex.exp z := by
  have hsub : (fun (n : ℕ) ↦ (n : ℂ) - 1) = (fun (n : ℕ) ↦ (n : ℂ)) + -(fun _ ↦ (1 : ℂ)) := by
    ext n; simp [sub_eq_add_neg]
  have hneg : eFun (-(fun _ : ℕ ↦ (1 : ℂ))) z = -Complex.exp z := by
    have h0 := eFun_add IsEFunction.one.isEntire_ePowerSeries
      IsEFunction.one.neg.isEntire_ePowerSeries z
    rw [add_neg_cancel, eFun_zero, eFun_one_complex] at h0
    exact eq_neg_of_add_eq_zero_right h0.symm
  rw [hsub, eFun_add isEFunction_natCast.isEntire_ePowerSeries
    IsEFunction.one.neg.isEntire_ePowerSeries, eFun_natCast, hneg]
  ring

/-- **The logarithmic series `-log(1 - z) = ∑_{n ≥ 1} zⁿ / n` is a G-function.** Here
`(0 : ℂ)⁻¹ = 0` gives the vanishing constant term, and the common denominators `Nat.lcmUpto n` are
bounded geometrically by `exp(log 4 + 4) ^ (n + 1)` via Chebyshev's `ψ`-estimate. -/
theorem isGFunction_inv_natCast : IsGFunction fun (n : ℕ) ↦ (n : ℂ)⁻¹ := by
  refine IsGFunction.of_house_le
    (fun n ↦ by simpa using isAlgebraic_ratCast ℚ (n : ℚ)⁻¹)
    (?_)
    ⟨1, zero_lt_one, fun n ↦ ?_⟩
    ⟨Real.exp (Real.log 4 + 4), Real.exp_pos _, Nat.lcmUpto, fun n ↦ ?_⟩
  · -- P-recurrence `0 * aₙ + (n + 1) aₙ₊₁ - (n + 2) aₙ₊₂ = 0` for all `n ≥ 0`.
    have hlead : -(Polynomial.X + 2 : (algebraicClosure ℚ ℂ)[X]) ≠ 0 :=
      neg_ne_zero.mpr (monic_X_add_C (2 : algebraicClosure ℚ ℂ)).ne_zero
    refine PowerSeries.isDFinite_iff_pRecursive.mpr
      ⟨2, ![0, Polynomial.X + 1, -(Polynomial.X + 2)], by simpa using hlead, fun n ↦ ?_⟩
    rw [Fin.sum_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Polynomial.eval_zero, Fin.val_one,
      Matrix.cons_val_one, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, coeff_mk,
      Algebra.smul_def, map_zero, zero_mul, zero_add, map_add, map_natCast, map_one, Fin.val_two,
      Matrix.cons_val, Polynomial.eval_neg, Polynomial.eval_ofNat, map_neg, map_ofNat,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    rw [mul_inv_cancel₀ h1, neg_mul, mul_inv_cancel₀ h2, add_neg_cancel]
  · have hq : ((n : ℂ)⁻¹) = (((n : ℚ)⁻¹ : ℚ) : ℂ) := by simp
    rw [hq, house_ratCast, one_pow, Rat.cast_inv, Rat.cast_natCast,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)
  · refine ⟨Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero n), ?_, fun m hm ↦ ?_⟩
    · have hpos : (0 : ℝ) < Nat.lcmUpto n :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero n))
      rw [← Real.exp_log hpos, ← Chebyshev.psi_eq_log_lcmUpto, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr
        ((Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)).trans ?_)
      have h4 : 0 ≤ Real.log 4 + 4 := by positivity
      push_cast
      nlinarith
    · rcases eq_or_ne m 0 with rfl | hm0
      · simp [isIntegral_zero]
      · obtain ⟨k, hk⟩ := Nat.dvd_lcmUpto (Nat.pos_of_ne_zero hm0) hm
        have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
        have heq : (Nat.lcmUpto n : ℂ) * (m : ℂ)⁻¹ = (k : ℂ) := by
          rw [hk, Nat.cast_mul, mul_right_comm, mul_inv_cancel₀ hm_ne, one_mul]
        rw [heq]
        exact isIntegral_natCast k

end PositiveExamples

/-! ### Sharpness counterexamples: `n!`, `e^(z²)`, and `1 / n!` -/

section Counterexamples

/-- No positive constant `C` bounds `(2k)! / k! = (k + 1).ascFactorial k` geometrically as
`C ^ (2k + 1)` for every `k`. -/
private theorem not_forall_ascFactorial_le_pow {C : ℝ} :
    ¬∀ k : ℕ, ((k + 1).ascFactorial k : ℝ) ≤ C ^ (2 * k + 1) := by
  intro h
  set M : ℝ := max 1 C
  have hM1 : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ M := le_max_right _ _
  set k : ℕ := ⌊M ^ 3⌋₊ + 1
  have hk_pos : 0 < k := Nat.succ_pos _
  have hMk : M ^ 3 < (k : ℝ) := by simpa [k] using Nat.lt_floor_add_one (M ^ 3)
  have hpow_lt : C ^ (2 * k + 1) < (k : ℝ) ^ k :=
    calc C ^ (2 * k + 1) ≤ M ^ (2 * k + 1) := (odd_two_mul_add_one k).pow_le_pow.mpr hCM
      _ ≤ M ^ (3 * k) := pow_le_pow_right₀ hM1 (by omega)
      _ = (M ^ 3) ^ k := pow_mul M 3 k
      _ < (k : ℝ) ^ k := pow_lt_pow_left₀ hMk (by positivity) hk_pos.ne'
  have hk_le_asc : k ^ k ≤ (k + 1).ascFactorial k :=
    (Nat.pow_le_pow_left (Nat.le_succ k) k).trans (Nat.pow_succ_le_ascFactorial (k + 1) k)
  have hk_le_real : (k : ℝ) ^ k ≤ ((k + 1).ascFactorial k : ℝ) := by exact_mod_cast hk_le_asc
  exact (hpow_lt.trans_le hk_le_real).not_ge (h k)

/-- No real `C` satisfies `∀ n, (n.factorial : ℝ) ≤ C ^ (n + 1)`. -/
private theorem not_forall_factorial_le_pow {C : ℝ} :
    ¬∀ n : ℕ, (n.factorial : ℝ) ≤ C ^ (n + 1) := by
  intro h
  refine not_forall_ascFactorial_le_pow (C := C) fun k ↦ ?_
  have hle : (k + 1).ascFactorial k ≤ (2 * k).factorial := by
    rw [two_mul, ← Nat.factorial_mul_ascFactorial]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos k)
  exact (Nat.cast_le.mpr hle).trans (h (2 * k))

/-- For `aₙ = n!`, `ePowerSeries a = ∑ Xⁿ` is not entire. -/
theorem not_isEntire_ePowerSeries_factorial :
    ¬(ePowerSeries fun n ↦ (n.factorial : ℂ)).IsEntire := by
  intro hent
  have hsum := summable_eFun hent 1
  have hconst : (fun n : ℕ ↦ (n.factorial : ℂ) * (1 : ℂ) ^ n / n.factorial) = fun _ ↦ (1 : ℂ) := by
    ext n
    have hne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simp [div_self hne]
  rw [hconst] at hsum
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hsum.tendsto_atTop_zero)

/-- The factorial sequence `n ↦ (n! : ℂ)` is **not** an E-function. -/
theorem not_isEFunction_factorial : ¬IsEFunction fun n ↦ (n.factorial : ℂ) :=
  fun ha ↦ not_isEntire_ePowerSeries_factorial ha.isEntire_ePowerSeries

/-- The exponential Taylor coefficient sequence of `e^(z²) = ∑_{k ≥ 0} ((2k)! / k!) z^{2k} / (2k)!`:
`expSqCoeff (2k) = (2k)! / k!` and `expSqCoeff (2k + 1) = 0`. -/
def expSqCoeff (n : ℕ) : ℂ :=
  if Even n then (((n.factorial / (n / 2).factorial : ℕ)) : ℂ) else 0

/-- At `2k`, `expSqCoeff (2k) = (k + 1).ascFactorial k = (2k)! / k!`. -/
@[simp]
theorem expSqCoeff_two_mul (k : ℕ) :
    expSqCoeff (2 * k) = ((k + 1).ascFactorial k : ℂ) := by
  have heven : Even (2 * k) := even_two_mul k
  have hdiv : (2 * k).factorial / k.factorial = (k + 1).ascFactorial k := by
    rw [two_mul, ← Nat.factorial_mul_ascFactorial, Nat.mul_div_right _ (Nat.factorial_pos k)]
  simp [expSqCoeff, heven, hdiv]

/-- At odd indices `2k + 1`, `expSqCoeff (2k + 1) = 0`. -/
@[simp]
theorem expSqCoeff_two_mul_add_one (k : ℕ) : expSqCoeff (2 * k + 1) = 0 := by
  simp [expSqCoeff]

/-- `eFun expSqCoeff z = Complex.exp (z ^ 2)` for every `z : ℂ`. -/
theorem eFun_exp_sq (z : ℂ) : eFun expSqCoeff z = Complex.exp (z ^ 2) := by
  have hterm_even : ∀ k : ℕ,
      expSqCoeff (2 * k) * z ^ (2 * k) / (2 * k).factorial = (z ^ 2) ^ k / k.factorial := by
    intro k
    rw [expSqCoeff_two_mul, pow_mul]
    have hfact : ((2 * k).factorial : ℂ) =
        (k.factorial : ℂ) * ((k + 1).ascFactorial k : ℂ) := by
      exact_mod_cast (two_mul k ▸ (Nat.factorial_mul_ascFactorial k k).symm)
    have hasc_ne : (((k + 1).ascFactorial k : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos k k).ne'
    have hk_ne : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    rw [hfact]
    field_simp
  have hsum_sq : HasSum (fun k : ℕ ↦ (z ^ 2) ^ k / k.factorial) (Complex.exp (z ^ 2)) := by
    simpa only [one_mul, eFun_one_complex] using IsEFunction.one.hasSum_eFun (z ^ 2)
  have heven : Summable fun k : ℕ ↦ expSqCoeff (2 * k) * z ^ (2 * k) / (2 * k).factorial := by
    simpa only [hterm_even] using hsum_sq.summable
  have hodd : Summable fun k : ℕ ↦
      expSqCoeff (2 * k + 1) * z ^ (2 * k + 1) / (2 * k + 1).factorial := by
    simp
  rw [eFun_def, ← tsum_even_add_odd heven hodd]
  simp only [hterm_even, expSqCoeff_two_mul_add_one, zero_mul, zero_div, tsum_zero, add_zero,
    hsum_sq.tsum_eq]

/-- **`e^(z²)` is not an E-function.** Although `eFun expSqCoeff = fun z ↦ exp (z²)` is entire and
satisfies the linear differential equation `f' - 2 z f = 0` with rational integer coefficients
`expSqCoeff n`, its even coefficients `(2k)! / k! = (k + 1).ascFactorial k ≥ k ^ k` violate the
geometric conjugate bound. -/
theorem not_isEFunction_exp_sq : ¬IsEFunction expSqCoeff := by
  intro ha
  obtain ⟨C, _, hnorm⟩ := ha.exists_norm_le
  refine not_forall_ascFactorial_le_pow (C := C) fun k ↦ ?_
  simpa only [expSqCoeff_two_mul, Complex.norm_natCast] using hnorm (2 * k)

/-- **`∑ zⁿ / n! = e^z` is not a G-function.** Although `aₙ = (n!)⁻¹` is rational, bounded by `1`,
and D-finite, any common denominator `dₙ` clearing `aₙ` into an algebraic integer must be divisible
by `n!`, violating the geometric denominator bound. -/
theorem not_isGFunction_inv_factorial : ¬IsGFunction fun n ↦ (n.factorial : ℂ)⁻¹ := by
  intro ha
  obtain ⟨D, _, d, hd⟩ := ha.den_le
  refine not_forall_factorial_le_pow (C := D) fun n ↦ ?_
  have hfact_pos : 0 < n.factorial := Nat.factorial_pos n
  have hz_ne : ((n.factorial : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr hfact_pos.ne')
  have hq : ((n.factorial : ℂ)⁻¹) = algebraMap ℚ ℂ ((n.factorial : ℚ)⁻¹) := by simp
  have hdeg : (minpoly ℚ ((n.factorial : ℂ)⁻¹)).natDegree = 1 := by
    rw [hq, minpoly.eq_X_sub_C, Polynomial.natDegree_X_sub_C]
  have hevertse := one_le_natDenominator_pow_mul_house_pow_mul_norm (ha.isAlgebraic n) hz_ne
  rw [hdeg, pow_one, Nat.sub_self, pow_zero, mul_one, norm_inv, Complex.norm_natCast] at hevertse
  have hfact_le_den : (n.factorial : ℝ) ≤ Algebra.natDenominator ((n.factorial : ℂ)⁻¹) := by
    have hmul := mul_le_mul_of_nonneg_right hevertse (Nat.cast_nonneg n.factorial)
    rwa [one_mul, inv_mul_cancel_right₀ (Nat.cast_ne_zero.mpr hfact_pos.ne')] at hmul
  have hdvd : Algebra.natDenominator ((n.factorial : ℂ)⁻¹) ∣ d n := by
    rw [Algebra.natDenominator_dvd_iff, nsmul_eq_mul]
    exact (hd n).2.2 n le_rfl
  have hden_le_d : Algebra.natDenominator ((n.factorial : ℂ)⁻¹) ≤ d n :=
    Nat.le_of_dvd (hd n).1 hdvd
  exact (hfact_le_den.trans (Nat.cast_le.mpr hden_le_d)).trans (hd n).2.1

end Counterexamples

end TauCeti
