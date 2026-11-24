/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Data.Nat.Choose.Sum

/-!
# Hurwitz convolution and factorial-divided formal power series

To a coefficient sequence `a : ℕ → K` in a semifield one attaches the factorial-divided formal
power series

  `TauCeti.ePowerSeries a = ∑ (aₙ / n!) Xⁿ`,

which is the formal Borel transform of the ordinary generating series `PowerSeries.mk a = ∑ aₙ Xⁿ`.
Under this normalization, termwise differentiation shifts the sequence
(`d⁄dX (ePowerSeries a) = ePowerSeries fun n ↦ a (n + 1)`), the constant-one sequence gives
`PowerSeries.exp K`, and the Cauchy product of two factorial-divided series corresponds to the
*Hurwitz* (or binomial) convolution

  `TauCeti.hurwitzMul a b n = ∑ k ≤ n, n.choose k • (a k * b (n - k))`

of their coefficient sequences (`TauCeti.ePowerSeries_hurwitzMul`).

In transcendence theory and the arithmetic of linear differential equations, this normalization
underlies Siegel's E-functions `∑ aₙ zⁿ / n!`: separating the factorial denominator from `aₙ` puts
the arithmetic size and denominator conditions on `aₙ` on the same geometric scale as for Siegel's
G-functions `∑ aₙ zⁿ`, while turning analytic multiplication and differentiation of entire
E-series into Hurwitz convolution and shifts of their coefficient sequences.

## Main definitions

* `TauCeti.hurwitzMul a b`: the binomial convolution `n ↦ ∑ k ≤ n, n.choose k • (a k * b (n - k))`.
* `TauCeti.ePowerSeries a`: the factorial-divided formal power series `∑ (aₙ / n!) Xⁿ`.

## Main results

* `TauCeti.hurwitzMul_zero`, `TauCeti.hurwitzMul_succ`, `TauCeti.hurwitzMul_comm`,
  `TauCeti.hurwitzMul_assoc`, `TauCeti.hurwitzMul_single_single`,
  `TauCeti.hurwitzMul_single_zero_one_left`, `TauCeti.hurwitzMul_single_zero_one_right`,
  `TauCeti.hurwitzMul_const_one`, `TauCeti.map_hurwitzMul`, `TauCeti.comp_hurwitzMul`: algebraic
  laws, evaluations, and ring-homomorphism compatibility of Hurwitz convolution.
* `TauCeti.ePowerSeries_hurwitzMul`, `TauCeti.derivative_ePowerSeries`,
  `TauCeti.iterate_derivative_ePowerSeries`, `TauCeti.rescale_ePowerSeries`,
  `TauCeti.map_ePowerSeries`, `TauCeti.ePowerSeries_const_one`: compatibility of `ePowerSeries`
  with Hurwitz multiplication, differentiation, rescaling, coefficient maps, and the formal
  exponential.

## References

* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1–3.2,
  §4.1.
* S. Fischler and T. Rivoal, *On Siegel's problem for E-functions*, Math. Z. **301** (2022),
  1429–1453 (arXiv:1910.06817), Definition 1.
-/

public section

open scoped PowerSeries

namespace TauCeti

/-! ### Hurwitz (binomial) convolution -/

section HurwitzMul

/-- The *Hurwitz* (or binomial) convolution of two sequences `a, b : ℕ → R`:
`hurwitzMul a b n = ∑ k ∈ Finset.range (n + 1), n.choose k • (a k * b (n - k))`. -/
def hurwitzMul {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), n.choose k • (a k * b (n - k))

/-- Unfolding `hurwitzMul` as a finite sum over `Finset.range (n + 1)`. -/
theorem hurwitzMul_def {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n = ∑ k ∈ Finset.range (n + 1), n.choose k • (a k * b (n - k)) :=
  (rfl)

/-- At `n = 0`, `hurwitzMul a b 0 = a 0 * b 0`. -/
@[simp]
theorem hurwitzMul_zero {R : Type*} [Semiring R] (a b : ℕ → R) :
    hurwitzMul a b 0 = a 0 * b 0 := by
  simp [hurwitzMul_def]

/-- `hurwitzMul` written over `Finset.antidiagonal n`. -/
theorem hurwitzMul_eq_sum_antidiagonal {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n = ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 • (a ij.1 * b ij.2) :=
  (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ n.choose i • (a i * b j)) n).symm

/-- `hurwitzMul` written with natural-number casts `(n.choose k : R)`. -/
theorem hurwitzMul_eq_sum_cast {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * a k * b (n - k) := by
  rw [hurwitzMul_def]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [nsmul_eq_mul, mul_assoc]

/-- Applying a ring homomorphism commutes with `hurwitzMul` at each index. -/
theorem map_hurwitzMul {F R S : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] (σ : F) (a b : ℕ → R) (n : ℕ) :
    σ (hurwitzMul a b n) = hurwitzMul (σ ∘ a) (σ ∘ b) n := by
  simp [hurwitzMul_def]

/-- Post-composing with a ring homomorphism commutes with `hurwitzMul`. -/
theorem comp_hurwitzMul {F R S : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] (σ : F) (a b : ℕ → R) :
    σ ∘ hurwitzMul a b = hurwitzMul (σ ∘ a) (σ ∘ b) :=
  funext (map_hurwitzMul σ a b)

/-- Left multiplication by the zero sequence gives the zero sequence. -/
@[simp]
theorem hurwitzMul_zero_left {R : Type*} [Semiring R] (b : ℕ → R) :
    hurwitzMul 0 b = 0 := by
  ext n
  simp [hurwitzMul_def]

/-- Right multiplication by the zero sequence gives the zero sequence. -/
@[simp]
theorem hurwitzMul_zero_right {R : Type*} [Semiring R] (a : ℕ → R) :
    hurwitzMul a 0 = 0 := by
  ext n
  simp [hurwitzMul_def]

/-- `hurwitzMul` distributes over addition on the left. -/
theorem hurwitzMul_add_left {R : Type*} [Semiring R] (a₁ a₂ b : ℕ → R) :
    hurwitzMul (a₁ + a₂) b = hurwitzMul a₁ b + hurwitzMul a₂ b := by
  ext n
  simp [hurwitzMul_def, add_mul, smul_add, Finset.sum_add_distrib]

/-- `hurwitzMul` distributes over addition on the right. -/
theorem hurwitzMul_add_right {R : Type*} [Semiring R] (a b₁ b₂ : ℕ → R) :
    hurwitzMul a (b₁ + b₂) = hurwitzMul a b₁ + hurwitzMul a b₂ := by
  ext n
  simp [hurwitzMul_def, mul_add, smul_add, Finset.sum_add_distrib]

/-- `hurwitzMul` commutes with negation on the left. -/
@[simp]
theorem hurwitzMul_neg_left {R : Type*} [Ring R] (a b : ℕ → R) :
    hurwitzMul (-a) b = -hurwitzMul a b := by
  ext n
  simp [hurwitzMul_def]

/-- `hurwitzMul` commutes with negation on the right. -/
@[simp]
theorem hurwitzMul_neg_right {R : Type*} [Ring R] (a b : ℕ → R) :
    hurwitzMul a (-b) = -hurwitzMul a b := by
  ext n
  simp [hurwitzMul_def]

/-- `hurwitzMul` distributes over subtraction on the left. -/
theorem hurwitzMul_sub_left {R : Type*} [Ring R] (a₁ a₂ b : ℕ → R) :
    hurwitzMul (a₁ - a₂) b = hurwitzMul a₁ b - hurwitzMul a₂ b := by
  simp [sub_eq_add_neg, hurwitzMul_add_left]

/-- `hurwitzMul` distributes over subtraction on the right. -/
theorem hurwitzMul_sub_right {R : Type*} [Ring R] (a b₁ b₂ : ℕ → R) :
    hurwitzMul a (b₁ - b₂) = hurwitzMul a b₁ - hurwitzMul a b₂ := by
  simp [sub_eq_add_neg, hurwitzMul_add_right]

/-- `hurwitzMul` commutes with scalar multiplication in its left argument under
`[IsScalarTower S R R]`. -/
@[simp]
theorem hurwitzMul_smul_left {S R : Type*} [Semiring S] [Semiring R] [Module S R]
    [IsScalarTower S R R] (c : S) (a b : ℕ → R) :
    hurwitzMul (c • a) b = c • hurwitzMul a b := by
  ext n
  rw [hurwitzMul_def, Pi.smul_apply, hurwitzMul_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Pi.smul_apply, smul_mul_assoc, smul_comm (n.choose k) c]

/-- `hurwitzMul` commutes with scalar multiplication in its right argument under
`[SMulCommClass S R R]`. -/
@[simp]
theorem hurwitzMul_smul_right {S R : Type*} [Semiring S] [Semiring R] [Module S R]
    [SMulCommClass S R R] (c : S) (a b : ℕ → R) :
    hurwitzMul a (c • b) = c • hurwitzMul a b := by
  ext n
  rw [hurwitzMul_def, Pi.smul_apply, hurwitzMul_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Pi.smul_apply, mul_smul_comm, smul_comm (n.choose k) c]

/-- Over a commutative semiring, `hurwitzMul` is commutative. -/
theorem hurwitzMul_comm {R : Type*} [CommSemiring R] (a b : ℕ → R) :
    hurwitzMul a b = hurwitzMul b a := by
  ext n
  rw [hurwitzMul_eq_sum_antidiagonal, hurwitzMul_eq_sum_antidiagonal]
  refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun ij ↦ by simp [add_comm]) fun ij hij ↦ ?_
  have hsum := Finset.mem_antidiagonal.mp hij
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm, ← hsum, Nat.choose_symm_add]

/-- `hurwitzMul` is associative. -/
theorem hurwitzMul_assoc {R : Type*} [Semiring R] (a b c : ℕ → R) :
    hurwitzMul (hurwitzMul a b) c = hurwitzMul a (hurwitzMul b c) := by
  ext n
  simp only [hurwitzMul_def, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  calc ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
        n.choose k • ((k.choose i • (a i * b (k - i))) * c (n - k))
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
          (n.choose i * (n - i).choose j) • (a i * (b j * c (n - i - j))) := by
        rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_bij (fun ⟨k, i⟩ _ ↦ ⟨i, k - i⟩) (fun ⟨k, i⟩ hki ↦ ?_)
          (fun ⟨k₁, i₁⟩ h₁ ⟨k₂, i₂⟩ h₂ heq ↦ ?_) (fun ⟨i, j⟩ hij ↦ ?_) (fun ⟨k, i⟩ hki ↦ ?_)
        · dsimp only
          simp only [Finset.mem_sigma, Finset.mem_range] at hki ⊢
          omega
        · dsimp only at heq ⊢
          simp only [Finset.mem_sigma, Finset.mem_range] at h₁ h₂
          have hi : i₁ = i₂ := congrArg Sigma.fst heq
          have hj : k₁ - i₁ = k₂ - i₂ := congrArg Sigma.snd heq
          have hk : k₁ = k₂ := by omega
          subst hk hi
          rfl
        · simp only [Finset.mem_sigma, Finset.mem_range] at hij
          refine ⟨⟨i + j, i⟩, ?_, Sigma.ext rfl (heq_of_eq (Nat.add_sub_cancel_left i j))⟩
          simp only [Finset.mem_sigma, Finset.mem_range]
          omega
        · dsimp only
          simp only [Finset.mem_sigma, Finset.mem_range] at hki
          have hik : i ≤ k := by omega
          have hsub : n - i - (k - i) = n - k := by omega
          rw [smul_mul_assoc, smul_smul, Nat.choose_mul hik, mul_assoc, hsub]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
          n.choose i • (a i * ((n - i).choose j • (b j * c (n - i - j)))) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [mul_smul, ← mul_smul_comm]

/-- Left Hurwitz multiplication by a sequence supported at `i`. -/
theorem hurwitzMul_single_left {R : Type*} [Semiring R] [DecidableEq ℕ]
    (i : ℕ) (x : R) (b : ℕ → R) (n : ℕ) :
    hurwitzMul (Pi.single i x) b n = if i ≤ n then n.choose i • (x * b (n - i)) else 0 := by
  rw [hurwitzMul_def]
  split_ifs with hin
  · rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · intro hi
      exact absurd (Finset.mem_range.mpr (by omega)) hi
  · refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hki : k ≠ i := by
      rw [Finset.mem_range] at hk
      omega
    simp [Pi.single_eq_of_ne hki]

/-- Right Hurwitz multiplication by a sequence supported at `j`. -/
theorem hurwitzMul_single_right {R : Type*} [Semiring R] [DecidableEq ℕ]
    (a : ℕ → R) (j : ℕ) (y : R) (n : ℕ) :
    hurwitzMul a (Pi.single j y) n = if j ≤ n then n.choose j • (a (n - j) * y) else 0 := by
  rw [hurwitzMul_def]
  split_ifs with hjn
  · rw [Finset.sum_eq_single (n - j)]
    · rw [Nat.sub_sub_self hjn, Pi.single_eq_same, Nat.choose_symm hjn]
    · intro k hk hkne
      have hsub : n - k ≠ j := by
        rw [Finset.mem_range] at hk
        omega
      simp [Pi.single_eq_of_ne hsub]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hsub : n - k ≠ j := by
      rw [Finset.mem_range] at hk
      omega
    simp [Pi.single_eq_of_ne hsub]

/-- Hurwitz product of two single-term sequences `Pi.single i x` and `Pi.single j y`. -/
@[simp]
theorem hurwitzMul_single_single {R : Type*} [Semiring R] [DecidableEq ℕ]
    (i j : ℕ) (x y : R) :
    hurwitzMul (Pi.single i x) (Pi.single j y) =
      Pi.single (i + j) ((i + j).choose i • (x * y)) := by
  ext n
  rw [hurwitzMul_single_left]
  by_cases h : n = i + j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    split_ifs with hin
    · rw [Pi.single_eq_of_ne (by omega), mul_zero, smul_zero]
    · rfl

/-- `Pi.single 0 1` is the left identity for `hurwitzMul`. -/
@[simp]
theorem hurwitzMul_single_zero_one_left {R : Type*} [Semiring R] [DecidableEq ℕ] (b : ℕ → R) :
    hurwitzMul (Pi.single 0 1) b = b := by
  ext n
  simp [hurwitzMul_single_left]

/-- `Pi.single 0 1` is the right identity for `hurwitzMul`. -/
@[simp]
theorem hurwitzMul_single_zero_one_right {R : Type*} [Semiring R] [DecidableEq ℕ] (a : ℕ → R) :
    hurwitzMul a (Pi.single 0 1) = a := by
  ext n
  simp [hurwitzMul_single_right]

/-- Hurwitz product of two constant-one sequences is `2 ^ n`. -/
@[simp]
theorem hurwitzMul_const_one {R : Type*} [Semiring R] (n : ℕ) :
    hurwitzMul (fun _ ↦ (1 : R)) (fun _ ↦ (1 : R)) n = 2 ^ n := by
  rw [hurwitzMul_def]
  simp only [mul_one, nsmul_eq_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow,
    Nat.cast_ofNat]

/-- Leibniz rule for Hurwitz convolution under the forward shift `n ↦ n + 1`. -/
theorem hurwitzMul_succ {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) :
    hurwitzMul a b (n + 1) =
      hurwitzMul (fun k ↦ a (k + 1)) b n + hurwitzMul a (fun k ↦ b (k + 1)) n := by
  rw [hurwitzMul_def, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.sub_zero, one_smul, Nat.choose_succ_succ, add_smul,
    Finset.sum_add_distrib, Nat.succ_sub_succ_eq_sub, Nat.succ_eq_add_one]
  have h1 : ∑ k ∈ Finset.range (n + 1), n.choose k • (a (k + 1) * b (n - k)) =
      hurwitzMul (fun k ↦ a (k + 1)) b n := rfl
  have h2 : (∑ k ∈ Finset.range (n + 1), n.choose (k + 1) • (a (k + 1) * b (n - k))) +
        a 0 * b (n + 1) = hurwitzMul a (fun k ↦ b (k + 1)) n := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero, hurwitzMul_def,
      Finset.sum_range_succ', Nat.choose_zero_right, Nat.sub_zero, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k < n := Finset.mem_range.mp hk
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [hsub]
  rw [add_assoc, h1, h2]

end HurwitzMul

/-! ### Factorial-divided formal power series -/

section EPowerSeries

/-- The factorial-divided formal power series `∑ (aₙ / n!) Xⁿ` attached to a sequence
`a : ℕ → K`. -/
def ePowerSeries {K : Type*} [Semifield K] (a : ℕ → K) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ a n / n.factorial

/-- Unfolding `ePowerSeries` as `PowerSeries.mk fun n ↦ a n / n.factorial`. -/
theorem ePowerSeries_def {K : Type*} [Semifield K] (a : ℕ → K) :
    ePowerSeries a = PowerSeries.mk fun n ↦ a n / n.factorial :=
  (rfl)

/-- The `n`-th coefficient of `ePowerSeries a` is `a n / n!`. -/
@[simp]
theorem coeff_ePowerSeries {K : Type*} [Semifield K] (a : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (ePowerSeries a) = a n / n.factorial :=
  PowerSeries.coeff_mk n _

/-- The constant term of `ePowerSeries a` is `a 0`. -/
@[simp]
theorem constantCoeff_ePowerSeries {K : Type*} [Semifield K] (a : ℕ → K) :
    PowerSeries.constantCoeff (ePowerSeries a) = a 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_ePowerSeries, Nat.factorial_zero,
    Nat.cast_one, div_one]

/-- In characteristic zero, `ePowerSeries` is injective. -/
theorem ePowerSeries_injective {K : Type*} [Semifield K] [CharZero K] :
    Function.Injective (ePowerSeries (K := K)) := by
  intro a b hab
  ext n
  have hn := congrArg (PowerSeries.coeff n) hab
  simp only [coeff_ePowerSeries] at hn
  have hfac : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact (div_left_inj₀ hfac).mp hn

/-- Two factorial-divided series in characteristic zero are equal iff their sequences are equal. -/
@[simp]
theorem ePowerSeries_inj {K : Type*} [Semifield K] [CharZero K] {a b : ℕ → K} :
    ePowerSeries a = ePowerSeries b ↔ a = b :=
  ePowerSeries_injective.eq_iff

/-- The zero sequence gives the zero power series. -/
@[simp]
theorem ePowerSeries_zero {K : Type*} [Semifield K] :
    ePowerSeries (0 : ℕ → K) = 0 := by
  ext n
  simp

/-- `ePowerSeries` preserves addition. -/
@[simp]
theorem ePowerSeries_add {K : Type*} [Semifield K] (a b : ℕ → K) :
    ePowerSeries (a + b) = ePowerSeries a + ePowerSeries b := by
  ext n
  simp [add_div]

/-- `ePowerSeries` preserves negation. -/
@[simp]
theorem ePowerSeries_neg {K : Type*} [Field K] (a : ℕ → K) :
    ePowerSeries (-a) = -ePowerSeries a := by
  ext n
  simp [neg_div]

/-- `ePowerSeries` preserves subtraction. -/
@[simp]
theorem ePowerSeries_sub {K : Type*} [Field K] (a b : ℕ → K) :
    ePowerSeries (a - b) = ePowerSeries a - ePowerSeries b := by
  ext n
  simp [sub_div]

/-- `ePowerSeries` commutes with scalar multiplication. -/
@[simp]
theorem ePowerSeries_smul {S K : Type*} [Semiring S] [Semifield K] [Module S K]
    [IsScalarTower S K K] (c : S) (a : ℕ → K) :
    ePowerSeries (c • a) = c • ePowerSeries a := by
  ext n
  simp [div_eq_mul_inv, smul_mul_assoc]

/-- `ePowerSeries` on a sequence supported at `n` gives `(c / n!) • X ^ n`. -/
theorem ePowerSeries_single {K : Type*} [Semifield K] [DecidableEq ℕ] (n : ℕ) (c : K) :
    ePowerSeries (Pi.single n c) = (c / n.factorial) • PowerSeries.X ^ n := by
  ext m
  rw [coeff_ePowerSeries, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
  by_cases hmn : m = n
  · subst hmn
    simp
  · simp [hmn]

/-- `ePowerSeries` on `Pi.single 0 c` is the constant power series `C c`. -/
@[simp]
theorem ePowerSeries_single_zero {K : Type*} [Semifield K] [DecidableEq ℕ] (c : K) :
    ePowerSeries (Pi.single 0 c) = PowerSeries.C c := by
  ext m
  cases m <;> simp [PowerSeries.coeff_C]

/-- The constant-one sequence maps to the formal exponential series `PowerSeries.exp K`. -/
@[simp]
theorem ePowerSeries_const_one {K : Type*} [Field K] [CharZero K] :
    ePowerSeries (fun _ ↦ (1 : K)) = PowerSeries.exp K := by
  ext n
  simp

/-- **Product of factorial-divided series.** The Cauchy product of `ePowerSeries a` and
`ePowerSeries b` is the factorial-divided series of `hurwitzMul a b`. -/
@[simp]
theorem ePowerSeries_hurwitzMul {K : Type*} [Semifield K] [CharZero K] (a b : ℕ → K) :
    ePowerSeries (hurwitzMul a b) = ePowerSeries a * ePowerSeries b := by
  ext n
  rw [coeff_ePowerSeries, hurwitzMul_eq_sum_antidiagonal, PowerSeries.coeff_mul,
    div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hsum := Finset.mem_antidiagonal.mp hij
  have hi : (ij.1.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj : (ij.2.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hchoose : (n.choose ij.1 : K) * ij.1.factorial * ij.2.factorial = n.factorial := by
    have hij2 : n - ij.1 = ij.2 := by omega
    exact_mod_cast hij2 ▸ Nat.choose_mul_factorial_mul_factorial (by omega : ij.1 ≤ n)
  rw [← div_eq_mul_inv, coeff_ePowerSeries, coeff_ePowerSeries, nsmul_eq_mul, div_mul_div_comm,
    div_eq_div_iff hn (mul_ne_zero hi hj)]
  calc (n.choose ij.1 : K) * (a ij.1 * b ij.2) * (ij.1.factorial * ij.2.factorial)
      = a ij.1 * b ij.2 * ((n.choose ij.1 : K) * ij.1.factorial * ij.2.factorial) := by ring
    _ = a ij.1 * b ij.2 * n.factorial := by rw [hchoose]

/-- Differentiating `ePowerSeries a` shifts the coefficient sequence by `1`. -/
@[simp]
theorem derivative_ePowerSeries {K : Type*} [Semifield K] [CharZero K] (a : ℕ → K) :
    d⁄dX (ePowerSeries a) = ePowerSeries fun n ↦ a (n + 1) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_ePowerSeries, coeff_ePowerSeries, Nat.factorial_succ,
    Nat.cast_mul, ← div_div, div_right_comm, ← Nat.cast_add_one,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))]

/-- Iterated differentiation of `ePowerSeries a` shifts the coefficient sequence by `m`. -/
@[simp]
theorem iterate_derivative_ePowerSeries {K : Type*} [Semifield K] [CharZero K]
    (a : ℕ → K) (m : ℕ) :
    (d⁄dX)^[m] (ePowerSeries a) = ePowerSeries fun n ↦ a (n + m) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, derivative_ePowerSeries, ih]
    simp [Nat.add_assoc]

/-- Rescaling the variable of `ePowerSeries a` by `c` multiplies `a n` by `c ^ n`. -/
theorem rescale_ePowerSeries {K : Type*} [Semifield K] (c : K) (a : ℕ → K) :
    PowerSeries.rescale c (ePowerSeries a) = ePowerSeries fun n ↦ c ^ n * a n := by
  ext n
  simp [PowerSeries.coeff_rescale, mul_div_assoc]

/-- Applying a semifield homomorphism coefficientwise commutes with `ePowerSeries`. -/
theorem map_ePowerSeries {K K' : Type*} [Semifield K] [Semifield K'] (σ : K →+* K') (a : ℕ → K) :
    PowerSeries.map σ (ePowerSeries a) = ePowerSeries (σ ∘ a) := by
  ext n
  simp

end EPowerSeries

end TauCeti
