/-
Copyright (c) 2023 Arend Mellendijk and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyAdditive

/-!
# Completely multiplicative arithmetic functions

An arithmetic function `f` is *completely multiplicative* if `f 1 = 1` and
`f (m * n) = f m * f n` for all `m n : ℕ`, not only for coprime ones as in
`ArithmeticFunction.IsMultiplicative`. Since arithmetic functions vanish at `0`, these are
exactly the coercions of the monoid-with-zero homomorphisms `ℕ →*₀ R`.

## Main definitions and results

* `ArithmeticFunction.IsCompletelyMultiplicative`: the predicate.
* `ArithmeticFunction.IsCompletelyMultiplicative.isMultiplicative`: it implies multiplicativity.
* `ArithmeticFunction.IsCompletelyMultiplicative.eq_iff_eq_on_primes`: a completely
  multiplicative function is determined by its values at primes.
* `ArithmeticFunction.completelyMultiplicativeEquiv`: completely multiplicative arithmetic
  functions are the same as `ℕ →*₀ R`, compatibly with evaluation.
* `ArithmeticFunction.IsCompletelyMultiplicative.pmul_mul`: pointwise multiplication by a
  completely multiplicative function distributes over Dirichlet convolution.
* `ArithmeticFunction.IsCompletelyMultiplicative.moebius_pmul_mul_self`: the Dirichlet inverse of
  a completely multiplicative `f` is `μ · f`.
* `ArithmeticFunction.IsCompletelyMultiplicative.ppow`: pointwise powers of a completely
  multiplicative function are completely multiplicative.
* Instances: `ζ`, `id`, `pow k`, `n ↦ n ^ ν` for complex `ν`, the Liouville function and
  `n ↦ k ^ f n` for completely additive `f`
  (`ArithmeticFunction.IsCompletelyAdditive.isCompletelyMultiplicative_powOfAdditive`);
  `ArithmeticFunction.not_isCompletelyMultiplicative_moebius`: `μ` is not completely
  multiplicative.

The Euler products of completely multiplicative functions are in
`TauCeti/NumberTheory/EulerProduct/CompletelyMultiplicative.lean`, and the instance for
Dirichlet characters is in `TauCeti/NumberTheory/DirichletCharacter/ArithmeticFunction.lean`.
-/

public section

open Nat

namespace ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

variable {R : Type*}

section MonoidWithZero

variable [MonoidWithZero R]

/-- An arithmetic function `f` is *completely multiplicative* if `f 1 = 1` and
`f (m * n) = f m * f n` for all `m n : ℕ`. -/
def IsCompletelyMultiplicative (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ m n, f (m * n) = f m * f n

/-- Unfolding the definition of complete multiplicativity. -/
theorem isCompletelyMultiplicative_iff {f : ArithmeticFunction R} :
    f.IsCompletelyMultiplicative ↔ f 1 = 1 ∧ ∀ m n, f (m * n) = f m * f n :=
  Iff.rfl

namespace IsCompletelyMultiplicative

variable {f : ArithmeticFunction R}

@[simp]
theorem map_one (hf : f.IsCompletelyMultiplicative) : f 1 = 1 :=
  hf.1

@[simp]
theorem map_mul (hf : f.IsCompletelyMultiplicative) (m n : ℕ) : f (m * n) = f m * f n :=
  hf.2 m n

/-- A completely multiplicative function is multiplicative. -/
theorem isMultiplicative (hf : f.IsCompletelyMultiplicative) : f.IsMultiplicative :=
  ⟨hf.1, fun {m n} _ ↦ hf.2 m n⟩

/-- Since arithmetic functions vanish at `0`, complete multiplicativity only needs to be checked
at nonzero arguments. -/
theorem iff_ne_zero :
    f.IsCompletelyMultiplicative ↔
      f 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n := by
  refine and_congr_right' ⟨fun h m n _ _ ↦ h m n, fun h m n ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact h hm hn

/-- Constructor for complete multiplicativity from its values at nonzero arguments. -/
theorem of_ne_zero (h₁ : f 1 = 1)
    (h : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n) :
    f.IsCompletelyMultiplicative :=
  iff_ne_zero.mpr ⟨h₁, h⟩

/-- A completely multiplicative arithmetic function as a monoid-with-zero homomorphism. -/
def toMonoidWithZeroHom (hf : f.IsCompletelyMultiplicative) : ℕ →*₀ R where
  toFun := f
  map_zero' := f.map_zero
  map_one' := hf.1
  map_mul' := hf.2

@[simp]
theorem coe_toMonoidWithZeroHom (hf : f.IsCompletelyMultiplicative) :
    ⇑hf.toMonoidWithZeroHom = f :=
  (rfl)

@[simp]
theorem map_pow (hf : f.IsCompletelyMultiplicative) (n k : ℕ) : f (n ^ k) = f n ^ k :=
  _root_.map_pow hf.toMonoidWithZeroHom n k

/-- Two completely multiplicative functions are equal if and only if they agree at primes. -/
theorem eq_iff_eq_on_primes {g : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) (hg : g.IsCompletelyMultiplicative) :
    f = g ↔ ∀ p, p.Prime → f p = g p := by
  refine ⟨fun h p _ ↦ h ▸ rfl, fun h ↦ ArithmeticFunction.ext fun n ↦ ?_⟩
  induction n using Nat.recOnMul with
  | zero => simp
  | one => rw [hf.map_one, hg.map_one]
  | prime p hp => exact h p hp
  | mul a b ha hb => rw [hf.map_mul, hg.map_mul, ha, hb]

end IsCompletelyMultiplicative

/-- The arithmetic function underlying a monoid-with-zero homomorphism `ℕ →*₀ R` is completely
multiplicative. -/
theorem isCompletelyMultiplicative_mk (g : ℕ →*₀ R) :
    IsCompletelyMultiplicative (⟨g, g.map_zero⟩ : ArithmeticFunction R) :=
  ⟨map_one g, map_mul g⟩

/-- An arithmetic function is completely multiplicative if and only if it is the coercion of a
(necessarily unique) monoid-with-zero homomorphism `ℕ →*₀ R`. -/
theorem isCompletelyMultiplicative_iff_existsUnique {f : ArithmeticFunction R} :
    f.IsCompletelyMultiplicative ↔ ∃! g : ℕ →*₀ R, ⇑g = ⇑f := by
  refine ⟨fun hf ↦ ⟨hf.toMonoidWithZeroHom, rfl, fun g hg ↦ DFunLike.coe_injective hg⟩, ?_⟩
  rintro ⟨g, hg, -⟩
  have : f = ⟨g, g.map_zero⟩ := DFunLike.coe_injective hg.symm
  exact this ▸ isCompletelyMultiplicative_mk g

/-- Completely multiplicative arithmetic functions are the same as monoid-with-zero homomorphisms
`ℕ →*₀ R`; see `completelyMultiplicativeEquiv_apply_apply` and
`completelyMultiplicativeEquiv_symm_apply_apply` for compatibility with evaluation. -/
def completelyMultiplicativeEquiv :
    {f : ArithmeticFunction R // f.IsCompletelyMultiplicative} ≃ (ℕ →*₀ R) where
  toFun f := f.property.toMonoidWithZeroHom
  invFun g := ⟨⟨g, g.map_zero⟩, isCompletelyMultiplicative_mk g⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem completelyMultiplicativeEquiv_apply_apply
    (f : {f : ArithmeticFunction R // f.IsCompletelyMultiplicative}) (n : ℕ) :
    completelyMultiplicativeEquiv f n = f.val n :=
  (rfl)

@[simp]
theorem completelyMultiplicativeEquiv_symm_apply_apply (g : ℕ →*₀ R) (n : ℕ) :
    (completelyMultiplicativeEquiv.symm g).val n = g n :=
  (rfl)

/-- The constant function `ζ` (equal to `1` away from `0`) is completely multiplicative. -/
theorem isCompletelyMultiplicative_zeta : IsCompletelyMultiplicative ζ :=
  .of_ne_zero rfl fun hm hn ↦ by simp [hm, hn]

/-- The Dirichlet unit `1` (the indicator of `1`) is completely multiplicative. -/
theorem isCompletelyMultiplicative_one : IsCompletelyMultiplicative (1 : ArithmeticFunction R) :=
  ⟨one_one, fun m n ↦ by
    by_cases hm : m = 1 <;> by_cases hn : n = 1 <;>
      simp [hm, hn, mul_eq_one]⟩

/-- The arithmetic function of a function `g : ℕ → R` that is `1` at `1` and multiplicative on
nonzero arguments is completely multiplicative. -/
theorem isCompletelyMultiplicative_toArithmeticFunction {g : ℕ → R} (h₁ : g 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → g (m * n) = g m * g n) :
    (toArithmeticFunction g).IsCompletelyMultiplicative :=
  .of_ne_zero (by simp [toArithmeticFunction, h₁]) fun hm hn ↦ by
    simp [toArithmeticFunction, hm, hn, hmul hm hn]

end MonoidWithZero

/-- The identity `n ↦ n` is completely multiplicative. -/
theorem isCompletelyMultiplicative_id : ArithmeticFunction.id.IsCompletelyMultiplicative :=
  ⟨by simp, fun m n ↦ by simp⟩

namespace IsCompletelyMultiplicative

/-- The pointwise product of completely multiplicative functions is completely
multiplicative. -/
theorem pmul [CommMonoidWithZero R] {f g : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) (hg : g.IsCompletelyMultiplicative) :
    (f.pmul g).IsCompletelyMultiplicative :=
  ⟨by simp [hf.map_one, hg.map_one], fun m n ↦ by
    simp only [pmul_apply, hf.map_mul, hg.map_mul, mul_mul_mul_comm]⟩

/-- The coercion of a completely multiplicative `ℕ`-valued function is completely
multiplicative. -/
theorem natCast [Semiring R] {f : ArithmeticFunction ℕ} (hf : f.IsCompletelyMultiplicative) :
    (f : ArithmeticFunction R).IsCompletelyMultiplicative :=
  ⟨by simp [hf.map_one], fun m n ↦ by simp [hf.map_mul]⟩

/-- The coercion of a completely multiplicative `ℤ`-valued function is completely
multiplicative. -/
theorem intCast [Ring R] {f : ArithmeticFunction ℤ} (hf : f.IsCompletelyMultiplicative) :
    (f : ArithmeticFunction R).IsCompletelyMultiplicative :=
  ⟨by simp [hf.map_one], fun m n ↦ by simp [hf.map_mul]⟩

/-- The pointwise powers of a completely multiplicative function are completely
multiplicative. -/
theorem ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsCompletelyMultiplicative)
    (k : ℕ) : (f.ppow k).IsCompletelyMultiplicative := by
  induction k with
  | zero => simpa [ppow_zero] using isCompletelyMultiplicative_zeta.natCast (R := R)
  | succ k ih => exact ppow_succ' (f := f) ▸ hf.pmul ih

/-- Pointwise multiplication by a completely multiplicative function distributes over
Dirichlet convolution: `f · (g ⋆ h) = (f · g) ⋆ (f · h)`. -/
theorem pmul_mul [CommSemiring R] {f : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) (g h : ArithmeticFunction R) :
    f.pmul (g * h) = f.pmul g * f.pmul h := by
  ext n
  simp only [pmul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← (mem_divisorsAntidiagonal.mp hx).1, hf.map_mul]
  ring

/-- The Dirichlet inverse of a completely multiplicative function `f` is `μ · f`: here
`(μ · f) ⋆ f = 1`. -/
theorem moebius_pmul_mul_self [Ring R] {f : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) : (μ : ArithmeticFunction R).pmul f * f = 1 := by
  ext n
  have key : ((μ : ArithmeticFunction R).pmul f * f) n =
      ((μ : ArithmeticFunction R) * ζ) n * f n := by
    simp only [ArithmeticFunction.mul_apply, pmul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp [← (mem_divisorsAntidiagonal.mp hx).1, hf.map_mul, mul_assoc,
      right_ne_zero_of_mem_divisorsAntidiagonal hx]
  rw [key, coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  split_ifs with h <;> simp [h, hf.map_one]

/-- The Dirichlet inverse of a completely multiplicative function `f` is `μ · f`: here
`f ⋆ (μ · f) = 1`. -/
theorem mul_moebius_pmul [Ring R] {f : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) : f * (μ : ArithmeticFunction R).pmul f = 1 := by
  ext n
  have key : (f * (μ : ArithmeticFunction R).pmul f) n =
      (ζ * (μ : ArithmeticFunction R)) n * f n := by
    simp only [ArithmeticFunction.mul_apply, pmul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp [← (mem_divisorsAntidiagonal.mp hx).1, hf.map_mul, (Int.cast_commute _ _).eq, mul_assoc,
      left_ne_zero_of_mem_divisorsAntidiagonal hx]
  rw [key, coe_zeta_mul_coe_moebius, ArithmeticFunction.one_apply]
  split_ifs with h <;> simp [h, hf.map_one]

end IsCompletelyMultiplicative

/-- The function `n ↦ n ^ k` is completely multiplicative. -/
theorem isCompletelyMultiplicative_pow (k : ℕ) : (pow k).IsCompletelyMultiplicative := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [pow_zero_eq_zeta]
    exact isCompletelyMultiplicative_zeta
  · exact ⟨by simp [pow_apply], fun m n ↦ by simp [pow_apply, hk, Nat.mul_pow]⟩

/-- For complex `ν`, the function `n ↦ n ^ ν` (with value `0` at `0`) is completely
multiplicative. -/
theorem isCompletelyMultiplicative_cpow (ν : ℂ) :
    (toArithmeticFunction fun n : ℕ ↦ (n : ℂ) ^ ν).IsCompletelyMultiplicative := by
  refine .of_ne_zero (by simp [toArithmeticFunction]) fun hm hn ↦ ?_
  simp [toArithmeticFunction, hm, hn, Complex.natCast_mul_cpow]

/-- The Liouville function is completely multiplicative. -/
theorem isCompletelyMultiplicative_liouville : liouville.IsCompletelyMultiplicative :=
  ⟨liouville_apply_one, liouville_apply_mul⟩

/-- Powers along a completely additive function are completely multiplicative, as for
`n ↦ k ^ Ω n`. -/
theorem IsCompletelyAdditive.isCompletelyMultiplicative_powOfAdditive [MonoidWithZero R]
    {f : ArithmeticFunction ℕ} (hf : f.IsCompletelyAdditive) (k : R) :
    (powOfAdditive k f).IsCompletelyMultiplicative :=
  ⟨powOfAdditive_apply_one k hf.map_one, hf.powOfAdditive_mul k⟩

/-- The Möbius function is not completely multiplicative: `μ(4) = 0 ≠ 1 = μ(2) ^ 2`. -/
theorem not_isCompletelyMultiplicative_moebius : ¬ IsCompletelyMultiplicative μ := by
  intro h
  have h4 := h.map_pow 2 2
  rw [moebius_apply_prime_pow prime_two two_ne_zero, moebius_apply_prime prime_two] at h4
  norm_num at h4

end ArithmeticFunction

/-! ### Checks -/

namespace ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega ArithmeticFunction.omega

/-- The Liouville function: `λ(4) = 1 = λ(2) ^ 2` and `λ(12) = -1 = λ(4) λ(3)`. -/
example : liouville 4 = 1 ∧ liouville 4 = liouville 2 ^ 2 ∧
    liouville 12 = -1 ∧ liouville 12 = liouville 4 * liouville 3 := by
  have h2 : liouville 2 = -1 := by
    rw [liouville_apply two_ne_zero, cardFactors_apply_prime prime_two, pow_one]
  have h3 : liouville 3 = -1 := by
    rw [liouville_apply three_ne_zero, cardFactors_apply_prime prime_three, pow_one]
  have h4 : liouville 4 = liouville 2 ^ 2 := isCompletelyMultiplicative_liouville.map_pow 2 2
  have h12 : liouville 12 = liouville 4 * liouville 3 :=
    isCompletelyMultiplicative_liouville.map_mul 4 3
  refine ⟨?_, h4, ?_, h12⟩ <;> simp [h2, h3, h4, h12]

/-- The Möbius function is multiplicative but not completely multiplicative:
`μ(4) = 0 ≠ 1 = μ(2) ^ 2`. -/
example : IsMultiplicative μ ∧ ¬ IsCompletelyMultiplicative μ :=
  ⟨isMultiplicative_moebius, not_isCompletelyMultiplicative_moebius⟩

/-- Dropping `f 1 = 1` would admit the zero function, which is not completely
multiplicative. -/
example : (∀ m n, (0 : ArithmeticFunction ℤ) (m * n) =
      (0 : ArithmeticFunction ℤ) m * (0 : ArithmeticFunction ℤ) n) ∧
    ¬ (0 : ArithmeticFunction ℤ).IsCompletelyMultiplicative :=
  ⟨fun _ _ ↦ by simp, fun h ↦ by simpa using h.map_one⟩

/-- The inverse formula at `f = λ`: `μ λ = μ²`, and `Σ_{d ∣ 4} λ(d) μ²(4 / d) = 0`. -/
example : pmul μ liouville = pmul μ μ ∧ (liouville * pmul μ μ) 4 = 0 := by
  have h : pmul μ liouville = pmul μ μ := by
    ext n
    rw [pmul_apply, pmul_apply]
    by_cases hn : Squarefree n
    · rw [liouville_apply hn.ne_zero, moebius_apply_of_squarefree hn]
    · simp [moebius_eq_zero_of_not_squarefree hn]
  refine ⟨h, ?_⟩
  have := isCompletelyMultiplicative_liouville.mul_moebius_pmul
  rw [intCoe_int, h] at this
  rw [this, one_apply_ne (by norm_num)]

/-- The indicator of the positive integers all of whose prime factors are `1` modulo `4` is
completely multiplicative, although it vanishes at `2` and at every prime `3` modulo `4`. -/
example :
    let f : ArithmeticFunction ℤ :=
      ⟨fun n ↦ if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 = 1 then 1 else 0, by simp⟩
    f.IsCompletelyMultiplicative ∧ f 2 = 0 ∧ ∀ p, p.Prime → p % 4 = 3 → f p = 0 := by
  refine ⟨.of_ne_zero (by simp) fun hm hn ↦ ?_, by simp [prime_two.primeFactors],
    fun p hp hp3 ↦ ?_⟩
  · simp only [coe_mk, primeFactors_mul hm hn, Finset.mem_union, or_imp, forall_and]
    split_ifs <;> simp_all
  · simp [hp.primeFactors, hp3]

/-- `2 ^ Ω` is completely multiplicative, while `2 ^ ω` is multiplicative but not completely
multiplicative: `2 ^ ω(4) = 2 ≠ 4 = (2 ^ ω(2)) ^ 2`. -/
example : (toArithmeticFunction fun n ↦ 2 ^ Ω n : ArithmeticFunction ℕ).IsCompletelyMultiplicative ∧
    (toArithmeticFunction fun n ↦ 2 ^ ω n : ArithmeticFunction ℕ).IsMultiplicative ∧
    ¬ (toArithmeticFunction fun n ↦ 2 ^ ω n : ArithmeticFunction ℕ).IsCompletelyMultiplicative := by
  refine ⟨.of_ne_zero (by simp [toArithmeticFunction]) fun hm hn ↦ ?_,
    IsMultiplicative.iff_ne_zero.mpr ⟨by simp [toArithmeticFunction], fun hm hn hmn ↦ ?_⟩,
    fun h ↦ ?_⟩
  · simp [toArithmeticFunction, hm, hn, cardFactors_mul hm hn, pow_add]
  · simp [toArithmeticFunction, hm, hn, cardDistinctFactors_mul hmn, pow_add]
  · have h4 := h.map_pow 2 2
    have hω : ω (2 ^ 2) = 1 := cardDistinctFactors_apply_prime_pow prime_two two_ne_zero
    norm_num at hω
    simp [toArithmeticFunction, hω, cardDistinctFactors_apply_prime prime_two] at h4

end ArithmeticFunction
