/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Completely multiplicative arithmetic functions

An arithmetic function `f` is *completely multiplicative* if `f 1 = 1` and
`f (m * n) = f m * f n` for all `m n : ℕ`, coprime or not. Mathlib's
`ArithmeticFunction.IsMultiplicative` asks this only for coprime arguments; the Möbius function
is multiplicative but not completely multiplicative. No condition is placed on the set of primes
at which `f` vanishes.

Since an arithmetic function vanishes at `0`, a completely multiplicative arithmetic function is
the same thing as a monoid-with-zero homomorphism `ℕ →*₀ R`, and the two notions are identified
by an equivalence commuting with evaluation. Through it, Mathlib's Euler product for completely
multiplicative functions applies.

Completely multiplicative functions interact with Dirichlet convolution through the pointwise
product: `f · (g ⋆ h) = (f · g) ⋆ (f · h)`. Over a commutative ring this makes `μ · f` the
Dirichlet inverse of `f`. These are the identities used to compute Dirichlet series of twisted
divisor functions and of functions such as Liouville's `λ`.

## Main definitions

* `ArithmeticFunction.IsCompletelyMultiplicative`: the predicate.
* `ArithmeticFunction.IsCompletelyMultiplicative.toMonoidWithZeroHom`: the underlying
  `ℕ →*₀ R`.
* `ArithmeticFunction.completelyMultiplicativeEquiv`: completely multiplicative arithmetic
  functions are the monoid-with-zero homomorphisms `ℕ →*₀ R`.

## Main results

* `ArithmeticFunction.IsCompletelyMultiplicative.isMultiplicative`: complete multiplicativity
  implies multiplicativity.
* `ArithmeticFunction.isCompletelyMultiplicative_iff_existsUnique`: `f` is completely
  multiplicative exactly when it is the coercion of a unique `ℕ →*₀ R`.
* `ArithmeticFunction.IsCompletelyMultiplicative.pmul_mul`: `f · (g ⋆ h) = (f · g) ⋆ (f · h)`.
* `ArithmeticFunction.IsCompletelyMultiplicative.coe_moebius_pmul_mul_self`: `(μ · f) ⋆ f = 1`.
* `ArithmeticFunction.IsCompletelyMultiplicative.eulerProduct_tprod`:
  `∏' p, (1 - f p)⁻¹ = ∑' n, f n` for absolutely summable `f`.
* `ArithmeticFunction.isCompletelyMultiplicative_liouville` and
  `ArithmeticFunction.isCompletelyMultiplicative_toArithmeticFunction_cpow`: Liouville's `λ` and
  `n ↦ n ^ ν` for complex `ν`; `ArithmeticFunction.not_isCompletelyMultiplicative_moebius`: the
  Möbius function is not completely multiplicative.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, Undergraduate Texts in Mathematics,
  Springer, 1976, Chapter 2 (completely multiplicative functions and their Dirichlet inverses).
* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem and More*, blueprint,
  Definition 9.1.8 and Theorems 9.1.66–9.1.67.
-/

public section

open Nat
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace ArithmeticFunction

variable {R : Type*}

/-- An arithmetic function `f` is **completely multiplicative** if `f 1 = 1` and
`f (m * n) = f m * f n` for all `m n : ℕ`, without any coprimality condition. -/
def IsCompletelyMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

/-- Unfolds `IsCompletelyMultiplicative`, to build or destructure it from other modules. -/
theorem isCompletelyMultiplicative_iff [MonoidWithZero R] {f : ArithmeticFunction R} :
    f.IsCompletelyMultiplicative ↔ f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n :=
  Iff.rfl

namespace IsCompletelyMultiplicative

section MonoidWithZero

variable [MonoidWithZero R] {f : ArithmeticFunction R}

@[simp]
theorem map_one (hf : f.IsCompletelyMultiplicative) : f 1 = 1 :=
  hf.1

@[simp]
theorem map_mul (hf : f.IsCompletelyMultiplicative) (m n : ℕ) : f (m * n) = f m * f n :=
  hf.2 m n

/-- A completely multiplicative arithmetic function is multiplicative. -/
theorem isMultiplicative (hf : f.IsCompletelyMultiplicative) : f.IsMultiplicative :=
  ⟨hf.map_one, fun {m n} _ ↦ hf.map_mul m n⟩

/-- A completely multiplicative arithmetic function as a monoid-with-zero homomorphism. -/
def toMonoidWithZeroHom (hf : f.IsCompletelyMultiplicative) : ℕ →*₀ R where
  toFun := f
  map_zero' := f.map_zero
  map_one' := hf.map_one
  map_mul' := hf.map_mul

@[simp]
theorem coe_toMonoidWithZeroHom (hf : f.IsCompletelyMultiplicative) :
    ⇑hf.toMonoidWithZeroHom = ⇑f :=
  (rfl)

@[simp]
theorem map_pow (hf : f.IsCompletelyMultiplicative) (n k : ℕ) : f (n ^ k) = f n ^ k :=
  _root_.map_pow hf.toMonoidWithZeroHom n k

end MonoidWithZero

/-- The pointwise product of completely multiplicative functions is completely
multiplicative. -/
theorem pmul [CommMonoidWithZero R] {f g : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) (hg : g.IsCompletelyMultiplicative) :
    (f.pmul g).IsCompletelyMultiplicative :=
  ⟨by simp [hf, hg], fun m n ↦ by
    simp only [pmul_apply, hf.map_mul, hg.map_mul, mul_mul_mul_comm]⟩

/-- The cast of a completely multiplicative `ℕ`-valued arithmetic function is completely
multiplicative. -/
theorem natCast [Semiring R] {f : ArithmeticFunction ℕ} (hf : f.IsCompletelyMultiplicative) :
    (f : ArithmeticFunction R).IsCompletelyMultiplicative :=
  ⟨by simp [hf], fun m n ↦ by simp [hf.map_mul]⟩

/-- The cast of a completely multiplicative `ℤ`-valued arithmetic function is completely
multiplicative. -/
theorem intCast [Ring R] {f : ArithmeticFunction ℤ} (hf : f.IsCompletelyMultiplicative) :
    (f : ArithmeticFunction R).IsCompletelyMultiplicative :=
  ⟨by simp [hf], fun m n ↦ by simp [hf.map_mul]⟩

end IsCompletelyMultiplicative

/-! ### Completely multiplicative functions are monoid-with-zero homomorphisms -/

section MonoidWithZeroHom

variable [MonoidWithZero R]

/-- Completely multiplicative arithmetic functions are the monoid-with-zero homomorphisms
`ℕ →*₀ R`; the equivalence commutes with evaluation. -/
def completelyMultiplicativeEquiv :
    {f : ArithmeticFunction R // f.IsCompletelyMultiplicative} ≃ (ℕ →*₀ R) where
  toFun f := f.property.toMonoidWithZeroHom
  invFun g := ⟨⟨g, g.map_zero⟩, g.map_one, g.map_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem completelyMultiplicativeEquiv_apply
    (f : {f : ArithmeticFunction R // f.IsCompletelyMultiplicative}) (n : ℕ) :
    completelyMultiplicativeEquiv f n = f.val n :=
  (rfl)

@[simp]
theorem completelyMultiplicativeEquiv_symm_apply (g : ℕ →*₀ R) (n : ℕ) :
    (completelyMultiplicativeEquiv.symm g).val n = g n :=
  (rfl)

/-- An arithmetic function is completely multiplicative exactly when it is the coercion of a
monoid-with-zero homomorphism `ℕ →*₀ R`, which is then unique. -/
theorem isCompletelyMultiplicative_iff_existsUnique {f : ArithmeticFunction R} :
    f.IsCompletelyMultiplicative ↔ ∃! g : ℕ →*₀ R, ⇑g = ⇑f := by
  refine ⟨fun hf ↦ ⟨hf.toMonoidWithZeroHom, rfl, fun g hg ↦ DFunLike.coe_injective hg⟩, ?_⟩
  rintro ⟨g, hg, -⟩
  exact ⟨hg ▸ g.map_one, fun m n ↦ hg ▸ g.map_mul m n⟩

end MonoidWithZeroHom

/-- An arithmetic function obtained from a function `ℕ → R` that is `1` at `1` and
multiplicative on nonzero arguments is completely multiplicative. -/
theorem isCompletelyMultiplicative_toArithmeticFunction [MonoidWithZero R] {g : ℕ → R}
    (h₁ : g 1 = 1) (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → g (m * n) = g m * g n) :
    (toArithmeticFunction g).IsCompletelyMultiplicative := by
  refine ⟨by simp [toArithmeticFunction, h₁], fun m n ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [toArithmeticFunction]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [toArithmeticFunction]
  simp [toArithmeticFunction, hm, hn, hmul hm hn]

/-! ### Examples -/

/-- The unit `δ₁` of Dirichlet convolution is completely multiplicative. -/
theorem isCompletelyMultiplicative_one [MonoidWithZero R] :
    (1 : ArithmeticFunction R).IsCompletelyMultiplicative :=
  ⟨by simp, fun m n ↦ by
    by_cases hm : m = 1 <;> by_cases hn : n = 1 <;>
      simp [hm, hn, mul_eq_one]⟩

/-- The constant function `ζ`, equal to `1` on positive integers, is completely multiplicative. -/
theorem isCompletelyMultiplicative_zeta : (ζ : ArithmeticFunction ℕ).IsCompletelyMultiplicative :=
  ⟨by simp, fun m n ↦ by
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [zeta_apply, hm, hn]⟩

/-- The identity `n ↦ n` is completely multiplicative. -/
theorem isCompletelyMultiplicative_id : ArithmeticFunction.id.IsCompletelyMultiplicative :=
  ⟨by simp, fun m n ↦ by simp⟩

/-- Liouville's function `λ` is completely multiplicative. -/
theorem isCompletelyMultiplicative_liouville : liouville.IsCompletelyMultiplicative :=
  ⟨liouville_apply_one, liouville_apply_mul⟩

/-- The power `n ↦ n ^ ν`, for complex `ν` and with value `0` at `0`, is completely
multiplicative. -/
theorem isCompletelyMultiplicative_toArithmeticFunction_cpow (ν : ℂ) :
    (toArithmeticFunction fun n : ℕ ↦ (n : ℂ) ^ ν).IsCompletelyMultiplicative :=
  isCompletelyMultiplicative_toArithmeticFunction (by simp)
    fun {m n} _ _ ↦ by rw [Nat.cast_mul, Complex.natCast_mul_cpow]

/-- The Möbius function is multiplicative but not completely multiplicative:
`μ 4 = 0 ≠ 1 = μ 2 ^ 2`. -/
theorem not_isCompletelyMultiplicative_moebius : ¬ IsCompletelyMultiplicative μ := by
  intro h
  have h4 := h.map_pow 2 2
  rw [moebius_apply_prime_pow Nat.prime_two two_ne_zero, moebius_apply_prime Nat.prime_two] at h4
  norm_num at h4

/-! ### Pointwise products and Dirichlet convolution -/

namespace IsCompletelyMultiplicative

/-- The pointwise powers of a completely multiplicative function are completely
multiplicative. -/
theorem ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsCompletelyMultiplicative)
    (k : ℕ) : (f.ppow k).IsCompletelyMultiplicative := by
  induction k with
  | zero =>
    rw [ppow_zero]
    exact isCompletelyMultiplicative_zeta.natCast
  | succ k ih => exact ppow_succ' (f := f) ▸ hf.pmul ih

end IsCompletelyMultiplicative

/-- The power `n ↦ n ^ k` is completely multiplicative. -/
theorem isCompletelyMultiplicative_pow (k : ℕ) : (pow k).IsCompletelyMultiplicative := by
  unfold pow
  exact isCompletelyMultiplicative_id.ppow k

namespace IsCompletelyMultiplicative

/-- Twisting by a completely multiplicative function preserves Dirichlet convolution:
`f · (g ⋆ h) = (f · g) ⋆ (f · h)`. -/
theorem pmul_mul [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsCompletelyMultiplicative)
    (g h : ArithmeticFunction R) : f.pmul (g * h) = f.pmul g * f.pmul h := by
  ext n
  simp only [pmul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, hf.map_mul]
  ring

/-- Over a commutative ring, the Dirichlet inverse of a completely multiplicative function `f`
is `μ · f`. -/
theorem coe_moebius_pmul_mul_self [CommRing R] {f : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) : (μ : ArithmeticFunction R).pmul f * f = 1 := by
  have hone : f.pmul 1 = 1 := by
    ext n
    by_cases hn : n = 1 <;> simp [hn, hf.map_one]
  calc (μ : ArithmeticFunction R).pmul f * f
      = f.pmul μ * f.pmul ζ := by rw [pmul_comm, pmul_zeta]
    _ = 1 := by rw [← hf.pmul_mul, coe_moebius_mul_coe_zeta, hone]

/-- Over a commutative ring, `μ · f` is a right Dirichlet inverse of a completely multiplicative
function `f`. -/
theorem self_mul_coe_moebius_pmul [CommRing R] {f : ArithmeticFunction R}
    (hf : f.IsCompletelyMultiplicative) : f * (μ : ArithmeticFunction R).pmul f = 1 := by
  rw [mul_comm, hf.coe_moebius_pmul_mul_self]

/-! ### Euler products -/

section EulerProduct

variable {F : Type*} [NormedField F] [CompleteSpace F] {f : ArithmeticFunction F}

/-- **The Euler product** of an absolutely summable completely multiplicative function, as a
`HasProd`: `∏' p, (1 - f p)⁻¹ = ∑' n, f n`. -/
theorem eulerProduct_hasProd (hf : f.IsCompletelyMultiplicative) (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ (1 - f p)⁻¹) (∑' n, f n) :=
  EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := hf.toMonoidWithZeroHom) hsum

/-- **The Euler product** of an absolutely summable completely multiplicative function:
`∏' p, (1 - f p)⁻¹ = ∑' n, f n`. -/
theorem eulerProduct_tprod (hf : f.IsCompletelyMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  (hf.eulerProduct_hasProd hsum).tprod_eq

end EulerProduct

end IsCompletelyMultiplicative

end ArithmeticFunction
