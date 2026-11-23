/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralClosure.PRootClosure
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Examples of `p`-root closures and complete integral closures away from an element

* For `p = 3`, `ℤ` is `3`-root closed in the Gaussian integers, so its `3`-root closure is `ℤ`,
  while `i` is integral over `ℤ`: the `p`-root closure can be strictly smaller than the integral
  closure.
* In characteristic `p`, the Frobenius embedding `𝔽_p[T] → 𝔽_p[T]`, `T ↦ T ^ p`, models
  `𝔽_p[T] ⊆ 𝔽_p[T^{1/p}]`; every element is `p`-radicial, so the `p`-root closure is everything.
* The complete integral closure of `ℤ` in `ℚ` away from `2` is `ℤ`.
-/

public section

namespace TauCeti

section GaussianInt

/-- A Gaussian integer lies in `ℤ` iff its imaginary part vanishes. -/
private theorem gaussianInt_mem_bot_iff {z : GaussianInt} :
    z ∈ (⊥ : Subalgebra ℤ GaussianInt) ↔ z.im = 0 := by
  rw [Algebra.mem_bot]
  refine ⟨?_, fun h ↦ ⟨z.re, Zsqrtd.ext (by simp) (by simp [h])⟩⟩
  rintro ⟨n, rfl⟩
  simp

/-- `b ^ 2 = 3 * a ^ 2` has no solution in positive integers: the two sides have `3`-adic
valuations of different parity. -/
private theorem sq_ne_three_mul_sq {a b : ℕ} (hb : b ≠ 0) : b ^ 2 ≠ 3 * a ^ 2 := by
  intro h
  have ha : a ≠ 0 := by
    rintro rfl
    simp_all
  have h3 := congrArg (multiplicity 3) h
  rw [Nat.multiplicity_mul (by norm_num) (pow_ne_zero 2 ha), Nat.multiplicity_pow,
    Nat.multiplicity_pow, Nat.Prime.multiplicity_self] at h3
  omega

/-- `ℤ` is `3`-root closed in `ℤ[i]`: if `(a + bi) ^ 3 = a ^ 3 - 3ab ^ 2 + (3a ^ 2 b - b ^ 3) i`
is an integer, then `b (3a ^ 2 - b ^ 2) = 0`, and `b ^ 2 = 3a ^ 2` forces `b = 0`. -/
theorem gaussianInt_bot_isPRootClosed_three :
    (⊥ : Subalgebra ℤ GaussianInt).IsPRootClosed 3 := by
  refine Subalgebra.isPRootClosed_iff.mpr fun z hz ↦ ?_
  rw [gaussianInt_mem_bot_iff] at hz ⊢
  have him : z.im * (3 * z.re ^ 2 - z.im ^ 2) = 0 := by
    simp only [pow_succ, pow_zero, one_mul, Zsqrtd.im_mul, Zsqrtd.re_mul] at hz
    linear_combination hz
  rcases mul_eq_zero.mp him with h | h
  · exact h
  · by_contra hne
    apply sq_ne_three_mul_sq (a := z.re.natAbs) (Int.natAbs_ne_zero.mpr hne)
    zify
    simp only [sq_abs]
    linarith

/-- The `3`-root closure of `ℤ` in `ℤ[i]` is `ℤ`. -/
example : pRootClosure 3 ℤ GaussianInt = ⊥ :=
  pRootClosure_eq_bot_iff.mpr gaussianInt_bot_isPRootClosed_three

/-- The `3`-root closure of `ℤ` in `ℤ[i]` is not its integral closure: `i` is integral but not in
`ℤ`. -/
example : pRootClosure 3 ℤ GaussianInt ≠ integralClosure ℤ GaussianInt := by
  intro h
  have hi : (⟨0, 1⟩ : GaussianInt) ∈ integralClosure ℤ GaussianInt := by
    refine IsIntegral.of_pow (n := 4) (by norm_num) ?_
    rw [show (⟨0, 1⟩ : GaussianInt) ^ 4 = 1 by ext <;> simp [pow_succ]]
    exact isIntegral_one
  rw [← h, pRootClosure_eq_bot_iff.mpr gaussianInt_bot_isPRootClosed_three,
    gaussianInt_mem_bot_iff] at hi
  exact one_ne_zero hi

end GaussianInt

section Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- Along the Frobenius embedding `𝔽_p[T] → 𝔽_p[T]`, `T ↦ T ^ p`, which models the inclusion
`𝔽_p[T] ⊆ 𝔽_p[T^{1/p}]`, every element has its `p`-th power in the image, so the `p`-root
closure is the whole ring. -/
example :
    letI := (Polynomial.expand (ZMod p) p).toRingHom.toAlgebra
    pRootClosure p (Polynomial (ZMod p)) (Polynomial (ZMod p)) = ⊤ := by
  let := (Polynomial.expand (ZMod p) p).toRingHom.toAlgebra
  refine eq_top_iff.mpr fun f _ ↦ mem_pRootClosure_of_pow_pow_mem (n := 1) ⟨f, ?_⟩
  rw [pow_one, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    ZMod.expand_card]

end Frobenius

section Dyadic

open scoped nonZeroDivisors

/-- The complete integral closure of `ℤ` in `ℚ` away from `2` is `ℤ`: it lies in the complete
integral closure, which for the Noetherian integrally closed domain `ℤ` is the integral
closure `ℤ`. -/
example : awayCompleteIntegralClosure (2 : ℤ) ℚ = ⊥ := by
  refine le_bot_iff.mp ((awayCompleteIntegralClosure_le_completeIntegralClosure
    (mem_nonZeroDivisors_of_ne_zero two_ne_zero)).trans ?_)
  have h : integralClosure ℤ ℚ = ⊥ :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff ℚ).mpr inferInstance
  rw [completeIntegralClosure_eq_integralClosure, h]

end Dyadic

end TauCeti
