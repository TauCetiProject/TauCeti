/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.DedekindCubic.RingOfIntegers
public import TauCeti.NumberTheory.NumberField.Index.CommonIndexDivisor
public import TauCeti.NumberTheory.NumberField.Monogenic
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic.LinearCombination
import TauCeti.NumberTheory.RamificationInertia.Splitting
import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# The primes above `2` in Dedekind's cubic field

Let `θ` be an algebraic integer with minimal polynomial `X³ - X² - 2X - 8` generating a number
field `K`, and let `β = (θ² - θ) / 2`, so that `𝓞 K = ℤ ⊕ ℤθ ⊕ ℤβ`. The multiplication relations
`θ² = θ + 2β`, `θβ = θ + 4` and `β² = β + 2θ - 2` reduce modulo `2` to `θ² = θ`, `θβ = θ` and
`β² = β`, which have exactly three solutions `(θ, β) ∈ {(0, 0), (0, 1), (1, 1)}` in `𝔽₂`. Each
gives a ring homomorphism `𝓞 K → 𝔽₂`, and their kernels are the three primes

`(2, θ, β)`, `(2, θ, β - 1)`, `(2, θ - 1, β - 1)`

of residue degree one. Since `[K : ℚ] = 3`, these are all the primes above `2`, and
`(2) = (2, θ, β) · (2, θ, β - 1) · (2, θ - 1, β - 1)`: the prime `2` splits completely.

There are only two monic polynomials of degree one over `𝔽₂`, so Kummer–Dedekind cannot produce
three primes of residue degree one above `2` from any single generator. Hence `2` divides the
index of every integral primitive element, and `K` is not monogenic, although `2` is unramified.

## Main definitions

* `TauCeti.NumberField.dedekindPrimeOne`, `dedekindPrimeTwo`, `dedekindPrimeThree`: the three
  displayed ideals.
* `TauCeti.NumberField.dedekindPrimeOneQuotEquiv`, `dedekindPrimeTwoQuotEquiv`,
  `dedekindPrimeThreeQuotEquiv`: their residue rings are `ZMod 2`.

## Main results

* `TauCeti.NumberField.dedekindCubic_primesOver_two_eq`: the primes above `2` are exactly the
  three ideals.
* `TauCeti.NumberField.dedekindCubic_ncard_primesOver_two_eq_finrank`: `2` splits completely.
* `TauCeti.NumberField.dedekindCubic_map_span_two_eq`:
  `(2) = (2, θ, β) · (2, θ, β - 1) · (2, θ - 1, β - 1)`.
* `TauCeti.NumberField.dedekindCubic_isCommonIndexDivisor_two`: `2` is a common index divisor.
* `TauCeti.NumberField.dedekindCubic_not_isMonogenic`: Dedekind's cubic field is not monogenic.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2, Exercise 1.
-/

public section
noncomputable section

open Polynomial NumberField Ideal
open scoped NumberField

namespace TauCeti.NumberField

section Ideals

variable {K : Type*} [Field K] [CharZero K] {θ : 𝓞 K}

/-- The ideal `(2, θ, β)` of Dedekind's cubic field, where `β = (θ² - θ) / 2`. -/
def dedekindPrimeOne (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) : Ideal (𝓞 K) :=
  span {2, θ, dedekindBeta hθ}

/-- The ideal `(2, θ, β - 1)` of Dedekind's cubic field, where `β = (θ² - θ) / 2`. -/
def dedekindPrimeTwo (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) : Ideal (𝓞 K) :=
  span {2, θ, dedekindBeta hθ - 1}

/-- The ideal `(2, θ - 1, β - 1)` of Dedekind's cubic field, where `β = (θ² - θ) / 2`. -/
def dedekindPrimeThree (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) : Ideal (𝓞 K) :=
  span {2, θ - 1, dedekindBeta hθ - 1}

/-- The ideal `(2, θ, β)` is the span of its displayed generators. -/
theorem dedekindPrimeOne_def (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    dedekindPrimeOne hθ = span {2, θ, dedekindBeta hθ} := by
  rw [dedekindPrimeOne]

/-- The ideal `(2, θ, β - 1)` is the span of its displayed generators. -/
theorem dedekindPrimeTwo_def (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    dedekindPrimeTwo hθ = span {2, θ, dedekindBeta hθ - 1} := by
  rw [dedekindPrimeTwo]

/-- The ideal `(2, θ - 1, β - 1)` is the span of its displayed generators. -/
theorem dedekindPrimeThree_def (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    dedekindPrimeThree hθ = span {2, θ - 1, dedekindBeta hθ - 1} := by
  rw [dedekindPrimeThree]

end Ideals

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
  (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
  (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)

/-! ### Reduction modulo `2` at a point of `𝔽₂` -/

section Residue

include hmin hgen

/-- Every algebraic integer of Dedekind's cubic field is `a + bθ + cβ` with integers `a, b, c`. -/
private theorem exists_eq_add_mul_add_mul (x : 𝓞 K) :
    ∃ a b c : ℤ, x = a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin) := by
  rw [← mem_dedekindOrder_iff, dedekindOrder_eq_ringOfIntegers hmin hgen]
  exact Algebra.mem_top

/-- The `ℤ`-linear map `a + bθ + cβ ↦ a + bt + cs` to `ZMod 2`. -/
private def residueLinearMap (t s : ℤ) : 𝓞 K →ₗ[ℤ] ZMod 2 :=
  (dedekindIntegralBasis hmin hgen).constr ℤ ![1, (t : ZMod 2), (s : ZMod 2)]

private theorem residueLinearMap_apply (t s a b c : ℤ) :
    residueLinearMap hmin hgen t s
        (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin)) =
      ((a + b * t + c * s : ℤ) : ZMod 2) := by
  have h (i : Fin 3) : residueLinearMap hmin hgen t s (dedekindIntegralBasis hmin hgen i) =
      ![1, (t : ZMod 2), (s : ZMod 2)] i :=
    (dedekindIntegralBasis hmin hgen).constr_basis ℤ _ i
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [dedekindIntegralBasis_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h0 h1 h2
  rw [← zsmul_one, ← zsmul_eq_mul, ← zsmul_eq_mul, map_add, map_add, map_zsmul, map_zsmul,
    map_zsmul, h0, h1, h2]
  push_cast
  simp only [zsmul_eq_mul, mul_one]

variable {hmin hgen} in
private theorem residueLinearMap_mul (t s : ℤ) (hts : (t * s : ZMod 2) = t) (x y : 𝓞 K) :
    residueLinearMap hmin hgen t s (x * y) =
      residueLinearMap hmin hgen t s x * residueLinearMap hmin hgen t s y := by
  set hrel := dedekindCubic_relation hmin
  obtain ⟨a, b, c, rfl⟩ := exists_eq_add_mul_add_mul hmin hgen x
  obtain ⟨d, e, f, rfl⟩ := exists_eq_add_mul_add_mul hmin hgen y
  -- The product in the integral basis, from the multiplication relations of `θ` and `β`.
  have hprod : ((a : 𝓞 K) + b * θ + c * dedekindBeta hrel) * (d + e * θ + f * dedekindBeta hrel) =
      ((a * d + 4 * b * f + 4 * c * e - 2 * c * f : ℤ) : 𝓞 K) +
        ((a * e + b * d + b * e + b * f + c * e + 2 * c * f : ℤ) : 𝓞 K) * θ +
        ((a * f + c * d + 2 * b * e + c * f : ℤ) : 𝓞 K) * dedekindBeta hrel := by
    push_cast
    linear_combination (b * e : 𝓞 K) * dedekindCubic_theta_sq hrel +
      (b * f + c * e : 𝓞 K) * dedekindCubic_theta_mul_beta hrel +
      (c * f : 𝓞 K) * dedekindCubic_beta_sq hrel
  have ht : ((t : ZMod 2)) * t = t := by
    generalize (t : ZMod 2) = u
    revert u
    decide
  have hs : ((s : ZMod 2)) * s = s := by
    generalize (s : ZMod 2) = u
    revert u
    decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [hprod, residueLinearMap_apply, residueLinearMap_apply, residueLinearMap_apply]
  push_cast
  linear_combination (-(b * e : ZMod 2)) * ht - (b * f + c * e : ZMod 2) * hts -
    (c * f : ZMod 2) * hs +
    (2 * b * f + 2 * c * e - c * f + c * f * t + b * e * s : ZMod 2) * h2

/-- The ring homomorphism `𝓞 K → ZMod 2` sending `θ ↦ t` and `β ↦ s`. It exists exactly when
`ts ≡ t` modulo `2`, the reduction of the relation `θβ = θ + 4`. -/
private def residueHom (t s : ℤ) (hts : (t * s : ZMod 2) = t) : 𝓞 K →+* ZMod 2 where
  toFun := residueLinearMap hmin hgen t s
  map_one' := by
    simpa using residueLinearMap_apply hmin hgen t s 1 0 0
  map_mul' := residueLinearMap_mul t s hts
  map_zero' := map_zero _
  map_add' := map_add _

private theorem residueHom_apply (t s : ℤ) (hts : (t * s : ZMod 2) = t) (x : 𝓞 K) :
    residueHom hmin hgen t s hts x = residueLinearMap hmin hgen t s x :=
  rfl

private theorem ker_residueHom (t s : ℤ) (hts : (t * s : ZMod 2) = t) :
    RingHom.ker (residueHom hmin hgen t s hts) =
      span {2, θ - t, dedekindBeta (dedekindCubic_relation hmin) - s} := by
  set β := dedekindBeta (dedekindCubic_relation hmin)
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, residueHom_apply] at hx
    obtain ⟨a, b, c, rfl⟩ := exists_eq_add_mul_add_mul hmin hgen x
    rw [residueLinearMap_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨k, hk⟩ := hx
    have hx : (a : 𝓞 K) + b * θ + c * β = k * 2 + b * (θ - t) + c * (β - s) := by
      have hk' : ((a + b * t + c * s : ℤ) : 𝓞 K) = 2 * k := by
        rw [hk]
        push_cast
        ring
      push_cast at hk'
      linear_combination hk'
    rw [hx]
    refine add_mem (add_mem (mul_mem_left _ _ (subset_span ?_))
      (mul_mem_left _ _ (subset_span ?_))) (mul_mem_left _ _ (subset_span ?_)) <;> simp
  · rw [span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, RingHom.mem_ker, residueHom_apply]
    rcases hx with rfl | rfl | rfl
    · have h := residueLinearMap_apply hmin hgen t s 2 0 0
      simp only [Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero] at h
      rw [h]
      decide
    · simpa [sub_eq_add_neg, add_comm] using residueLinearMap_apply hmin hgen t s (-t) 1 0
    · simpa [sub_eq_add_neg, add_comm] using residueLinearMap_apply hmin hgen t s (-s) 0 1

private theorem residueHom_theta (t s : ℤ) (hts : (t * s : ZMod 2) = t) :
    residueHom hmin hgen t s hts θ = t := by
  simpa [residueHom_apply] using residueLinearMap_apply hmin hgen t s 0 1 0

private theorem residueHom_beta (t s : ℤ) (hts : (t * s : ZMod 2) = t) :
    residueHom hmin hgen t s hts (dedekindBeta (dedekindCubic_relation hmin)) = s := by
  simpa [residueHom_apply] using residueLinearMap_apply hmin hgen t s 0 0 1

end Residue

/-! ### The three primes above `2` -/

include hmin hgen

private theorem dedekindPrimeOne_eq_ker :
    dedekindPrimeOne (dedekindCubic_relation hmin) =
      RingHom.ker (residueHom hmin hgen 0 0 (by simp)) := by
  rw [ker_residueHom, dedekindPrimeOne]
  simp

private theorem dedekindPrimeTwo_eq_ker :
    dedekindPrimeTwo (dedekindCubic_relation hmin) =
      RingHom.ker (residueHom hmin hgen 0 1 (by simp)) := by
  rw [ker_residueHom, dedekindPrimeTwo]
  simp

private theorem dedekindPrimeThree_eq_ker :
    dedekindPrimeThree (dedekindCubic_relation hmin) =
      RingHom.ker (residueHom hmin hgen 1 1 (by simp)) := by
  rw [ker_residueHom, dedekindPrimeThree]
  simp

/-- The residue ring of `(2, θ, β)` is `ZMod 2`: the reduction sends `θ ↦ 0` and `β ↦ 0`, see
`dedekindPrimeOneQuotEquiv_mk`. -/
def dedekindPrimeOneQuotEquiv :
    𝓞 K ⧸ dedekindPrimeOne (dedekindCubic_relation hmin) ≃+* ZMod 2 :=
  (quotEquivOfEq (dedekindPrimeOne_eq_ker hmin hgen)).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))

/-- The residue ring of `(2, θ, β - 1)` is `ZMod 2`: the reduction sends `θ ↦ 0` and `β ↦ 1`,
see `dedekindPrimeTwoQuotEquiv_mk`. -/
def dedekindPrimeTwoQuotEquiv :
    𝓞 K ⧸ dedekindPrimeTwo (dedekindCubic_relation hmin) ≃+* ZMod 2 :=
  (quotEquivOfEq (dedekindPrimeTwo_eq_ker hmin hgen)).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))

/-- The residue ring of `(2, θ - 1, β - 1)` is `ZMod 2`: the reduction sends `θ ↦ 1` and
`β ↦ 1`, see `dedekindPrimeThreeQuotEquiv_mk`. -/
def dedekindPrimeThreeQuotEquiv :
    𝓞 K ⧸ dedekindPrimeThree (dedekindCubic_relation hmin) ≃+* ZMod 2 :=
  (quotEquivOfEq (dedekindPrimeThree_eq_ker hmin hgen)).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))

/-- Reduction modulo `(2, θ, β)` sends `θ` to `0`. -/
@[simp] theorem dedekindPrimeOneQuotEquiv_mk_theta :
    dedekindPrimeOneQuotEquiv hmin hgen (Ideal.Quotient.mk _ θ) = 0 := by
  simp only [dedekindPrimeOneQuotEquiv, RingEquiv.trans_apply, quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueHom_theta]
  simp

/-- Reduction modulo `(2, θ, β)` sends `β` to `0`. -/
@[simp] theorem dedekindPrimeOneQuotEquiv_mk_beta :
    dedekindPrimeOneQuotEquiv hmin hgen
        (Ideal.Quotient.mk _ (dedekindBeta (dedekindCubic_relation hmin))) = 0 := by
  simp only [dedekindPrimeOneQuotEquiv, RingEquiv.trans_apply, quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueHom_beta]
  simp

/-- Reduction modulo `(2, θ, β)` sends `a + bθ + cβ` to `a`. -/
theorem dedekindPrimeOneQuotEquiv_mk (a b c : ℤ) :
    dedekindPrimeOneQuotEquiv hmin hgen
        (Ideal.Quotient.mk _ (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin))) =
      (a : ZMod 2) := by
  simp only [map_add, map_mul, map_intCast, dedekindPrimeOneQuotEquiv_mk_theta,
    dedekindPrimeOneQuotEquiv_mk_beta]
  ring

/-- An algebraic integer `a + bθ + cβ` lies in `(2, θ, β)` exactly when `2 ∣ a`. -/
@[simp] theorem mem_dedekindPrimeOne_iff (a b c : ℤ) :
    (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin) : 𝓞 K) ∈
        dedekindPrimeOne (dedekindCubic_relation hmin) ↔ 2 ∣ a := by
  rw [← Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (dedekindPrimeOneQuotEquiv hmin hgen).injective,
    dedekindPrimeOneQuotEquiv_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- Reduction modulo `(2, θ, β - 1)` sends `θ` to `0`. -/
@[simp] theorem dedekindPrimeTwoQuotEquiv_mk_theta :
    dedekindPrimeTwoQuotEquiv hmin hgen (Ideal.Quotient.mk _ θ) = 0 := by
  simp only [dedekindPrimeTwoQuotEquiv, RingEquiv.trans_apply, quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueHom_theta]
  simp

/-- Reduction modulo `(2, θ, β - 1)` sends `β` to `1`. -/
@[simp] theorem dedekindPrimeTwoQuotEquiv_mk_beta :
    dedekindPrimeTwoQuotEquiv hmin hgen
        (Ideal.Quotient.mk _ (dedekindBeta (dedekindCubic_relation hmin))) = 1 := by
  simp only [dedekindPrimeTwoQuotEquiv, RingEquiv.trans_apply, quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueHom_beta]
  simp

/-- Reduction modulo `(2, θ, β - 1)` sends `a + bθ + cβ` to `a + c`. -/
theorem dedekindPrimeTwoQuotEquiv_mk (a b c : ℤ) :
    dedekindPrimeTwoQuotEquiv hmin hgen
        (Ideal.Quotient.mk _ (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin))) =
      ((a + c : ℤ) : ZMod 2) := by
  simp only [map_add, map_mul, map_intCast, dedekindPrimeTwoQuotEquiv_mk_theta,
    dedekindPrimeTwoQuotEquiv_mk_beta]
  push_cast
  ring

/-- An algebraic integer `a + bθ + cβ` lies in `(2, θ, β - 1)` exactly when `2 ∣ a + c`. -/
@[simp] theorem mem_dedekindPrimeTwo_iff (a b c : ℤ) :
    (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin) : 𝓞 K) ∈
        dedekindPrimeTwo (dedekindCubic_relation hmin) ↔ 2 ∣ a + c := by
  rw [← Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (dedekindPrimeTwoQuotEquiv hmin hgen).injective,
    dedekindPrimeTwoQuotEquiv_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- Reduction modulo `(2, θ - 1, β - 1)` sends `θ` to `1`. -/
@[simp] theorem dedekindPrimeThreeQuotEquiv_mk_theta :
    dedekindPrimeThreeQuotEquiv hmin hgen (Ideal.Quotient.mk _ θ) = 1 := by
  simp only [dedekindPrimeThreeQuotEquiv, RingEquiv.trans_apply, quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueHom_theta]
  simp

/-- Reduction modulo `(2, θ - 1, β - 1)` sends `β` to `1`. -/
@[simp] theorem dedekindPrimeThreeQuotEquiv_mk_beta :
    dedekindPrimeThreeQuotEquiv hmin hgen
        (Ideal.Quotient.mk _ (dedekindBeta (dedekindCubic_relation hmin))) = 1 := by
  simp only [dedekindPrimeThreeQuotEquiv, RingEquiv.trans_apply, quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueHom_beta]
  simp

/-- Reduction modulo `(2, θ - 1, β - 1)` sends `a + bθ + cβ` to `a + b + c`. -/
theorem dedekindPrimeThreeQuotEquiv_mk (a b c : ℤ) :
    dedekindPrimeThreeQuotEquiv hmin hgen
        (Ideal.Quotient.mk _ (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin))) =
      ((a + b + c : ℤ) : ZMod 2) := by
  simp only [map_add, map_mul, map_intCast, dedekindPrimeThreeQuotEquiv_mk_theta,
    dedekindPrimeThreeQuotEquiv_mk_beta]
  push_cast
  ring

/-- An algebraic integer `a + bθ + cβ` lies in `(2, θ - 1, β - 1)` exactly when `2 ∣ a + b + c`. -/
@[simp] theorem mem_dedekindPrimeThree_iff (a b c : ℤ) :
    (a + b * θ + c * dedekindBeta (dedekindCubic_relation hmin) : 𝓞 K) ∈
        dedekindPrimeThree (dedekindCubic_relation hmin) ↔ 2 ∣ a + b + c := by
  rw [← Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (dedekindPrimeThreeQuotEquiv hmin hgen).injective,
    dedekindPrimeThreeQuotEquiv_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- The ideal `(2, θ, β)` is maximal. -/
theorem isMaximal_dedekindPrimeOne :
    (dedekindPrimeOne (dedekindCubic_relation hmin)).IsMaximal :=
  Quotient.maximal_of_isField _
    ((dedekindPrimeOneQuotEquiv hmin hgen).toMulEquiv.isField (Field.toIsField _))

/-- The ideal `(2, θ, β - 1)` is maximal. -/
theorem isMaximal_dedekindPrimeTwo :
    (dedekindPrimeTwo (dedekindCubic_relation hmin)).IsMaximal :=
  Quotient.maximal_of_isField _
    ((dedekindPrimeTwoQuotEquiv hmin hgen).toMulEquiv.isField (Field.toIsField _))

/-- The ideal `(2, θ - 1, β - 1)` is maximal. -/
theorem isMaximal_dedekindPrimeThree :
    (dedekindPrimeThree (dedekindCubic_relation hmin)).IsMaximal :=
  Quotient.maximal_of_isField _
    ((dedekindPrimeThreeQuotEquiv hmin hgen).toMulEquiv.isField (Field.toIsField _))

/-- The prime `(2, θ, β)` lies over `2`. -/
theorem liesOver_dedekindPrimeOne :
    (dedekindPrimeOne (dedekindCubic_relation hmin)).LiesOver (span {(2 : ℤ)}) :=
  (liesOver_span_iff (isMaximal_dedekindPrimeOne hmin hgen).ne_top Int.prime_two).mpr
    (subset_span (by simp))

/-- The prime `(2, θ, β - 1)` lies over `2`. -/
theorem liesOver_dedekindPrimeTwo :
    (dedekindPrimeTwo (dedekindCubic_relation hmin)).LiesOver (span {(2 : ℤ)}) :=
  (liesOver_span_iff (isMaximal_dedekindPrimeTwo hmin hgen).ne_top Int.prime_two).mpr
    (subset_span (by simp))

/-- The prime `(2, θ - 1, β - 1)` lies over `2`. -/
theorem liesOver_dedekindPrimeThree :
    (dedekindPrimeThree (dedekindCubic_relation hmin)).LiesOver (span {(2 : ℤ)}) :=
  (liesOver_span_iff (isMaximal_dedekindPrimeThree hmin hgen).ne_top Int.prime_two).mpr
    (subset_span (by simp))

/-- The prime `(2, θ, β)` has absolute norm `2`: its residue field has two elements. -/
@[simp] theorem absNorm_dedekindPrimeOne :
    absNorm (dedekindPrimeOne (dedekindCubic_relation hmin)) = 2 := by
  rw [absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (dedekindPrimeOneQuotEquiv hmin hgen).toEquiv, Nat.card_zmod]

/-- The prime `(2, θ, β - 1)` has absolute norm `2`: its residue field has two elements. -/
@[simp] theorem absNorm_dedekindPrimeTwo :
    absNorm (dedekindPrimeTwo (dedekindCubic_relation hmin)) = 2 := by
  rw [absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (dedekindPrimeTwoQuotEquiv hmin hgen).toEquiv, Nat.card_zmod]

/-- The prime `(2, θ - 1, β - 1)` has absolute norm `2`: its residue field has two elements. -/
@[simp] theorem absNorm_dedekindPrimeThree :
    absNorm (dedekindPrimeThree (dedekindCubic_relation hmin)) = 2 := by
  rw [absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (dedekindPrimeThreeQuotEquiv hmin hgen).toEquiv, Nat.card_zmod]

/-- The prime `(2, θ, β)` is nonzero. -/
theorem dedekindPrimeOne_ne_bot : dedekindPrimeOne (dedekindCubic_relation hmin) ≠ ⊥ :=
  ne_of_apply_ne absNorm (by rw [absNorm_dedekindPrimeOne hmin hgen, absNorm_bot]; decide)

/-- The prime `(2, θ, β - 1)` is nonzero. -/
theorem dedekindPrimeTwo_ne_bot : dedekindPrimeTwo (dedekindCubic_relation hmin) ≠ ⊥ :=
  ne_of_apply_ne absNorm (by rw [absNorm_dedekindPrimeTwo hmin hgen, absNorm_bot]; decide)

/-- The prime `(2, θ - 1, β - 1)` is nonzero. -/
theorem dedekindPrimeThree_ne_bot : dedekindPrimeThree (dedekindCubic_relation hmin) ≠ ⊥ :=
  ne_of_apply_ne absNorm (by rw [absNorm_dedekindPrimeThree hmin hgen, absNorm_bot]; decide)

/-- The primes `(2, θ, β)` and `(2, θ, β - 1)` are distinct. -/
theorem dedekindPrimeOne_ne_dedekindPrimeTwo :
    dedekindPrimeOne (dedekindCubic_relation hmin) ≠
      dedekindPrimeTwo (dedekindCubic_relation hmin) := by
  intro h
  have hmem : dedekindBeta (dedekindCubic_relation hmin) ∈
      dedekindPrimeOne (dedekindCubic_relation hmin) :=
    subset_span (by simp)
  rw [h, dedekindPrimeTwo_eq_ker hmin hgen, RingHom.mem_ker, residueHom_beta] at hmem
  simp at hmem

/-- The primes `(2, θ, β)` and `(2, θ - 1, β - 1)` are distinct. -/
theorem dedekindPrimeOne_ne_dedekindPrimeThree :
    dedekindPrimeOne (dedekindCubic_relation hmin) ≠
      dedekindPrimeThree (dedekindCubic_relation hmin) := by
  intro h
  have hmem : θ ∈ dedekindPrimeOne (dedekindCubic_relation hmin) := subset_span (by simp)
  rw [h, dedekindPrimeThree_eq_ker hmin hgen, RingHom.mem_ker, residueHom_theta] at hmem
  simp at hmem

/-- The primes `(2, θ, β - 1)` and `(2, θ - 1, β - 1)` are distinct. -/
theorem dedekindPrimeTwo_ne_dedekindPrimeThree :
    dedekindPrimeTwo (dedekindCubic_relation hmin) ≠
      dedekindPrimeThree (dedekindCubic_relation hmin) := by
  intro h
  have hmem : θ ∈ dedekindPrimeTwo (dedekindCubic_relation hmin) := subset_span (by simp)
  rw [h, dedekindPrimeThree_eq_ker hmin hgen, RingHom.mem_ker, residueHom_theta] at hmem
  simp at hmem

/-! ### The splitting of `2` -/

private instance : (span {(2 : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime 2

private theorem ncard_dedekindPrimes :
    ({dedekindPrimeOne (dedekindCubic_relation hmin),
      dedekindPrimeTwo (dedekindCubic_relation hmin),
      dedekindPrimeThree (dedekindCubic_relation hmin)} : Set (Ideal (𝓞 K))).ncard = 3 :=
  Set.ncard_eq_three.mpr ⟨_, _, _, dedekindPrimeOne_ne_dedekindPrimeTwo hmin hgen,
    dedekindPrimeOne_ne_dedekindPrimeThree hmin hgen,
    dedekindPrimeTwo_ne_dedekindPrimeThree hmin hgen, rfl⟩

/-- The primes of `𝓞 K` above `2` are exactly `(2, θ, β)`, `(2, θ, β - 1)` and
`(2, θ - 1, β - 1)`. -/
theorem dedekindCubic_primesOver_two_eq :
    (span {(2 : ℤ)}).primesOver (𝓞 K) =
      {dedekindPrimeOne (dedekindCubic_relation hmin),
        dedekindPrimeTwo (dedekindCubic_relation hmin),
        dedekindPrimeThree (dedekindCubic_relation hmin)} := by
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨(isMaximal_dedekindPrimeOne hmin hgen).isPrime, liesOver_dedekindPrimeOne hmin hgen⟩,
      ⟨(isMaximal_dedekindPrimeTwo hmin hgen).isPrime, liesOver_dedekindPrimeTwo hmin hgen⟩,
      ⟨(isMaximal_dedekindPrimeThree hmin hgen).isPrime, liesOver_dedekindPrimeThree hmin hgen⟩⟩
  · rw [ncard_dedekindPrimes hmin hgen, ← dedekindCubic_finrank_eq_three hmin hgen,
      ← RingOfIntegers.rank K]
    exact RamificationInertia.ncard_primesOver_le_finrank _

/-- **The prime `2` splits completely in Dedekind's cubic field**: there are `[K : ℚ]` primes
above it. -/
theorem dedekindCubic_ncard_primesOver_two_eq_finrank :
    ((span {(2 : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K := by
  rw [dedekindCubic_primesOver_two_eq hmin hgen, ncard_dedekindPrimes hmin hgen,
    dedekindCubic_finrank_eq_three hmin hgen]

open RamificationInertia in
/-- Every prime above `2` is unramified with residue degree one. -/
theorem dedekindCubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(2 : ℤ)}).primesOver (𝓞 K)) :
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
  have hPprime : P.IsPrime := hP.1
  have hPlies : P.LiesOver (span {(2 : ℤ)}) := hP.2
  refine ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
    (span {(2 : ℤ)}) P ?_
  rw [dedekindCubic_ncard_primesOver_two_eq_finrank hmin hgen, RingOfIntegers.rank K]

/-- **Dedekind's factorization of `2`**: `(2) = (2, θ, β) · (2, θ, β - 1) · (2, θ - 1, β - 1)`. -/
theorem dedekindCubic_map_span_two_eq :
    (span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
      dedekindPrimeOne (dedekindCubic_relation hmin) *
        dedekindPrimeTwo (dedekindCubic_relation hmin) *
        dedekindPrimeThree (dedekindCubic_relation hmin) := by
  classical
  have hfin : ((span {(2 : ℤ)}).primesOver (𝓞 K)).toFinset =
      {dedekindPrimeOne (dedekindCubic_relation hmin),
        dedekindPrimeTwo (dedekindCubic_relation hmin),
        dedekindPrimeThree (dedekindCubic_relation hmin)} := by
    ext P
    simp only [Set.mem_toFinset, dedekindCubic_primesOver_two_eq hmin hgen, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [map_algebraMap_eq_finsetProd_pow (by simp), Finset.prod_congr rfl fun P hP => by
    rw [(dedekindCubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one hmin hgen
      (Set.mem_toFinset.mp hP)).1, pow_one], hfin,
    Finset.prod_insert (by simp [dedekindPrimeOne_ne_dedekindPrimeTwo hmin hgen,
      dedekindPrimeOne_ne_dedekindPrimeThree hmin hgen]),
    Finset.prod_insert (by simp [dedekindPrimeTwo_ne_dedekindPrimeThree hmin hgen]),
    Finset.prod_singleton, mul_assoc]

/-! ### Non-monogenicity -/

/-- **`2` is a common index divisor of Dedekind's cubic field**: it divides the index of every
integral primitive element. There are three primes of residue degree one above `2`, but only
two monic polynomials of degree one over `𝔽₂`. -/
theorem dedekindCubic_isCommonIndexDivisor_two : IsCommonIndexDivisor 2 K := by
  refine isCommonIndexDivisor_of_ncard_lt_ncard 2 (d := 1) ?_
  have huniv : primesOverOfInertiaDeg K 2 1 = Set.univ := by
    ext ⟨P, hP⟩
    simp only [mem_primesOverOfInertiaDeg_iff, Set.mem_univ, iff_true]
    rw [Nat.cast_ofNat] at hP
    exact (dedekindCubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one hmin hgen hP).2
  rw [ncard_monicIrreduciblesOfDegree_one, Nat.card_zmod, huniv, Set.ncard_univ,
    Nat.card_coe_set_eq, Nat.cast_ofNat, dedekindCubic_ncard_primesOver_two_eq_finrank hmin hgen,
    dedekindCubic_finrank_eq_three hmin hgen]
  norm_num

/-- **Dedekind's cubic field is not monogenic**: its ring of integers is not `ℤ[α]` for any
algebraic integer `α`. -/
theorem dedekindCubic_not_isMonogenic : ¬ IsMonogenic K := by
  rw [isMonogenic_iff_exists_index_eq_one]
  exact (dedekindCubic_isCommonIndexDivisor_two hmin hgen).not_exists_index_eq_one (by norm_num)

end TauCeti.NumberField

end
end
