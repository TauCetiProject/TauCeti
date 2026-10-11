/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.NumberTheory.QuadraticOrder.Basic
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
import TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger
public import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Nonsquare quadratic orders

For a nonsquare integer `D ≡ 0, 1 mod 4`, the rational quadratic algebra is a number field.
The subalgebra `ℤ[(D + √D)/2]` constructed in `QuadraticOrder/Basic` is therefore an actual
`GlobalNumberFields.NumberFieldOrder`, of discriminant `D`.

This order is maximal exactly when `D` is a fundamental discriminant. For a fundamental
`D`, the supplier's discriminant/index formula and Stickelberger's congruence force index one.
If `D` is not fundamental, a proper square factor `D = p²e` with `e ≡ 0, 1 mod 4` supplies
the integral element `(e + √D/p)/2` outside the order.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open QuadraticAlgebra

namespace TauCeti.QuadraticOrder

/-- The integral quadratic order in the nonsquare number field. -/
noncomputable def numberFieldOrder (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] :
    GlobalNumberFields.NumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) where
  toSubalgebra := toSubalgebra D hD
  finite := inferInstance
  spans := span_toSubalgebra_eq_top D hD

/-- The field order has the subalgebra constructed in the rational quadratic algebra. -/
@[simp] theorem numberFieldOrder_toSubalgebra (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] : (numberFieldOrder D hD).toSubalgebra = toSubalgebra D hD := (rfl)

/-- The discriminant of the field order is its defining integer. -/
@[simp] theorem numberFieldOrder_discr (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] : (numberFieldOrder D hD).discr = D := by
  rw [← (numberFieldOrder D hD).discr_eq_discr (basis D hD)]
  exact discr_basis D hD

/-- A fundamental-discriminant order is maximal. -/
private theorem numberFieldOrder_eq_maximal_of_isFundamentalDiscr (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] (hfund : Int.IsFundamentalDiscr D) :
    numberFieldOrder D hD =
      GlobalNumberFields.maximalNumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) := by
  rw [← GlobalNumberFields.NumberFieldOrder.index_eq_one_iff]
  by_contra hidx
  obtain ⟨p, hp, hpidx⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hidx
  obtain ⟨n, hn⟩ := hpidx
  have hdisc := (numberFieldOrder D hD).discr_eq_index_sq_mul
  rw [numberFieldOrder_discr, hn, Nat.cast_mul, mul_pow, mul_assoc] at hdisc
  apply (Int.isFundamentalDiscr_iff_forall_prime.mp hfund).2 p hp
  refine ⟨(n : ℤ) ^ 2 * NumberField.discr (QuadraticAlgebra ℚ (D : ℚ) 0), hdisc, ?_⟩
  rw [Int.mul_emod, Int.sq_emod_four]
  rcases TauCeti.NumberField.discr_emod_four_eq_zero_or_one
      (QuadraticAlgebra ℚ (D : ℚ) 0) with hd | hd
  · simp [hd]
  · simp only [hd, mul_one]
    omega

/-- A nonfundamental discriminant produces a proper suborder of the ring of integers. -/
private theorem numberFieldOrder_ne_maximal_of_not_isFundamentalDiscr (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] (hfund : ¬ Int.IsFundamentalDiscr D) :
    numberFieldOrder D hD ≠
      GlobalNumberFields.maximalNumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) := by
  have hfactor : ¬ ∀ p : ℕ, p.Prime →
      ¬ ∃ e : ℤ, D = (p : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) :=
    fun h ↦ hfund (Int.isFundamentalDiscr_iff_forall_prime.mpr ⟨hD, h⟩)
  push Not at hfactor
  obtain ⟨p, hp, e, hDe, he⟩ := hfactor
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hDeQ : (D : ℚ) = (p : ℚ) ^ 2 * (e : ℚ) := by exact_mod_cast hDe
  let φ : QuadraticAlgebra ℚ (e : ℚ) 0 →ₐ[ℚ] QuadraticAlgebra ℚ (D : ℚ) 0 :=
    QuadraticAlgebra.changeGenerator (D : ℚ) 0 (p : ℚ)⁻¹ 0
      (by simp only [mul_zero, sub_zero]; rw [hDeQ]; field_simp; ring)
      (by simp)
  have hgen : IsIntegral ℤ (generator e) := by
    simpa only [coe_basis_one] using QuadraticOrder.isIntegral e he (basis e he 1)
  have hint : IsIntegral ℤ (φ (generator e)) := hgen.map (φ.restrictScalars ℤ)
  have hnotmem : φ (generator e) ∉ toSubalgebra D hD := by
    intro hmem
    obtain ⟨m, n, hmn⟩ := (mem_toSubalgebra_iff D hD _).mp hmem
    have hi := congrArg QuadraticAlgebra.im hmn
    have hnQ : (p : ℚ) * (n : ℚ) = 1 := by
      have hn' : (p : ℚ)⁻¹ = (n : ℚ) := by
        simpa [φ, mul_comm] using hi
      rw [← hn', mul_inv_cancel₀ hpQ]
    have hnZ : (p : ℤ) * n = 1 := by exact_mod_cast hnQ
    have hu : IsUnit (p : ℤ) := isUnit_iff_dvd_one.mpr ⟨n, hnZ.symm⟩
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact hp.ne_one hu
  intro hmax
  apply hnotmem
  have hmem : φ (generator e) ∈ (numberFieldOrder D hD).toSubalgebra := by
    rw [hmax, GlobalNumberFields.maximalNumberFieldOrder_toSubalgebra,
      mem_integralClosure_iff]
    exact hint
  exact hmem

/-- The quadratic field order is maximal exactly when its discriminant is fundamental. -/
@[simp] theorem numberFieldOrder_eq_maximal_iff (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] :
    numberFieldOrder D hD =
      GlobalNumberFields.maximalNumberFieldOrder (QuadraticAlgebra ℚ (D : ℚ) 0) ↔
        Int.IsFundamentalDiscr D := by
  constructor
  · intro hmax
    by_contra hfund
    exact numberFieldOrder_ne_maximal_of_not_isFundamentalDiscr D hD hfund hmax
  · exact numberFieldOrder_eq_maximal_of_isFundamentalDiscr D hD

end TauCeti.QuadraticOrder


